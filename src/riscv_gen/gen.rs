use koopa::ir::{BasicBlock, Function, Program, Type, Value};

use crate::{
  koopa_gen::gen::{FetchValueType, KoopaValueDataToString, TypeUtils},
  riscv_gen::riscv_isa::{Directive, RiscvAsmLine},
  utils::new_tmp_idx,
};

use super::{
  frame_manager::{CrazySpiller, FrameManager, RtValue},
  riscv_isa::{Imm, Imm12, Inst, Label, LabelKind, Reg, RiscvProg, FUNC_ARG_REGS},
};

pub struct RiscvGen<'a> {
  riscv_prog: RiscvProg,
  koopa_prog: &'a Program,
  fmnger: Option<FrameManager<'a, CrazySpiller>>,
}

impl<'a> RiscvGen<'a> {
  pub fn new(prog: &'a Program) -> Self {
    Type::set_ptr_size(4);

    Self {
      riscv_prog: RiscvProg::new(),
      koopa_prog: prog,
      fmnger: None,
    }
  }

  pub fn gen(mut self) -> RiscvProg {
    let prog = self.koopa_prog;

    for global_alloc in prog.inst_layout() {
      self.gen_global_alloc(prog.borrow_value(global_alloc.clone()));
    }

    for (fhandle, fdata) in prog.funcs() {
      // skip external functions that do not have an entry block.
      if fdata.layout().bbs().is_empty() {
        continue;
      }

      self.gen_on_func(fhandle, fdata);
    }

    return self.riscv_prog;
  }

  fn gen_on_func(&mut self, fhandle: &Function, fdata: &'a koopa::ir::FunctionData) {
    self.riscv_prog.extend([
      RiscvAsmLine::Diretive(Directive::Text),
      RiscvAsmLine::Diretive(Directive::Globl(fdata.name()[1..].to_string())),
      RiscvAsmLine::Label(Label::new(
        fdata.name()[1..].to_string(),
        LabelKind::NativeFunc,
      )),
    ]);

    self.fmnger = Some(FrameManager::<CrazySpiller>::new(
      self.koopa_prog,
      fdata,
      Reg::all()
        .iter()
        .filter(|r| ![Reg::Zero, Reg::Ra, Reg::Sp, Reg::T0, Reg::T1, Reg::A0].contains(r))
        .cloned()
        .collect::<Vec<_>>()
        .as_slice(),
    ));

    // Prologue. Move Sp and save all callee-saved registers.
    let flen = self.fmnger().frame_len;
    self.riscv_prog.more_insts([
      Inst::Li(Reg::T0, Imm::new(flen)),
      Inst::Sub(Reg::Sp, Reg::Sp, Reg::T0),
    ]);

    for reg in self.fmnger().need_callee_saved_regs() {
      let reg_loc = self.fmnger().reg_buffer_loc(&reg);
      self.store_reg_to(&reg, &reg_loc, Some(&Reg::T0));
    }

    // basic block translation
    for (bbhandle, bbdata) in fdata.layout().bbs() {
      self
        .riscv_prog
        .append_label(self.bb_label(fhandle, bbhandle));

      for (inst, _inst_node) in bbdata.insts() {
        let idata = fdata.dfg().value(*inst);
        self.riscv_prog.comment(idata.to_string());
        match idata.kind() {
          koopa::ir::ValueKind::Alloc(_) => {}
          koopa::ir::ValueKind::Load(load) => {
            let dest = self.rt_val(inst, None);
            let src_ptr = self.rt_val(&load.src(), Some(Reg::T0));
            let sz = idata.ty().size();
            if sz != 4 {
              unimplemented!("only support 4 bytes load");
            }

            // load the src ptr into T0
            let src_reg = self.deref_rtval(src_ptr, Some(Reg::T0));

            // store the value to dest
            // use T1 to secure src_reg == T0
            self.store_reg_to(&src_reg, &dest, Some(&Reg::T1));
          }
          koopa::ir::ValueKind::Store(store) => {
            let src = store.value();
            let dst_ptr = store.dest();

            let src_data = fdata.dfg().value(src);
            let dst_ptr_type = dst_ptr.get_type(&self.koopa_prog, self.func_data());

            let ty = dst_ptr_type.ptr_inner();
            assert!(src_data.ty().eq(&ty), "store type mismatch");
            if ty.size() != 4 {
              unimplemented!("only support 4 bytes store");
            }

            let src_reg = self.find_rtval_and_get_reg(src, Reg::T0);

            // T0 may be occupied by src_reg now. Switch to T1.
            let dst_loc = self.rt_val(&dst_ptr, Some(Reg::T1));

            // use T1 to secure src_reg == T0
            self.store_reg_to_ref(src_reg, dst_loc, Some(&Reg::T1));
          }
          koopa::ir::ValueKind::GetPtr(getptr) => {
            let idx_loc = self.rt_val(&getptr.index(), Some(Reg::T0));
            let size_unit = getptr
              .src()
              .get_type(&self.koopa_prog, self.func_data())
              .ptr_inner()
              .size() as i32;
            self.advance_ptr(
              &getptr.src(),
              size_unit,
              idx_loc,
              self.fmnger().local_value(inst),
            );
          }
          koopa::ir::ValueKind::GetElemPtr(getelem) => {
            let idx_loc = self.rt_val(&getelem.index(), Some(Reg::T0));
            let size_unit = getelem
              .src()
              .get_type(&self.koopa_prog, self.func_data())
              .ptr_inner()
              .array_inner() // Think about *[[i32, 3], 4] -> [i32, 3]
              .size() as i32;

            self.advance_ptr(
              &getelem.src(),
              size_unit,
              idx_loc,
              self.fmnger().local_value(inst),
            );
          }
          koopa::ir::ValueKind::Binary(binary) => {
            let lhs_reg = self.find_rtval_and_get_reg(binary.lhs(), Reg::T0);
            let rhs_reg = self.find_rtval_and_get_reg(binary.rhs(), Reg::T1);
            // Note: T0 and T1 may be occupied by lhs_reg and rhs_reg now.

            // the result is put to lhs_reg
            match binary.op() {
              koopa::ir::BinaryOp::NotEq => self.riscv_prog.more_insts([
                Inst::Xor(lhs_reg, lhs_reg, rhs_reg),
                // if lhs != rhs, then lhs != 0
                Inst::Snez(lhs_reg, lhs_reg),
                // In such case, lhs = 1 now.
              ]),
              koopa::ir::BinaryOp::Eq => self.riscv_prog.more_insts([
                Inst::Xor(lhs_reg, lhs_reg, rhs_reg),
                Inst::Seqz(lhs_reg, lhs_reg),
              ]),
              koopa::ir::BinaryOp::Gt => self
                .riscv_prog
                .more_insts([Inst::Sgt(lhs_reg, lhs_reg, rhs_reg)]),
              koopa::ir::BinaryOp::Lt => self
                .riscv_prog
                .more_insts([Inst::Slt(lhs_reg, lhs_reg, rhs_reg)]),
              koopa::ir::BinaryOp::Ge => self.riscv_prog.more_insts([
                Inst::Slt(lhs_reg, lhs_reg, rhs_reg),
                Inst::Xori(lhs_reg, lhs_reg, Imm12::try_from(1).unwrap()),
              ]),
              koopa::ir::BinaryOp::Le => self.riscv_prog.more_insts([
                Inst::Sgt(lhs_reg, lhs_reg, rhs_reg),
                Inst::Xori(lhs_reg, lhs_reg, Imm12::try_from(1).unwrap()),
              ]),
              koopa::ir::BinaryOp::Add => self
                .riscv_prog
                .append_inst(Inst::Add(lhs_reg, lhs_reg, rhs_reg)),
              koopa::ir::BinaryOp::Sub => self
                .riscv_prog
                .append_inst(Inst::Sub(lhs_reg, lhs_reg, rhs_reg)),
              koopa::ir::BinaryOp::Mul => self
                .riscv_prog
                .append_inst(Inst::Mul(lhs_reg, lhs_reg, rhs_reg)),
              koopa::ir::BinaryOp::Div => self
                .riscv_prog
                .append_inst(Inst::Div(lhs_reg, lhs_reg, rhs_reg)),
              koopa::ir::BinaryOp::Mod => self
                .riscv_prog
                .append_inst(Inst::Rem(lhs_reg, lhs_reg, rhs_reg)),
              koopa::ir::BinaryOp::And => self
                .riscv_prog
                .append_inst(Inst::And(lhs_reg, lhs_reg, rhs_reg)),
              koopa::ir::BinaryOp::Or => self
                .riscv_prog
                .append_inst(Inst::Or(lhs_reg, lhs_reg, rhs_reg)),
              koopa::ir::BinaryOp::Xor => self
                .riscv_prog
                .append_inst(Inst::Xor(lhs_reg, lhs_reg, rhs_reg)),
              koopa::ir::BinaryOp::Shl => self
                .riscv_prog
                .append_inst(Inst::Sll(lhs_reg, lhs_reg, rhs_reg)),
              koopa::ir::BinaryOp::Shr => self
                .riscv_prog
                .append_inst(Inst::Srl(lhs_reg, lhs_reg, rhs_reg)),
              koopa::ir::BinaryOp::Sar => self
                .riscv_prog
                .append_inst(Inst::Sra(lhs_reg, lhs_reg, rhs_reg)),
            }

            self.store_reg_to(
              &lhs_reg,
              &self.fmnger().local_value(inst),
              Some(&Reg::T1), // lhs_reg will not be T1.
            );
          }
          koopa::ir::ValueKind::Branch(branch) => {
            let cond_reg = self.find_rtval_and_get_reg(branch.cond(), Reg::T0);
            let true_label = Label::new(format!("case1_{}", new_tmp_idx()), LabelKind::BranchTmp);

            // Riscv Branch has range limitation.
            // We need to make sure branch only jumps locally.
            self.riscv_prog.more_insts([
              Inst::Bnez(cond_reg, true_label.clone()),
              Inst::J(self.bb_label(fhandle, &branch.false_bb())),
            ]);
            self.riscv_prog.append_label(true_label);
            self
              .riscv_prog
              .more_insts([Inst::J(self.bb_label(fhandle, &branch.true_bb()))])
          }

          koopa::ir::ValueKind::Jump(jmp) => self
            .riscv_prog
            .more_insts([Inst::J(self.bb_label(fhandle, &jmp.target()))]),

          koopa::ir::ValueKind::Call(call) => {
            // save caller-saved registers
            for reg in self.fmnger().need_caller_saved_regs() {
              self.store_reg_to(&reg, &self.fmnger().reg_buffer_loc(&reg), Some(&Reg::T0));
            }

            // prepare arguments
            for (idx, arg) in call.args().iter().enumerate() {
              let arg_reg = self.find_rtval_and_get_reg(*arg, Reg::T0);
              if FUNC_ARG_REGS.contains(&arg_reg) {
                unimplemented!(
                  "Such a src arg_reg, let's say A0, reg may be covered by previous args setup."
                )
              }
              self.store_reg_to(&arg_reg, &self.fmnger().func_call_arg_rtval(idx), None);
              // The offset is small so we don't need temp.
            }

            // call

            if self
              .koopa_prog
              .func(call.callee())
              .layout()
              .bbs()
              .is_empty()
            {
              // foreign function.
              self.riscv_prog.more_insts([Inst::Call(Label::new(
                self.koopa_prog.func(call.callee()).name()[1..].to_string(),
                LabelKind::ForeignFunc,
              ))]);
            } else {
              self.riscv_prog.more_insts([Inst::Call(Label::new(
                self.koopa_prog.func(call.callee()).name()[1..].to_string(),
                LabelKind::NativeFunc,
              ))]);
            }

            // save return value to T0

            let mut has_retval = false;
            let mut ret_rtval = None;
            if self.fmnger().func_data().dfg().value(*inst).ty().is_i32() {
              has_retval = true;
              ret_rtval = Some(self.fmnger().local_value(inst));
              self.store_reg_to(&Reg::A0, &ret_rtval.unwrap(), Some(&Reg::T1));
            }

            // restore caller-saved registers
            for reg in self
              .fmnger()
              .active_reg
              .clone()
              .iter()
              .filter(|reg| reg.is_caller_saved())
            {
              if has_retval {
                if let RtValue::Reg(ret_reg) = ret_rtval.unwrap() {
                  if *reg == ret_reg {
                    // We don't restore this reg since it is covered by the return value.
                    continue;
                  }
                }
              }
              let load_reg = self.into_reg(self.fmnger().reg_buffer_loc(reg), *reg);
              assert!(load_reg == *reg);
            }
          }
          koopa::ir::ValueKind::Return(ret) => {
            if let Some(ret) = ret.value() {
              let ret_reg = self.find_rtval_and_get_reg(ret, Reg::A0);
              self.store_reg_to(&ret_reg, &RtValue::Reg(Reg::A0), None);
            }

            // Epilogue. Restore all callee-saved registers and move Sp.
            for reg in self.fmnger().need_callee_saved_regs() {
              let load_reg = self.into_reg(self.fmnger().reg_buffer_loc(&reg), reg);
              assert!(load_reg == reg);
            }

            self.riscv_prog.more_insts([
              Inst::Li(Reg::T0, Imm::new(self.fmnger().frame_len)),
              Inst::Add(Reg::Sp, Reg::Sp, Reg::T0),
            ]);

            self.riscv_prog.append_inst(Inst::Ret);
          }
          _ => panic!("gen_on_func: unexpected value kind"),
        }
      }
    }

    self.fmnger = None;
  }

  fn gen_global_alloc(&mut self, value: std::cell::Ref<'a, koopa::ir::entities::ValueData>) {
    self.riscv_prog.extend([
      RiscvAsmLine::Diretive(Directive::Data),
      RiscvAsmLine::Diretive(Directive::Globl(value.name().as_ref().unwrap().clone())),
      RiscvAsmLine::Label(Label::new(
        value.name().as_ref().unwrap().clone(),
        LabelKind::GlobalVar,
      )),
    ]);

    match value.kind() {
      koopa::ir::ValueKind::GlobalAlloc(alloc) => {
        let init_data = self.koopa_prog.borrow_value(alloc.init());
        let words = self.globl_value_to_words(init_data);
        for i in words {
          self.riscv_prog.append_directive(Directive::Word(i));
        }
      }
      _ => panic!("gen_global_alloc: unexpected value kind"),
    }
  }

  fn globl_value_to_words(
    &self,
    value: std::cell::Ref<'a, koopa::ir::entities::ValueData>,
  ) -> Vec<i32> {
    match value.kind() {
      koopa::ir::ValueKind::Integer(v) => vec![v.value()],
      koopa::ir::ValueKind::ZeroInit(_) => {
        let ty = value.ty();
        let size = ty.size();
        assert!(size % 4 == 0, "size must be multiple of 4");
        vec![0; size / 4]
      }
      koopa::ir::ValueKind::Undef(_) => unimplemented!(),
      koopa::ir::ValueKind::Aggregate(agg) => {
        let mut words = Vec::new();
        for elem in agg.elems() {
          let elem_data = self.koopa_prog.borrow_value(elem.clone());
          let elem_words = self.globl_value_to_words(elem_data);
          words.extend(elem_words);
        }
        words
      }
      _ => panic!("value_to_words: unexpected value kind"),
    }
  }

  fn bb_label(&self, fhandle: &Function, bbhandle: &BasicBlock) -> Label {
    Label::new(
      self
        .koopa_prog
        .func(*fhandle)
        .dfg()
        .bb(*bbhandle)
        .name()
        .clone()
        .unwrap()
        .as_str()[1..]
        .to_string(),
      LabelKind::BasicBlock {
        func_name: self.koopa_prog.func(*fhandle).name()[1..].to_string(),
      },
    )
  }

  /// Advance the pointer by `inner_size * idx` and store the result to `target`.
  fn advance_ptr(&mut self, ptr: &Value, size_unit: i32, idx: RtValue, target: RtValue) {
    let idx_reg = self.into_reg(idx, Reg::T1);
    // idx_reg maybe T1, or T0, or something else.

    let tmp_reg = if idx_reg != Reg::T0 { Reg::T0 } else { Reg::T1 };

    // ptr += inner_size * idx
    self.riscv_prog.more_insts([
      Inst::Li(tmp_reg, Imm::new(size_unit)),
      Inst::Mul(idx_reg, idx_reg, tmp_reg),
    ]);
    // Now idx_reg = inner_size * idx

    let ptr_reg = self.find_rtval_and_get_reg(*ptr, tmp_reg);
    assert!(ptr_reg != idx_reg);

    self
      .riscv_prog
      .append_inst(Inst::Add(ptr_reg, ptr_reg, idx_reg));
    // Now ptr_reg = ptr + inner_size * idx

    // ptr_reg maybe T0, or T1, or something else.
    // Secure tmp2_reg != ptr_reg in all cases.
    let tmp2_reg = if ptr_reg != Reg::T0 { Reg::T0 } else { Reg::T1 };
    self.store_reg_to(&ptr_reg, &target, Some(&tmp2_reg));
  }

  /// If the value is a global alloc or constant, then the result is loaded into `oncall_reg`.
  ///
  /// Side effect:
  /// oncall_reg may be occupied.
  fn rt_val(&mut self, val: &Value, may_used: Option<Reg>) -> RtValue {
    if val.is_global() {
      // It must be a global alloc.
      let vdata = self.koopa_prog.borrow_value(*val);
      let vkind = vdata.kind();
      assert!(vkind.is_global_alloc());
      let oncall_reg = may_used.unwrap();
      self.riscv_prog.append_inst(Inst::La(
        oncall_reg,
        Label::new(vdata.name().as_ref().unwrap().clone(), LabelKind::GlobalVar),
      ));
      return RtValue::Reg(oncall_reg);
    } else {
      return self.fmnger.as_ref().unwrap().local_value(val);
    };
  }

  fn fmnger(&self) -> &FrameManager<'a, CrazySpiller> {
    self.fmnger.as_ref().unwrap()
  }

  /// Take the value in RtValue into a reg.
  ///
  /// If the value lies in a register itself, the register will be returned.
  ///
  /// Otherwise, the value will be loaded into the given may_used registers.
  ///
  /// In mental model, programmer can assume that the may_used register is
  /// the register that is used to store the value.
  ///
  ///
  /// Side effect:
  /// oncall_reg may be occupied under such conditions:
  /// 1. The value is a stack offset or constant.
  /// 2. The value is on stack.
  #[must_use]
  pub(crate) fn into_reg(&mut self, src_loc: RtValue, may_used: Reg) -> Reg {
    match src_loc {
      RtValue::SpOffset(offset) => {
        self.riscv_prog.more_insts([
          Inst::Li(may_used, Imm::new(offset)),
          Inst::Add(may_used, Reg::Sp, may_used),
        ]);
        may_used
      }

      RtValue::Reg(reg) => reg,
      RtValue::Integer(v) => {
        self.riscv_prog.append_inst(Inst::Li(may_used, Imm::new(v)));
        may_used
      }

      RtValue::Stack(offset) => {
        if let Ok(offset) = Imm12::try_from(offset) {
          self
            .riscv_prog
            .more_insts([Inst::Lw(may_used, Reg::Sp, offset)])
        } else {
          self.riscv_prog.more_insts([
            Inst::Li(may_used, Imm::new(offset)),
            Inst::Add(may_used, Reg::Sp, may_used),
            Inst::Lw(may_used, may_used, Imm12::zero()),
          ]);
        }
        return may_used;
      }
      RtValue::RegRef(_) => panic!("into_reg: unexpected RtValue"),
    }
  }

  /// Store the value in the register to the given RtValue location.
  ///
  /// Need to promise:
  /// src != temp
  pub(crate) fn store_reg_to(&mut self, src: &Reg, dest: &RtValue, temp: Option<&Reg>) -> bool {
    match dest {
      RtValue::SpOffset(_) => panic!("store_reg_to: SpOffset is not supported"),
      RtValue::Reg(reg) => {
        if reg != src {
          self.riscv_prog.append_inst(Inst::Mv(*reg, *src));
        }
        return false;
      }
      RtValue::Integer(_) => panic!("store_reg_to: Const is not supported"),
      RtValue::Stack(ofs) => {
        if let Ok(ofs) = Imm12::try_from(*ofs) {
          self.riscv_prog.more_insts([Inst::Sw(*src, Reg::Sp, ofs)]);
          return false;
        } else {
          let temp = *temp.expect("store_reg_to: temp register is not provided");
          assert!(
            temp != *src,
            "store_reg_to: temp register should not be the same as src"
          );
          self.riscv_prog.more_insts([
            Inst::Li(temp, Imm::new(*ofs)),
            Inst::Add(temp, Reg::Sp, temp),
            Inst::Sw(*src, temp, Imm12::zero()),
          ]);
          return true;
        }
      }
      RtValue::RegRef(_) => panic!("store_reg_to: unexpected RtValue"),
    }
  }

  fn func_data(&self) -> &koopa::ir::FunctionData {
    return self.fmnger().func_data();
  }

  /// Dereference the RtValue to a register.
  ///
  /// Side effect:
  /// oncall may be messed up.
  fn deref_rtval(&mut self, src_ptr: RtValue, oncall: Option<Reg>) -> Reg {
    match src_ptr {
      RtValue::Integer(_) => panic!("deref_rtval: Const is not supported"),
      RtValue::SpOffset(ofs) => self.into_reg(RtValue::Stack(ofs), oncall.unwrap()),
      RtValue::Stack(ofs) => {
        let reg = self.into_reg(RtValue::Stack(ofs), oncall.unwrap());
        self
          .riscv_prog
          .more_insts([Inst::Lw(reg, reg, Imm12::zero())]);
        reg
      }
      RtValue::Reg(reg) => {
        self
          .riscv_prog
          .more_insts([Inst::Lw(reg, reg, Imm12::zero())]);
        reg
      }
      RtValue::RegRef(reg) => reg,
    }
  }

  /// Fetch value from src_reg and store it into *dst_loc.
  ///
  /// Side effect:
  /// oncall may be messed up.
  ///
  /// Need to promise:
  /// src_reg != oncall
  fn store_reg_to_ref(&mut self, src_reg: Reg, dst_loc: RtValue, oncall: Option<&Reg>) {
    match dst_loc {
      RtValue::Integer(_) => panic!("store_reg_to_ref: Const is not supported"),
      RtValue::SpOffset(ofs) => {
        self.store_reg_to(&src_reg, &RtValue::Stack(ofs), oncall);
      }
      RtValue::Reg(reg) => {
        self
          .riscv_prog
          .more_insts([Inst::Sw(src_reg, reg, Imm12::zero())]);
      }
      RtValue::Stack(ofs) => {
        let oncall = oncall.unwrap();
        assert!(src_reg != *oncall);
        let reg = self.into_reg(RtValue::Stack(ofs), *oncall);
        assert!(&reg == oncall);

        self
          .riscv_prog
          .more_insts([Inst::Sw(src_reg, *oncall, Imm12::zero())]);
      }
      RtValue::RegRef(reg) => {
        self.riscv_prog.more_insts([Inst::Mv(src_reg, reg)]);
      }
    }
  }

  /// Side effect:
  /// oncall may be occupied.
  fn find_rtval_and_get_reg(&mut self, ptr: Value, oncall: Reg) -> Reg {
    let ptr_loc = self.rt_val(&ptr, Some(oncall));
    self.into_reg(ptr_loc, oncall)
  }
}
