use std::collections::HashSet;

use koopa::ir::{BasicBlock, Function, Program, Type, Value};

use crate::{
  koopa_gen::gen::{FetchValueType, KoopaValueDataToString, TypeUtils},
  riscv_gen::{
    riscv_isa::{Directive, RiscvAsmLine},
    rtvalue::RtValue,
  },
  utils::new_tmp_idx,
};

use super::{
  frame_manager::FrameManager,
  reg_allocators::RegisterAllocator,
  riscv_isa::{Imm, Imm12, Inst, Label, LabelKind, Reg, RiscvProg},
};

pub struct RiscvGen<'a, Allocator: RegisterAllocator> {
  riscv_prog: RiscvProg,
  koopa_prog: &'a Program,
  fmnger: Option<FrameManager<'a, Allocator>>,
}

impl<'a, Allocator: RegisterAllocator> RiscvGen<'a, Allocator> {
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

    for fhandle in prog.func_layout() {
      let fdata = prog.func(*fhandle);
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
      RiscvAsmLine::Diretive(Directive::Globl(fdata.name().to_string())),
      RiscvAsmLine::Label(Label::new(
        fdata.name()[1..].to_string(),
        LabelKind::NativeFunc,
      )),
    ]);

    self.fmnger = Some(FrameManager::new(
      self.koopa_prog,
      fdata,
      Reg::all()
        .iter()
        .filter(|r| ![Reg::Zero, Reg::Ra, Reg::Sp, Reg::T0, Reg::T1].contains(r))
        .cloned()
        .collect::<Vec<_>>()
        .as_slice(),
    ));

    // Prologue. Move Sp and save all callee-saved registers.
    self.riscv_prog.comment("Prologue".to_string());
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
            let dest = self.rt_val(inst);
            let src_ptr = self.rt_val(&load.src());
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
            let dst_loc = self.rt_val(&dst_ptr);

            // use T1 to secure src_reg == T0
            self.store_reg_to_ref(src_reg, dst_loc, Some(&Reg::T1));
          }
          koopa::ir::ValueKind::GetPtr(getptr) => {
            let idx_loc = self.rt_val(&getptr.index());
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
            let idx_loc = self.rt_val(&getelem.index());
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

            // src, dest
            let to_assign: Vec<(RtValue, RtValue)> = call
              .args()
              .iter()
              .enumerate()
              .map(|(idx, arg)| {
                let arg_rtval = self.rt_val(arg);
                let dst_rtval = self.fmnger().next_args_rtval(idx);
                (arg_rtval, dst_rtval)
              })
              .collect();

            // this is somehow tricky... Considering that A0..A7 may be allocated to some arguments,
            self.shuffle_rtval(to_assign, Reg::T0, Reg::T1);

            // call

            self.riscv_prog.more_insts([Inst::Call(Label::new(
              self.koopa_prog.func(call.callee()).name()[1..].to_string(),
              if self
                .koopa_prog
                .func(call.callee())
                .layout()
                .bbs()
                .is_empty()
              {
                LabelKind::ForeignFunc
              } else {
                LabelKind::NativeFunc
              },
            ))]);

            // save return value to T1

            let mut ret_rtval = None;
            if self.fmnger().func_data().dfg().value(*inst).ty().is_i32() {
              ret_rtval = Some(self.fmnger().local_value(inst));
              self.riscv_prog.append_inst(Inst::Mv(Reg::T1, Reg::A0));
            }

            // restore caller-saved registers
            for reg in self.fmnger().need_caller_saved_regs() {
              let load_reg = self.into_reg(self.fmnger().reg_buffer_loc(&reg), reg);
              assert!(load_reg == reg);
            }

            // move the return val to the destination
            if let Some(ret) = ret_rtval {
              self.store_reg_to(&Reg::T1, &ret, Some(&Reg::T0));
            }
          }
          koopa::ir::ValueKind::Return(ret) => {
            if let Some(ret) = ret.value() {
              let ret_reg = self.find_rtval_and_get_reg(ret, Reg::A0);
              self.store_reg_to(&ret_reg, &RtValue::Reg(Reg::A0), None);
            }

            // Epilogue. Restore all callee-saved registers and move Sp.
            self.riscv_prog.comment("Eplilogue".to_string());
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
        let words = self.globl_value_to_directives(init_data);
        self.riscv_prog.more_directive(words);
      }
      _ => panic!("gen_global_alloc: unexpected value kind"),
    }
  }

  fn globl_value_to_directives(
    &self,
    value: std::cell::Ref<'a, koopa::ir::entities::ValueData>,
  ) -> Vec<Directive> {
    match value.kind() {
      koopa::ir::ValueKind::Integer(v) => vec![Directive::Word(v.value())],
      koopa::ir::ValueKind::ZeroInit(_) => {
        let ty = value.ty();
        let size = ty.size();
        vec![Directive::Zero(size)]
      }
      koopa::ir::ValueKind::Undef(_) => unimplemented!(),
      koopa::ir::ValueKind::Aggregate(agg) => {
        let mut words = Vec::new();
        for elem in agg.elems() {
          let elem_data = self.koopa_prog.borrow_value(elem.clone());
          let elem_words = self.globl_value_to_directives(elem_data);
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
  /// use T0 and T1.
  fn advance_ptr(&mut self, ptr: &Value, size_unit: i32, idx: RtValue, target: RtValue) {
    let idx_reg = self.into_reg(idx, Reg::T1);
    assert!(idx_reg != Reg::T0);

    // ptr += inner_size * idx
    self.riscv_prog.more_insts([
      Inst::Li(Reg::T0, Imm::new(size_unit)),
      Inst::Mul(idx_reg, idx_reg, Reg::T0),
    ]);
    // Now idx_reg = inner_size * idx

    let ptr_reg = self.find_rtval_and_get_reg(*ptr, Reg::T0);
    assert!(ptr_reg != idx_reg);

    self
      .riscv_prog
      .append_inst(Inst::Add(Reg::T0, ptr_reg, idx_reg));
    // Now T0 = ptr + inner_size * idx
    // we don't need ptr_reg and idx_reg anymore.
    self.store_reg_to(&Reg::T0, &target, Some(&Reg::T1));
  }

  fn rt_val(&self, val: &Value) -> RtValue {
    if val.is_global() {
      // It must be a global alloc.
      let vdata = self.koopa_prog.borrow_value(*val);
      let vkind = vdata.kind();
      match vkind {
        koopa::ir::ValueKind::GlobalAlloc(_) => {
          return RtValue::Label(Label::new(
            vdata.name().as_ref().unwrap().clone(),
            LabelKind::GlobalVar,
          ));
        }
        koopa::ir::ValueKind::Integer(v) => {
          return RtValue::Integer(v.value());
        }
        _ => panic!("rt_val: unexpected value kind"),
      }
    } else {
      return self.fmnger.as_ref().unwrap().local_value(val);
    };
  }

  fn fmnger(&self) -> &FrameManager<'a, Allocator> {
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
      RtValue::Label(label) => {
        self.riscv_prog.append_inst(Inst::La(may_used, label));
        may_used
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
      RtValue::Label(_) | RtValue::RegRef(_) => panic!("store_reg_to: unexpected RtValue"),
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
      RtValue::Label(label) => {
        self.riscv_prog.more_insts([
          Inst::La(oncall.unwrap(), label),
          Inst::Lw(oncall.unwrap(), oncall.unwrap(), Imm12::zero()),
        ]);
        oncall.unwrap()
      }
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
        self.riscv_prog.more_insts([Inst::Mv(reg, src_reg)]);
      }
      RtValue::Label(label) => {
        let oncall = oncall.unwrap();
        assert!(src_reg != *oncall);

        self.riscv_prog.more_insts([
          Inst::La(*oncall, label),
          Inst::Sw(src_reg, *oncall, Imm12::zero()),
        ]);
      }
    }
  }

  /// Side effect:
  /// oncall may be occupied.
  fn find_rtval_and_get_reg(&mut self, ptr: Value, oncall: Reg) -> Reg {
    let loc = self.rt_val(&ptr);
    self.into_reg(loc, oncall)
  }

  fn shuffle_rtval(&mut self, src_dst: Vec<(RtValue, RtValue)>, tmp1: Reg, loop_brk_tmp: Reg) {
    // // in CrazySpiller case we don't need shuffle.
    // // No value will comes from reg.

    // for (src, dest) in src_dst.iter() {
    //   match src {
    //     RtValue::Integer(_) | RtValue::SpOffset(_) | RtValue::Stack(_) | RtValue::Label(_) => {
    //       let reg = self.into_reg(src.clone(), tmp1);
    //       self.store_reg_to(&reg, dest, Some(&loop_brk_tmp));
    //     }

    //     RtValue::Reg(_) | RtValue::RegRef(_) => panic!("shuffle_rtval: unexpected src RtValue"),
    //   }
    // }

    // return;

    self.riscv_prog.comment("shuffle arguments".to_string());

    // make sure all dest are regs.
    let mut src_dst: Vec<(RtValue, Reg)> = src_dst
      .into_iter()
      .filter_map(|(src, dest)| match dest {
        RtValue::Reg(dest) => Some((src, dest)),
        RtValue::Stack(ofs) => {
          let src_reg = self.into_reg(src.clone(), tmp1);
          self.store_reg_to(&src_reg, &RtValue::Stack(ofs), Some(&loop_brk_tmp));
          return None; // don't collect
        }
        RtValue::Integer(_) | RtValue::SpOffset(_) | RtValue::RegRef(_) | RtValue::Label(_) => {
          panic!("shuffle_rtval: unexpected dest RtValue")
        }
      })
      .collect();

    while src_dst.is_empty() == false {
      let data_src_reg: HashSet<Reg> = src_dst
        .iter()
        .filter_map(|(src, _dst)| match src {
          RtValue::Reg(reg) => Some(*reg),
          _ => None,
        })
        .collect();

      let (mut pending, can_fire) = src_dst
        .into_iter()
        .partition::<Vec<(RtValue, Reg)>, _>(|(_src, dst)| data_src_reg.contains(dst));

      if can_fire.len() == 0 {
        // need to manually break the loop.
        assert!(pending.len() > 0);
        let first_pair = pending.iter().next().unwrap();
        // just make compiler happy
        let (src, dst) = (first_pair.0.clone(), first_pair.1.clone());

        assert!(
          data_src_reg.contains(&loop_brk_tmp) == false,
          "T1 is still occupied after some rounds."
        );
        self
          .riscv_prog
          .append_inst(Inst::Mv(loop_brk_tmp, src.reg()));

        // remove src->dst, add look_brk_tmp->dst
        pending.retain(|(_src, see_dst)| dst != *see_dst);
        pending.push((RtValue::Reg(loop_brk_tmp), dst));
      } else {
        // fire all can_fire and go to next round.
        for (src, dst) in can_fire {
          let src_reg = self.into_reg(src, tmp1);
          self.store_reg_to(&src_reg, &RtValue::Reg(dst), Some(&tmp1));
        }
      }

      src_dst = pending;
    }
  }
}
