use std::borrow::Borrow;

use koopa::ir::{BasicBlock, Function, Program, Type, Value};

use crate::{
  koopa_gen::gen::{KoopaValueDataToString, TypeUtils},
  riscv_gen::riscv_isa::{Directive, RiscvAsmLine},
};

use super::{
  frame_manager::{CrazySpiller, FrameAlloc, FrameManager},
  riscv_isa::{Imm, Imm12, Inst, Label, LabelKind, Reg, RiscvProg},
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
      RiscvAsmLine::Label(Label::new(fdata.name()[1..].to_string(), LabelKind::Func)),
    ]);

    self.fmnger = Some(FrameManager::<CrazySpiller>::new(
      self.koopa_prog,
      fdata,
      Reg::all()
        .iter()
        .filter(|r| *r != &Reg::Zero && ![Reg::Ra, Reg::Sp, Reg::T0, Reg::T1, Reg::A0].contains(r))
        .cloned()
        .collect::<Vec<_>>()
        .as_slice(),
    ));

    // Prologue. Move Sp and save all callee-saved registers.
    let flen = self.fmnger().frame_len;
    self.riscv_prog.more_insts([
      Inst::Li(Reg::T0, Imm::new(-flen)),
      Inst::Sub(Reg::Sp, Reg::Sp, Reg::T0),
    ]);

    for reg in self
      .fmnger()
      .active_reg
      .clone()
      .iter()
      .filter(|reg| reg.is_callee_saved())
      .collect::<Vec<_>>()
    {
      let reg_loc = self.fmnger().reg_loc(reg);
      self.store_reg_to(reg, &reg_loc, Some(&Reg::T0));
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
          koopa::ir::ValueKind::Load(ptr) => {
            let dest = self.fmnger().local_alloc(inst);
            let src_ptr = self.global_to_local(&ptr.src(), Some(Reg::T0));
            let sz = idata.ty().size();
            if sz != 4 {
              unimplemented!("only support 4 bytes load");
            }

            // load the src ptr into T0
            let src_reg = self.hold_to_reg(src_ptr, Reg::T0);

            // deref the src_ptr
            self
              .riscv_prog
              .append_inst(Inst::Lw(src_reg, src_reg, Imm12::zero()));

            // store the value to dest
            self.store_reg_to(&src_reg, &dest, Some(&Reg::T1));
          }
          koopa::ir::ValueKind::Store(store) => {
            let src = store.value();
            let dst_ptr = store.dest();

            let src_data = fdata.dfg().value(src);
            let dst_ptr_data = fdata.dfg().value(dst_ptr);

            let ty = dst_ptr_data.ty().ptr_inner();
            assert!(src_data.ty().eq(&ty), "store type mismatch");
            if ty.size() != 4 {
              unimplemented!("only support 4 bytes store");
            }

            // non-constant value case
            let src_reg = self.global_to_local(&src, Some(Reg::T0));
            let dst_loc = self.global_to_local(&dst_ptr, Some(Reg::T1));

            self.store_reg_to(src_reg.reg(), &dst_loc, Some(&Reg::T1));
          }
          koopa::ir::ValueKind::GetPtr(getptr) => {
            let idx_loc = self.global_to_local(&getptr.index(), Some(Reg::T0));
            self.advance_ptr(
              &getptr.src(),
              fdata.dfg().value(getptr.src()).ty().ptr_inner().size() as i32,
              idx_loc,
              self.fmnger().local_alloc(inst),
            );
          }
          koopa::ir::ValueKind::GetElemPtr(getelem) => {
            let idx_loc = self.global_to_local(&getelem.index(), Some(Reg::T0));
            self.advance_ptr(
              &getelem.src(),
              fdata
                .dfg()
                .value(getelem.src())
                .ty()
                .ptr_inner()
                .array_inner() // Think about *[[i32, 3], 4] -> [i32, 3]
                .size() as i32,
              idx_loc,
              self.fmnger().local_alloc(inst),
            );
          }
          koopa::ir::ValueKind::Binary(binary) => {
            let lhs_loc = self.global_to_local(&binary.lhs(), Some(Reg::T0));
            let rhs_loc = self.global_to_local(&binary.rhs(), Some(Reg::T1));

            let lhs_reg = self.hold_to_reg(lhs_loc, Reg::T0);
            let rhs_reg = self.hold_to_reg(rhs_loc, Reg::T1);

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
              &self.fmnger().local_alloc(inst),
              Some(&Reg::T1), // lhs_reg may equal to T0
            );
          }
          koopa::ir::ValueKind::Branch(branch) => {
            let cond_loc = self.global_to_local(&branch.cond(), Some(Reg::T0));
            let cond_reg = self.hold_to_reg(cond_loc, Reg::T0);

            self.riscv_prog.more_insts([
              Inst::Bnez(cond_reg, self.bb_label(fhandle, &branch.true_bb())),
              Inst::J(self.bb_label(fhandle, &branch.false_bb())),
            ]);
          }
          koopa::ir::ValueKind::Jump(jmp) => self
            .riscv_prog
            .more_insts([Inst::J(self.bb_label(fhandle, &jmp.target()))]),
          koopa::ir::ValueKind::Call(call) => {
            // save caller-saved registers
            for reg in self
              .fmnger()
              .active_reg
              .clone()
              .iter()
              .filter(|reg| reg.is_caller_saved())
            {
              self.store_reg_to(reg, &self.fmnger().reg_loc(reg), Some(&Reg::T0));
            }

            // prepare arguments
            for (idx, arg) in call.args().iter().enumerate() {
              let arg_loc = self.global_to_local(arg, Some(Reg::T0));
              let arg_reg = self.hold_to_reg(arg_loc, Reg::T0);
              self.store_reg_to(&arg_reg, &self.fmnger().arg_loc(idx), None); // small offset
            }

            // call
            self.riscv_prog.more_insts([Inst::Call(Label::new(
              self.koopa_prog.func(call.callee()).name().to_string(),
              LabelKind::Func,
            ))]);

            // save return value to T0
            self.store_reg_to(&Reg::A0, &self.fmnger().local_alloc(inst), Some(&Reg::T0));

            // restore caller-saved registers
            for reg in self
              .fmnger()
              .active_reg
              .clone()
              .iter()
              .filter(|reg| reg.is_caller_saved())
            {
              let load_reg = self.hold_to_reg(self.fmnger().reg_loc(reg), *reg);
              assert!(load_reg == *reg);
            }

            // move T0 to the destination of Koopa Call Inst
            self.store_reg_to(&Reg::T0, &self.fmnger().local_alloc(inst), Some(&Reg::T1));
          }
          koopa::ir::ValueKind::Return(ret) => {
            if let Some(ret) = ret.value() {
              let ret_loc = self.global_to_local(&ret, Some(Reg::A0));
              let ret_reg = self.hold_to_reg(ret_loc, Reg::A0);

              if ret_reg != Reg::A0 {
                self.riscv_prog.append_inst(Inst::Mv(Reg::A0, ret_reg));
              }
            }

            // Epilogue. Restore all callee-saved registers and move Sp.
            for reg in self
              .fmnger()
              .active_reg
              .clone()
              .iter()
              .filter(|reg| reg.is_callee_saved())
            {
              let load_reg = self.hold_to_reg(self.fmnger().reg_loc(reg), *reg);
              assert!(load_reg == *reg);
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
  fn advance_ptr(&mut self, ptr: &Value, size_unit: i32, idx: FrameAlloc, target: FrameAlloc) {
    let idx_reg = self.hold_to_reg(idx, Reg::T1);
    assert!(idx_reg != Reg::T0);
    let tmp_reg = if idx_reg != Reg::T0 { Reg::T0 } else { Reg::T1 };

    // ptr += inner_size * idx
    self.riscv_prog.more_insts([
      Inst::Li(tmp_reg, Imm::new(size_unit)),
      Inst::Mul(idx_reg, idx_reg, tmp_reg),
    ]);
    // Now idx_reg = inner_size * idx

    let ptr_loc = self.global_to_local(ptr, Some(tmp_reg));
    let ptr_reg = self.hold_to_reg(ptr_loc, tmp_reg);
    assert!(ptr_reg != idx_reg);

    self
      .riscv_prog
      .append_inst(Inst::Add(ptr_reg, ptr_reg, idx_reg));

    // Now ptr_reg = ptr + inner_size * idx
    let tmp2_reg = if ptr_reg != Reg::T0 { Reg::T0 } else { Reg::T1 };
    self.store_reg_to(&ptr_reg, &target, Some(&tmp2_reg));
  }

  /// If the value is a global alloc or constant, then the result is loaded into `oncall_reg`.
  /// Otherwise, the result is stored in the frame and the frame location is returned.
  fn global_to_local(&mut self, val: &Value, oncall_reg: Option<Reg>) -> FrameAlloc {
    if val.is_global() {
      // It must be a global alloc.
      let vdata = self.koopa_prog.borrow_value(*val);
      let vkind = vdata.kind();
      assert!(vkind.is_global_alloc());
      let oncall_reg = oncall_reg.unwrap();
      self.riscv_prog.append_inst(Inst::La(
        oncall_reg,
        Label::new(vdata.name().as_ref().unwrap().clone(), LabelKind::GlobalVar),
      ));
      return FrameAlloc::Reg(oncall_reg);
    } else {
      let vkind = self.fmnger().func_data().dfg().value(*val).kind();
      if vkind.is_const() {
        let oncall_reg = oncall_reg.unwrap();
        let cc = match vkind {
          koopa::ir::ValueKind::Integer(v) => v.value(),
          koopa::ir::ValueKind::ZeroInit(_) => 0,
          _ => panic!("Unexpected constant value"),
        };
        self
          .riscv_prog
          .append_inst(Inst::Li(oncall_reg, Imm::new(cc)));
        return FrameAlloc::Reg(oncall_reg);
      } else {
        return self.fmnger.as_ref().unwrap().local_alloc(val);
      }
    };
  }

  fn fmnger(&self) -> &FrameManager<'a, CrazySpiller> {
    self.fmnger.as_ref().unwrap()
  }

  /// Load a frame allocation from the memory to a register, if it is a SpOffset.
  /// If the src_loc is a register, it will return the register.
  /// Otherwise, it will load the value to the oncall_reg and return the oncall_reg.
  #[must_use]
  pub(crate) fn hold_to_reg(&mut self, src_loc: FrameAlloc, oncall_reg: Reg) -> Reg {
    match src_loc {
      FrameAlloc::SpOffset(offset) => {
        if let Ok(offset) = Imm12::try_from(offset) {
          self
            .riscv_prog
            .more_insts([Inst::Lw(oncall_reg, Reg::Sp, offset)])
        } else {
          self.riscv_prog.more_insts([
            Inst::Li(oncall_reg, Imm::new(offset)),
            Inst::Add(oncall_reg, Reg::Sp, oncall_reg),
            Inst::Lw(oncall_reg, oncall_reg, Imm12::zero()),
          ]);
        }
        return oncall_reg;
      }
      FrameAlloc::Reg(reg) => reg,
    }
  }

  /// Store the value in the register to the memory.
  /// If the offset is too large, it will use the temp register to store the offset, and return true.
  /// Otherwise, it will return false.
  pub(crate) fn store_reg_to(&mut self, src: &Reg, dest: &FrameAlloc, temp: Option<&Reg>) -> bool {
    match dest {
      FrameAlloc::SpOffset(ofs) => {
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
      FrameAlloc::Reg(reg) => {
        if reg != src {
          self.riscv_prog.append_inst(Inst::Mv(*reg, *src));
        }
        return false;
      }
    }
  }
}
