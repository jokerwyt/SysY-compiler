use koopa::ir::{BasicBlock, Function, Program, Type, Value};

use crate::{
  koopa_gen::gen::TypeUtils,
  riscv_gen::riscv_isa::{Directive, RiscvAsmLine},
};

use super::{
  frame_manager::{AbstractAlloc, CrazySpiller, FrameAlloc, FrameManager},
  riscv_isa::{Imm, Imm12, Inst, Label, LabelKind, Reg, RiscvProg},
};

pub struct RiscvGen<'a> {
  riscv_prog: RiscvProg,
  koopa_prog: &'a Program,
}

impl<'a> RiscvGen<'a> {
  pub fn new(prog: &'a Program) -> Self {
    Type::set_ptr_size(4);

    Self {
      riscv_prog: RiscvProg::new(),
      koopa_prog: prog,
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

  fn gen_on_func(&mut self, fhandle: &Function, fdata: &koopa::ir::FunctionData) {
    self.riscv_prog.extend([
      RiscvAsmLine::Diretive(Directive::Text),
      RiscvAsmLine::Diretive(Directive::Globl(fdata.name().to_string())),
      RiscvAsmLine::Label(Label::new(fdata.name().to_string(), LabelKind::Func)),
    ]);

    let fmnger = FrameManager::<CrazySpiller>::new(
      fdata,
      Reg::all()
        .iter()
        .filter(|r| *r != &Reg::Zero && ![Reg::Ra, Reg::Sp, Reg::T0, Reg::T1, Reg::A0].contains(r))
        .cloned()
        .collect::<Vec<_>>()
        .as_slice(),
    );

    // Prologue. Move Sp and save all callee-saved registers.
    self.riscv_prog.more_insts([
      Inst::Li(Reg::T0, Imm::new(-fmnger.frame_len)),
      Inst::Sub(Reg::Sp, Reg::Sp, Reg::T0),
    ]);

    for reg in fmnger.active_reg.iter().filter(|reg| reg.is_callee_saved()) {
      self
        .riscv_prog
        .store_reg_to(reg, &fmnger.reg_loc(reg), Some(&Reg::T0));
    }

    // basic block translation
    for (bbhandle, bbdata) in fdata.layout().bbs() {
      self
        .riscv_prog
        .append_label(self.bb_label(fhandle, bbhandle));

      for (inst, inst_node) in bbdata.insts() {
        let idata = fdata.dfg().value(*inst);
        match idata.kind() {
          koopa::ir::ValueKind::Alloc(_) => {}
          koopa::ir::ValueKind::Load(ptr) => {
            let dest = fmnger.loc(inst);
            let src_ptr = fmnger.loc(&ptr.src());
            let sz = idata.ty().size();
            if sz != 4 {
              unimplemented!("only support 4 bytes load");
            }

            // load the src ptr into T0
            self.riscv_prog.load_to_reg(src_ptr, Reg::T0);

            // deref the src_ptr
            self
              .riscv_prog
              .append_inst(Inst::Lw(Reg::T0, Reg::T0, Imm12::zero()));

            // store the value to dest
            self
              .riscv_prog
              .store_reg_to(&Reg::T0, &dest, Some(&Reg::T1));
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

            // src = (Value | Initializer)
            // Initializer ::= INT | "undef" | Aggregate | "zeroinit";

            // prepare src value in T0
            // consider constant value specially
            match src_data.kind() {
              koopa::ir::ValueKind::Integer(v) => {
                self
                  .riscv_prog
                  .append_inst(Inst::Li(Reg::T0, Imm::new(v.value())));
              }
              koopa::ir::ValueKind::ZeroInit(_) => {
                self.riscv_prog.append_inst(Inst::Li(Reg::T0, Imm::new(0)));
              }
              _ => {
                // non-constant value case
                self.riscv_prog.load_to_reg(fmnger.loc(&src), Reg::T0);
              }
            }

            self
              .riscv_prog
              .store_reg_to(&Reg::T0, &fmnger.loc(&dst_ptr), Some(&Reg::T1));
          }
          koopa::ir::ValueKind::GetPtr(getptr) => {
            self.advance_ptr(
              fmnger.loc(&getptr.src()),
              fdata.dfg().value(getptr.src()).ty().ptr_inner().size() as i32,
              fmnger.loc(&getptr.index()),
              fmnger.loc(inst),
            );
          }
          koopa::ir::ValueKind::GetElemPtr(getelem) => {
            self.advance_ptr(
              fmnger.loc(&getelem.src()),
              fdata
                .dfg()
                .value(getelem.src())
                .ty()
                .ptr_inner()
                .array_inner() // Think about *[[i32, 3], 4] -> [i32, 3]
                .size() as i32,
              fmnger.loc(&getelem.index()),
              fmnger.loc(inst),
            );
          }
          koopa::ir::ValueKind::Binary(binary) => {
            self
              .riscv_prog
              .load_to_reg(fmnger.loc(&binary.lhs()), Reg::T0);
            self
              .riscv_prog
              .load_to_reg(fmnger.loc(&binary.rhs()), Reg::T1);

            // the result is put to T0.
            match binary.op() {
              koopa::ir::BinaryOp::NotEq => self.riscv_prog.more_insts([
                Inst::Xor(Reg::T0, Reg::T0, Reg::T1),
                // if T0 != T1, then T0 != 0
                Inst::Snez(Reg::T0, Reg::T0),
                // In such case, T0 = 1 now.
              ]),
              koopa::ir::BinaryOp::Eq => self.riscv_prog.more_insts([
                Inst::Xor(Reg::T0, Reg::T0, Reg::T1),
                Inst::Seqz(Reg::T0, Reg::T0),
              ]),
              koopa::ir::BinaryOp::Gt => {
                self
                  .riscv_prog
                  .more_insts([Inst::Sgt(Reg::T0, Reg::T0, Reg::T1)])
              }
              koopa::ir::BinaryOp::Lt => {
                self
                  .riscv_prog
                  .more_insts([Inst::Slt(Reg::T0, Reg::T0, Reg::T1)])
              }
              koopa::ir::BinaryOp::Ge => self.riscv_prog.more_insts([
                Inst::Slt(Reg::T0, Reg::T0, Reg::T1),
                Inst::Xori(Reg::T0, Reg::T0, Imm12::try_from(1).unwrap()),
              ]),
              koopa::ir::BinaryOp::Le => self.riscv_prog.more_insts([
                Inst::Sgt(Reg::T0, Reg::T0, Reg::T1),
                Inst::Xori(Reg::T0, Reg::T0, Imm12::try_from(1).unwrap()),
              ]),
              koopa::ir::BinaryOp::Add => {
                self
                  .riscv_prog
                  .append_inst(Inst::Add(Reg::T0, Reg::T0, Reg::T1))
              }
              koopa::ir::BinaryOp::Sub => {
                self
                  .riscv_prog
                  .append_inst(Inst::Sub(Reg::T0, Reg::T0, Reg::T1))
              }
              koopa::ir::BinaryOp::Mul => {
                self
                  .riscv_prog
                  .append_inst(Inst::Mul(Reg::T0, Reg::T0, Reg::T1))
              }
              koopa::ir::BinaryOp::Div => {
                self
                  .riscv_prog
                  .append_inst(Inst::Div(Reg::T0, Reg::T0, Reg::T1))
              }
              koopa::ir::BinaryOp::Mod => {
                self
                  .riscv_prog
                  .append_inst(Inst::Rem(Reg::T0, Reg::T0, Reg::T1))
              }
              koopa::ir::BinaryOp::And => {
                self
                  .riscv_prog
                  .append_inst(Inst::And(Reg::T0, Reg::T0, Reg::T1))
              }
              koopa::ir::BinaryOp::Or => {
                self
                  .riscv_prog
                  .append_inst(Inst::Or(Reg::T0, Reg::T0, Reg::T1))
              }
              koopa::ir::BinaryOp::Xor => {
                self
                  .riscv_prog
                  .append_inst(Inst::Xor(Reg::T0, Reg::T0, Reg::T1))
              }
              koopa::ir::BinaryOp::Shl => {
                self
                  .riscv_prog
                  .append_inst(Inst::Sll(Reg::T0, Reg::T0, Reg::T1))
              }
              koopa::ir::BinaryOp::Shr => {
                self
                  .riscv_prog
                  .append_inst(Inst::Srl(Reg::T0, Reg::T0, Reg::T1))
              }
              koopa::ir::BinaryOp::Sar => {
                self
                  .riscv_prog
                  .append_inst(Inst::Sra(Reg::T0, Reg::T0, Reg::T1))
              }
            }
          }
          koopa::ir::ValueKind::Branch(branch) => {
            self
              .riscv_prog
              .load_to_reg(fmnger.loc(&branch.cond()), Reg::T0);

            self.riscv_prog.more_insts([
              Inst::Bnez(Reg::T0, self.bb_label(fhandle, &branch.true_bb())),
              Inst::J(self.bb_label(fhandle, &branch.false_bb())),
            ]);
          }
          koopa::ir::ValueKind::Jump(jmp) => self
            .riscv_prog
            .more_insts([Inst::J(self.bb_label(fhandle, &jmp.target()))]),
          koopa::ir::ValueKind::Call(call) => {
            // save caller-saved registers
            for reg in fmnger.active_reg.iter().filter(|reg| reg.is_caller_saved()) {
              self
                .riscv_prog
                .store_reg_to(reg, &fmnger.reg_loc(reg), Some(&Reg::T0));
            }

            // prepare arguments
            for (idx, arg) in call.args().iter().enumerate() {
              self.riscv_prog.load_to_reg(fmnger.loc(arg), Reg::T0);
              self
                .riscv_prog
                .store_reg_to(&Reg::T0, &fmnger.arg_loc(idx), None);
            }

            // call
            self.riscv_prog.more_insts([Inst::Call(Label::new(
              self.koopa_prog.func(call.callee()).name().to_string(),
              LabelKind::Func,
            ))]);

            // save return value to T0
            self
              .riscv_prog
              .store_reg_to(&Reg::A0, &fmnger.loc(inst), Some(&Reg::T0));

            // restore caller-saved registers
            for reg in fmnger.active_reg.iter().filter(|reg| reg.is_caller_saved()) {
              self.riscv_prog.load_to_reg(fmnger.reg_loc(reg), *reg);
            }

            // move T0 to the destination of Koopa Call Inst
            self
              .riscv_prog
              .store_reg_to(&Reg::T0, &fmnger.loc(inst), Some(&Reg::T1));
          }
          koopa::ir::ValueKind::Return(ret) => {
            if let Some(ret) = ret.value() {
              self.riscv_prog.load_to_reg(fmnger.loc(&ret), Reg::A0);
            }

            // Epilogue. Restore all callee-saved registers and move Sp.
            for reg in fmnger.active_reg.iter().filter(|reg| reg.is_callee_saved()) {
              self.riscv_prog.load_to_reg(fmnger.reg_loc(reg), *reg);
            }

            self.riscv_prog.more_insts([
              Inst::Li(Reg::T0, Imm::new(fmnger.frame_len)),
              Inst::Add(Reg::Sp, Reg::Sp, Reg::T0),
            ]);

            self.riscv_prog.append_inst(Inst::Ret);
          }
          _ => panic!("gen_on_func: unexpected value kind"),
        }
      }
    }
  }

  fn gen_global_alloc(&mut self, value: std::cell::Ref<'a, koopa::ir::entities::ValueData>) {
    self.riscv_prog.extend([
      RiscvAsmLine::Diretive(Directive::Data),
      RiscvAsmLine::Diretive(Directive::Globl(value.name().as_ref().unwrap().clone())),
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
        .unwrap(),
      LabelKind::BasicBlock {
        func_name: self.koopa_prog.func(*fhandle).name().to_string(),
      },
    )
  }

  fn advance_ptr(&mut self, ptr: FrameAlloc, size_unit: i32, idx: FrameAlloc, target: FrameAlloc) {
    self.riscv_prog.load_to_reg(idx, Reg::T1);

    // ptr += inner_size * idx
    self.riscv_prog.more_insts([
      Inst::Li(Reg::T0, Imm::new(size_unit)),
      Inst::Mul(Reg::T1, Reg::T1, Reg::T0),
    ]);
    // Now T1 = inner_size * idx
    self.riscv_prog.load_to_reg(ptr, Reg::T0);
    self
      .riscv_prog
      .append_inst(Inst::Add(Reg::T0, Reg::T0, Reg::T1));

    // Now T0 = ptr + inner_size * idx
    self.riscv_prog.store_reg_to(&Reg::T0, &target, None);
  }
}
