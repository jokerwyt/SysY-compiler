use super::frame_manager::FrameAlloc;

#[derive(Clone, Copy, Debug, PartialEq, Hash, Eq)]
pub enum Reg {
  Zero,
  Ra,
  Sp,
  Gp,
  Tp,
  T0,
  T1,
  T2,
  S0,
  S1,
  A0,
  A1,
  A2,
  A3,
  A4,
  A5,
  A6,
  A7,
  S2,
  S3,
  S4,
  S5,
  S6,
  S7,
  S8,
  S9,
  S10,
  S11,
  T3,
  T4,
  T5,
  T6,
}

pub const REGS: [Reg; 32] = [
  Reg::Zero,
  Reg::Ra,
  Reg::Sp,
  Reg::Gp,
  Reg::Tp,
  Reg::T0,
  Reg::T1,
  Reg::T2,
  Reg::S0,
  Reg::S1,
  Reg::A0,
  Reg::A1,
  Reg::A2,
  Reg::A3,
  Reg::A4,
  Reg::A5,
  Reg::A6,
  Reg::A7,
  Reg::S2,
  Reg::S3,
  Reg::S4,
  Reg::S5,
  Reg::S6,
  Reg::S7,
  Reg::S8,
  Reg::S9,
  Reg::S10,
  Reg::S11,
  Reg::T3,
  Reg::T4,
  Reg::T5,
  Reg::T6,
];

pub const CALLER_SAVED_REGS: [Reg; 16] = [
  Reg::Ra,
  Reg::T0,
  Reg::T1,
  Reg::T2,
  Reg::A0,
  Reg::A1,
  Reg::A2,
  Reg::A3,
  Reg::A4,
  Reg::A5,
  Reg::A6,
  Reg::A7,
  Reg::T3,
  Reg::T4,
  Reg::T5,
  Reg::T6,
];

pub const CALLEE_SAVED_REGS: [Reg; 12] = [
  Reg::S0,
  Reg::S1,
  Reg::S2,
  Reg::S3,
  Reg::S4,
  Reg::S5,
  Reg::S6,
  Reg::S7,
  Reg::S8,
  Reg::S9,
  Reg::S10,
  Reg::S11,
];

impl Reg {
  pub fn all() -> Vec<Reg> {
    REGS.to_vec()
  }

  pub fn is_callee_saved(&self) -> bool {
    CALLEE_SAVED_REGS.contains(self)
  }

  pub fn is_caller_saved(&self) -> bool {
    !self.is_callee_saved()
  }

  pub fn to_string(&self) -> String {
    match self {
      Reg::Zero => "zero".to_string(),
      Reg::Ra => "ra".to_string(),
      Reg::Sp => "sp".to_string(),
      Reg::Gp => "gp".to_string(),
      Reg::Tp => "tp".to_string(),
      Reg::T0 => "t0".to_string(),
      Reg::T1 => "t1".to_string(),
      Reg::T2 => "t2".to_string(),
      Reg::S0 => "s0".to_string(),
      Reg::S1 => "s1".to_string(),
      Reg::A0 => "a0".to_string(),
      Reg::A1 => "a1".to_string(),
      Reg::A2 => "a2".to_string(),
      Reg::A3 => "a3".to_string(),
      Reg::A4 => "a4".to_string(),
      Reg::A5 => "a5".to_string(),
      Reg::A6 => "a6".to_string(),
      Reg::A7 => "a7".to_string(),
      Reg::S2 => "s2".to_string(),
      Reg::S3 => "s3".to_string(),
      Reg::S4 => "s4".to_string(),
      Reg::S5 => "s5".to_string(),
      Reg::S6 => "s6".to_string(),
      Reg::S7 => "s7".to_string(),
      Reg::S8 => "s8".to_string(),
      Reg::S9 => "s9".to_string(),
      Reg::S10 => "s10".to_string(),
      Reg::S11 => "s11".to_string(),
      Reg::T3 => "t3".to_string(),
      Reg::T4 => "t4".to_string(),
      Reg::T5 => "t5".to_string(),
      Reg::T6 => "t6".to_string(),
    }
  }

  pub fn idx(&self) -> usize {
    match self {
      Reg::Zero => 0,
      Reg::Ra => 1,
      Reg::Sp => 2,
      Reg::Gp => 3,
      Reg::Tp => 4,
      Reg::T0 => 5,
      Reg::T1 => 6,
      Reg::T2 => 7,
      Reg::S0 => 8,
      Reg::S1 => 9,
      Reg::A0 => 10,
      Reg::A1 => 11,
      Reg::A2 => 12,
      Reg::A3 => 13,
      Reg::A4 => 14,
      Reg::A5 => 15,
      Reg::A6 => 16,
      Reg::A7 => 17,
      Reg::S2 => 18,
      Reg::S3 => 19,
      Reg::S4 => 20,
      Reg::S5 => 21,
      Reg::S6 => 22,
      Reg::S7 => 23,
      Reg::S8 => 24,
      Reg::S9 => 25,
      Reg::S10 => 26,
      Reg::S11 => 27,
      Reg::T3 => 28,
      Reg::T4 => 29,
      Reg::T5 => 30,
      Reg::T6 => 31,
    }
  }
}

pub enum Directive {
  Text,
  Data,
  Globl(String),
  Zero(usize),
  Word(i32),
}

impl Directive {
  pub fn to_string(&self) -> String {
    match self {
      Directive::Text => ".text".to_string(),
      Directive::Data => ".data".to_string(),
      Directive::Globl(s) => format!(".globl {}", s),
      Directive::Zero(n) => format!(".zero {}", n),
      Directive::Word(n) => format!(".word {}", n),
    }
  }
}

pub struct Imm {
  pub value: i32,
}
impl Imm {
  pub(crate) fn new(src_ptr_mem: i32) -> Imm {
    Imm { value: src_ptr_mem }
  }
}

pub struct Imm12 {
  pub value: i32,
}

impl Imm12 {
  pub fn zero() -> Self {
    Self { value: 0 }
  }
}

impl TryFrom<i32> for Imm12 {
  type Error = ();

  fn try_from(value: i32) -> Result<Self, Self::Error> {
    if value >= -2048 && value <= 2047 {
      Ok(Imm12 { value })
    } else {
      Err(())
    }
  }
}

pub struct Label {
  pub name: String,
  kind: LabelKind,
}

pub enum LabelKind {
  Func,
  BasicBlock { func_name: String },
}

impl LabelKind {
  pub fn as_str(&self) -> String {
    match self {
      LabelKind::Func => "koopa_func".to_string(),
      LabelKind::BasicBlock { func_name } => format!("koopa_{}_bb", func_name),
    }
  }
}

impl Label {
  pub fn new(name: String, ty: LabelKind) -> Self {
    Self {
      name: format!("{}_{}", ty.as_str(), name),
      kind: ty,
    }
  }
}

// beqz/bnez
// j
// call/ret
// lw
// sw
// add/addi
// sub
// slt/sgt
// seqz/snez
// xor/xori
// or/ori
// and/andi
// sll/srl/sra
// mul/div/rem
// li
// la
// mv
pub enum Inst {
  Beqz(Reg, Label),
  Bnez(Reg, Label),
  J(Label),
  Call(Label),
  Ret,
  Lw(Reg, Reg, Imm12),

  /// sw r_src, i(r_dstaddr)
  Sw(Reg, Reg, Imm12),
  Add(Reg, Reg, Reg),
  Addi(Reg, Reg, Imm12),
  Sub(Reg, Reg, Reg),

  /// slt r_dest, r_src1, r_src2
  Slt(Reg, Reg, Reg),
  Sgt(Reg, Reg, Reg),

  /// seqz r_dest, r_src
  Seqz(Reg, Reg),
  Snez(Reg, Reg),
  Xor(Reg, Reg, Reg),
  Xori(Reg, Reg, Imm12),
  Or(Reg, Reg, Reg),
  Ori(Reg, Reg, Imm12),
  And(Reg, Reg, Reg),
  Andi(Reg, Reg, Imm12),
  Sll(Reg, Reg, Reg),
  Srl(Reg, Reg, Reg),
  Sra(Reg, Reg, Reg),
  Mul(Reg, Reg, Reg),
  Div(Reg, Reg, Reg),
  Rem(Reg, Reg, Reg),
  Li(Reg, Imm),
  La(Reg, Label),

  /// mv r_dest, r_src
  Mv(Reg, Reg),
}

impl Inst {
  pub fn to_string(&self) -> String {
    match self {
      Inst::Beqz(r, l) => format!("beqz {}, {}", r.to_string(), l.name,),
      Inst::Bnez(r, l) => format!("bnez {}, {}", r.to_string(), l.name,),
      Inst::J(l) => format!("j {}", l.name,),
      Inst::Call(l) => format!("call {}", l.name,),
      Inst::Ret => format!("ret"),
      Inst::Lw(r1, r2, i) => format!("lw {}, {}({})", r1.to_string(), i.value, r2.to_string(),),
      Inst::Sw(r1, r2, i) => format!("sw {}, {}({})", r1.to_string(), i.value, r2.to_string(),),
      Inst::Add(r1, r2, r3) => format!(
        "add {}, {}, {}",
        r1.to_string(),
        r2.to_string(),
        r3.to_string(),
      ),
      Inst::Addi(r1, r2, i) => format!("addi {}, {}, {}", r1.to_string(), r2.to_string(), i.value,),
      Inst::Sub(r1, r2, r3) => format!(
        "sub {}, {}, {}",
        r1.to_string(),
        r2.to_string(),
        r3.to_string(),
      ),
      Inst::Slt(r1, r2, r3) => format!(
        "slt {}, {}, {}",
        r1.to_string(),
        r2.to_string(),
        r3.to_string(),
      ),
      Inst::Sgt(r1, r2, r3) => format!(
        "sgt {}, {}, {}",
        r1.to_string(),
        r2.to_string(),
        r3.to_string(),
      ),
      Inst::Seqz(r1, r2) => format!("seqz {}, {}", r1.to_string(), r2.to_string(),),
      Inst::Snez(r1, r2) => format!("snez {}, {}", r1.to_string(), r2.to_string(),),
      Inst::Xor(r1, r2, r3) => format!(
        "xor {}, {}, {}",
        r1.to_string(),
        r2.to_string(),
        r3.to_string(),
      ),
      Inst::Xori(r1, r2, i) => format!("xori {}, {}, {}", r1.to_string(), r2.to_string(), i.value,),
      Inst::Or(r1, r2, r3) => format!(
        "or {}, {}, {}",
        r1.to_string(),
        r2.to_string(),
        r3.to_string(),
      ),
      Inst::Ori(r1, r2, i) => format!("ori {}, {}, {}", r1.to_string(), r2.to_string(), i.value,),
      Inst::And(r1, r2, r3) => format!(
        "and {}, {}, {}",
        r1.to_string(),
        r2.to_string(),
        r3.to_string(),
      ),
      Inst::Andi(r1, r2, i) => format!("andi {}, {}, {}", r1.to_string(), r2.to_string(), i.value,),
      Inst::Sll(r1, r2, r3) => format!(
        "sll {}, {}, {}",
        r1.to_string(),
        r2.to_string(),
        r3.to_string()
      ),
      Inst::Srl(r1, r2, r3) => format!(
        "srl {}, {}, {}",
        r1.to_string(),
        r2.to_string(),
        r3.to_string()
      ),
      Inst::Sra(r1, r2, r3) => format!(
        "sra {}, {}, {}",
        r1.to_string(),
        r2.to_string(),
        r3.to_string()
      ),
      Inst::Mul(r1, r2, r3) => format!(
        "mul {}, {}, {}",
        r1.to_string(),
        r2.to_string(),
        r3.to_string(),
      ),
      Inst::Div(r1, r2, r3) => format!(
        "div {}, {}, {}",
        r1.to_string(),
        r2.to_string(),
        r3.to_string(),
      ),
      Inst::Rem(r1, r2, r3) => format!(
        "rem {}, {}, {}",
        r1.to_string(),
        r2.to_string(),
        r3.to_string(),
      ),
      Inst::Li(r, i) => format!("li {}, {}", r.to_string(), i.value,),
      Inst::La(r, l) => format!("la {}, {}", r.to_string(), l.name,),
      Inst::Mv(r1, r2) => format!("mv {}, {}", r1.to_string(), r2.to_string(),),
    }
  }
}

pub enum RiscvAsmLine {
  Diretive(Directive),
  Label(Label),
  Inst(Inst),
}

pub struct RiscvProg {
  pub lines: Vec<RiscvAsmLine>,
}

impl RiscvProg {
  pub fn append_asm_line(&mut self, line: RiscvAsmLine) {
    self.lines.push(line);
  }

  pub fn append_directive(&mut self, directive: Directive) {
    self.lines.push(RiscvAsmLine::Diretive(directive));
  }

  pub fn append_label(&mut self, label: Label) {
    self.lines.push(RiscvAsmLine::Label(label));
  }

  pub fn append_inst(&mut self, inst: Inst) {
    self.lines.push(RiscvAsmLine::Inst(inst));
  }

  pub fn more_insts(&mut self, insts: impl IntoIterator<Item = Inst>) {
    self.lines.extend(insts.into_iter().map(RiscvAsmLine::Inst));
  }

  pub(crate) fn new() -> RiscvProg {
    Self { lines: Vec::new() }
  }

  pub(crate) fn extend(&mut self, lines: impl IntoIterator<Item = RiscvAsmLine>) {
    self.lines.extend(lines.into_iter())
  }

  pub(crate) fn load_to_reg(&mut self, dst_ptr_alloc: FrameAlloc, target: Reg) {
    match dst_ptr_alloc {
      FrameAlloc::SpOffset(offset) => {
        if let Ok(offset) = Imm12::try_from(offset) {
          self.more_insts([Inst::Lw(target, Reg::Sp, offset)])
        } else {
          self.more_insts([
            Inst::Li(target, Imm::new(offset)),
            Inst::Add(target, Reg::Sp, target),
            Inst::Lw(target, target, Imm12::zero()),
          ]);
        }
      }
      FrameAlloc::Reg(reg) => {
        if target != reg {
          self.append_inst(Inst::Mv(target, reg));
        }
      }
    }
  }

  /// Store the value in the register to the memory.
  /// If the offset is too large, it will use the temp register to store the offset, and return true.
  /// Otherwise, it will return false.
  pub(crate) fn store_reg_to(&mut self, src: &Reg, dest: &FrameAlloc, temp: Option<&Reg>) -> bool {
    match dest {
      FrameAlloc::SpOffset(ofs) => {
        if let Ok(ofs) = Imm12::try_from(*ofs) {
          self.more_insts([Inst::Sw(*src, Reg::Sp, ofs)]);
          return false;
        } else {
          let temp = *temp.expect("store_reg_to: temp register is not provided");
          assert!(
            temp != *src,
            "store_reg_to: temp register should not be the same as src"
          );
          self.more_insts([
            Inst::Li(temp, Imm::new(*ofs)),
            Inst::Add(temp, Reg::Sp, temp),
            Inst::Sw(*src, temp, Imm12::zero()),
          ]);
          return true;
        }
      }
      FrameAlloc::Reg(reg) => {
        if reg != src {
          self.append_inst(Inst::Mv(*reg, *src));
        }
        return false;
      }
    }
  }
}
