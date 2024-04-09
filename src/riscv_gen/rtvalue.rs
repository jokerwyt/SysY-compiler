use super::riscv_isa::{Label, Reg};

/// This struct is used to describe the value or the storage location of it in runtime.
#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum RtValue {
  Integer(i32),  // Integer
  SpOffset(i32), // the value is Sp+offset.
  Stack(i32),    // the value is 4B. Its address is Sp+offset.
  Reg(Reg),      // when value itself is stored in a register
  RegRef(Reg),   // The value is a ptr pointing to a register.
  // It's helpful when you want to use reg scheduler for things like alloc.
  Label(Label), // It's a 32-bit const address.
}

impl RtValue {
  pub(crate) fn reg(&self) -> Reg {
    match self {
      RtValue::Reg(reg) => *reg,
      _ => panic!("Not a register"),
    }
  }
}
