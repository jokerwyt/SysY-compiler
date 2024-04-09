use std::collections::HashMap;

use koopa::ir::{FunctionData, Value};

use super::{riscv_isa::Reg, rtvalue::RtValue};

pub mod crazy_spiller;
pub mod first_come_first_serve;

pub trait RegisterAllocator {
  fn new(func: &FunctionData, available_regs: &[Reg]) -> Self;

  /// Return the number of stack needed for local variables.
  /// Note that: Frame size = Saved Registers + Local Variables + Outgoing Arguments
  /// Here we only consider Local Variables part.
  fn memory_usage(&self) -> i32;

  /// For stack allocation:
  /// We assume there is an interval on stack for us to use.
  /// And the offset we give out is from 0..mem_usage().
  ///
  /// For FuncArgRef:
  /// We must bind it according to the calling convention.
  fn desicions(&self) -> &HashMap<Value, RtValue>;

  fn decision(&self, value: &Value) -> RtValue {
    self.desicions().get(value).unwrap().clone()
  }

  fn reg_used(&self) -> Vec<Reg> {
    self
      .desicions()
      .values()
      .filter_map(|alloc| match alloc {
        RtValue::Reg(reg) => Some(reg.clone()),
        RtValue::RegRef(reg) => Some(reg.clone()),
        _ => None,
      })
      .collect()
  }
}
