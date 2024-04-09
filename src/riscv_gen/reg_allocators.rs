use std::collections::HashMap;

use koopa::ir::{FunctionData, Value};

use crate::koopa_gen::gen::TypeUtils;

use super::{
  riscv_isa::{Reg, FUNC_ARG_REGS},
  rtvalue::RtValue,
};

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

/// It spills all variables to the stack.
pub struct CrazySpiller {
  peak_mem: usize,

  /// Note that we don't know the frame size now.
  /// Therefore, the offset in Stack and SpOffset variant is from 0..peak_mem, instead of Sp offset.
  /// Actually we should add outgoing_args_cnt * 4 to them.
  mapping: HashMap<Value, RtValue>,
}

impl RegisterAllocator for CrazySpiller {
  fn new(func: &FunctionData, available_regs: &[Reg]) -> Self {
    let mut available_regs = available_regs.iter().cloned().collect::<Vec<_>>();
    let mut ret = Self {
      peak_mem: 0,
      mapping: HashMap::new(),
    };

    for (vhandle, vdata) in func.dfg().values() {
      if vdata.kind().is_local_inst() == false {
        continue;
      }

      match vdata.kind() {
        koopa::ir::ValueKind::GlobalAlloc(_)
        | koopa::ir::ValueKind::ZeroInit(_)
        | koopa::ir::ValueKind::Undef(_)
        | koopa::ir::ValueKind::Aggregate(_)
        | koopa::ir::ValueKind::Integer(_)
        | koopa::ir::ValueKind::BlockArgRef(_) => panic!("Unexpected value kind"),
        koopa::ir::ValueKind::FuncArgRef(arg) => {
          if arg.index() >= FUNC_ARG_REGS.len() {
            continue;
          }

          let reg = FUNC_ARG_REGS[arg.index()];
          // This FuncArgRef must be binded to this register.
          assert!(available_regs.contains(&reg));
          ret.mapping.insert(*vhandle, RtValue::Reg(reg));
          available_regs.retain(|r| r != &reg);
        }
        koopa::ir::ValueKind::Alloc(_) => {
          ret
            .mapping
            .insert(*vhandle, RtValue::SpOffset(ret.peak_mem as i32));
          // we will update it to the offset later.
          ret.peak_mem += vdata.ty().ptr_inner().size();
        }
        koopa::ir::ValueKind::Load(_)
        | koopa::ir::ValueKind::Store(_)
        | koopa::ir::ValueKind::GetPtr(_)
        | koopa::ir::ValueKind::GetElemPtr(_)
        | koopa::ir::ValueKind::Binary(_)
        | koopa::ir::ValueKind::Branch(_)
        | koopa::ir::ValueKind::Jump(_)
        | koopa::ir::ValueKind::Call(_)
        | koopa::ir::ValueKind::Return(_) => {
          if vdata.ty().size() > 0 {
            ret
              .mapping
              .insert(*vhandle, RtValue::Stack(ret.peak_mem as i32));
            ret.peak_mem += vdata.ty().size();
          }
        }
      }
    }
    ret
  }

  fn memory_usage(&self) -> i32 {
    self.peak_mem as i32
  }

  fn desicions(&self) -> &HashMap<Value, RtValue> {
    &self.mapping
  }
}

pub struct FirstComeFirstServe {
  peak_mem: usize,

  /// Note that we don't know the frame size now.
  /// Therefore, the offset in Stack and SpOffset variant is from 0..peak_mem, instead of Sp offset.
  /// Actually we should add outgoing_args_cnt * 4 to them.
  mapping: HashMap<Value, RtValue>,
}

impl RegisterAllocator for FirstComeFirstServe {
  fn new(func: &FunctionData, available_regs: &[Reg]) -> Self {
    let mut available_regs = available_regs.iter().cloned().collect::<Vec<_>>();

    let mut ret = Self {
      peak_mem: 0,
      mapping: HashMap::new(),
    };

    // bind all FuncArgRef first
    for (vhandle, vdata) in func.dfg().values() {
      match vdata.kind() {
        koopa::ir::ValueKind::FuncArgRef(arg) => {
          if arg.index() >= FUNC_ARG_REGS.len() {
            continue;
          }
          let reg = FUNC_ARG_REGS[arg.index()];
          // This FuncArgRef must be binded to this register.
          assert!(available_regs.contains(&reg));
          ret.mapping.insert(*vhandle, RtValue::Reg(reg));
          available_regs.retain(|r| r != &reg);
        }
        _ => { /* handle next */ }
      }
    }

    for (vhandle, vdata) in func.dfg().values() {
      if vdata.kind().is_local_inst() == false {
        continue;
      }

      match vdata.kind() {
        koopa::ir::ValueKind::GlobalAlloc(_)
        | koopa::ir::ValueKind::ZeroInit(_)
        | koopa::ir::ValueKind::Undef(_)
        | koopa::ir::ValueKind::Aggregate(_)
        | koopa::ir::ValueKind::Integer(_)
        | koopa::ir::ValueKind::BlockArgRef(_) => panic!("Unexpected value kind"),

        koopa::ir::ValueKind::FuncArgRef(_) => { /* done already */ }
        koopa::ir::ValueKind::Alloc(_) => {
          if vdata.ty().ptr_inner().is_array() == false && available_regs.is_empty() == false {
            let reg = available_regs.pop().unwrap();
            ret.mapping.insert(*vhandle, RtValue::RegRef(reg));
            dbg!(format!("{} assigned to {:?}", vdata.ty(), reg));
          } else {
            ret
              .mapping
              .insert(*vhandle, RtValue::SpOffset(ret.peak_mem as i32));
            // we will update it to the offset later.
            ret.peak_mem += vdata.ty().ptr_inner().size();
          }
        }
        koopa::ir::ValueKind::Load(_)
        | koopa::ir::ValueKind::Store(_)
        | koopa::ir::ValueKind::GetPtr(_)
        | koopa::ir::ValueKind::GetElemPtr(_)
        | koopa::ir::ValueKind::Binary(_)
        | koopa::ir::ValueKind::Branch(_)
        | koopa::ir::ValueKind::Jump(_)
        | koopa::ir::ValueKind::Call(_)
        | koopa::ir::ValueKind::Return(_) => {
          if vdata.ty().size() > 0 {
            // need to allocate.
            if vdata.ty().size() == 4 && available_regs.is_empty() == false {
              let reg = available_regs.pop().unwrap();
              ret.mapping.insert(*vhandle, RtValue::Reg(reg));
              dbg!(format!("{} assigned to {:?}", vdata.ty(), reg));
            } else {
              ret
                .mapping
                .insert(*vhandle, RtValue::Stack(ret.peak_mem as i32));
              ret.peak_mem += vdata.ty().size();
            }
          }
        }
      }
    }
    ret
  }

  fn memory_usage(&self) -> i32 {
    self.peak_mem as i32
  }

  fn desicions(&self) -> &HashMap<Value, RtValue> {
    &self.mapping
  }
}
