use std::collections::HashMap;

use koopa::ir::{FunctionData, Value};

use crate::koopa_gen::gen::TypeUtils;

use super::{
  frame_manager::{FrameAllocator, RtValue},
  riscv_isa::Reg,
};

/// It spills all variables to the stack.
pub struct CrazySpiller {
  peak_mem: usize,

  /// Note that we don't know the frame size now.
  /// Therefore, the offset in Stack and SpOffset variant is from 0..peak_mem, instead of Sp offset.
  /// Actually we should add outgoing_args_cnt * 4 to them.
  mapping: HashMap<Value, RtValue>,
}

impl FrameAllocator for CrazySpiller {
  fn new(func: &FunctionData, _available_regs: &[Reg]) -> Self {
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
        | koopa::ir::ValueKind::FuncArgRef(_)
        | koopa::ir::ValueKind::Integer(_)
        | koopa::ir::ValueKind::BlockArgRef(_) => panic!("Unexpected value kind"),

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

/*

FirstComeFirstServe:

running test "perf/00_bitset1" ... PASSED
time elapsed: 0H-0M-2S-527645us
running test "perf/01_bitset2" ... PASSED
time elapsed: 0H-0M-5S-242720us
running test "perf/02_bitset3" ... PASSED
time elapsed: 0H-0M-7S-593520us
running test "perf/03_mm1" ... PASSED
time elapsed: 0H-0M-15S-826678us
running test "perf/04_mm2" ... PASSED
time elapsed: 0H-0M-11S-908456us
running test "perf/05_mm3" ... PASSED
time elapsed: 0H-0M-7S-944928us
running test "perf/06_mv1" ... zPASSED
time elapsed: 0H-0M-8S-299798us
running test "perf/07_mv2" ... PASSED
time elapsed: 0H-0M-4S-518682us
running test "perf/08_mv3" ... PASSED
time elapsed: 0H-0M-6S-98433us
running test "perf/09_spmv1" ... PASSED
time elapsed: 0H-0M-5S-872928us
running test "perf/10_spmv2" ... PASSED
time elapsed: 0H-0M-4S-49810us
running test "perf/11_spmv3" ... PASSED
time elapsed: 0H-0M-5S-708408us
running test "perf/12_fft0" ... PASSED
time elapsed: 0H-0M-7S-413194us
running test "perf/13_fft1" ... PASSED
time elapsed: 0H-0M-16S-248265us
running test "perf/14_fft2" ... PASSED
time elapsed: 0H-0M-16S-53609us
running test "perf/15_transpose0" ... PASSED
time elapsed: 0H-0M-5S-427398us
running test "perf/16_transpose1" ... PASSED
time elapsed: 0H-0M-8S-628133us
running test "perf/17_transpose2" ... PASSED
time elapsed: 0H-0M-7S-960903us
running test "perf/18_brainfuck-bootstrap" ... PASSED
time elapsed: 0H-0M-36S-514612us
running test "perf/19_brainfuck-calculator" ... PASSED
time elapsed: 0H-0M-42S-598605us
PASSED (130/130)

*/
pub struct FirstComeFirstServe {
  peak_mem: usize,

  /// Note that we don't know the frame size now.
  /// Therefore, the offset in Stack and SpOffset variant is from 0..peak_mem, instead of Sp offset.
  /// Actually we should add outgoing_args_cnt * 4 to them.
  mapping: HashMap<Value, RtValue>,
}

impl FrameAllocator for FirstComeFirstServe {
  fn new(func: &FunctionData, available_regs: &[Reg]) -> Self {
    let mut regs = available_regs.iter().cloned().collect::<Vec<_>>();

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
        | koopa::ir::ValueKind::FuncArgRef(_)
        | koopa::ir::ValueKind::Integer(_)
        | koopa::ir::ValueKind::BlockArgRef(_) => panic!("Unexpected value kind"),

        koopa::ir::ValueKind::Alloc(_) => {
          if vdata.ty().ptr_inner().is_array() == false && regs.is_empty() == false {
            let reg = regs.pop().unwrap();
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
            if vdata.ty().size() == 4 && regs.is_empty() == false {
              let reg = regs.pop().unwrap();
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
