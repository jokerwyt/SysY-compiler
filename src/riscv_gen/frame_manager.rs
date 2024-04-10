use std::collections::HashSet;

use koopa::ir::{FunctionData, Program, Value};

#[allow(unused)]
use super::reg_allocators::{
  crazy_spiller::CrazySpiller, first_come_first_serve::FirstComeFirstServe, greedy::Greedy,
  RegisterAllocator,
};

use super::{
  riscv_isa::{Reg, FUNC_ARG_REGS},
  rtvalue::RtValue,
};

pub struct FrameManager<'a, Allocator = Greedy>
where
  Allocator: RegisterAllocator,
{
  #[allow(dead_code)]
  prog: &'a Program,
  func: &'a FunctionData,

  /// Frame
  /// (High addr) Saved Registers | Local Variables | Outgoing Arguments (Low addr, Sp)
  /// Saved Registers: [Sp + outgoing_args_cnt * 4 + allocator.mem_usage() * 4, Sp + frame_len)
  /// Local Variables: [Sp + outgoing_args_cnt * 4, Sp + outgoing_args_cnt * 4 + allocator.mem_usage() * 4)
  /// Outgoing Arguments: [Sp, outgoing_args_cnt * 4)
  pub frame_len: i32,

  outgoing_args_cnt: i32,

  allocator: Allocator,

  /// Registers that may be modified in this function (i.e. from the start label to ret)
  /// do not include T0 and T1.
  reg_occupied: HashSet<Reg>,
}

impl<'a, Allocator> FrameManager<'a, Allocator>
where
  Allocator: RegisterAllocator,
{
  pub fn new(prog: &'a Program, func: &'a FunctionData, available_regs: &[Reg]) -> Self {
    let mut manager = Self {
      prog,
      func,
      frame_len: 0,
      allocator: Allocator::new(func, available_regs),
      reg_occupied: HashSet::new(),
      outgoing_args_cnt: 0,
    };

    // Outgoing Arguments part.
    let mut longest_args = 0;
    for (_vhandle, vdata) in func.dfg().values() {
      if let koopa::ir::ValueKind::Call(call) = vdata.kind() {
        let params = call.args().len();
        longest_args = longest_args.max(params);
      }
    }

    manager.outgoing_args_cnt = ((longest_args as i32) - 8).max(0);

    // there is function call inside.
    manager.reg_occupied = manager.allocator.reg_used();

    // Ra are implicitly used by return.
    manager.reg_occupied.insert(Reg::Ra);

    // Saved Registers part.
    manager.frame_len = 4 * (manager.reg_occupied.len() as i32)
      + manager.allocator.memory_usage()
      + 4 * manager.outgoing_args_cnt;

    // align to 16
    manager.frame_len = (manager.frame_len + 15) & !15;

    manager
  }

  /// Return the offset to Sp of saved register in the frame.
  pub fn reg_buffer_loc(&self, reg: &Reg) -> RtValue {
    let idx = self.reg_occupied.iter().position(|r| r == reg).unwrap();
    RtValue::Stack(4 * (idx as i32) + self.allocator.memory_usage() + 4 * self.outgoing_args_cnt)
  }

  pub fn func_data(&self) -> &FunctionData {
    self.func
  }

  /// Return RtValue of local values.
  pub fn local_value(&self, val: &Value) -> RtValue {
    assert!(val.is_global() == false);
    let vdata = self.func_data().dfg().value(*val);
    // part1. handle some special cases.
    match vdata.kind() {
      koopa::ir::ValueKind::ZeroInit(_)
      | koopa::ir::ValueKind::Undef(_)
      | koopa::ir::ValueKind::Aggregate(_) => panic!("Unexpected value kind"),

      koopa::ir::ValueKind::Integer(v) => return RtValue::Integer(v.value()),
      koopa::ir::ValueKind::FuncArgRef(arg) => {
        if arg.index() >= FUNC_ARG_REGS.len() {
          return RtValue::Stack((arg.index() - FUNC_ARG_REGS.len()) as i32 * 4 + self.frame_len);
        } else {
          /* The allocator will assign the correct reg to it */
        }
      }
      koopa::ir::ValueKind::BlockArgRef(_) => unimplemented!("BlockArgRef"),
      koopa::ir::ValueKind::GlobalAlloc(_) => panic!("Unexpected value kind"),
      _ => {}
    }
    // part2. handle local instructions or func arg refs.
    assert!(
      vdata.kind().is_local_inst() || matches!(vdata.kind(), koopa::ir::ValueKind::FuncArgRef(_))
    );
    let loc = self.allocator.decision(val);
    match loc {
      RtValue::Integer(_) | RtValue::Reg(_) | RtValue::RegRef(_) | RtValue::Label(_) => return loc,
      RtValue::SpOffset(ofs_from_0) => {
        return RtValue::SpOffset(ofs_from_0 + self.outgoing_args_cnt * 4);
      }
      RtValue::Stack(ofs_from_0) => {
        return RtValue::Stack(ofs_from_0 + self.outgoing_args_cnt * 4);
      }
    };
    // dbg!(self.func_data().dfg().value(*val).ty(), ret);
  }

  /// Outgoing arg rtval for next call.
  pub(crate) fn next_args_rtval(&self, idx: usize) -> RtValue {
    if idx >= FUNC_ARG_REGS.len() {
      RtValue::Stack((idx - FUNC_ARG_REGS.len()) as i32 * 4)
    } else {
      RtValue::Reg(FUNC_ARG_REGS[idx])
    }
  }

  pub(crate) fn need_caller_saved_regs(&self) -> HashSet<Reg> {
    self
      .reg_occupied
      .clone()
      .into_iter()
      .filter(|reg| reg.is_caller_saved())
      .collect()
  }

  pub(crate) fn need_callee_saved_regs(&self) -> HashSet<Reg> {
    self
      .reg_occupied
      .clone()
      .into_iter()
      .filter(|reg| reg.is_callee_saved())
      .collect()
  }
}
