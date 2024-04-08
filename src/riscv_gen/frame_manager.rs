use std::collections::HashMap;

use koopa::ir::{FunctionData, Program, Value};

use crate::koopa_gen::gen::TypeUtils;

use super::riscv_isa::{Reg, FUNC_ARG_REGS};

pub struct FrameManager<'a, Allocator>
where
  Allocator: FrameAllocator,
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

  /// Registers that need to be saved.
  /// We don't care about other registers, since they are not active;
  pub active_reg: Vec<Reg>,
}

/// This struct is used to describe the value or the storage location of it in runtime.
#[derive(Clone, Copy, Debug)]
pub enum RtValue {
  Integer(i32),  // Integer
  SpOffset(i32), // the value is Sp+offset.
  Stack(i32),    // the value is 4B. Its address is Sp+offset.
  Reg(Reg),      // when value itself is stored in a register
  RegRef(Reg),   // The value is a ptr pointing to a register.
                 // It's helpful when you want to use reg scheduler for things like alloc.
}

impl RtValue {}

#[derive(Clone)]
pub enum AbstractAlloc {
  Mem(i32),
  Reg(Reg),
}

impl<'a, Allocator> FrameManager<'a, Allocator>
where
  Allocator: FrameAllocator,
{
  pub fn new(prog: &'a Program, func: &'a FunctionData, available_regs: &[Reg]) -> Self {
    let mut manager = Self {
      prog,
      func,
      frame_len: 0,
      allocator: Allocator::new(func, available_regs),
      active_reg: vec![],
      outgoing_args_cnt: 0,
    };

    // Outgoing Arguments part.
    let mut is_leave_func = true;
    let mut longest_args = 0;
    for (_vhandle, vdata) in func.dfg().values() {
      if let koopa::ir::ValueKind::Call(call) = vdata.kind() {
        let params = call.args().len();
        longest_args = longest_args.max(params);
        is_leave_func = false;
      }
    }

    manager.outgoing_args_cnt = ((longest_args as i32) - 8).max(0);

    if is_leave_func == false {
      // there is function call inside.
      manager.active_reg = manager.allocator.reg_used();

      // Ra and A0 are implicitly used in non-leave func.
      if manager.active_reg.contains(&Reg::Ra) == false {
        manager.active_reg.push(Reg::Ra);
      }
      if manager.active_reg.contains(&Reg::A0) == false {
        manager.active_reg.push(Reg::A0);
      }
    } else {
      // only save callee saved registers, since there is no function call inside.
      manager.active_reg = manager
        .allocator
        .reg_used()
        .iter()
        .filter(|reg| reg.is_callee_saved())
        .cloned()
        .collect();
    }

    // Saved Registers part.
    manager.frame_len = 4 * (manager.active_reg.len() as i32)
      + manager.allocator.memory_usage()
      + 4 * manager.outgoing_args_cnt;

    // align to 16
    manager.frame_len = (manager.frame_len + 15) & !15;

    manager
  }

  /// Return the offset to Sp of saved register in the frame.
  pub fn reg_buffer_loc(&self, reg: &Reg) -> RtValue {
    let idx = self.active_reg.iter().position(|r| r == reg).unwrap();
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
        if arg.index() >= 8 {
          return RtValue::Stack((arg.index() - 8) as i32 * 4 + self.frame_len);
        } else {
          return self.func_call_arg_rtval(arg.index());
        }
      }
      koopa::ir::ValueKind::BlockArgRef(_) => unimplemented!("BlockArgRef"),
      koopa::ir::ValueKind::GlobalAlloc(_) => panic!("Unexpected value kind"),
      _ => {}
    }
    // part2. handle local instructions.
    assert!(vdata.kind().is_local_inst());
    let loc = self.allocator.decision(val);
    match loc {
      RtValue::Integer(_) | RtValue::Reg(_) | RtValue::RegRef(_) => return loc,
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
  pub(crate) fn func_call_arg_rtval(&self, idx: usize) -> RtValue {
    if idx >= FUNC_ARG_REGS.len() {
      RtValue::Stack((idx - FUNC_ARG_REGS.len()) as i32 * 4)
    } else {
      RtValue::Reg(FUNC_ARG_REGS[idx])
    }
  }

  pub(crate) fn need_caller_saved_regs(&self) -> Vec<Reg> {
    self
      .active_reg
      .clone()
      .into_iter()
      .filter(|reg| reg.is_caller_saved())
      .collect()
  }

  pub(crate) fn need_callee_saved_regs(&self) -> Vec<Reg> {
    self
      .active_reg
      .clone()
      .into_iter()
      .filter(|reg| reg.is_callee_saved())
      .collect()
  }
}

pub trait FrameAllocator {
  fn new(func: &FunctionData, available_regs: &[Reg]) -> Self;

  /// Return the number of stack needed for local variables.
  /// Note that: Frame size = Saved Registers + Local Variables + Outgoing Arguments
  /// Here we only consider Local Variables part.
  fn memory_usage(&self) -> i32;

  /// We assume there is an interval on stack for us to use.
  /// And the offset we give out is from 0..mem_usage().
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
