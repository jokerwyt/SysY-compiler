use std::collections::HashMap;

use koopa::ir::{FunctionData, Value};

use super::riscv_isa::{Imm, Imm12, Inst, Reg, RiscvProg};

pub struct FrameManager<'a, Allocator>
where
  Allocator: FrameAllocator,
{
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

#[derive(Clone, Copy)]
pub enum FrameAlloc {
  SpOffset(i32),
  Reg(Reg),
}

#[derive(Clone)]
pub enum AbstractAlloc {
  Mem(i32),
  Reg(Reg),
}

impl<'a, Allocator> FrameManager<'a, Allocator>
where
  Allocator: FrameAllocator,
{
  pub fn new(func: &'a FunctionData, available_regs: &[Reg]) -> Self {
    let mut manager = Self {
      func,
      frame_len: 0,
      allocator: Allocator::new(func, available_regs),
      active_reg: vec![],
      outgoing_args_cnt: 0,
    };

    // Outgoing Arguments part.
    let mut is_leave_func = false;
    let mut longest_args = 0;
    for (vhandle, vdata) in func.dfg().values() {
      if let koopa::ir::ValueKind::Call(call) = vdata.kind() {
        let params = call.args().len();
        longest_args = longest_args.max(params);
        is_leave_func = true;
      }
    }

    manager.outgoing_args_cnt = ((longest_args as i32) - 8).max(0);

    if is_leave_func == false {
      // there is function call inside.
      manager.active_reg = manager.allocator.reg_used();
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

    manager
  }

  /// Return the offset to Sp of saved register in the frame.
  pub fn reg_loc(&self, reg: &Reg) -> FrameAlloc {
    let idx = self.active_reg.iter().position(|r| r == reg).unwrap();
    FrameAlloc::SpOffset(
      4 * (idx as i32) + self.allocator.memory_usage() + 4 * self.outgoing_args_cnt,
    )
  }

  /// Return the allocation of local values in the frame.
  pub fn loc(&self, val: &Value) -> FrameAlloc {
    match self.allocator.alloc(val) {
      AbstractAlloc::Mem(i32) => FrameAlloc::SpOffset(i32 + 4 * self.outgoing_args_cnt),
      AbstractAlloc::Reg(reg) => FrameAlloc::Reg(reg),
    }
  }

  pub(crate) fn arg_loc(&self, idx: usize) -> FrameAlloc {
    let arg_regs = vec![
      Reg::A0,
      Reg::A1,
      Reg::A2,
      Reg::A3,
      Reg::A4,
      Reg::A5,
      Reg::A6,
      Reg::A7,
    ];

    if idx >= arg_regs.len() {
      FrameAlloc::SpOffset((idx - arg_regs.len()) as i32 * 4)
    } else {
      FrameAlloc::Reg(arg_regs[idx])
    }
  }
}

pub trait FrameAllocator {
  fn new(func: &FunctionData, available_regs: &[Reg]) -> Self;

  /// Return the number of stack needed for local variables.
  /// Note that: Frame size = Saved Registers + Local Variables + Outgoing Arguments
  /// Here we only consider Local Variables part.
  fn memory_usage(&self) -> i32;

  /// All variables that mapped to either[0, memory_usage), or registers.
  fn get_mapping(&self) -> &HashMap<Value, AbstractAlloc>;

  fn alloc(&self, value: &Value) -> AbstractAlloc {
    self.get_mapping().get(value).unwrap().clone()
  }

  fn reg_used(&self) -> Vec<Reg> {
    self
      .get_mapping()
      .values()
      .filter_map(|alloc| match alloc {
        AbstractAlloc::Reg(reg) => Some(reg.clone()),
        _ => None,
      })
      .collect()
  }
}

/// It spills all variables to the stack.
pub struct CrazySpiller {
  peak_mem: usize,
  mapping: HashMap<Value, AbstractAlloc>,
}

impl FrameAllocator for CrazySpiller {
  fn new(func: &FunctionData, available_regs: &[Reg]) -> Self {
    let mut ret = Self {
      peak_mem: 0,
      mapping: HashMap::new(),
    };

    for (vhandle, vdata) in func.dfg().values() {
      match vdata.kind() {
        koopa::ir::ValueKind::GlobalAlloc(_)
        | koopa::ir::ValueKind::Integer(_)
        | koopa::ir::ValueKind::ZeroInit(_)
        | koopa::ir::ValueKind::Undef(_)
        | koopa::ir::ValueKind::Aggregate(_)
        | koopa::ir::ValueKind::FuncArgRef(_)
        | koopa::ir::ValueKind::BlockArgRef(_) => panic!("Unexpected value kind"),

        koopa::ir::ValueKind::Alloc(_)
        | koopa::ir::ValueKind::Load(_)
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
              .insert(*vhandle, AbstractAlloc::Mem(ret.peak_mem as i32));
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

  fn get_mapping(&self) -> &HashMap<Value, AbstractAlloc> {
    &self.mapping
  }
}
