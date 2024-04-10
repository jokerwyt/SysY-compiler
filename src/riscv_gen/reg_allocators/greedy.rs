use std::collections::{hash_map::Keys, HashMap};

use koopa::ir::{entities::ValueData, BasicBlock, FunctionData, Value};

use crate::{
  koopa_gen::gen::TypeUtils,
  riscv_gen::{
    riscv_isa::{Reg, FUNC_ARG_REGS},
    rtvalue::RtValue,
  },
};

use super::RegisterAllocator;

pub struct Greedy {
  peak_mem: usize,

  /// Note that we don't know the frame size now.
  /// Therefore, the offset in Stack and SpOffset variant is from 0..peak_mem, instead of Sp offset.
  /// Actually we should add outgoing_args_cnt * 4 to them.
  binding: HashMap<Value, RtValue>,
}

impl RegisterAllocator for Greedy {
  fn new(func: &FunctionData, available_regs: &[Reg]) -> Self {
    let available_regs = available_regs.iter().cloned().collect::<Vec<_>>();
    let mut ret = Self {
      peak_mem: 0,
      binding: HashMap::new(),
    };

    let liveness = Liveness::new(func);

    // interval considering values and their users
    let interval: HashMap<Value, (usize, usize)> = liveness
      .values()
      .filter_map(|val| {
        let mut occur: Vec<(usize, usize)> = func
          .dfg()
          .value(*val)
          .used_by()
          .iter()
          .map(|value| liveness.interval(*value))
          .collect();

        occur.push(liveness.interval(*val));

        // get first dimension min and second dimension max
        let (min, _) = occur.iter().min_by_key(|(a, _)| *a).unwrap();
        let (_, max) = occur.iter().max_by_key(|(_, b)| *b).unwrap();
        Some((*val, (*min, *max)))
      })
      .collect();

    // bind all FuncArgRef first
    for (vhandle, vdata) in func.dfg().values() {
      match vdata.kind() {
        koopa::ir::ValueKind::FuncArgRef(arg) => {
          if arg.index() >= FUNC_ARG_REGS.len() {
            continue;
          }
          let reg = FUNC_ARG_REGS[arg.index()];
          // This FuncArgRef must be binded to this register.
          ret.binding.insert(*vhandle, RtValue::Reg(reg));
        }
        _ => { /* handle next */ }
      }
    }

    // calc the weight of each value
    // = number of values that use this value / interval length
    let mut weight: Vec<(Value, f32)> = liveness
      .values()
      .map(|v| {
        let (min, max) = interval.get(v).unwrap();
        let len = max - min + 1;
        let used_by = func.dfg().value(*v).used_by().len() as f32;
        (*v, used_by / (len as f32))
      })
      .collect();

    // sort by weight
    weight.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
    assert!(weight.len() <= 1 || weight.windows(2).all(|w| w[0].1 >= w[1].1));

    for (val, _weight) in weight {
      if ret.binding.contains_key(&val) {
        // skip already binded values
        continue;
      }

      let is_alloc = matches!(func.dfg().value(val).kind(), koopa::ir::ValueKind::Alloc(_));

      let size = func.dfg().value(val).alloc_size();

      if size > 4 {
        // only support 4B in reg now.
        continue;
      }

      // 1-size array allocation should also spill.
      if is_alloc && func.dfg().value(val).ty().ptr_inner().is_array() {
        continue;
      }

      let (l, r) = interval.get(&val).unwrap();
      let occupied_regs: Vec<Reg> = ret
        .binding
        .iter()
        .filter_map(|(value, rtval)| {
          let (ll, rr) = interval.get(value).unwrap();

          // if [l, r] and [ll, rr] has intersection
          if l <= rr && r >= ll {
            match rtval {
              RtValue::Reg(reg) => Some(*reg),
              RtValue::RegRef(reg) => Some(*reg),
              _ => panic!("Unexpected RtValue"),
            }
          } else {
            None
          }
        })
        .collect();

      available_regs.iter().any(|reg| {
        if !occupied_regs.contains(reg) {
          ret.binding.insert(
            val,
            if is_alloc {
              RtValue::RegRef(*reg)
            } else {
              RtValue::Reg(*reg)
            },
          );
          return true;
        }
        false
      });
    }

    for val in liveness.values() {
      if ret.binding.contains_key(&val) == false {
        // all left values are 4B.
        let is_alloc = matches!(
          func.dfg().value(*val).kind(),
          koopa::ir::ValueKind::Alloc(_)
        );
        let size = func.dfg().value(*val).alloc_size();
        ret.binding.insert(
          *val,
          if is_alloc {
            RtValue::SpOffset(ret.peak_mem as i32)
          } else {
            RtValue::Stack(ret.peak_mem as i32)
          },
        );
        ret.peak_mem += size;
      }
    }
    ret
  }

  fn memory_usage(&self) -> i32 {
    self.peak_mem as i32
  }

  fn desicions(&self) -> &HashMap<Value, RtValue> {
    &self.binding
  }
}

trait AllocSize {
  fn alloc_size(&self) -> usize;
}

impl AllocSize for ValueData {
  fn alloc_size(&self) -> usize {
    match self.kind() {
      koopa::ir::ValueKind::Alloc(_) => self.ty().ptr_inner().size(),
      _ => self.ty().size(),
    }
  }
}

pub(crate) struct Liveness<'a> {
  v_idx: HashMap<Value, usize>,
  b_idx: HashMap<BasicBlock, usize>,
  func_data: &'a FunctionData,
  earliest: HashMap<BasicBlock, usize>, // the earliest block that this basic block can reach
  latest: HashMap<BasicBlock, usize>,   // the latest block that can reach this basic block
}

impl<'a> Liveness<'a> {
  fn first_inst_idx(&self, bb: BasicBlock) -> usize {
    let first_inst = self
      .func_data
      .layout()
      .bbs()
      .node(&bb)
      .unwrap()
      .insts()
      .front_key()
      .unwrap();
    self.get_value_idx(&first_inst)
  }

  fn last_inst_idx(&self, bb: BasicBlock) -> usize {
    let last_inst = self
      .func_data
      .layout()
      .bbs()
      .node(&bb)
      .unwrap()
      .insts()
      .back_key()
      .unwrap();
    self.get_value_idx(&last_inst)
  }

  /// return the interval of this value
  pub fn interval(&self, val: Value) -> (usize, usize) {
    // TODO: optimize for value within one block

    let bb = self.func_data.layout().parent_bb(val);
    if bb == None {
      // this value is a FuncArgRef
      assert!(matches!(
        self.func_data.dfg().value(val).kind(),
        koopa::ir::ValueKind::FuncArgRef(_)
      ));
      return (0, self.get_value_idx(&val));
    }
    let bb = bb.unwrap();

    let earliest = self.earliest_succ_bb(bb);
    let latest = self.latest_pred_bb(bb);

    let l = self.first_inst_idx(self.block(earliest));
    let r = self.last_inst_idx(self.block(latest));

    (l, r)
  }

  pub fn new(fdata: &'a FunctionData) -> Self {
    // let mut linear_order = Vec::new();
    let mut idx = HashMap::new();

    // insert all FuncArgRef first
    for (vhandle, vdata) in fdata.dfg().values() {
      if let koopa::ir::ValueKind::FuncArgRef(_) = vdata.kind() {
        idx.insert(*vhandle, idx.len());
      }
    }

    for (_bhandle, _bnode) in fdata.layout().bbs() {
      for (inst, _) in _bnode.insts() {
        idx.insert(*inst, idx.len());
      }
    }

    let mut ret = Self {
      func_data: fdata,
      earliest: HashMap::new(),
      latest: HashMap::new(),
      b_idx: HashMap::new(),
      v_idx: idx,
    };

    fdata
      .layout()
      .bbs()
      .iter()
      .enumerate()
      .for_each(|(idx, (bb, _))| {
        ret.earliest.insert(*bb, idx);
        ret.latest.insert(*bb, idx);
        ret.b_idx.insert(*bb, idx);
      });

    let mut changed = fdata
      .layout()
      .bbs()
      .iter()
      .map(|(bb, _)| *bb)
      .collect::<Vec<BasicBlock>>();

    while changed.is_empty() == false {
      let mut next_changed = Vec::new();
      for bb in changed {
        let mut earliest = *ret.earliest.get(&bb).unwrap();
        let mut latest = *ret.latest.get(&bb).unwrap();

        let pred = fdata
          .dfg()
          .bb(bb)
          .used_by()
          .iter()
          .map(|val| fdata.layout().parent_bb(*val).unwrap())
          .collect::<Vec<BasicBlock>>();

        let last_inst = fdata
          .layout()
          .bbs()
          .node(&bb)
          .unwrap()
          .insts()
          .back_key()
          .unwrap();
        let succ = fdata.dfg().value(*last_inst).succs();

        for pred in pred {
          latest = latest.max(*ret.latest.get(&pred).unwrap());
        }
        for succ in succ {
          earliest = earliest.min(*ret.earliest.get(&succ).unwrap());
        }

        if earliest != *ret.earliest.get(&bb).unwrap() || latest != *ret.latest.get(&bb).unwrap() {
          next_changed.push(bb);
          ret.earliest.insert(bb, earliest);
          ret.latest.insert(bb, latest);
        }
      }

      changed = next_changed;
    }

    ret
  }

  pub fn block(&self, idx: usize) -> BasicBlock {
    *self.func_data.layout().bbs().iter().nth(idx).unwrap().0
  }

  pub fn earliest_succ_bb(&self, bb: BasicBlock) -> usize {
    *self.earliest.get(&bb).unwrap()
  }

  pub fn latest_pred_bb(&self, bb: BasicBlock) -> usize {
    *self.latest.get(&bb).unwrap()
  }

  pub fn values(&self) -> Keys<Value, usize> {
    self.v_idx.keys()
  }

  fn get_value_idx(&self, value: &Value) -> usize {
    *self.v_idx.get(value).unwrap()
  }

  fn block_idx(&self, bb: BasicBlock) -> usize {
    *self.b_idx.get(&bb).unwrap()
  }
}

trait GetSuccBB {
  fn succs(&self) -> Vec<BasicBlock>;
}

impl GetSuccBB for ValueData {
  fn succs(&self) -> Vec<BasicBlock> {
    match self.kind() {
      koopa::ir::ValueKind::Branch(branch) => {
        let mut ret = Vec::new();
        ret.push(branch.true_bb());
        ret.push(branch.false_bb());
        ret
      }
      koopa::ir::ValueKind::Jump(jump) => vec![jump.target()],
      koopa::ir::ValueKind::Return(_) => vec![],
      _ => todo!(),
    }
  }
}
