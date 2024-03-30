//! We implement the IR generation for the SysY language in this module.
//! The comments here demonstrate how we pass the AST of Sys-Y and generate Koopa IR.
//!
//! pub enum AstData {
//!   CompUnit(CompUnit),
//!     Produces a [koopa::ir::Program].
//!
//!   Decl(Decl),
//!     Takes a base BB.
//!
//!   ConstDecl(ConstDecl),
//!     Takes a base BB.
//!
//!   BType,
//!     Don't care.
//!
//!   ConstDef(ConstDef),
//!     Takes a base BB if local. produces a [koopa::ir::Value].
//!
//!     If const int, it's an Integer.
//!     If global const array, it's a ptr from GlobalAlloc initialized with Aggregate.
//!     If local const array, it's a ptr from Alloc followed by Aggregate store initialization.
//!
//!     Stored into SymTableEntryData: IntDef or ArrayDef
//!
//!   ConstInitVal(ConstInitVal),
//!     Produces Value::Int or Value::Aggregate.
//!
//!   VarDecl(VarDecl),
//!     Takes a BB.
//!
//!   VarDef(VarDef),
//!     Takes a BB, produces a [koopa::ir::Value].
//!
//!     If global [int|array], it's a ptr from GlobalAlloc initialized with Int or Aggregate,
//!     If local [int|array], it's a ptr from Alloc followed by manual initialization.
//!
//!     Stored into SymTableEntryData: IntDef or ArrayDef
//!
//!   InitVal(InitVal),
//!     If local, it takes a BB, a Value ptr from Alloc, and option shape, produces nothing
//!     If Global, takes nothing and produces a Int or Aggregate.
//!
//!     If global initval:
//!       It must be a Int / Aggregate after const_eval, and will be used in GlobalAlloc initialized.
//!
//!     If local initval:
//!       We can suppose that every Value inside needs computation on the spot.
//!       The ptr and shape will be transferred down for initializing.
//!       The initialization will be done locally, and no side effect.
//!
//!   FuncDef(FuncDef),
//!     Takes a [koopa::ir::Program], produces a [koopa::ir::Function].
//!
//!     Stored into SymTableEntryData: FuncDef
//!
//!   FuncFParams(FuncFParams),
//!     Takes a BB.
//!
//!   FuncFParam(FuncFParam),
//!     Takes the entry BB, produces a [koopa::ir::Value].
//!     The FuncArgRef value provided by the function declaration will be copied into an
//!     manually Alloc. The originall value will be discarded.
//!
//!     For int, it's a *i32 Value from Alloc.
//!     For array, it's *[i32, 3] for int[][3] for example, also from Alloc.
//!
//!     The generated Value will be inserted into symbol table. IntDef / FuncParamArrayDef.
//!
//!
//!   Block(Block),
//!     Takes an entry BB, return the last BB.
//!
//!     When passing Block, the outside gives it the first bb and it will return the last
//!     unclosed basic block. The control will continue on the next Values of that block.
//!
//!     The place the BB is generated is responsible for inserting it into DFG.
//!
//!   BlockItem(BlockItem),
//!     Takes an entry BB, return the last BB.
//!
//!   Stmt(Stmt),
//!     Takes an base BB, return an optional last BB.
//!
//!     IfElse Stmt:
//!       The eval is placed at the base BB, and two BB called br1 and br0 will be
//!       generated. Another empty block will be created as the last BB.
//!
//!     While Stmt:
//!       At least basic blocks: cond, body, and another new "next block" as last BB.
//!       Cond block and "last block" handle will be stored in AstData.
//!
//!     Break Stmt:
//!       Find the nearest while and jump to its next block.
//!       No last block.
//!
//!     Continue Stmt:
//!       Jumps to the nearest while's cond block.
//!       No last block.
//!
//!   Exp(Exp),
//!     Takes a base BB, produces a [koopa::ir::Value].
//!
//!     We should first check if it's const. If it's, return an Integer Value directly.
//!     Otherwise, it will be a ptr, or a i32.
//!
//!
//!   LVal(LVal),
//!     Takes a BB, produces a [koopa::ir::Value].
//!     Ptr or i32.
//!
//!     Find the LVal in symbol tables, and consider cases:
//!     1. for const int, it shoule be Int.
//!     2. for other cases (const array, variable int, variable array), it's a ptr.
//!
//!     If it's an array deref, return the corresponding ptr type. (*i32, *[i32, 5], ...)
//!     Partial deref and complete deref will be handled consitently.
//!
//!   PrimaryExp(PrimaryExp),
//!     Takes a BB, produces a [koopa::ir::Value].
//!
//!     Ptr (for all LVal, some Exp),
//!     or i32 (for all Number and some other Exp).
//!
//!   UnaryExp(UnaryExp),
//!     Takes a BB, produces a [koopa::ir::Value].
//!
//!     For PrimaryExp, take the sub value.
//!     For function call, the produced ValueKind is Call, and the type will be i32 or unit.
//!     For arithmetic, check the sub UnaryExp:
//!       1) if i32, then take the Value.
//!       2) if ptr, then assert(*i32), and use Load to make it i32.
//!
//!
//!   FuncRParams(FuncRParams),
//!     Don't care.
//!     Simply pass the Value list to the function call.
//!
//!   /// Including grammar non-terminators:\
//!   /// MulExp, AddExp, RelExp, EqExp, LAndExp, LOrExp\
//!   /// Lhs: [AstData::BinaryExp]\
//!   /// Rhs: [AstData::UnaryExp] | [AstData::BinaryExp]
//!   BinaryExp(BinaryExp),
//!     Takes a BB, produces a [koopa::ir::Value].
//!     Pointers: *i32 ptr will be Loaded. Other pointers will panic.
//!
//!   ConstExp(ConstExp),
//!     Takes a BB, produces a [koopa::ir::Value]
//! }

use core::panic;

use koopa::ir::builder::{
  BasicBlockBuilder, GlobalBuilder, GlobalInstBuilder, LocalBuilder, LocalInstBuilder,
  ValueBuilder, ValueInserter,
};
use koopa::ir::{self, BasicBlock, Function, FunctionData, Program, Type, Value};

use crate::ast::{AstData, AstNodeId, BinaryOp, ConstInitVal, Decl, FuncFParam, InitVal, UnaryOp};
use crate::ast_data_write_as;
use crate::sym_table::{SymIdent, SymTableEntry, SymTableEntryData};
use crate::utils::dfs::{DfsVisitor, TreeId};
use crate::utils::Res;
use crate::{ast, ast::ast_nodes_read, ast::ast_nodes_write, ast_is};

pub struct KoopaGen;

impl KoopaGen {
  /// Eval all compile-time constant int. (except const array deref)
  fn eval_const_int(ast_id: &AstNodeId) -> i32 {
    let ast_data = ast_id.get_ast_data();
    match ast_data {
      ast::AstData::Exp(exp) => {
        return Self::eval_const_int(&exp.l_or_exp);
      }
      ast::AstData::LVal(lval) => {
        // Some lval can be a constant.
        // Note Again: we only consider the case where the lval is a single value.
        if lval.is_array() == false {
          return ast_id.find_const_int(lval.ident).unwrap();
        } else {
          panic!("Array deref is not allowed in const eval");
        }
      }
      ast::AstData::PrimaryExp(exp) => match exp {
        ast::PrimaryExp::Exp(sub_exp) => {
          return Self::eval_const_int(&sub_exp);
        }
        ast::PrimaryExp::LVal(sub_lval) => {
          return Self::eval_const_int(&sub_lval);
        }
        ast::PrimaryExp::Number(x) => return x,
      },
      ast::AstData::UnaryExp(uexp) => match uexp {
        ast::UnaryExp::PrimaryExp { pexp, .. } => {
          return Self::eval_const_int(&pexp);
        }
        ast::UnaryExp::Call { .. } => panic!("Function call is not allowed in const eval"),
        ast::UnaryExp::Unary {
          exp: sub_exp, op, ..
        } => {
          let sub_v = Self::eval_const_int(&sub_exp);
          return UnaryOp::eval(op, sub_v);
        }
      },
      ast::AstData::BinaryExp(bexp) => {
        match bexp {
          // But we still need to match since there are two kinds of method to
          // evaluate: (unary | binary)
          ast::BinaryExp::Unary { exp: sub_exp, .. } => {
            return Self::eval_const_int(&sub_exp);
          }
          ast::BinaryExp::Binary { lhs, op, rhs, .. } => {
            let lhs_v = Self::eval_const_int(&lhs);
            let rhs_v = Self::eval_const_int(&rhs);
            return BinaryOp::eval(lhs_v, op, rhs_v);
          }
        }
      }
      ast::AstData::ConstExp(const_exp) => return Self::eval_const_int(&const_exp.0),
      ast::AstData::CompUnit(_)
      | ast::AstData::Decl(_)
      | ast::AstData::ConstDecl(_)
      | ast::AstData::BType
      | ast::AstData::ConstDef(_)
      | ast::AstData::ConstInitVal(_)
      | ast::AstData::VarDecl(_)
      | ast::AstData::VarDef(_)
      | ast::AstData::InitVal(_)
      | ast::AstData::FuncDef(_)
      | ast::AstData::FuncFParams(_)
      | ast::AstData::FuncFParam(_)
      | ast::AstData::Block(_)
      | ast::AstData::BlockItem(_)
      | ast::AstData::Stmt(_)
      | ast::AstData::FuncRParams(_) => panic!("Invalid AstData for const eval"),
    }
  }

  pub fn gen_on_compile_unit(unit_id: &AstNodeId) -> Program {
    unit_id.create_symbol_table();
    let mut prog = Program::new();
    let comp_unit = unit_id.get_ast_data().into_comp_unit();

    for item in comp_unit.items {
      match item.get_ast_data() {
        ast::AstData::Decl(decl) => match decl {
          ast::Decl::ConstDecl(decl) | ast::Decl::VarDecl(decl) => {
            KoopaGen::gen_on_global_decl(&decl, &mut prog)
          }
        },
        ast::AstData::FuncDef(func_def) => {
          // generate the entry basic block, and put all initialized values into the symbol table.
          let params = KoopaGen::gen_on_func_fparams(&func_def.func_f_params);

          let func = prog.new_func(FunctionData::with_param_names(
            func_def.ident.clone(),
            params.clone(),
            match func_def.has_retval {
              true => Type::get_i32(),
              false => Type::get_unit(),
            },
          ));

          // generate the function body
          let func_data = prog.func_mut(func);

          // add function into global symbol table
          SymTableEntry {
            symbol: SymIdent::Func(func_def.ident.clone()),
            kind: SymTableEntryData::FuncDef(func),
            func: None,
          }
          .into_llt(unit_id);

          let entry_bb = func_data
            .dfg_mut()
            .new_bb()
            .basic_block(Some("%entry".to_string()));
          func_data.layout_mut().bbs_mut().extend([entry_bb]);

          // re-Alloc the function parameters, and add them into the function symbol table.
          for (idx, (name, ty)) in params.iter().enumerate() {
            let name = name.clone().unwrap();

            let alloc = func_data.dfg_mut().new_value().alloc(ty.clone());
            let arg = func_data.params()[idx];
            let store = func_data.dfg_mut().new_value().store(arg, alloc);
            func_data
              .layout_mut()
              .bb_mut(entry_bb)
              .insts_mut()
              .extend([alloc, store]);

            let entry = SymTableEntry {
              symbol: SymIdent::Value(name),
              kind: match ty.is_i32() {
                true => SymTableEntryData::VarIntDef(alloc),
                false => SymTableEntryData::FuncParamArrayDef(alloc, ty.clone()),
              },
              func: Some(func),
            };
            entry.into_llt(&item);
          }
          KoopaGen::gen_on_block(&func_def.block, func, entry_bb);
        }
        _ => panic!("Invalid item in CompUnit"),
      }
    }
    prog
  }

  fn gen_on_global_decl(decl_id: &AstNodeId, prog: &mut Program) {
    let decl = decl_id.get_ast_data().into_decl();
    match decl {
      ast::Decl::ConstDecl(const_decl) => {
        for def in const_decl.get_ast_data().into_const_decl().const_defs {
          let const_def = def.get_ast_data().into_const_def();

          // resolve possible index.
          let mut shape = vec![];
          for const_exp in &const_def.idx {
            shape.push(KoopaGen::eval_const_int(const_exp));
          }

          // for const def, see whether it's a single value or an array.
          if const_def.is_array() {
            let aggre = KoopaGen::gen_on_global_init(&const_def.const_init_val, &shape, prog);
            let alloc = prog.new_value().global_alloc(aggre);
            SymTableEntry {
              symbol: SymIdent::Value(const_def.ident.clone()),
              kind: SymTableEntryData::ArrayDef(alloc, shape.into_type()),
              func: None,
            }
            .into_llt(decl_id);
          } else {
            // A Integer Value is inserted into the symbol table.
            let value = KoopaGen::gen_on_global_init(&const_def.const_init_val, &shape, prog);
            SymTableEntry {
              symbol: SymIdent::Value(const_def.ident.clone()),
              kind: SymTableEntryData::ConstIntDef(value.into_i32(prog)),
              func: None,
            }
            .into_llt(decl_id);
          }
        }
      }
      ast::Decl::VarDecl(var_decl) => {
        for def in var_decl.get_ast_data().into_var_decl().var_defs {
          let var_def = def.get_ast_data().into_var_def();

          // resolve possible index.
          let mut shape = vec![];
          for const_exp in &var_def.idx {
            shape.push(KoopaGen::eval_const_int(const_exp));
          }

          // for var def, see whether it's a single value or an array.
          if var_def.is_array() {
            let array_init;
            // A variable doesn't have to be initialized.
            if let Some(init_val) = &var_def.init_val {
              // But if it's initialized, global array must have const initialized list.
              array_init = KoopaGen::gen_on_global_init(init_val, &shape, prog);
            } else {
              // An uninitialized array will be zeroinit.
              array_init = prog.new_value().zero_init(shape.into_type());
            }
            let alloc = prog.new_value().global_alloc(array_init);
            SymTableEntry {
              symbol: SymIdent::Value(var_def.ident.clone()),
              kind: SymTableEntryData::ArrayDef(alloc, shape.into_type()),
              func: None,
            }
            .into_llt(decl_id);
          } else {
            // A Integer Value is inserted into the symbol table.
            let init = if let Some(init_val) = &var_def.init_val {
              KoopaGen::gen_on_global_init(init_val, &vec![], prog).into_i32(prog)
            } else {
              0
            };
            SymTableEntry {
              symbol: SymIdent::Value(var_def.ident.clone()),
              kind: SymTableEntryData::VarIntDef(prog.new_value().integer(init)),
              func: None,
            }
            .into_llt(decl_id);
          }
        }
      }
    }
  }

  fn gen_on_func_fparams(ast_id: &AstNodeId) -> Vec<(Option<String>, Type)> {
    let data = ast_id.get_ast_data().into_func_f_params();

    let mut params = vec![];
    for p in data.params {
      let fparam = p.get_ast_data().into_func_f_param();
      params.push((Some(fparam.name().clone()), fparam.into_type()));
    }
    params
  }

  /// Generate Koopa on a Sys-y Block.
  /// Return the sink BasicBlock.
  fn gen_on_block(ast_id: &AstNodeId, func: Function, base_bb: BasicBlock) -> BasicBlock {
    let data = ast_id.get_ast_data().into_block();
    let mut last_bb = base_bb;

    for item in data.items {
      match item.get_ast_data() {
        AstData::BlockItem(ast::BlockItem::Decl(decl)) => {
          todo!()
        }
        AstData::BlockItem(ast::BlockItem::Stmt(stmt)) => todo!(),
        _ => panic!("Invalid AstData for gen_on_block"),
      }
    }
    last_bb
  }

  /// Generate an Koopa Aggregate or Integer on Sys-Y ConstInitVal or InitVal.
  /// The shape is the reference to the shape of the array.
  /// When the shape is empty, return an Integer.
  /// Otherwise, return an Aggregate.
  fn gen_on_global_init(ast_id: &AstNodeId, shape: &[i32], prog: &mut Program) -> Value {
    let data = ast_id.get_ast_data();

    if shape.is_empty() {
      return match data {
        ast::AstData::ConstInitVal(ast::ConstInitVal::Single(const_exp)) => prog
          .new_value()
          .integer(KoopaGen::eval_const_int(&const_exp)),
        ast::AstData::InitVal(ast::InitVal::Single(exp)) => {
          prog.new_value().integer(KoopaGen::eval_const_int(&exp))
        }
        _ => panic!("Invalid AstData for gen_on_const with shape empty"),
      };
    }

    let seq = match data {
      ast::AstData::ConstInitVal(ast::ConstInitVal::Sequence(seq)) => seq,
      ast::AstData::InitVal(ast::InitVal::Sequence(seq)) => seq,
      _ => panic!("Invalid AstData for gen_on_global_init"),
    };

    // We use a stack to parse the intialization list, and generate an Aggregate.
    // Every element in the stack has a size. For example, the shape is [3][5][7].
    // And all sizes of elements can only be 1, 7, 7 * 5 or 7 * 5 * 3. They are descending from the bottom to top.
    //
    // Reduce:
    // when there are 7 elements with size 1 in the stack, we can pop them and push a new one with size 7 * 1.

    let mut agg_builder = AggregateBuilder::new(shape);

    for (_idx, init_val) in seq.iter().enumerate() {
      match init_val.get_ast_data() {
        ast::AstData::InitVal(InitVal::Single(exp))
        | ast::AstData::ConstInitVal(ConstInitVal::Single(exp)) => agg_builder.push_single(
          prog.new_value().integer(KoopaGen::eval_const_int(&exp)),
          prog,
        ),

        AstData::ConstInitVal(ConstInitVal::Sequence(_))
        | AstData::InitVal(InitVal::Sequence(_)) => {
          let sub_shape = agg_builder.checker.append_sequence(true);
          agg_builder.push_sequence(
            KoopaGen::gen_on_global_init(&init_val, sub_shape, prog),
            prog,
          )
        }
        _ => panic!("Invalid AstData for gen_on_global_init"),
      };
    }

    if agg_builder.checker.progress == 0 {
      return prog.new_value().zero_init(shape.into_type());
    }

    // push zero_init of the stack top type, until the shape is filled.
    // Done in log time.
    while agg_builder.stack.first().unwrap().1 != 0 {
      if agg_builder.checker.can_append_sequence() {
        let zero = prog
          .new_value()
          .zero_init(agg_builder.checker.append_sequence(true).into_type());
        agg_builder.push_sequence(zero, prog);
      } else {
        agg_builder.push_single(prog.new_value().integer(0), prog);
      }
    }
    assert_eq!(agg_builder.stack.len(), 1);
    agg_builder.stack.first().unwrap().2
  }
}

trait IntoType {
  fn into_type(&self) -> Type;
}

impl IntoType for [i32] {
  fn into_type(&self) -> Type {
    let mut ty = Type::get_i32();
    let reversed = self.iter().rev();
    for len in reversed {
      ty = Type::get_array(ty, len.clone() as usize);
    }
    ty
  }
}

impl IntoType for FuncFParam {
  fn into_type(&self) -> Type {
    match self {
      FuncFParam::Single { btype, ident } => Type::get_i32(),
      FuncFParam::Array {
        btype,
        ident,
        shape_no_first_dim,
      } => {
        let mut ty = Type::get_i32();
        for len in shape_no_first_dim.iter().rev() {
          ty = Type::get_array(ty, KoopaGen::eval_const_int(len) as usize);
        }
        ty
      }
    }
  }
}

trait IntoI32 {
  fn into_i32(&self, prog: &Program) -> i32;
}

impl IntoI32 for Value {
  fn into_i32(&self, prog: &Program) -> i32 {
    match prog.borrow_value(self.clone()).kind() {
      ir::ValueKind::Integer(x) => x.value(),
      _ => panic!("Value is not an integer"),
    }
  }
}

struct InitValChecker<'a> {
  expect_shape: &'a [i32],
  progress: i32,
}

impl<'a> InitValChecker<'a> {
  fn new(shape: &'a [i32]) -> Self {
    Self {
      expect_shape: shape,
      progress: 0,
    }
  }

  /// Append a single.
  fn append_single(&mut self) {
    self.progress += 1;
    assert!(self.progress <= self.expect_shape.iter().product());
  }

  fn can_append_sequence(&self) -> bool {
    self.progress % self.expect_shape.last().unwrap() == 0
  }

  /// Append a sequence.
  /// Return the expected shape of the sequence.
  ///
  ///
  /// If the next one is a list, we need to find the expected shape
  /// for example, if we are now targeting at [3][5][7]
  /// if progress is aligned to 5*7 (0, 35, ...) , then 5*7 is the expected shape for this sub init list
  /// if progress is aligned to 7 and not aligned to 5*7, (7, 14, 21, 28),
  ///  then 7 is the expected shape for this sub init list.
  ///
  /// if progress is not aligned to even 7, then we should panic.
  ///
  /// # Panic
  /// Panic if the current progress is not aligned to the last dimension.
  fn append_sequence(&mut self, dry_run: bool) -> &'a [i32] {
    assert!(self.can_append_sequence());

    let mut tail_size = 1;
    let mut start_dim = 1;

    // expect_shape[1..] means sub shape is always smaller than the original one.
    for (idx, size) in self.expect_shape[1..].iter().enumerate().rev() {
      if self.progress % (tail_size * size) != 0 {
        break;
      }
      tail_size *= size;
      start_dim = idx;
    }
    if dry_run == false {
      self.progress += tail_size;
      assert!(self.progress <= self.expect_shape.iter().product());
    }
    &self.expect_shape[start_dim..]
  }
}

struct AggregateBuilder<'a> {
  /// size, start_dim, Value
  stack: Vec<(i32, usize, Value)>,

  expected_shape: &'a [i32],
  checker: InitValChecker<'a>,
}

impl<'a> AggregateBuilder<'a> {
  fn new(shape: &'a [i32]) -> Self {
    Self {
      stack: vec![],
      expected_shape: shape,
      checker: InitValChecker::new(shape),
    }
  }

  fn reduce(&mut self, val_src: &mut Program) {
    let last_size = self.stack.last().unwrap().0;
    let same_size_cnt = self
      .stack
      .iter()
      .filter(|(size, _, _)| *size == last_size)
      .count();
    let stack_top_start_dim = self.stack.last().unwrap().1 as usize;
    assert!(stack_top_start_dim > 0);

    if same_size_cnt == self.expected_shape[stack_top_start_dim - 1] as usize {
      let elems = self
        .stack
        .drain(self.stack.len() - same_size_cnt..)
        .map(|(_, _, val)| val)
        .collect();
      let aggre = val_src.new_value().aggregate(elems);
      self.stack.push((
        last_size * same_size_cnt as i32,
        stack_top_start_dim - 1,
        aggre,
      ));

      self.reduce(val_src)
    }
  }

  fn push_single(&mut self, val: Value, val_src: &mut Program) {
    self.checker.append_single();
    self.stack.push((1, self.expected_shape.len(), val));
    self.reduce(val_src);
  }

  fn push_sequence(&mut self, val: Value, val_src: &mut Program) {
    let sub_seq = self.checker.append_sequence(false);
    self.stack.push((
      sub_seq.iter().product(),
      self.expected_shape.len() - sub_seq.len(),
      val,
    ));
    self.reduce(val_src)
  }
}
