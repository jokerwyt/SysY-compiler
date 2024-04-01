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

use koopa::ir::builder::{
  BasicBlockBuilder, GlobalInstBuilder, LocalBuilder, LocalInstBuilder, ValueBuilder,
};
use koopa::ir::dfg::DataFlowGraph;

use koopa::ir::layout::InstList;

use koopa::ir::{self, BasicBlock, Function, FunctionData, Program, Type, Value};

use crate::ast::{AstData, AstNodeId, BinaryOp, ConstInitVal, FuncFParam, InitVal, UnaryOp};
use crate::ast_data_write_as;
use crate::sym_table::{SymIdent, SymTableEntry, SymTableEntryData};

use crate::{ast, ast::ast_nodes_read, ast::ast_nodes_write, ast_is};

pub struct KoopaGen;

impl KoopaGen {
  /// Eval all compile-time constant int. (except const array deref)
  pub fn eval_const_int(ast_id: &AstNodeId) -> i32 {
    let ast_data = ast_id.get_ast_data();
    match ast_data {
      ast::AstData::Exp(exp) => {
        return Self::eval_const_int(&exp.l_or_exp);
      }
      ast::AstData::LVal(lval) => {
        // Some lval can be a constant.
        // Note Again: we only consider the case where the lval is an int.
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
    let mut ctx = KoopaGenCtx::new(&mut prog);

    let comp_unit = unit_id.get_ast_data().into_comp_unit();

    for item in comp_unit.items {
      match item.get_ast_data() {
        ast::AstData::Decl(_) => KoopaGen::gen_on_decl(&item, &mut ctx),
        ast::AstData::FuncDef(func_def) => {
          item.create_symbol_table(); // For function parameters.

          // generate the entry basic block, and put all initialized values into the symbol table.
          let params = KoopaGen::gen_on_func_fparams(&func_def.func_f_params);

          let func = ctx.prog_mut().new_func(FunctionData::with_param_names(
            format!("@{}", func_def.ident),
            params.clone(),
            match func_def.has_retval {
              true => Type::get_i32(),
              false => Type::get_unit(),
            },
          ));

          // generate the function body

          // add function into global symbol table
          SymTableEntry {
            symbol: SymIdent::Func(func_def.ident.clone()),
            kind: SymTableEntryData::FuncDef(func),
            func: None,
          }
          .into_llt(unit_id);

          ctx.func = Some(func);
          ctx.bb = Some(ctx.new_bb("%entry".to_string()));

          // re-Alloc the function parameters, and add them into the function symbol table.
          for (idx, (name, ty)) in params.iter().enumerate() {
            let name = name.clone().unwrap();

            let alloc = ctx.func_data_mut().dfg_mut().new_value().alloc(ty.clone());
            let arg = ctx.func_data_mut().params()[idx];
            let store = ctx.func_data_mut().dfg_mut().new_value().store(arg, alloc);
            ctx.insts_mut().extend([alloc, store]);

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
          KoopaGen::gen_on_block(&func_def.block, &mut ctx);
        }
        _ => panic!("Invalid item in CompUnit"),
      }
    }
    prog
  }

  fn gen_on_decl(decl_id: &AstNodeId, ctx: &mut KoopaGenCtx) {
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

          // Integer or Aggregate, depends on the shape.
          let value =
            KoopaGen::gen_on_prog_init_val(&const_def.const_init_val, &shape, ctx.prog_mut());

          // for const def, see whether it's an int or an array.
          if const_def.is_array() {
            // const array case.
            let alloc;
            if ctx.is_global() {
              alloc = ctx.prog_mut().new_value().global_alloc(value);
            } else {
              // We are inside a function.
              // A local array will be allocated and initialized via a store.
              alloc = ctx.dfg_mut().new_value().alloc(shape.into_type());
              let store = ctx.dfg_mut().new_value().store(value, alloc);
              ctx.insts_mut().extend([alloc, store]);
            }
            // No matter global or local, the address is inserted into the symbol table.
            SymTableEntry {
              symbol: SymIdent::Value(const_def.ident.clone()),
              kind: SymTableEntryData::ArrayDef(alloc, shape.into_type()),
              func: ctx.func_handle(),
            }
            .into_llt(decl_id);
          } else {
            // const int case.
            // No matter global or local, an int is inserted into the symbol table.
            SymTableEntry {
              symbol: SymIdent::Value(const_def.ident.clone()),
              kind: SymTableEntryData::ConstIntDef(value.into_i32(ctx.prog_mut())),
              func: ctx.func_handle(),
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

          let alloc = ctx.dfg_mut().new_value().alloc(shape.into_type());
          ctx.insts_mut().extend([alloc]);

          // Local var initialization.
          if let Some(init_val) = &var_def.init_val {
            // If it has an initialization, we need to apply it locally.
            if var_def.is_array() {
              KoopaGen::gen_on_local_array_init_val(init_val, &shape, ctx, alloc);
            } else {
              KoopaGen::gen_on_local_int_init_val(init_val, ctx, alloc);
            }
          } else {
            // Local var and no init_val. Do nothing.
          }

          if var_def.is_array() {
            SymTableEntry {
              symbol: SymIdent::Value(var_def.ident.clone()),
              kind: SymTableEntryData::ArrayDef(alloc, shape.into_type()),
              func: ctx.func_handle(),
            }
            .into_llt(decl_id);
          } else {
            // A Integer Value is inserted into the symbol table.
            SymTableEntry {
              symbol: SymIdent::Value(var_def.ident.clone()),
              kind: SymTableEntryData::VarIntDef(alloc),
              func: ctx.func_handle(),
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
  /// Entry block is placed in the ctx.
  /// When it returns, the current block in ctx is the sink block.
  ///
  fn gen_on_block(ast_id: &AstNodeId, ctx: &mut KoopaGenCtx) {
    ast_id.create_symbol_table(); // block symbol tables.

    let data = ast_id.get_ast_data().into_block();

    for item in data.items {
      match item.get_ast_data() {
        AstData::BlockItem(ast::BlockItem::Decl(decl)) => {
          Self::gen_on_decl(&decl, ctx);
        }
        AstData::BlockItem(ast::BlockItem::Stmt(stmt)) => {
          Self::gen_on_stmt(&stmt, ctx);
          if ctx.bb.is_none() {
            // Break or continue in the only path.
            // We can drop all the following items.
            return;
          }
        }
        _ => panic!("Invalid AstData for gen_on_block"),
      }
    }
  }

  /// Generate an Koopa Aggregate or Integer on Sys-Y ConstInitVal or InitVal.
  /// The shape is the reference to the shape of the array.
  /// When the shape is empty, return an Integer.
  /// Otherwise, return an Aggregate.
  fn gen_on_prog_init_val(ast_id: &AstNodeId, shape: &[i32], prog: &mut Program) -> Value {
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
            KoopaGen::gen_on_prog_init_val(&init_val, sub_shape, prog),
            prog,
          )
        }
        _ => panic!("Invalid AstData for gen_on_global_init"),
      };
    }

    if agg_builder.checker.progress == 0 {
      return prog.new_value().zero_init(shape.into_type());
    }

    agg_builder.close_up_with_zeroinit(prog)
  }

  /// Examples:
  /// Ok:
  /// int a = 3
  ///
  /// Not Ok:
  /// int a = {}
  /// int a = {3}
  fn gen_on_local_int_init_val(init_val: &AstNodeId, ctx: &mut KoopaGenCtx, alloc: Value) {
    let data = init_val.get_ast_data();
    match data {
      ast::AstData::InitVal(ast::InitVal::Single(exp)) => {
        let value = KoopaGen::gen_on_exp(&exp, ctx);
        let store = ctx.dfg_mut().new_value().store(value, alloc);
        ctx.append_ins(store);
      }
      _ => panic!("Invalid AstData for gen_on_local_int_init_val"),
    }
  }

  /// Store value into a local array manually, according to the expected shape.
  /// alloc should be a ptr (to some array or to a specific i32 location)
  ///
  /// Examples:
  /// int a[3] = {}
  /// int b[3] = {1}
  /// int c[3] = {1, 2, 3}
  /// int d[3][3] = {1, 2, 3, {4, 5}, {7, 8, 9}}
  ///
  /// Not Ok:
  /// int a[3][3] = {1, 2, 3, {4, 5}, {{}, 8, 9}}
  ///
  fn gen_on_local_array_init_val(
    init_val: &AstNodeId,
    shape: &[i32],
    ctx: &mut KoopaGenCtx,
    mut alloc: Value,
  ) {
    let zero = ctx.new_local_value().integer(0);
    // downcast alloc to *i32
    while ctx.dfg_mut().value(alloc).ty().ptr_inner().is_i32() == false {
      alloc = ctx.new_local_value().get_elem_ptr(alloc, zero);
      ctx.append_ins(alloc);
    }
    match init_val.get_ast_data().into_init_val() {
      InitVal::Single(_) => panic!("Invalid AstData for gen_on_local_array_init_val"),
      InitVal::Sequence(seq) => {
        let mut checker = InitValChecker::new(shape);

        for item in seq {
          match item.get_ast_data().into_init_val() {
            InitVal::Single(exp) => {
              let loc = ctx.new_local_value().integer(checker.progress + 1);
              checker.append_single();
              let value = KoopaGen::gen_on_exp(&exp, ctx);
              let get_ptr = ctx.new_local_value().get_ptr(alloc, loc);
              let store = ctx.new_local_value().store(value, get_ptr);
              ctx.insts_mut().extend([get_ptr, store]);
            }
            InitVal::Sequence(_) => {
              let loc = ctx.new_local_value().integer(checker.progress + 1);
              let sub_shape = checker.append_sequence(true);

              let sub_alloc = ctx.new_local_value().get_ptr(alloc, loc);
              ctx.append_ins(sub_alloc);
              Self::gen_on_local_array_init_val(&item, &sub_shape, ctx, sub_alloc);
            }
          }
        }

        // Fill the rest with zero.
        // Too slow, but it works.
        while checker.finished() == false {
          let loc = ctx.new_local_value().integer(checker.progress + 1);
          let get_ptr = ctx.new_local_value().get_ptr(alloc, loc);
          let store = ctx.new_local_value().store(zero, get_ptr);
          ctx.insts_mut().extend([get_ptr, store]);
          checker.append_single();
        }
      }
    }
  }

  /// Generate Koopa on a Sys-Y Stmt.
  /// Return the possible sink block.
  fn gen_on_stmt(stmt: &AstNodeId, ctx: &mut KoopaGenCtx<'_>) {
    match stmt.get_ast_data().into_stmt() {
      ast::Stmt::Assign(lval, exp) => {
        let lval = KoopaGen::gen_on_lval(&lval, ctx, false);
        let exp = KoopaGen::gen_on_exp(&exp, ctx);

        let store = ctx.new_local_value().store(exp, lval);
        ctx.append_ins(store);
      }
      ast::Stmt::Exp(e) => {
        if let Some(exp) = e {
          let _ = KoopaGen::gen_on_exp(&exp, ctx);
        }
      }
      ast::Stmt::Block(_) => {
        KoopaGen::gen_on_block(stmt, ctx);
      }
      ast::Stmt::IfElse {
        expr,
        branch1,
        branch0,
      } => {
        // Eval on the current block
        let cond = KoopaGen::gen_on_exp(&expr, ctx);
        let true_bb = ctx.new_bb(format!("%br-1-{}", branch1.name()));
        let sink_bb = ctx.new_bb(format!("%if-sink-{}", stmt.name()));

        if let Some(branch0) = branch0 {
          let false_bb = ctx.new_bb(format!("%br-0-{}", branch0.name()));
          let branch = ctx.new_local_value().branch(cond, true_bb, false_bb);
          ctx.append_ins(branch);

          ctx.upd_bb(false_bb);
          KoopaGen::gen_on_block(&branch0, ctx);
          // now ctx.bb is branch0 sink bb.
          if ctx.bb.is_some() {
            let jump = ctx.new_local_value().jump(sink_bb);
            ctx.append_ins(jump);
          }
        } else {
          let branch = ctx.new_local_value().branch(cond, true_bb, sink_bb);
          ctx.append_ins(branch);
        }

        ctx.upd_bb(true_bb);
        KoopaGen::gen_on_block(&branch1, ctx);
        // now ctx.bb is branch1 sink bb.
        if ctx.bb.is_some() {
          let jump = ctx.new_local_value().jump(sink_bb);
          ctx.append_ins(jump);
        }

        ctx.upd_bb(sink_bb);
      }
      ast::Stmt::While {
        expr,
        block,
        cond_bb: _,
        end_bb: _,
      } => {
        let cond_bb = ctx.new_bb(format!("%while-cond-{}", stmt.name()));
        let body_bb = ctx.new_bb(format!("%while-body-{}", stmt.name()));
        let end_bb = ctx.new_bb(format!("%while-end-{}", stmt.name()));

        // update AST stored data, for future break and continue.
        ast_data_write_as!(stmt, Stmt, |stmt| {
          if let ast::Stmt::While {
            expr: _,
            block: _,
            cond_bb: cond_bb_ref,
            end_bb: end_bb_ref,
          } = stmt
          {
            *cond_bb_ref = Some(cond_bb);
            *end_bb_ref = Some(end_bb);
          } else {
            panic!("Invalid Stmt type");
          }
        });

        let jump = ctx.new_local_value().jump(cond_bb);
        ctx.append_ins(jump);

        ctx.upd_bb(cond_bb);
        let cond = KoopaGen::gen_on_exp(&expr, ctx);
        let branch = ctx.new_local_value().branch(cond, body_bb, end_bb);
        ctx.append_ins(branch);

        ctx.upd_bb(body_bb);
        KoopaGen::gen_on_block(&block, ctx);
        // now ctx.bb is body sink bb.
        if ctx.bb.is_some() {
          let jump = ctx.new_local_value().jump(cond_bb);
          ctx.append_ins(jump);
        }

        ctx.upd_bb(end_bb);
      }
      ast::Stmt::Break => {
        let while_stmt = stmt.get_nearest_while().unwrap();
        if let ast::Stmt::While { end_bb, .. } = while_stmt.get_ast_data().into_stmt() {
          let jump = ctx.new_local_value().jump(end_bb.unwrap());
          ctx.append_ins(jump);
          ctx.bb = None;
        } else {
          panic!("Invalid Stmt type for break");
        }
      }
      ast::Stmt::Continue => {
        let while_stmt = stmt.get_nearest_while().unwrap();
        if let ast::Stmt::While { cond_bb, .. } = while_stmt.get_ast_data().into_stmt() {
          let jump = ctx.new_local_value().jump(cond_bb.unwrap());
          ctx.append_ins(jump);
          ctx.bb = None;
        } else {
          panic!("Invalid Stmt type for continue");
        }
      }
      ast::Stmt::Return(exp) => {
        if let Some(exp) = exp {
          let ret = KoopaGen::gen_on_exp(&exp, ctx);
          let ret_inst = ctx.new_local_value().ret(Some(ret));
          ctx.append_ins(ret_inst);
        } else {
          let ret_inst = ctx.new_local_value().ret(None);
          ctx.append_ins(ret_inst);
        }
        ctx.bb = None;
      }
    }
  }

  /// Generate Koopa on a Sys-Y LVal.
  /// Return a Value whose type is ptr, or i32 if required.
  ///
  /// FunctionRParams is a special case, it will be handled mauanlly in gen_on_func_rparams.
  /// Partial deref is impossible.
  fn gen_on_lval(lval: &AstNodeId, ctx: &mut KoopaGenCtx<'_>, want_i32: bool) -> Value {
    let lval_data = lval.get_ast_data().into_lval();
    let sym_entry = lval
      .lookup_sym_table(&SymIdent::Value(lval_data.ident.clone()))
      .unwrap();

    let ret_ptr = match sym_entry.kind {
      SymTableEntryData::FuncDef(_) => panic!("Function is not a LVal"),
      SymTableEntryData::ConstIntDef(v) => {
        assert!(want_i32 == true, "Try to get a ptr from a const int");

        // Return directly instead of going down for deref.
        return ctx.new_local_value().integer(v);
      }
      SymTableEntryData::VarIntDef(alloc) => alloc,
      SymTableEntryData::ArrayDef(mut alloc, _ty) => {
        // Partial deref is impossible.
        // a[3][5][7]
        // middle value:
        // a ==> *[[[i32, 7], 5], 3]
        // a[1] ==> *[[i32, 7], 5]
        // a[1][2] ==> *[i32, 7]
        // a[1][2][3] ==> *i32

        for i in lval_data.idx {
          let idx = KoopaGen::gen_on_exp(&i, ctx);
          alloc = ctx.new_local_value().get_elem_ptr(alloc, idx);
          ctx.append_ins(alloc);
        }

        alloc
      }
      SymTableEntryData::FuncParamArrayDef(mut alloc, _ty) => {
        // int a[][3][5] means *[[i32, 5], 3] in Koopa
        // the first dimension we use getptr, and them getelemptr.
        // Partial deref is impossible.
        //
        // a[][5][7]
        // middle value:
        // a ==> *[[i32, 7], 5]
        // a[1] ==> *[[i32, 7], 5] (special)
        //
        // a[1][2] ==> *[i32, 7]
        // a[1][2][3] ==> *i32

        assert!(lval_data.idx.len() >= 1, "Invalid FuncParamArrayDef");

        let fisrt_dim = KoopaGen::gen_on_exp(&lval_data.idx[0], ctx);
        alloc = ctx.new_local_value().get_ptr(alloc, fisrt_dim);
        ctx.append_ins(alloc);

        for i in lval_data.idx[1..].iter() {
          let idx = KoopaGen::gen_on_exp(&i, ctx);
          alloc = ctx.new_local_value().get_elem_ptr(alloc, idx);
          ctx.append_ins(alloc);
        }

        alloc
      }
    };

    if want_i32 == false {
      return ret_ptr;
    } else {
      let load = ctx.new_local_value().load(ret_ptr);
      ctx.append_ins(load);
      return load;
    }
  }

  fn gen_on_exp(exp: &AstNodeId, ctx: &mut KoopaGenCtx<'_>) -> Value {
    return Self::gen_on_binary_exp(&exp.get_ast_data().into_exp().l_or_exp, ctx);
  }

  fn gen_on_unary_exp(exp: &AstNodeId, ctx: &mut KoopaGenCtx<'_>) -> Value {
    match exp.get_ast_data().into_unary_exp() {
      ast::UnaryExp::PrimaryExp { pexp } => {
        return KoopaGen::gen_on_primary_exp(&pexp, ctx);
      }
      ast::UnaryExp::Call { ident, params } => {
        let args = KoopaGen::gen_on_func_rparams(&params, ctx);
        let func = exp
          .lookup_sym_table(&SymIdent::Func(ident.clone()))
          .unwrap();
        match func.kind {
          SymTableEntryData::FuncDef(f) => {
            let call = ctx.new_local_value().call(f, args);
            ctx.append_ins(call);
            return call;
          }
          SymTableEntryData::VarIntDef(_)
          | SymTableEntryData::ConstIntDef(_)
          | SymTableEntryData::ArrayDef(_, _)
          | SymTableEntryData::FuncParamArrayDef(_, _) => {
            panic!("Invalid function call");
          }
        }
      }
      ast::UnaryExp::Unary { op, exp } => {
        let sub_exp = KoopaGen::gen_on_unary_exp(&exp, ctx);
        let zero = ctx.new_local_value().integer(0);

        let binary = match op {
          UnaryOp::Pos => None,
          UnaryOp::Neg => Some(ctx.new_local_value().binary(
            koopa::ir::BinaryOp::Sub,
            zero,
            sub_exp,
          )),
          UnaryOp::Not => Some(ctx.new_local_value().binary(
            koopa::ir::BinaryOp::Eq,
            zero,
            sub_exp,
          )),
        };

        if let Some(binary) = binary {
          ctx.append_ins(binary);
          return binary;
        } else {
          return sub_exp;
        }
      }
    }
  }

  fn gen_on_binary_exp(exp: &AstNodeId, ctx: &mut KoopaGenCtx<'_>) -> Value {
    match exp.get_ast_data().into_binary_exp() {
      ast::BinaryExp::Unary { exp } => {
        return KoopaGen::gen_on_unary_exp(&exp, ctx);
      }
      ast::BinaryExp::Binary { lhs, op, rhs } => {
        match op {
          BinaryOp::Add
          | BinaryOp::Sub
          | BinaryOp::Mul
          | BinaryOp::Div
          | BinaryOp::Mod
          | BinaryOp::Lt
          | BinaryOp::Le
          | BinaryOp::Gt
          | BinaryOp::Ge
          | BinaryOp::Eq
          | BinaryOp::Ne => {
            let lhs = KoopaGen::gen_on_binary_exp(&lhs, ctx);
            let rhs = if ast_is!(&rhs, BinaryExp) {
              KoopaGen::gen_on_binary_exp(&rhs, ctx)
            } else {
              KoopaGen::gen_on_unary_exp(&rhs, ctx)
            };
            let binary = ctx.new_local_value().binary(op.to_koopa_op(), lhs, rhs);
            ctx.append_ins(binary);
            return binary;
          }
          BinaryOp::And => {
            let zero = ctx.new_local_value().integer(0);
            let lhs_v = KoopaGen::gen_on_binary_exp(&lhs, ctx);
            let temp_alloc = ctx.new_local_value().alloc(Type::get_i32());
            let default_store_0 = ctx.new_local_value().store(zero, temp_alloc);
            ctx.insts_mut().extend([temp_alloc, default_store_0]);

            let rhs_bb = ctx.new_bb("%and-rhs".to_string());
            let sink_bb = ctx.new_bb("%and-sink".to_string());

            let branch = ctx.new_local_value().branch(lhs_v, rhs_bb, sink_bb);
            ctx.append_ins(branch);

            ctx.upd_bb(rhs_bb);

            let rhs_v = if ast_is!(&rhs, BinaryExp) {
              KoopaGen::gen_on_binary_exp(&rhs, ctx)
            } else {
              KoopaGen::gen_on_unary_exp(&rhs, ctx)
            };

            let rhs_converted =
              ctx
                .new_local_value()
                .binary(koopa::ir::BinaryOp::NotEq, zero, rhs_v);
            let store_rhs = ctx.new_local_value().store(rhs_converted, temp_alloc);
            let jump = ctx.new_local_value().jump(sink_bb);
            ctx.insts_mut().extend([rhs_converted, store_rhs, jump]);

            ctx.upd_bb(sink_bb);

            let load = ctx.new_local_value().load(temp_alloc);
            ctx.append_ins(load);
            return load;
          }
          BinaryOp::Or => {
            let one = ctx.new_local_value().integer(1);
            let temp_alloc = ctx.new_local_value().alloc(Type::get_i32());
            let default_store_1 = ctx.new_local_value().store(one, temp_alloc);
            ctx.insts_mut().extend([temp_alloc, default_store_1]);

            let rhs_bb = ctx.new_bb("%or-rhs".to_string());
            let sink_bb = ctx.new_bb("%or-sink".to_string());

            let lhs_v = KoopaGen::gen_on_binary_exp(&lhs, ctx);
            let branch = ctx.new_local_value().branch(lhs_v, sink_bb, rhs_bb);
            ctx.append_ins(branch);

            ctx.upd_bb(rhs_bb);

            let rhs_v = if ast_is!(&rhs, BinaryExp) {
              KoopaGen::gen_on_binary_exp(&rhs, ctx)
            } else {
              KoopaGen::gen_on_unary_exp(&rhs, ctx)
            };

            let zero = ctx.new_local_value().integer(0);
            let rhs_converted =
              ctx
                .new_local_value()
                .binary(koopa::ir::BinaryOp::NotEq, zero, rhs_v);
            let store_lhs = ctx.new_local_value().store(rhs_converted, temp_alloc);
            let jump = ctx.new_local_value().jump(sink_bb);
            ctx.insts_mut().extend([rhs_converted, store_lhs, jump]);

            ctx.upd_bb(sink_bb);

            let load = ctx.new_local_value().load(temp_alloc);
            ctx.append_ins(load);
            return load;
          }
        };
      }
    }
  }

  fn gen_on_primary_exp(pexp: &AstNodeId, ctx: &mut KoopaGenCtx<'_>) -> Value {
    match pexp.get_ast_data().into_primary_exp() {
      ast::PrimaryExp::Exp(exp) => {
        return KoopaGen::gen_on_exp(&exp, ctx);
      }
      ast::PrimaryExp::LVal(lval) => {
        return KoopaGen::gen_on_lval(&lval, ctx, true);
      }
      ast::PrimaryExp::Number(x) => {
        return ctx.new_local_value().integer(x);
      }
    }
  }

  fn gen_on_func_rparams(params: &AstNodeId, ctx: &mut KoopaGenCtx<'_>) -> Vec<Value> {
    let data = params.get_ast_data().into_func_r_params();

    let mut args = vec![];
    for p in data.params {
      let exp = p.get_ast_data().into_exp();
      let mut value = None;

      // special case: array parameter.
      if let Some(lval) = exp.is_pure_lval() {
        let lval = lval.get_ast_data().into_lval();
        let sym_entry = p.lookup_sym_table(&SymIdent::Value(lval.ident)).unwrap();

        // is it array? func_array (no 1st dim info), or normal array?
        match sym_entry.kind {
          SymTableEntryData::FuncDef(_) => panic!("Function is not a LVal"),
          SymTableEntryData::ConstIntDef(_) => {}
          SymTableEntryData::VarIntDef(_alloc) => {}
          SymTableEntryData::ArrayDef(mut alloc, _) => {
            // int a[3][5] means *[[i32, 5], 3] in Koopa
            // a, we should get *[i32, 5]
            // a[1], we should get *i32
            // a[1][2], we should get i32.

            // use getelemptr to deref
            for i in lval.idx {
              let idx = KoopaGen::gen_on_exp(&i, ctx);
              alloc = ctx.new_local_value().get_elem_ptr(alloc, idx);
              ctx.append_ins(alloc);
            }

            // now middle value:
            // a ==> *[[i32, 5], 3]
            // a[1] ==> *[i32, 5]
            // a[1][2] ==> *i32

            // an extra getelemptr is needed.
            // for example, a[2] we will get a ptr to [i32, 5]. But for func array args, we need *i32 actually.

            let zero = ctx.new_local_value().integer(0);
            let extra_get_elem_ptr = ctx.new_local_value().get_elem_ptr(alloc, zero);
            ctx.append_ins(extra_get_elem_ptr);

            value = Some(extra_get_elem_ptr);
          }
          SymTableEntryData::FuncParamArrayDef(mut alloc, _) => {
            // int a[][5] means *[i32, 5] in Koopa
            // a, we should get *[i32, 5]
            // a[1], we should get *i32
            // a[1][2], we don't handle it here.

            // first we nedd to see whether it's a partial deref, or full deref.
            // apply following code on full deref will cause panic.

            let inner_ty = ctx.dfg_mut().value(alloc).ty().ptr_inner();
            let shape_without_1dim = inner_ty.get_array_shape();

            // see if it's a deref

            if lval.idx.len() < shape_without_1dim.len() + 1 {
              for i in lval.idx {
                let idx = KoopaGen::gen_on_exp(&i, ctx);
                alloc = ctx.new_local_value().get_elem_ptr(alloc, idx);
                ctx.append_ins(alloc);
              }

              // now alloc value:
              // a ==> *[i32, 5]
              // a[1] ==> *i32

              value = Some(alloc);
            }
          }
        };
      }

      if value.is_none() {
        args.push(KoopaGen::gen_on_exp(&p, ctx));
      } else {
        args.push(value.unwrap());
      }
    }
    args
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
      FuncFParam::Single { btype: _, ident: _ } => Type::get_i32(),
      FuncFParam::Array {
        btype: _,
        ident: _,
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

  fn finished(&self) -> bool {
    self.progress == self.expect_shape.iter().product()
  }

  /// Return the last element that we reached, according to progress
  #[allow(dead_code)]
  fn get_last_elem(&self) -> Vec<i32> {
    let mut last_elem = vec![];
    let mut progress = self.progress;
    for size in self.expect_shape.iter().rev() {
      last_elem.push(progress % size);
      progress /= size;
    }
    last_elem.reverse();
    last_elem
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

  fn reduce(&mut self, prog: &mut Program) {
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
      let aggre = prog.new_value().aggregate(elems);
      self.stack.push((
        last_size * same_size_cnt as i32,
        stack_top_start_dim - 1,
        aggre,
      ));

      self.reduce(prog)
    }
  }

  fn push_single(&mut self, val: Value, prog: &mut Program) {
    self.checker.append_single();
    self.stack.push((1, self.expected_shape.len(), val));
    self.reduce(prog);
  }

  fn push_sequence(&mut self, val: Value, prog: &mut Program) {
    let sub_seq = self.checker.append_sequence(false);
    self.stack.push((
      sub_seq.iter().product(),
      self.expected_shape.len() - sub_seq.len(),
      val,
    ));
    self.reduce(prog)
  }

  /// Close up the stack with zero init.
  /// Return the final value.
  fn close_up_with_zeroinit(&mut self, prog: &mut Program) -> Value {
    // push zero_init of the stack top type, until the shape is filled.
    // Done in log time.
    while self.stack.first().unwrap().1 != 0 {
      if self.checker.can_append_sequence() {
        let zero = prog
          .new_value()
          .zero_init(self.checker.append_sequence(true).into_type());
        self.push_sequence(zero, prog);
      } else {
        self.push_single(prog.new_value().integer(0), prog);
      }
    }
    assert_eq!(self.stack.len(), 1);
    self.stack.first().unwrap().2
  }
}

struct KoopaGenCtx<'a> {
  prog: &'a mut Program,
  func: Option<Function>,
  bb: Option<BasicBlock>,
}

impl<'a> KoopaGenCtx<'a> {
  fn new(prog: &'a mut Program) -> Self {
    Self {
      prog,
      func: None,
      bb: None,
    }
  }

  fn is_global(&self) -> bool {
    self.func.is_none()
  }

  fn prog_mut(&mut self) -> &mut Program {
    self.prog
  }

  fn func_data_mut(&mut self) -> &mut FunctionData {
    self.prog.func_mut(self.func.unwrap())
  }

  // fn bb_data_mut(&mut self) -> &mut BasicBlockData {
  //   self
  //     .prog
  //     .func_mut(self.func.unwrap())
  //     .dfg_mut()
  //     .bb_mut(self.bb.unwrap())
  // }

  fn insts_mut(&mut self) -> &mut InstList {
    self
      .prog
      .func_mut(self.func.unwrap())
      .layout_mut()
      .bb_mut(self.bb.unwrap())
      .insts_mut()
  }

  fn append_ins(&mut self, ins: Value) {
    self.insts_mut().extend([ins]);
  }

  fn dfg_mut(&mut self) -> &mut DataFlowGraph {
    self.func_data_mut().dfg_mut()
  }

  fn new_local_value(&mut self) -> LocalBuilder<'_> {
    self.dfg_mut().new_value()
  }

  fn func_handle(&self) -> Option<Function> {
    self.func
  }

  #[allow(dead_code)]
  fn current_bb(&self) -> BasicBlock {
    self.bb.unwrap()
  }

  fn new_bb(&mut self, name: String) -> BasicBlock {
    let bb = self
      .func_data_mut()
      .dfg_mut()
      .new_bb()
      .basic_block(Some(name));
    self.func_data_mut().layout_mut().bbs_mut().extend([bb]);
    bb
  }

  fn upd_bb(&mut self, bb: BasicBlock) -> &mut Self {
    self.bb = Some(bb);
    self
  }
}

trait GetArrayShape {
  fn ptr_inner(&self) -> Type;
  fn get_array_shape(&self) -> Vec<i32>;
}

impl GetArrayShape for Type {
  /// it will return vec![] for i32
  fn get_array_shape(&self) -> Vec<i32> {
    let mut shape = vec![];
    let mut tmp = Some(self);

    while let Some(inner) = tmp {
      match inner.kind() {
        ir::TypeKind::Array(sub_type, size) => {
          tmp = Some(sub_type);
          shape.push(*size as i32);
        }
        ir::TypeKind::Int32 => {
          tmp = None;
        }
        _ => panic!("Not an array or i32"),
      }
    }
    shape
  }

  fn ptr_inner(&self) -> Type {
    match self.kind() {
      ir::TypeKind::Pointer(inner) => inner.clone(),
      _ => panic!("Not a ptr"),
    }
  }
}
