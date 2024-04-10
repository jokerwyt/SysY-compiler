// We implement the IR generation for the SysY language in this module.
// The comments here demonstrate how we pass the AST of Sys-Y and generate Koopa IR.
//
// We maintain a context struct KoopaGenCtx to store the current state of the generation.
// It includes the current program, function, basic block, and other necessary information.
// And we suppose all statements should have a sink basic block, which is placed in the ctx.

use koopa::ir::builder::{
  BasicBlockBuilder, GlobalInstBuilder, LocalBuilder, LocalInstBuilder, ValueBuilder,
};
use koopa::ir::dfg::DataFlowGraph;

use koopa::ir::entities::ValueData;
use koopa::ir::layout::InstList;

use koopa::ir::{self, BasicBlock, Function, FunctionData, Program, Type, Value};

use crate::ast_data_write_as;
use crate::koopa_gen::ast::{
  AstData, AstNodeId, BinaryOp, ConstInitVal, FuncFParam, InitVal, InitValUnified, IsInitVal,
  UnaryOp,
};
use crate::koopa_gen::sym_table::{SymIdent, SymTableEntry, SymTableEntryData};

use crate::ast_is;
use crate::koopa_gen::{ast, ast::ast_nodes_read, ast::ast_nodes_write};

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

    Self::declare_sysy_runtime(unit_id, &mut ctx);

    let comp_unit = unit_id.get_ast_data().into_comp_unit();

    for item in comp_unit.items {
      assert!(ctx.func.is_none() && ctx.bb.is_none());

      match item.get_ast_data() {
        ast::AstData::Decl(_) => {
          KoopaGen::gen_on_decl(&item, &mut ctx);
        }
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
          let new_bb = ctx.new_bb_and_append("%entry".to_string());
          ctx.upd_bb(new_bb);

          // re-Alloc the function parameters, and add them into the function symbol table.
          for (idx, (name, ty)) in params.iter().enumerate() {
            let name = name.clone().unwrap();

            let alloc = ctx.new_local_value().alloc(ty.clone());
            let arg = ctx.func_data_mut().params()[idx];
            let store = ctx.new_local_value().store(arg, alloc);
            ctx.insts_mut().extend([alloc, store]);

            let entry = SymTableEntry {
              symbol: SymIdent::Value(name[1..].to_string()), // skip the first @
              kind: match ty.is_i32() {
                true => SymTableEntryData::VarIntDef(alloc),
                false => SymTableEntryData::FuncParamArrayDef(alloc, ty.clone()),
              },
              func: Some(func),
            };
            entry.into_llt(&item);
          }
          KoopaGen::gen_on_block(&func_def.block, &mut ctx);

          // default return, and has sink block
          if ctx.bb.is_some() {
            // If func_def.has_retval == true, and the user code really runs here, it's actually an UB.
            // But we cannot panic now, since the user may promise it will never reach here.
            let zero = Some(ctx.new_local_value().integer(0));
            let ret = ctx
              .new_local_value()
              .ret(if func_def.has_retval { zero } else { None });
            ctx.close_up(ret);
          }
          ctx.func = None;
        }
        _ => panic!("Invalid item in CompUnit"),
      }
    }
    prog
  }

  fn gen_on_decl(decl_id: &AstNodeId, ctx: &mut KoopaGenCtx) {
    let decl = decl_id.get_ast_data().into_decl();
    match decl {
      // local & global const decl case.
      ast::Decl::ConstDecl(const_decl) => {
        for def in const_decl.get_ast_data().into_const_decl().const_defs {
          let const_def = def.get_ast_data().into_const_def();

          // resolve possible index.
          let mut shape = vec![];
          for const_exp in &const_def.idx {
            shape.push(KoopaGen::eval_const_int(const_exp));
          }

          // Integer or Aggregate, depends on the shape.

          if ctx.is_global() {
            let value =
              KoopaGen::gen_on_prog_init_val(&const_def.const_init_val, &shape, ctx.prog_mut());

            if const_def.is_array() {
              // global const array case.
              let alloc = ctx.prog_mut().new_value().global_alloc(value);
              ctx.prog_mut().set_value_name(alloc, const_def.koopa_name());
              SymTableEntry {
                symbol: SymIdent::Value(const_def.ident.clone()),
                kind: SymTableEntryData::ArrayDef(alloc),
                func: ctx.func_handle(),
              }
              .into_llt(decl_id);
            } else {
              // global const int case.
              SymTableEntry {
                symbol: SymIdent::Value(const_def.ident.clone()),
                kind: SymTableEntryData::ConstIntDef(value.into_i32(ctx.prog_mut())),
                func: ctx.func_handle(),
              }
              .into_llt(decl_id);
            }
          } else {
            // local const
            if const_def.is_array() {
              // local const array case.
              let alloc = ctx.new_local_value().alloc(shape.into_type());
              ctx.dfg_mut().set_value_name(alloc, const_def.koopa_name());
              ctx.dfg_mut().set_value_name(alloc, const_def.koopa_name());
              ctx.append_ins(alloc);

              KoopaGen::gen_on_local_array_init_val(&const_def.const_init_val, &shape, ctx, alloc);

              SymTableEntry {
                symbol: SymIdent::Value(const_def.ident.clone()),
                kind: SymTableEntryData::ArrayDef(alloc),
                func: ctx.func_handle(),
              }
              .into_llt(decl_id);
            } else {
              // make sure it's ConstInitVal::Single(ConstExp)
              let const_initval = const_def
                .const_init_val
                .get_ast_data()
                .into_const_init_val();

              let const_exp = match const_initval {
                ConstInitVal::Single(exp) => exp,
                _ => panic!("Invalid ConstInitVal for local const int"),
              };

              SymTableEntry {
                symbol: SymIdent::Value(const_def.ident.clone()),
                // all Sys-y const can be evaluated at compile time.
                kind: SymTableEntryData::ConstIntDef(KoopaGen::eval_const_int(&const_exp)),
                func: ctx.func_handle(),
              }
              .into_llt(decl_id);
            }
          }
        }
      }
      // local & global variable case.
      ast::Decl::VarDecl(var_decl) => {
        for def in var_decl.get_ast_data().into_var_decl().var_defs {
          let var_def = def.get_ast_data().into_var_def();

          // resolve possible index.
          let mut shape = vec![];
          for const_exp in &var_def.idx {
            shape.push(KoopaGen::eval_const_int(const_exp));
          }

          if ctx.is_global() {
            // global variable case
            let init_value = if let Some(init_val) = &var_def.init_val {
              // Integer or Aggregate, depends on the shape.
              KoopaGen::gen_on_prog_init_val(&init_val, &shape, ctx.prog_mut())
            } else {
              // No init value, we need to zero-init it.
              ctx.prog_mut().new_value().zero_init(shape.into_type())
            };

            let alloc = ctx.prog_mut().new_value().global_alloc(init_value);
            ctx.prog_mut().set_value_name(alloc, var_def.koopa_name());
            if var_def.is_array() {
              // global variable array case.
              SymTableEntry {
                symbol: SymIdent::Value(var_def.ident.clone()),
                kind: SymTableEntryData::ArrayDef(alloc),
                func: ctx.func_handle(),
              }
              .into_llt(decl_id);
            } else {
              // global variable int case.
              SymTableEntry {
                symbol: SymIdent::Value(var_def.ident.clone()),
                kind: SymTableEntryData::VarIntDef(alloc),
                func: ctx.func_handle(),
              }
              .into_llt(decl_id);
            }
          } else {
            // local variable case
            let alloc = ctx.new_local_value().alloc(shape.into_type());
            ctx.dfg_mut().set_value_name(alloc, var_def.koopa_name());
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
                kind: SymTableEntryData::ArrayDef(alloc),
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
  }

  /// The name returned is starting with '@'.
  fn gen_on_func_fparams(ast_id: &AstNodeId) -> Vec<(Option<String>, Type)> {
    let data = ast_id.get_ast_data().into_func_f_params();

    let mut params = vec![];
    for p in data.params {
      let fparam = p.get_ast_data().into_func_f_param();
      params.push((
        Some(format!("@{}", fparam.name().clone())),
        fparam.into_type(),
      ));
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

    let seq = InitValUnified::from_ast_node(ast_id).get_sequence();

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
  /// init_val can be a ConstInitVal, or InitVal.
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
    alloc: Value,
  ) {
    let zero = ctx.new_local_value().integer(0);

    let initval_unified = InitValUnified::from_ast_node(init_val);
    let seq = initval_unified.get_sequence();

    let mut checker = InitValChecker::new(shape);

    for item in seq {
      // item is ConstInitVal or InitVal
      assert!(ast_is!(&item, ConstInitVal) || ast_is!(&item, InitVal));

      let initval = InitValUnified::from_ast_node(&item);
      if initval.is_single() {
        let loc = Self::get_array_elem_ptr(alloc, &checker.get_next_loc(), ctx);
        checker.append_single();
        let value = KoopaGen::gen_on_exp(&initval.get_single_exp(), ctx);
        let store = ctx.new_local_value().store(value, loc);
        ctx.append_ins(store);
      } else {
        let next_loc = checker.get_next_loc();
        let sub_shape = checker.append_sequence(false);
        let sub_alloc =
          Self::get_array_elem_ptr(alloc, &next_loc[..&next_loc.len() - sub_shape.len()], ctx);

        ctx.append_ins(sub_alloc);
        Self::gen_on_local_array_init_val(&item, &sub_shape, ctx, sub_alloc);
      }
    }

    while checker.finished() == false {
      if false && checker.can_append_sequence() {
        // Reason that we disable this branch:
        // It works well, but our backend does not support zero_init for store.

        let next_loc = checker.get_next_loc();
        let sub_shape = checker.append_sequence(false);
        let sub_alloc =
          Self::get_array_elem_ptr(alloc, &next_loc[..&next_loc.len() - sub_shape.len()], ctx);

        let zero_init = ctx.new_local_value().zero_init(sub_shape.into_type());
        let store = ctx.new_local_value().store(zero_init, sub_alloc);
        ctx.append_ins(store);
      } else {
        let loc = Self::get_array_elem_ptr(alloc, &checker.get_next_loc(), ctx);
        let store = ctx.new_local_value().store(zero, loc);
        ctx.append_ins(store);
        checker.append_single();
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
      ast::Stmt::Block(block) => {
        KoopaGen::gen_on_block(&block, ctx);
      }
      ast::Stmt::IfElse {
        expr,
        branch1,
        branch0,
      } => {
        // Eval on the current block
        let cond = KoopaGen::gen_on_exp(&expr, ctx);
        let true_bb = ctx.new_bb_and_append(format!("%br_1_{}", branch1.name_len8()));
        let sink_bb;

        if let Some(branch0) = branch0 {
          let false_bb = ctx.new_bb_and_append(format!("%br_0_{}", branch0.name_len8()));
          sink_bb = ctx.new_bb_and_append(format!("%if_sink_{}", stmt.name_len8()));

          let branch = ctx.new_local_value().branch(cond, true_bb, false_bb);
          ctx.close_up(branch);

          ctx.upd_bb(false_bb);
          KoopaGen::gen_on_stmt(&branch0, ctx);
          // now ctx.bb is branch0 sink bb.
          if ctx.bb.is_some() {
            let jump = ctx.new_local_value().jump(sink_bb);
            ctx.close_up(jump);
          }
        } else {
          sink_bb = ctx.new_bb_and_append(format!("%if_sink_{}", stmt.name_len8()));

          let branch = ctx.new_local_value().branch(cond, true_bb, sink_bb);
          ctx.close_up(branch);
        }

        ctx.upd_bb(true_bb);
        KoopaGen::gen_on_stmt(&branch1, ctx);
        // now ctx.bb is branch1 sink bb.
        if ctx.bb.is_some() {
          let jump = ctx.new_local_value().jump(sink_bb);
          ctx.close_up(jump);
        }
        ctx.upd_bb(sink_bb);
      }
      ast::Stmt::While {
        expr,
        block,
        cond_bb: _,
        end_bb: _,
      } => {
        let cond_bb = ctx.new_bb_and_append(format!("%while_cond_{}", stmt.name_len8()));
        let body_bb = ctx.new_bb_and_append(format!("%while_body_{}", stmt.name_len8()));
        let end_bb = ctx.new_bb_and_append(format!("%while_sink_{}", stmt.name_len8()));

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
        ctx.close_up(jump);

        ctx.upd_bb(cond_bb);
        let cond = KoopaGen::gen_on_exp(&expr, ctx);
        let branch = ctx.new_local_value().branch(cond, body_bb, end_bb);
        ctx.close_up(branch);

        ctx.upd_bb(body_bb);
        KoopaGen::gen_on_stmt(&block, ctx);
        // now ctx.bb is body sink bb.
        if ctx.bb.is_some() {
          let jump = ctx.new_local_value().jump(cond_bb);
          ctx.close_up(jump);
        }

        ctx.upd_bb(end_bb);
      }
      ast::Stmt::Break => {
        let while_stmt = stmt.get_nearest_while().unwrap();
        if let ast::Stmt::While { end_bb, .. } = while_stmt.get_ast_data().into_stmt() {
          let jump = ctx.new_local_value().jump(end_bb.unwrap());
          ctx.close_up(jump);
        } else {
          panic!("Invalid Stmt type for break");
        }
      }
      ast::Stmt::Continue => {
        let while_stmt = stmt.get_nearest_while().unwrap();
        if let ast::Stmt::While { cond_bb, .. } = while_stmt.get_ast_data().into_stmt() {
          let jump = ctx.new_local_value().jump(cond_bb.unwrap());
          ctx.close_up(jump);
        } else {
          panic!("Invalid Stmt type for continue");
        }
      }
      ast::Stmt::Return(exp) => {
        let ret = if let Some(exp) = exp {
          let ret = KoopaGen::gen_on_exp(&exp, ctx);
          ctx.new_local_value().ret(Some(ret))
        } else {
          ctx.new_local_value().ret(None)
        };
        ctx.close_up(ret);
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
      SymTableEntryData::ArrayDef(mut alloc) => {
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
        // int a[][3][5] means *[[i32, 5], 3] in Koopa args.
        // And we will store it into alloc, i.e, **[[i32, 5], 3]
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

        // deref to remove the temporary variable ptr first
        let deref = ctx.new_local_value().load(alloc);
        ctx.append_ins(deref);
        alloc = deref;

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
          | SymTableEntryData::ArrayDef(_)
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
            ctx
              .dfg_mut()
              .set_value_name(temp_alloc, Some(format!("%and_temp_{}", exp.name_len8())));
            let default_store_0 = ctx.new_local_value().store(zero, temp_alloc);
            ctx.insts_mut().extend([temp_alloc, default_store_0]);

            let rhs_bb = ctx.new_bb_and_append(format!("%and_rhs_{}", exp.name_len8()));
            let sink_bb = ctx.new_bb_and_append(format!("%and_sink_{}", exp.name_len8()));

            let branch = ctx.new_local_value().branch(lhs_v, rhs_bb, sink_bb);
            ctx.close_up(branch);

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
            ctx.insts_mut().extend([rhs_converted, store_rhs]);
            ctx.close_up(jump);

            ctx.upd_bb(sink_bb);

            let load = ctx.new_local_value().load(temp_alloc);
            ctx.append_ins(load);
            return load;
          }
          BinaryOp::Or => {
            let one = ctx.new_local_value().integer(1);
            let temp_alloc = ctx.new_local_value().alloc(Type::get_i32());
            ctx
              .dfg_mut()
              .set_value_name(temp_alloc, Some(format!("%or_temp_{}", exp.name_len8())));
            let default_store_1 = ctx.new_local_value().store(one, temp_alloc);
            ctx.insts_mut().extend([temp_alloc, default_store_1]);

            let rhs_bb = ctx.new_bb_and_append(format!("%or_rhs_{}", exp.name_len8()));
            let sink_bb = ctx.new_bb_and_append(format!("%or_sink_{}", exp.name_len8()));

            let lhs_v = KoopaGen::gen_on_binary_exp(&lhs, ctx);
            let branch = ctx.new_local_value().branch(lhs_v, sink_bb, rhs_bb);
            ctx.close_up(branch);

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
            ctx.insts_mut().extend([rhs_converted, store_lhs]);
            ctx.close_up(jump);

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
        let sym_entry = p
          .lookup_sym_table(&SymIdent::Value(lval.ident.clone()))
          .unwrap();

        // is it array? func_array (no 1st dim info), or normal array?
        match sym_entry.kind {
          SymTableEntryData::FuncDef(_) => panic!("Function is not a LVal"),
          SymTableEntryData::ConstIntDef(_) => {}
          SymTableEntryData::VarIntDef(_alloc) => {}
          SymTableEntryData::ArrayDef(mut alloc) => {
            // int a[3][5] means *[[i32, 5], 3] in Koopa
            // a, we should get *[i32, 5]
            // a[1], we should get *i32
            // a[1][2], we should get i32.

            let array_dim = if alloc.is_global() {
              ctx
                .prog_mut()
                .borrow_value(alloc)
                .ty()
                .ptr_inner()
                .get_array_shape()
                .len()
            } else {
              ctx
                .dfg_mut()
                .value(alloc)
                .ty()
                .ptr_inner()
                .get_array_shape()
                .len()
            };

            // is it a partial deref?
            if lval.idx.len() < array_dim {
              // use getelemptr to deref
              for i in &lval.idx {
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
          }
          SymTableEntryData::FuncParamArrayDef(mut alloc, _) => {
            // int a[][5] means *[i32, 5] in Koopa
            // but alloc is **[i32, 5] because it's a function parameter.
            //
            // a, we should get *[i32, 5]
            // a[1], we should get *i32
            // a[1][2], we don't handle it here.

            // first we nedd to see whether it's a partial deref, or full deref.
            // apply following code on full deref will cause panic.

            let alloc_type = ctx.dfg_mut().value(alloc).ty();
            let inner_ty = alloc_type.ptr_inner().ptr_inner();
            let shape_without_1dim = inner_ty.get_array_shape();

            // see if it's a deref

            if lval.idx.len() < shape_without_1dim.len() + 1 {
              // remove the first *.
              let deref = ctx.new_local_value().load(alloc);
              ctx.append_ins(deref);
              alloc = deref;

              // now alloc is,
              // for exmaple, *[i32, 5], stands for a[][5]
              //
              // if out deref is a[1], then the function should receive a[] (i.e. *i32).

              if let Some(first_dim) = lval.idx.first() {
                // use get_ptr to deref the first dimension.
                let first_dim = Self::gen_on_exp(first_dim, ctx);
                let get_ptr = ctx.new_local_value().get_ptr(alloc, first_dim);
                ctx.append_ins(get_ptr);
                alloc = get_ptr;

                for i in &lval.idx[1..] {
                  let idx = KoopaGen::gen_on_exp(&i, ctx);
                  alloc = ctx.new_local_value().get_elem_ptr(alloc, idx);
                  ctx.append_ins(alloc);
                }

                // an extra get_elem_ptr is needed to align up.

                let zero = ctx.new_local_value().integer(0);
                let extra_get_elem_ptr = ctx.new_local_value().get_elem_ptr(alloc, zero);
                ctx.append_ins(extra_get_elem_ptr);
                alloc = extra_get_elem_ptr;
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

  /// Use some get_elem_ptr to deref an alloc.
  ///
  /// Example:
  /// get_array_elem_ptr(Value(*[[[i32, 7], 5], 3]), [1, 2], ctx) -> *[i32, 7] points to a[1][2][0].
  fn get_array_elem_ptr(alloc: Value, indices: &[i32], ctx: &mut KoopaGenCtx) -> Value {
    let mut ptr = alloc;
    for idx in indices {
      let idx = ctx.new_local_value().integer(*idx);
      ptr = ctx.new_local_value().get_elem_ptr(ptr, idx);
      ctx.append_ins(ptr);
    }
    ptr
  }

  fn declare_sysy_runtime(comp_unit: &AstNodeId, ctx: &mut KoopaGenCtx<'_>) {
    // int getint()
    // int getch()
    // int getarray(int[])
    // void putint(int)
    // void putch(int)
    // void putarray(int, int[])
    // void starttime()
    // void stoptime()

    let funcs: Vec<(String, Vec<Type>, Type)> = vec![
      ("@getint".to_string(), vec![], Type::get_i32()), // int getint()
      ("@getch".to_string(), vec![], Type::get_i32()),  // int getch()
      (
        "@getarray".to_string(),
        vec![Type::get_pointer(Type::get_i32())],
        Type::get_i32(),
      ), // int getarray(int[])
      (
        "@putint".to_string(),
        vec![Type::get_i32()],
        Type::get_unit(),
      ), // void putint(int)
      (
        "@putch".to_string(),
        vec![Type::get_i32()],
        Type::get_unit(),
      ), // void putch(int)
      (
        "@putarray".to_string(),
        vec![Type::get_i32(), Type::get_pointer(Type::get_i32())],
        Type::get_unit(),
      ), // void putarray(int, int[])
      ("@starttime".to_string(), vec![], Type::get_unit()), // void starttime()
      ("@stoptime".to_string(), vec![], Type::get_unit()), // void stoptime()
    ];

    for (name, params, ret) in funcs {
      let func = ctx
        .prog
        .new_func(FunctionData::new_decl(name.clone(), params, ret));

      SymTableEntry {
        symbol: SymIdent::Func(name[1..].to_string()),
        kind: SymTableEntryData::FuncDef(func),
        func: ctx.func_handle(),
      }
      .into_llt(comp_unit);
    }
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
        Type::get_pointer(ty)
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
  fn get_next_loc(&self) -> Vec<i32> {
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
      start_dim = idx + 1;
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

    if stack_top_start_dim == 0 {
      return;
    }

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
    while self.checker.finished() == false {
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
    bb
  }

  fn append_bb(&mut self, bb: BasicBlock) {
    self.func_data_mut().layout_mut().bbs_mut().extend([bb]);
  }

  fn new_bb_and_append(&mut self, name: String) -> BasicBlock {
    let bb = self.new_bb(name);
    self.append_bb(bb);
    bb
  }

  fn upd_bb(&mut self, bb: BasicBlock) {
    assert!(self.bb.is_none());
    self.bb = Some(bb);
  }

  fn close_up(&mut self, br_or_jmp_or_ret: Value) {
    self.insts_mut().extend([br_or_jmp_or_ret]);
    self.bb = None;
  }
}

pub trait TypeUtils {
  fn ptr_inner(&self) -> Type;
  fn get_array_shape(&self) -> Vec<i32>;
  fn array_inner(&self) -> Type;
  fn is_array(&self) -> bool;
}

impl TypeUtils for Type {
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

  fn array_inner(&self) -> Type {
    match self.kind() {
      ir::TypeKind::Array(inner, _) => inner.clone(),
      _ => panic!("Not an array"),
    }
  }

  fn is_array(&self) -> bool {
    match self.kind() {
      ir::TypeKind::Array(_, _) => true,
      _ => false,
    }
  }
}

pub(crate) trait KoopaValueDataToString {
  fn to_string(&self) -> String;
}

impl KoopaValueDataToString for ValueData {
  fn to_string(&self) -> String {
    match self.kind() {
      ir::ValueKind::Integer(_)
      | ir::ValueKind::ZeroInit(_)
      | ir::ValueKind::Undef(_)
      | ir::ValueKind::Aggregate(_)
      | ir::ValueKind::FuncArgRef(_)
      | ir::ValueKind::BlockArgRef(_) => "".to_string(),
      ir::ValueKind::Alloc(_) => {
        let ty = self.ty();
        format!("alloc --> {}", ty.to_string())
      }
      ir::ValueKind::GlobalAlloc(_) => {
        let ty = self.ty();
        format!("global_alloc --> {}", ty.to_string())
      }
      ir::ValueKind::Load(_) => {
        let ty = self.ty();
        format!("load --> {}", ty.to_string())
      }
      ir::ValueKind::Store(_) => {
        let ty = self.ty();
        format!("store --> {}", ty.to_string())
      }
      ir::ValueKind::GetPtr(_) => {
        let ty = self.ty();
        format!("getptr --> {}", ty.to_string())
      }
      ir::ValueKind::GetElemPtr(_) => {
        let ty = self.ty();
        format!("getelemptr --> {}", ty.to_string())
      }
      ir::ValueKind::Binary(_) => {
        let ty = self.ty();
        format!("binary --> {}", ty.to_string())
      }
      ir::ValueKind::Branch(_) => {
        let ty = self.ty();
        format!("branch --> {}", ty.to_string())
      }
      ir::ValueKind::Jump(_) => {
        let ty = self.ty();
        format!("jump --> {}", ty.to_string())
      }
      ir::ValueKind::Call(_) => {
        let ty = self.ty();
        format!("call --> {}", ty.to_string())
      }
      ir::ValueKind::Return(_) => {
        let ty = self.ty();
        format!("ret --> {}", ty.to_string())
      }
    }
  }
}

pub(crate) trait FetchValueType<'a> {
  fn get_type(&self, prog: &'a Program, func: &'a FunctionData) -> Type;
}

impl<'a> FetchValueType<'a> for Value {
  fn get_type(&self, prog: &'a Program, func: &'a FunctionData) -> Type {
    if self.is_global() {
      let value = prog.borrow_value(*self);
      value.ty().clone()
    } else {
      func.dfg().value(*self).ty().clone()
    }
  }
}
