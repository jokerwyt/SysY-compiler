use crate::{define_wrapper, global_mapper, utils::dfs::TreeId};
use uuid::Uuid;

use crate::utils::uuid_mapper::UuidOwner;

/// Given the AstNodeId, return true if the corresponding AstNode keeps a
/// specific variant of AstData.
#[macro_export]
macro_rules! ast_is {
  ($node_id:expr, $variant:ident) => {
    ast_nodes_read(
      $node_id.inner(),
      |node| matches!(&node.ast, ast::AstData::$variant(_)),
    ).unwrap()
  };
}

/// Convert an &mut AstNode into &mut AstData::$variant
#[macro_export]
macro_rules! ast_node_into {
  ($node:expr, $variant:ident) => {
    if let ast::AstData::$variant(data) = &mut $node.ast {
      data
    } else {
      panic!("ast_node_into!() failed")
    }
  };
}

/// Convert a &AstNode into AstData::$variant
#[macro_export]
macro_rules! ast_into {
  ($node_id:expr, $variant:ident) => {
    ast_nodes_read(
      $node_id,
      |node| {
        ast_node_into!(node, $variant).clone()
      },
    ).unwrap()
  };
}

#[macro_export]
macro_rules! ast_data_read_as {
  ($node_id:expr, $variant:ident, |$data:ident| $closure:expr) => {
    ast_nodes_read(
      $node_id,
      |node| {
        if let ast::AstData::$variant($data) = &node.ast {
          $closure
        } else {
          panic!("ast_data_read_as!() failed")
        }
      },
    ).unwrap()
  };
}

#[macro_export]
macro_rules! ast_data_write_as {
  ($node_id:expr, $variant:ident, |$data:ident| $closure:expr) => {
    ast_nodes_write(
      $node_id,
      |node| {
        if let ast::AstData::$variant($data) = &mut node.ast {
          $closure
        } else {
          panic!("ast_data_read_as!() failed")
        }
      },
    ).unwrap()
  };
}

global_mapper!(AST_NODES, ast_nodes_read, ast_nodes_write, ast_nodes_register, AstNode);


impl AstNodeId {
  /// # Panic
  /// Panic if the AstNodeId does not exist.
  pub fn get_ast_data(&self) -> AstData {
    ast_nodes_read(self.inner(), |node| {
      node.ast.clone()
    }).unwrap()
  }
  
  /// Get const single value inside of a node
  pub fn const_single_value(&self) -> Option<i32> {
    match self.get_ast_data() {
      AstData::ConstInitVal(c_init_val) => {
        match c_init_val {
            ConstInitVal::Single(_, v) => v,
            _ => panic!("A const init val is not evaluated when const_single_value()")
        }
      }
      AstData::InitVal(InitVal::Single(_, v)) => v,
      AstData::Exp(exp) => {
        match exp {
          Exp{const_value: Some(v), ..} => Some(v),
          _ => None
        }
      }
      AstData::PrimaryExp(exp) => {
        match exp {
          PrimaryExp::Exp(_, Some(v)) |
          PrimaryExp::Number(v) => Some(v),
          _ => None
        }
      }
      AstData::UnaryExp(exp) => {
        match exp {
          UnaryExp::PrimaryExp{const_value: Some(v), ..} | 
          UnaryExp::Unary{const_value: Some(v), ..} => Some(v),
          _ => None
        }
      }
      AstData::BinaryExp(exp) => {
        match exp {
          BinaryExp::Unary{const_value: Some(v), ..} |
          BinaryExp::Binary{const_value: Some(v), ..} => Some(v),
          _ => None
        }
      }
      AstData::ConstExp(exp) => {
        match exp {
          ConstExp(_, Some(v)) => Some(v),
          _ => panic!("A const exp is not evaluated when const_single_value()")
        }
      }
      _ => None
    }
  }
}

define_wrapper!(AstNodeId, Uuid);

pub type AstBox = Box<AstNode>;

pub struct AstNode {
  pub id: AstNodeId, 
  pub ast: AstData,
  pub parent: Option<AstNodeId>,
}

impl UuidOwner for AstNode {
  fn id(&self) -> Uuid {
    self.id.0
  }
}

impl AstNode {
  /// Insert a node and set its children's parent
  pub fn register(node: AstNode) -> AstNodeId {
    let cur_id = node.id.clone();
    AST_NODES.with_borrow_mut(|nodes| {
      for child in node.ast.get_childrens() {
        let mut child = nodes.borrow_mut(&child.into()).unwrap();
        child.parent = Some(cur_id.clone());
      }
    });
    ast_nodes_register(node);
    cur_id
  }

  pub fn new(ast: AstData) -> AstNode {
    let cur_id = Uuid::new_v4();
    AstNode {
      id: cur_id.into(),
      ast,
      parent: None,
    }
  }

  pub fn new_comp_unit(items: Vec<AstNodeId>) -> AstNodeId {
    let ast = AstData::CompUnit(CompUnit{items});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_decl_const_decl(const_decl: AstNodeId) -> AstNodeId {
    let ast = AstData::Decl(Decl::ConstDecl(const_decl));
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_decl_var_decl(var_decl: AstNodeId) -> AstNodeId {
    let ast = AstData::Decl(Decl::VarDecl(var_decl));
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_const_decl(btype: AstNodeId, const_defs: Vec<AstNodeId>) -> AstNodeId {
    let ast = AstData::ConstDecl(ConstDecl{btype, const_defs});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_const_def(ident: String, idx: Vec<AstNodeId>, const_init_val: AstNodeId) -> AstNodeId {
    let ast = AstData::ConstDef(ConstDef{ident, idx, const_init_val});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_const_init_val_single(exp: AstNodeId) -> AstNodeId {
    let ast = AstData::ConstInitVal(ConstInitVal::Single(exp, None));
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_const_init_val_sequence(exps: Vec<AstNodeId>) -> AstNodeId {
    let ast = AstData::ConstInitVal(ConstInitVal::Sequence(exps));
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_val_decl(btype: AstNodeId, var_defs: Vec<AstNodeId>) -> AstNodeId {
    let ast = AstData::VarDecl(VarDecl{btype, var_defs});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_var_def(ident: String, idx: Vec<AstNodeId>, init_val: Option<AstNodeId>) -> AstNodeId {
    let ast = AstData::VarDef(VarDef{ident, idx, init_val});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_init_val_single(exp: AstNodeId) -> AstNodeId {
    let ast = AstData::InitVal(InitVal::Single(exp, None));
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_init_val_sequence(init_vals: Vec<AstNodeId>) -> AstNodeId {
    let ast = AstData::InitVal(InitVal::Sequence(init_vals));
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_func_def(has_retval: bool, ident: String, func_f_params: AstNodeId, block: AstNodeId) -> AstNodeId {
    let ast = AstData::FuncDef(FuncDef{has_retval, ident, func_f_params, block});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_func_f_params(params: Vec<AstNodeId>) -> AstNodeId {
    let ast = AstData::FuncFParams(FuncFParams{params});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_func_f_param(btype: AstNodeId, ident: String, idx: Option<Vec<AstNodeId>>) -> AstNodeId {
    if let Some(idx) = idx {
      let ast = AstData::FuncFParam(FuncFParam::Array{btype, ident, shape_no_first_dim: idx});
      AstNode::register(AstNode::new(ast))
    } else {
      let ast = AstData::FuncFParam(FuncFParam::Single{btype, ident});
      AstNode::register(AstNode::new(ast))
    }
  }

  pub fn new_block(items: Vec<AstNodeId>) -> AstNodeId {
    let ast = AstData::Block(Block{items});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_block_item_decl(decl: AstNodeId) -> AstNodeId {
    let ast = AstData::BlockItem(BlockItem::Decl(decl));
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_block_item_stmt(stmt: AstNodeId) -> AstNodeId {
    let ast = AstData::BlockItem(BlockItem::Stmt(stmt));
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_stmt_assign(lval: AstNodeId, exp: AstNodeId) -> AstNodeId {
    let ast = AstData::Stmt(Stmt::Assign(lval, exp));
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_stmt_exp(exp: Option<AstNodeId>) -> AstNodeId {
    let ast = AstData::Stmt(Stmt::Exp(exp));
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_stmt_block(block: AstNodeId) -> AstNodeId {
    let ast = AstData::Stmt(Stmt::Block(block));
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_stmt_if_else(expr: AstNodeId, branch1: AstNodeId, branch0: Option<AstNodeId>) -> AstNodeId {
    let ast = AstData::Stmt(Stmt::IfElse{expr, branch1, branch0});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_stmt_while(expr: AstNodeId, block: AstNodeId) -> AstNodeId {
    let ast = AstData::Stmt(Stmt::While{expr, block});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_stmt_break() -> AstNodeId {
    let ast = AstData::Stmt(Stmt::Break);
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_stmt_continue() -> AstNodeId {
    let ast = AstData::Stmt(Stmt::Continue);
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_stmt_return(exp: Option<AstNodeId>) -> AstNodeId {
    let ast = AstData::Stmt(Stmt::Return(exp));
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_exp(l_or_exp: AstNodeId) -> AstNodeId {
    let ast = AstData::Exp(Exp{l_or_exp, const_value: None});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_lval(ident: String, idx: Vec<AstNodeId>) -> AstNodeId {
    let ast = AstData::LVal(LVal{ident, idx});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_primary_exp_exp(exp: AstNodeId) -> AstNodeId {
    let ast = AstData::PrimaryExp(PrimaryExp::Exp(exp, None));
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_primary_exp_lval(lval: AstNodeId) -> AstNodeId {
    let ast = AstData::PrimaryExp(PrimaryExp::LVal(lval));
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_primary_exp_number(num: i32) -> AstNodeId {
    let ast = AstData::PrimaryExp(PrimaryExp::Number(num));
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_unary_exp_primary(pexp: AstNodeId) -> AstNodeId {
    let ast = AstData::UnaryExp(UnaryExp::PrimaryExp{pexp, const_value: None});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_unary_exp_call(ident: String, params: AstNodeId) -> AstNodeId {
    let ast = AstData::UnaryExp(UnaryExp::Call{ident, params});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_unary_exp_unary(op: UnaryOp, exp: AstNodeId) -> AstNodeId {
    let ast = AstData::UnaryExp(UnaryExp::Unary{op, exp, const_value: None});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_binary_exp_unary(exp: AstNodeId) -> AstNodeId {
    let ast = AstData::BinaryExp(BinaryExp::Unary{exp, const_value: None});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_binary_exp_binary(lhs: AstNodeId, op: BinaryOp, rhs: AstNodeId) -> AstNodeId {
    let ast = AstData::BinaryExp(BinaryExp::Binary{lhs, op, rhs, const_value: None});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_const_exp(exp: AstNodeId) -> AstNodeId {
    let ast = AstData::ConstExp(ConstExp(exp, None));
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_binary_exp(lhs: AstNodeId, op: BinaryOp, rhs: AstNodeId) -> AstNodeId {
    let ast = AstData::BinaryExp(BinaryExp::Binary{lhs, op, rhs, const_value: None});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_func_r_params(params: Vec<AstNodeId>) -> AstNodeId {
    let ast = AstData::FuncRParams(FuncRParams{params});
    AstNode::register(AstNode::new(ast))
  }

  pub fn new_btype() -> AstNodeId {
    let ast = AstData::BType;
    AstNode::register(AstNode::new(ast))
  }
  
}



#[derive(Debug, Clone)]
pub enum AstData {
  CompUnit(CompUnit),
  Decl(Decl),
  ConstDecl(ConstDecl),
  BType,
  ConstDef(ConstDef), 
  ConstInitVal(ConstInitVal),
  VarDecl(VarDecl),
  VarDef(VarDef), 
  InitVal(InitVal),
  FuncDef(FuncDef),
  FuncFParams(FuncFParams), 
  FuncFParam(FuncFParam),
  Block(Block),
  BlockItem(BlockItem),

  /// Including grammar non-terminators:\
  /// Stmt, StmtIfClose, StmtIfOpen and StmtNotEndInStmt\
  /// \
  /// We don't need to distinguish them any more after we finish LR(1) analysis.\
  Stmt(Stmt), 

  Exp(Exp),
  LVal(LVal),
  PrimaryExp(PrimaryExp),
  UnaryExp(UnaryExp),
  FuncRParams(FuncRParams),

  /// Including grammar non-terminators:\
  /// MulExp, AddExp, RelExp, EqExp, LAndExp, LOrExp\
  /// Lhs: [AstData::BinaryExp]\
  /// Rhs: [AstData::UnaryExp] | [AstData::BinaryExp]
  BinaryExp(BinaryExp),
  ConstExp(ConstExp),
}

impl AstData {
  pub fn get_childrens(&self) -> Vec<AstNodeId> {
    match self {
      AstData::CompUnit(CompUnit{items}) => items.clone(),
      AstData::Decl(Decl::ConstDecl(const_decl)) => vec![const_decl.clone()],
      AstData::Decl(Decl::VarDecl(var_decl)) => vec![var_decl.clone()],
      AstData::ConstDecl(ConstDecl{const_defs, ..}) => const_defs.clone(),
      AstData::ConstDef(ConstDef{idx, const_init_val, ..}) => {
        let mut res = idx.clone();
        res.push(const_init_val.clone());
        res
      },
      AstData::ConstInitVal(ConstInitVal::Single(exp, ..)) => vec![exp.clone()],
      AstData::ConstInitVal(ConstInitVal::Sequence(exps)) => exps.clone(),
      AstData::VarDecl(VarDecl{var_defs, ..}) => var_defs.clone(),
      AstData::VarDef(VarDef{idx, init_val, ..}) => {
        let mut res = idx.clone();
        if let Some(init_val) = init_val {
          res.push(init_val.clone());
        }
        res
      },
      AstData::InitVal(InitVal::Single(exp, _)) => vec![exp.clone()],
      AstData::InitVal(InitVal::Sequence(init_vals)) => init_vals.clone(),
      AstData::FuncDef(FuncDef{func_f_params, block, ..}) => vec![func_f_params.clone(), block.clone()],
      AstData::FuncFParams(FuncFParams{params}) => params.clone(),
      AstData::FuncFParam(FuncFParam::Single{btype, ..}) => vec![btype.clone()],
      AstData::FuncFParam(FuncFParam::Array{btype, shape_no_first_dim, ..}) => {
        let mut res = shape_no_first_dim.clone();
        res.push(btype.clone());
        res
      },
      AstData::Block(Block{items}) => items.clone(),
      AstData::BlockItem(BlockItem::Decl(decl)) => vec![decl.clone()],
      AstData::BlockItem(BlockItem::Stmt(stmt)) => vec![stmt.clone()],
      AstData::Stmt(Stmt::Assign(lval, exp)) => vec![lval.clone(), exp.clone()],
      AstData::Stmt(Stmt::Exp(Some(exp))) => vec![exp.clone()],
      AstData::Stmt(Stmt::Exp(None)) => vec![],
      AstData::Stmt(Stmt::Block(block)) => vec![block.clone()],
      AstData::Stmt(Stmt::IfElse{expr, branch1, branch0}) => {
        let mut res = vec![expr.clone(), branch1.clone()];
        if let Some(branch0) = branch0 {
          res.push(branch0.clone());
        }
        res
      },
      AstData::Stmt(Stmt::While{expr, block}) => vec![expr.clone(), block.clone()],
      AstData::Stmt(Stmt::Return(Some(exp))) => vec![exp.clone()],
      AstData::Stmt(Stmt::Return(None)) => vec![],
      AstData::Stmt(Stmt::Break) => vec![],
      AstData::Stmt(Stmt::Continue) => vec![],
      AstData::Exp(Exp{l_or_exp, ..}) => vec![l_or_exp.clone()],
      AstData::LVal(LVal{idx, ..}) => idx.clone(),
      AstData::UnaryExp(UnaryExp::PrimaryExp{pexp, ..}) => vec![pexp.clone()],
      AstData::UnaryExp(UnaryExp::Call{params, ..}) => vec![params.clone()],
      AstData::UnaryExp(UnaryExp::Unary{exp, ..}) => vec![exp.clone()],
      AstData::BinaryExp(BinaryExp::Binary{lhs, rhs, ..}) => vec![lhs.clone(), rhs.clone()],
      AstData::BinaryExp(BinaryExp::Unary{exp, ..}) => vec![exp.clone()],
      AstData::ConstExp(ConstExp(exp, ..)) => vec![exp.clone()],
      AstData::BType => vec![],
      AstData::PrimaryExp(PrimaryExp::Exp(uuid, ..)) => vec![uuid.clone()],
      AstData::PrimaryExp(PrimaryExp::LVal(uuid, ..)) => vec![uuid.clone()],
      AstData::PrimaryExp(PrimaryExp::Number(_)) => vec![],
      AstData::FuncRParams(FuncRParams{params}) => params.clone()
    }
  }
}

#[derive(Debug, Clone)]
pub struct CompUnit {
  /// [AstData::Decl] | [AstData::FuncDef]
  pub items: Vec<AstNodeId>
}

#[derive(Debug, Clone)]
pub enum Decl {
  ConstDecl(AstNodeId),
  VarDecl(AstNodeId),
}

#[derive(Debug, Clone)]
pub struct ConstDecl {
  /// [AstData::BType]
  pub btype: AstNodeId,
  
  // [AstData::ConstDef]
  pub const_defs: Vec<AstNodeId>
}

pub struct BType;

#[derive(Debug, Clone)]
pub struct ConstIdxList {
  /// [AstData::ConstExp]
  pub const_exps: Vec<AstNodeId>, 
  pub eval_out: Option<Vec<i32>>
}

#[derive(Debug, Clone)]
pub struct ConstDef {
  pub ident: String,
  /// [AstData::ConstExp]
  pub idx: Vec<AstNodeId>,
  /// [AstData::ConstInitVal]
  pub const_init_val: AstNodeId
}

impl ConstDef {
  pub fn is_array(&self) -> bool {
    self.idx.len() > 0
  }
}

#[derive(Debug, Clone)]
pub enum ConstInitVal {
  /// Contains an [AstData::ConstExp]
  Single(AstNodeId, Option<i32>),
  /// Contains many [AstData::ConstInitVal]
  Sequence(Vec<AstNodeId>)
}

impl ConstInitVal {
  pub fn const_mut(&mut self) -> Option<&mut Option<i32>> {
    match self {
      ConstInitVal::Single(_, v) => v.into(),
      _ => None
    }
  }
}

#[derive(Debug, Clone)]
pub struct VarDecl {
  /// [AstData::BType]
  pub btype: AstNodeId,

  /// [AstData::VarDef]
  pub var_defs: Vec<AstNodeId>,
}

#[derive(Debug, Clone)]
pub struct VarDef {
  pub ident: String,
  /// [AstData::ConstExp]
  pub idx: Vec<AstNodeId>, 
  /// [AstData::InitVal]
  pub init_val: Option<AstNodeId>
}

impl VarDef {
  pub fn is_array(&self) -> bool {
    self.idx.len() > 0
  }

  pub fn has_init_val(&self) -> bool {
    self.init_val.is_some()
  }
}

#[derive(Debug, Clone)]
pub enum InitVal {
  /// [AstData::Exp]
  Single(AstNodeId, Option<i32>),

  /// [AstData::InitVal]
  Sequence(Vec<AstNodeId>)
}

impl InitVal {
  pub fn const_mut(&mut self) -> Option<&mut Option<i32>> {
    match self {
      InitVal::Single(_, v) => v.into(),
      _ => None
    }
  }
}

#[derive(Debug, Clone)]
pub struct FuncDef {
  /// void or int
  pub has_retval: bool, 

  pub ident: String,
  /// [AstData::FuncFParams]
  pub func_f_params: AstNodeId,
  pub block: AstNodeId,
}

#[derive(Debug, Clone)]
pub struct FuncFParams {
  /// [AstData::FuncFParam]
  pub params: Vec<AstNodeId>
}

#[derive(Debug, Clone)]
pub enum FuncFParam {
  Single{
    /// [AstData::BType]
    btype: AstNodeId,
    ident: String,
  },
  Array{
    /// [AstData::BType]
    btype: AstNodeId,
    ident: String,

    /// [AstData::ConstExp]
    /// A formal parameter array will omit the first dim
    shape_no_first_dim: Vec<AstNodeId>,
  }
}

impl FuncFParam {
  pub fn is_array(&self) -> bool {
    match self {
      FuncFParam::Single{..} => false,
      FuncFParam::Array{..} => true,
    }
  }

}

#[derive(Debug, Clone)]
pub struct Block {
  /// [AstData::BlockItem]
  pub items: Vec<AstNodeId>,
}

#[derive(Debug, Clone)]
pub enum BlockItem {
  /// Contains an [AstData::Decl]
  Decl(AstNodeId), 
  /// Contains an [AstData::Stmt]
  Stmt(AstNodeId), 
}

#[derive(Debug, Clone)]
pub enum Stmt {
  /// Contains an [AstData::LVal and an [AstData::Exp]
  Assign(AstNodeId, AstNodeId),
  /// Contains a possible [AstData::Exp, or empty statement (;)]
  Exp (Option<AstNodeId>),
  /// Contains an [AstData::Block]
  Block(AstNodeId),
  IfElse{
    /// [AstData::Exp]
    expr: AstNodeId, 
    /// [AstData::Stmt]
    branch1: AstNodeId, 
    /// [AstData::Stmt]
    branch0: Option<AstNodeId>
  },
  While{
    /// [AstData::Exp]
    expr: AstNodeId,
    /// [AstData::Stmt]
    block: AstNodeId
  },
  Break,
  Continue,
  /// Contains a possible [AstData::Exp]
  Return(Option<AstNodeId>),
}

#[derive(Debug, Clone)]
pub struct Exp {
  /// [AstData::LOrExp]
  pub l_or_exp: AstNodeId, 
  pub const_value: Option<i32>,
}

#[derive(Debug, Clone)]
pub struct LVal {
  pub ident: String, 
  /// [AstData::Exp]
  pub idx: Vec<AstNodeId>,
}

#[derive(Debug, Clone)]
pub enum PrimaryExp {
  /// Contains an [AstData::Exp]
  Exp(AstNodeId, Option<i32>),
  /// Contains an [AstData::LVal]
  LVal(AstNodeId),
  Number(i32),
}

impl PrimaryExp {
  pub fn const_mut(&mut self) -> Option<&mut Option<i32>> {
    match self {
      PrimaryExp::Exp(_, v) => v.into(),
      _ => None
    }
  }
}

#[derive(Debug, Clone)]
pub enum UnaryExp {
  PrimaryExp{
    /// [AstData::PrimaryExp]
    pexp: AstNodeId,
    const_value: Option<i32>,
  },
  Call{
    ident: String,
    /// [AstData::FuncRParams]
    params: AstNodeId,
  },
  Unary{
    op: UnaryOp,
    /// [AstData::UnaryExp]
    exp: AstNodeId,
    const_value: Option<i32>,
  },
}

impl UnaryExp {
  pub fn const_mut(&mut self) -> Option<&mut Option<i32>> {
    match self {
      UnaryExp::PrimaryExp{const_value, ..} => const_value.into(),
      UnaryExp::Unary{const_value, ..} => const_value.into(),
      _ => None
    }
  }
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOp {
  Pos,
  Neg,
  Not,
}

impl UnaryOp {
  pub fn from_str(s: &str) -> Option<UnaryOp> {
    match s {
      "+" => Some(UnaryOp::Pos),
      "-" => Some(UnaryOp::Neg),
      "!" => Some(UnaryOp::Not),
      _ => None,
    }
  }

  pub fn eval(op: UnaryOp, v: i32) -> i32 {
    match op {
      UnaryOp::Pos => v,
      UnaryOp::Neg => -v,
      UnaryOp::Not => if v == 0 { 1 } else { 0 },
    }
  }
}

#[derive(Debug, Clone)]
pub struct FuncRParams {
  /// [AstData::Exp]
  pub params: Vec<AstNodeId>
}

#[derive(Debug, Clone)]
pub enum BinaryExp {
  Unary{
    /// [AstData::UnaryExp]
    exp: AstNodeId,
    const_value: Option<i32>,
  },
  Binary{
    /// [AstData::BinaryExp]
    lhs: AstNodeId,
    op: BinaryOp,
    /// [AstData::UnaryExp] | [AstData::BinaryExp]
    rhs: AstNodeId,
    const_value: Option<i32>,
  },
}

impl BinaryExp {
  pub fn const_mut(&mut self) -> &mut Option<i32> {
    match self {
      BinaryExp::Unary{const_value, ..} => const_value.into(),
      BinaryExp::Binary{const_value, ..} => const_value.into(),
    }
  }
}

#[derive(Debug, Clone, Copy)]
pub enum BinaryOp {
  Add,
  Sub,
  Mul,
  Div,
  Mod,
  Lt,
  Le,
  Gt,
  Ge,
  Eq,
  Ne,
  And,
  Or,
}

impl BinaryOp {
  pub fn from_str(s: &str) -> Option<BinaryOp> {
    match s {
      "+" => Some(BinaryOp::Add),
      "-" => Some(BinaryOp::Sub),
      "*" => Some(BinaryOp::Mul),
      "/" => Some(BinaryOp::Div),
      "%" => Some(BinaryOp::Mod),
      "<" => Some(BinaryOp::Lt),
      "<=" => Some(BinaryOp::Le),
      ">" => Some(BinaryOp::Gt),
      ">=" => Some(BinaryOp::Ge),
      "==" => Some(BinaryOp::Eq),
      "!=" => Some(BinaryOp::Ne),
      "&&" => Some(BinaryOp::And),
      "||" => Some(BinaryOp::Or),
      _ => None,
    }
  }

  pub fn eval(v1: i32, op: BinaryOp, v2: i32) -> i32 {
    match op {
      BinaryOp::Add => v1 + v2,
      BinaryOp::Sub => v1 - v2,
      BinaryOp::Mul => v1 * v2,
      BinaryOp::Div => v1 / v2,
      BinaryOp::Mod => v1 % v2,
      BinaryOp::Lt => if v1 < v2 { 1 } else { 0 },
      BinaryOp::Le => if v1 <= v2 { 1 } else { 0 },
      BinaryOp::Gt => if v1 > v2 { 1 } else { 0 },
      BinaryOp::Ge => if v1 >= v2 { 1 } else { 0 },
      BinaryOp::Eq => if v1 == v2 { 1 } else { 0 },
      BinaryOp::Ne => if v1 != v2 { 1 } else { 0 },
      BinaryOp::And => if v1 != 0 && v2 != 0 { 1 } else { 0 },
      BinaryOp::Or => if v1 != 0 || v2 != 0 { 1 } else { 0 },
    }
  }
}

#[derive(Debug, Clone)]
/// Contains an [AstData::Exp] and the const evaluation result
pub struct ConstExp(pub AstNodeId, pub Option<i32>);

impl TreeId for AstNodeId {
  /// get parent AstNodeId
  /// 
  /// # Panic
  /// Panic if the AstNodeId does not exist.
  fn get_parent(&self) -> Option<AstNodeId> {
    ast_nodes_read(&self.0, |node| {
      node.parent.clone()
    }).unwrap()
  }

  /// get children AstNodeId
  /// 
  /// # Panic
  /// Panic if the AstNodeId does not exist.
  fn get_childrens(&self) -> Vec<AstNodeId> {
    self.get_ast_data().get_childrens()
  }
}

impl AstNodeId {
  pub fn to_string(&self, human_friendly: bool) -> String {
    // use dfs visitor
    let res = std::cell::RefCell::new(String::new());
    let depth = std::cell::RefCell::new(0);
    let visitor 
      = crate::utils::dfs::DfsVisitor::<_, _, AstNodeId>::new(
        |node| {
          *depth.borrow_mut() += 1;
          let data = node.get_ast_data();
          let mut res = res.borrow_mut();
          if human_friendly {
            res.push_str(&format!("{}{:?} {{\n", "  ".repeat(*depth.borrow()), data));
          } else {
            res.push_str(&format!("{:?} {{", data));
          }

          Ok(())
        },
        |_| { 
          *depth.borrow_mut() -= 1;
          let mut res = res.borrow_mut();
          if human_friendly {
            res.push_str(&format!("{}}}\n", "  ".repeat(*depth.borrow())));
          } else {
            res.push_str("}");
          }
          Ok(())
        },
      );
    visitor.dfs(self).unwrap();
    res.take()
  }
}