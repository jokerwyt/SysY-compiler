use std::{cell::{OnceCell, RefCell}, collections::HashMap, sync::OnceLock};

use uuid::Uuid;

use crate::utils::{GlobalMapper, UuidOwner};

/// transfer a AstNode into a specific variant
macro_rules! ast_into {
    ($node:expr, $variant:ident) => {
        if let AstData::$variant(data) = &$node.ast {
            Some(data)
        } else {
            panic!("ast_into! failed: expected {:?}, got {:?}", stringify!($variant), $node.ast)
        }
    };
}

/// return true if the AstNode is a specific variant
macro_rules! ast_is {
    ($node:expr, $variant:ident) => {
        if let AstData::$variant(_) = &$node.ast {
            true
        } else {
            false
        }
    };
}

/// get const_value: Option<i32> from a AstNodeId.
fn get_const_value(node: AstNodeId) -> Option<i32> {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
        let mut node = nodes.borrow(&node).unwrap();
        if let AstData::Exp(exp) = &node.ast {
            exp.const_value
        } else {
            panic!("get const value of a non-expression")
        }
    })
}


thread_local! {
  static AST_NODES: RefCell<GlobalMapper<AstNode>> = RefCell::new(GlobalMapper {
    data: HashMap::new()
  });
}

pub type AstNodeId = Uuid;
pub type AstBox = Box<AstNode>;

pub struct AstNode {
  pub id: Uuid, 
  pub ast: AstData,
  pub parent: Option<Uuid>,
}

impl UuidOwner for AstNode {
  fn id(&self) -> Uuid {
    self.id
  }
}

impl AstNode {
  pub fn new_comp_unit(items: Vec<AstNodeId>) -> AstNodeId {
    AST_NODES.with(|nodes| {
      let mut nodes = nodes.borrow_mut();

      let cur_id = Uuid::new_v4();
      for item in &items {
        let mut node = nodes.borrow_mut(item).unwrap();
        node.parent = Some(cur_id);
      }

       nodes.insert(AstNode {
          id: cur_id, 
          ast: AstData::CompUnit(CompUnit(items)),
          parent: None,
      });
 
      // assign pid to children

      cur_id
    })
  }

  pub fn new_const_def(ident: Ident, idx: Vec<AstNodeId>, const_init_val: AstNodeId) -> AstNodeId {
    AST_NODES.with(|nodes| {
      let mut nodes = nodes.borrow_mut();
      let cur_id = Uuid::new_v4();
      
      for idx in &idx {
        let mut node = nodes.borrow_mut(idx).unwrap();
        node.parent = Some(cur_id);
      }
      {
        let mut node = nodes.borrow_mut(&const_init_val).unwrap();
        node.parent = Some(cur_id);
      }

      nodes.insert(AstNode {
          id: cur_id,
          ast: AstData::ConstDef(ConstDef {
            ident,
            idx: idx.clone(),
            const_init_val,
          }),
          parent: None,
      });

      cur_id
    })
  }

  pub fn new_const_init_val_single(exp: AstNodeId) -> AstNodeId {
    AST_NODES.with(|nodes| {
      let mut nodes = nodes.borrow_mut();
      let cur_id = Uuid::new_v4();
      {
        let mut node = nodes.borrow_mut(&exp).unwrap();
        node.parent = Some(cur_id);
      }

      nodes.insert(AstNode {
          id: cur_id, 
          ast: AstData::ConstInitVal(ConstInitVal::Single(exp)),
          parent: None,
      });


      cur_id
    })
  }

  pub fn new_const_init_val_sequence(exps: Vec<AstNodeId>) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      let cur_id = Uuid::new_v4();
      
      for exp in &exps {
        let mut node = nodes.borrow_mut(&exp).unwrap();
        node.parent = Some(cur_id);
      }

      nodes.insert(AstNode {
          id: cur_id, 
          ast: AstData::ConstInitVal(ConstInitVal::Sequence(exps)),
          parent: None,
      });

      cur_id
    })
  }

  pub fn new_var_def(ident: Ident, idx: Vec<AstNodeId>, init_val: Option<AstNodeId>) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      let cur_id = Uuid::new_v4();
      
      for idx in &idx {
        let mut node = nodes.borrow_mut(&idx).unwrap();
        node.parent = Some(cur_id);
      }

      nodes.insert(AstNode {
          id: cur_id, 
          ast: AstData::VarDef(VarDef {
            ident,
            idx,
            init_val,
          }),
          parent: None,
      });


      if let Some(init_val) = init_val {
        let mut node = nodes.borrow_mut(&init_val).unwrap();
        node.parent = Some(cur_id);
      }

      cur_id
    })
  }

  pub fn new_init_val_single(exp: AstNodeId) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      let cur_id = nodes.insert(AstNode {
          id: Uuid::new_v4(),
          ast: AstData::InitVal(InitVal::Single(exp)),
          parent: None,
      });

      let mut node = nodes.borrow_mut(&exp).unwrap();
      node.parent = Some(cur_id);

      cur_id
    })
  }

  pub fn new_init_val_sequence(exps: Vec<AstNodeId>) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      let cur_id = Uuid::new_v4();
      for exp in &exps {
        let mut node = nodes.borrow_mut(&exp).unwrap();
        node.parent = Some(cur_id);
      }
      nodes.insert(AstNode {
          id: cur_id,
          ast: AstData::InitVal(InitVal::Sequence(exps)),
          parent: None,
      });

      cur_id
    })
  }

  pub fn new_func_def(has_retval: bool, ident: Ident, func_f_params: Vec<AstNodeId>, block: AstNodeId) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      
      let cur_id = Uuid::new_v4();
      for param in &func_f_params {
        let mut node = nodes.borrow_mut(&param).unwrap();
        node.parent = Some(cur_id);
      }

      let cur_id = nodes.insert(AstNode {
          id: cur_id, 
          ast: AstData::FuncDef(FuncDef {
            has_retval,
            ident,
            func_f_params,
            block,
          }),
          parent: None,
      });


      let mut node = nodes.borrow_mut(&block).unwrap();
      node.parent = Some(cur_id);

      cur_id
    })
  }

  pub fn new_func_f_param(ident: Ident, shape_exclude_first_dimension: Option<Vec<AstNodeId>>) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      let cur_id = Uuid::new_v4();

      if let Some(shape_exclude_first_dimension) = &shape_exclude_first_dimension {
        for idx in shape_exclude_first_dimension {
          let mut node = nodes.borrow_mut(&idx).unwrap();
          node.parent = Some(cur_id);
        }
      }
      
      nodes.insert(AstNode {
          id: cur_id, 
          ast: AstData::FuncFParam(FuncFParam {
            ident,
            shape_exclude_first_dimension,
          }),
          parent: None,
      });


      cur_id
    })
  }

  pub fn new_block(items: Vec<AstNodeId>) -> AstNodeId {
    AST_NODES.with(|nodes| {
      let mut nodes = nodes.borrow_mut();
      let cur_id = Uuid::new_v4();
      for item in &items {
        let mut node = nodes.borrow_mut(&item).unwrap();
        node.parent = Some(cur_id);
      }
      
      nodes.insert(AstNode {
          id: cur_id, 
          ast: AstData::Block(Block {
            items,
          }),
          parent: None,
      });

      cur_id
    })
  }

  pub fn new_block_item_decl(decl: AstNodeId) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      let cur_id = nodes.insert(AstNode {
          id: Uuid::new_v4(),
          ast: AstData::BlockItem(BlockItem::Decl(decl)),
          parent: None,
      });

      let mut node = nodes.borrow_mut(&decl).unwrap();
      node.parent = Some(cur_id);

      cur_id
    })
  }

  pub fn new_block_item_stmt(stmt: AstNodeId) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      let cur_id = nodes.insert(AstNode {
          id: Uuid::new_v4(),
          ast: AstData::BlockItem(BlockItem::Stmt(stmt)),
          parent: None,
      });

      let mut node = nodes.borrow_mut(&stmt).unwrap();
      node.parent = Some(cur_id);

      cur_id
    })
  }

  pub fn new_stmt_if_else(exp: AstNodeId, if_block: AstNodeId, else_block: Option<AstNodeId>) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      let cur_id = nodes.insert(AstNode {
          id: Uuid::new_v4(),
          ast: AstData::Stmt(Stmt::IfElse(exp, if_block, else_block)),
          parent: None,
      });

      let mut node = nodes.borrow_mut(&exp).unwrap();
      node.parent = Some(cur_id);

      let mut node = nodes.borrow_mut(&if_block).unwrap();
      node.parent = Some(cur_id);

      if let Some(else_block) = else_block {
        let mut node = nodes.borrow_mut(&else_block).unwrap();
        node.parent = Some(cur_id);
      }

      cur_id
    })
  }

  pub fn new_stmt_while(exp: AstNodeId, block: AstNodeId) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      let cur_id = nodes.insert(AstNode {
          id: Uuid::new_v4(),
          ast: AstData::Stmt(Stmt::While(exp, block)),
          parent: None,
      });

      let mut node = nodes.borrow_mut(&exp).unwrap();
      node.parent = Some(cur_id);

      let mut node = nodes.borrow_mut(&block).unwrap();
      node.parent = Some(cur_id);

      cur_id
    })
  }

  pub fn new_stmt_assign(lval: AstNodeId, exp: AstNodeId) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      let cur_id = nodes.insert(AstNode {
          id: Uuid::new_v4(),
          ast: AstData::Stmt(Stmt::Assign(lval, exp)),
          parent: None,
      });

      let mut node = nodes.borrow_mut(&lval).unwrap();
      node.parent = Some(cur_id);

      let mut node = nodes.borrow_mut(&exp).unwrap();
      node.parent = Some(cur_id);

      cur_id
    })
  }

  pub fn new_stmt_exp(exp: Option<AstNodeId>) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      let cur_id = nodes.insert(AstNode {
          id: Uuid::new_v4(),
          ast: AstData::Stmt(Stmt::Exp(exp)),
          parent: None,
      });

      if let Some(exp) = exp {
        let mut node = nodes.borrow_mut(&exp).unwrap();
        node.parent = Some(cur_id);
      }

      cur_id
    })
  }

  pub fn new_stmt_break() -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      nodes.insert(AstNode {
          id: Uuid::new_v4(),
          ast: AstData::Stmt(Stmt::Break),
          parent: None,
      })
    })
  }

  pub fn new_stmt_continue() -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      nodes.insert(AstNode {
          id: Uuid::new_v4(),
          ast: AstData::Stmt(Stmt::Continue),
          parent: None,
      })
    })
  }

  pub fn new_stmt_return(exp: Option<AstNodeId>) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      let cur_id = nodes.insert(AstNode {
          id: Uuid::new_v4(),
          ast: AstData::Stmt(Stmt::Return(exp)),
          parent: None,
      });

      if let Some(exp) = exp {
        let mut node = nodes.borrow_mut(&exp).unwrap();
        node.parent = Some(cur_id);
      }

      cur_id
    })
  }

  pub fn new_lval(name: Ident, idx: Vec<AstNodeId>) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();

      let cur_id = Uuid::new_v4();

      for idx in &idx {
        let mut node = nodes.borrow_mut(&idx).unwrap();
        node.parent = Some(cur_id);
      }
      
      nodes.insert(AstNode {
          id: cur_id,
          ast: AstData::LVal(LVal {
              name,
              idx,
          }),
          parent: None,
      });


      cur_id
    })
  }

  pub fn new_primary_exp_number(num: i32) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      nodes.insert(AstNode {
          id: Uuid::new_v4(),
          ast: AstData::Exp(Exp {
              exp_data: ExpData::Number(num),
              const_value: Some(num),
          }),
          parent: None,
      })
    })
  }

  pub fn new_exp_call(ident: Ident, args: Vec<AstNodeId>) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      let cur_id = Uuid::new_v4();

      for arg in &args {
        let mut node = nodes.borrow_mut(&arg).unwrap();
        node.parent = Some(cur_id);
      }
      
      nodes.insert(AstNode {
          id: cur_id, 
          ast: AstData::Exp(Exp {
              exp_data: ExpData::Call(ident, args),
              const_value: None,
          }),
          parent: None,
      });

      cur_id
    })
  }

  pub fn new_exp_unary(op: UnaryOp, exp: AstNodeId) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      let cur_id = nodes.insert(AstNode {
          id: Uuid::new_v4(),
          ast: AstData::Exp(Exp {
              exp_data: ExpData::Unary(op, exp),
              const_value: {
                let exp = get_const_value(exp);
                if let Some(exp) = exp {
                  Some(UnaryOp::eval(op, exp))
                } else {
                  None
                }
              }
          }),
          parent: None,
      });

      let mut node = nodes.borrow_mut(&exp).unwrap();
      node.parent = Some(cur_id);

      cur_id
    })
  }

  pub fn new_exp_binary(lhs: AstNodeId, op: BinaryOp, rhs: AstNodeId) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      let cur_id = nodes.insert(AstNode {
          id: Uuid::new_v4(),
          ast: AstData::Exp(Exp {
              exp_data: ExpData::Binary(lhs, op, rhs),
              const_value: {
                let (lhs, rhs) = (get_const_value(lhs), get_const_value(rhs));
                if let (Some(lhs), Some(rhs)) = (lhs, rhs) {
                  Some(BinaryOp::eval(lhs, op, rhs))
                } else {
                  None
                }
              }
          }),
          parent: None,
      });

      let mut node = nodes.borrow_mut(&lhs).unwrap();
      node.parent = Some(cur_id);

      let mut node = nodes.borrow_mut(&rhs).unwrap();
      node.parent = Some(cur_id);

      cur_id
    })
  }

  pub fn new_const_decl(const_defs: Vec<AstNodeId>) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      let cur_id = Uuid::new_v4();

      for const_def in &const_defs {
        let mut node = nodes.borrow_mut(&const_def).unwrap();
        node.parent = Some(cur_id);
      }
      
      nodes.insert(AstNode {
          id: cur_id, 
          ast: AstData::ConstDecl(ConstDecl(const_defs)),
          parent: None,
      });

      cur_id
    })
  }

  pub fn new_var_decl(var_defs: Vec<AstNodeId>) -> AstNodeId {
    AST_NODES.with(|nodes| {

      let mut nodes = nodes.borrow_mut();
      let cur_id = Uuid::new_v4();
      for var_def in &var_defs {
        let mut node = nodes.borrow_mut(&var_def).unwrap();
        node.parent = Some(cur_id);
      }
      
      nodes.insert(AstNode {
          id: cur_id, 
          ast: AstData::VarDecl(VarDecl {
              var_defs,
          }),
          parent: None,
      });


      cur_id
    })
  }
}



pub enum AstData {
  CompUnit(CompUnit),
  FuncDef(FuncDef),
  ConstDecl(ConstDecl),
  VarDecl(VarDecl),
  ConstDef(ConstDef), 
  VarDef(VarDef), 
  FuncFParam(FuncFParam),
  Block(Block),
  BlockItem(BlockItem),
  Stmt(Stmt),
  Exp(Exp),
  InitVal(InitVal),
  ConstInitVal(ConstInitVal),
  LVal(LVal)
}

pub type Ident = String;

pub struct CompUnit(Vec<AstNodeId>);

pub struct FuncFParams(Vec<AstNodeId>);

pub enum CompUnitItem {
  FuncDef(AstNodeId),
  Decl(AstNodeId),
}

pub enum Decl {
  Const(AstNodeId),
  Var(AstNodeId),
} 

pub struct ConstDecl(Vec<AstNodeId>);

pub struct ConstDef {
  pub ident: Ident,
  pub idx: Vec<AstNodeId>, // alternative array index
  pub const_init_val: AstNodeId
}

pub struct VarDecl {
  pub var_defs: Vec<AstNodeId>,
}

pub struct VarDef {
  pub ident: Ident,
  pub idx: Vec<AstNodeId>, // alternative array index
  pub init_val: Option<AstNodeId>
}

pub struct FuncDef {
  /// void or int
  pub has_retval: bool, 

  pub ident: String,
  pub func_f_params: Vec<AstNodeId>,
  pub block: AstNodeId,
}

pub struct Block {
  pub items: Vec<AstNodeId>,
}


pub enum BlockItem {
  Decl(AstNodeId),
  Stmt(AstNodeId),
}

pub enum Stmt {
  Assign(AstNodeId, AstNodeId),
  Exp (Option<AstNodeId>),
  Block(AstNodeId),
  IfElse(AstNodeId, AstNodeId, Option<AstNodeId>),
  While(AstNodeId, AstNodeId),
  Break,
  Continue,
  Return(Option<AstNodeId>),
  Empty, // ;
}

pub enum ConstInitVal {
  Single(AstNodeId),
  Sequence(Vec<AstNodeId>)
}

pub enum InitVal {
  Single(AstNodeId),
  Sequence(Vec<AstNodeId>)
}

pub enum FuncType {
  Void,
  Int
}

pub struct FuncFParam {
  pub ident: Ident,

  /// A formal parameter array will omit the first dim
  pub shape_exclude_first_dimension: Option<Vec<AstNodeId>>,
}

pub struct LVal {
  pub name: Ident, 
  pub idx: Vec<AstNodeId>,
}

pub type Number = i32;

pub struct Exp {
  pub exp_data: ExpData,
  pub const_value: Option<i32>
}

pub enum ExpData {
  LVal(AstNodeId), 
  Number(i32),
  Binary(AstNodeId, BinaryOp, AstNodeId),
  Unary(UnaryOp, AstNodeId),
  Call(Ident, Vec<AstNodeId>),
}

#[derive(Clone, Copy)]
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

#[derive(Clone, Copy)]
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
