use uuid::Uuid;

pub type AstCompUnit = Box<AstNode>;
pub type AstCompUnitItem = Box<AstNode>;
pub type AstFuncDef = Box<AstNode>;
pub type AstDecl = Box<AstNode>;
pub type AstConstDecl = Box<AstNode>;
pub type AstVarDecl = Box<AstNode>;
pub type AstConstDef = Box<AstNode>;
pub type AstVarDef = Box<AstNode>;
pub type AstFuncFParam = Box<AstNode>;
pub type AstBlock = Box<AstNode>;
pub type AstBlockItem = Box<AstNode>;
pub type AstStmt = Box<AstNode>;
pub type AstExp = Box<AstNode>;
pub type AstInitVal = Box<AstNode>;
pub type AstLVal = Box<AstNode>;
pub type AstConstInitVal = Box<AstNode>;

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

pub struct AstNode {
  pub id: Uuid, 
  pub ast: AstData,
  pub parent: Option<Uuid>,
}

impl AstNode {
  pub fn new_comp_unit(comp_unit: Vec<AstNode>) -> AstNode {
    AstNode {
      id: Uuid::new_v4(),
      ast: AstData::CompUnit(comp_unit),
      parent: None,
    }
  }
  pub fn new_decl_const_decl(const_decl: AstNode) -> AstNode {
    AstNode {
      id: Uuid::new_v4(),
      ast: AstData::Decl(Decl::Const(const_decl)),
      parent: None,
    }
  }

  pub fn new_comp_unit_item_func_def(func_def: AstNode) -> AstNode {
    AstNode {
      id: Uuid::new_v4(),
      ast: AstData::FuncDef(func_def),
      parent: None,
    }
  }
}

pub enum AstData {
  CompUnit(CompUnit),
  FuncDef(FuncDef),
  ConstDecl(ConstDecl),
  VarDecl(VarDecl),
  ConstDef(ConstDef), 
  VarDef(VarDef), 
  FuncFParams(FuncFParams),
  Block(Block),
  BlockItem(BlockItem),
  Stmt(Stmt),
  Exp(Exp),
  InitVal(InitVal),
  ConstInitVal(ConstInitVal),
}

pub type Ident = String;

pub type CompUnit = Vec<AstCompUnitItem>;

pub enum CompUnitItem {
  FuncDef(AstFuncDef),
  Decl(AstDecl),
}

pub enum Decl {
  Const(AstConstDecl),
  Var(AstVarDecl),
} 

pub struct ConstDecl {
  pub const_defs: Vec<AstConstDef>,
}

pub struct ConstDef {
  pub ident: Ident,
  pub idx: Vec<AstExp>, // alternative array index
  pub const_init_val: AstInitVal
}

pub struct VarDecl {
  pub var_defs: Vec<AstVarDef>,
}

pub struct VarDef {
  pub ident: Ident,
  pub idx: Vec<AstExp>, // alternative array index
  pub init_val: Option<AstInitVal>
}

pub struct FuncDef {
  /// void or int
  pub has_retval: bool, 

  pub ident: String,
  pub func_f_params: Vec<AstFuncFParam>,
  pub block: AstBlock,
}

pub struct Block {
  pub items: Vec<AstBlockItem>,
}


pub enum BlockItem {
  Decl(AstDecl),
  Stmt(AstStmt),
}

pub enum Stmt {
  Assign(AstLVal, AstExp),
  Exp (Option<AstExp>),
  Block(AstBlock),
  IfElse(AstExp, AstStmt, Option<AstStmt>),
  While(AstExp, AstStmt),
  Break,
  Continue,
  Return(Option<AstExp>),
  Empty, // ;
}

pub enum ConstInitVal {
  Single(AstExp),
  Sequence(Vec<AstInitVal>)
}

pub enum InitVal {
  Single(AstExp),
  Sequence(Vec<AstInitVal>)
}

pub enum FuncType {
  Void,
  Int
}

pub struct FuncFParam {
  pub ident: Ident,

  /// A formal parameter array will omit the first dim
  pub shape_exclude_first_dimension: Option<Vec<AstExp>>,
}

pub struct LVal {
  pub name: Ident, 
  pub idx: Vec<AstExp>,
}

pub type Number = i32;

pub struct Exp {
  pub exp_data: ExpData,
  pub const_value: Option<i32>
}

pub enum ExpData {
  LVal(AstLVal), 
  Number(i32),
  Binary(AstExp, BinaryOp, AstExp),
  Unary(UnaryOp, AstExp),
  Call(Ident, Vec<AstExp>),
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
