use crate::utils::RcRef;

use crate::semantics::SymbolTable;

pub trait Ast { }

pub type AstRcRef = RcRef<dyn Ast>;

pub type Ident = String;

pub type CompUnit = Vec<RcRef<CompUnitItem>>;

pub enum CompUnitItem {
  FuncDef(RcRef<FuncDef>),
  Decl(RcRef<Decl>),
}

pub enum Decl {
  Const(RcRef<ConstDecl>),
  Var(RcRef<VarDecl>),
}

pub struct ConstDecl {
  pub const_defs: Vec<RcRef<ConstDef>>,
}

pub struct ConstDef {
  pub ident: Ident,
  pub idx: Vec<RcRef<ExpEval>>, // alternative array index
  pub const_init_val: RcRef<InitVal>
}

pub struct VarDecl {
  pub var_defs: Vec<RcRef<VarDef>>,
}

pub struct VarDef {
  pub ident: Ident,
  pub idx: Vec<RcRef<ExpEval>>, // alternative array index
  pub init_val: Option<RcRef<InitVal>>
}

pub struct FuncDef {
  /// void or int
  pub has_retval: bool, 

  pub ident: String,
  pub func_f_params: FuncFParams,
  pub block: RcRef<Block>,
}

pub type FuncFParams = Vec<RcRef<FuncFParam>>;

pub struct Block {
  pub items: Vec<RcRef<BlockItem>>,
  pub sym_table: Option<RcRef<SymbolTable>>
}

impl Block {
  pub fn new(items: Vec<RcRef<BlockItem>>) -> Self {
    Block {
      items, 
      sym_table: None,
    }
  }
}

pub enum BlockItem {
  Decl(RcRef<Decl>),
  Stmt(RcRef<Stmt>),
}

pub enum Stmt {
  Assign(RcRef<LVal>, RcRef<ExpEval>),
  Exp (Option<RcRef<ExpEval>>),
  Block(RcRef<Block>),
  IfElse(RcRef<ExpEval>, RcRef<Stmt>, Option<RcRef<Stmt>>),
  While(RcRef<ExpEval>, RcRef<Stmt>),
  Break,
  Continue,
  Return(Option<RcRef<ExpEval>>),
  Empty, // ;
}

pub enum InitVal {
  Single(RcRef<ExpEval>),
  Sequence(Vec<RcRef<InitVal>>)
}

pub enum FuncType {
  Void,
  Int
}

pub struct FuncFParam {
  pub ident: Ident,

  /// A formal parameter array will omit the first dim
  pub shape_except_first_dimension: Option<Vec<RcRef<ExpEval>>>,
}

pub struct LVal {
  pub name: Ident, 
  pub idx: Vec<RcRef<ExpEval>>,
}

pub type Number = i32;

pub struct ExpEval {
  pub exp: RcRef<ExpInside>,
  pub const_value: Option<i32>
}

impl ExpEval {
  pub fn new_lval(lval: RcRef<LVal>) -> Self {
    ExpEval {
      exp: RcRef::new(ExpInside::LVal(lval)),
      const_value: None
    }
  }

  pub fn new_number(n: Number) -> Self {
    ExpEval {
      exp: RcRef::new(ExpInside::Number(n)),
      const_value: Some(n)
    }
  }

  pub fn new_binary(exp1: RcRef<ExpEval>, op: BinaryOp, exp2: RcRef<ExpEval>) -> Self {
    let const_value = match (exp1.borrow().const_value, exp2.borrow().const_value) {
      (Some(v1), Some(v2)) => {
        Some(BinaryOp::eval(v1, op, v2))
      },
      _ => None,
    };
    ExpEval {
      exp: RcRef::new(ExpInside::Binary(exp1, op, exp2)),
      const_value,
    }
  }

  pub fn new_unary(op: UnaryOp, exp: RcRef<ExpEval>) -> Self {
    let const_value = match exp.borrow().const_value {
      Some(v) => {
        Some(UnaryOp::eval(op, v))
      },
      None => None,
    };
    ExpEval {
      exp: RcRef::new(ExpInside::Unary(op, exp)),
      const_value,
    }
  }

  pub fn new_call(ident: Ident, exps: Vec<RcRef<ExpEval>>) -> Self {
    ExpEval {
      exp: RcRef::new(ExpInside::Call(ident, exps)),
      const_value: None,
    }
  }
}

pub enum ExpInside {
  LVal(RcRef<LVal>), 
  Number(Number),
  Binary(RcRef<ExpEval>, BinaryOp, RcRef<ExpEval>),
  Unary(UnaryOp, RcRef<ExpEval>),
  Call(Ident, Vec<RcRef<ExpEval>>),
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

// impl Ast for all types

impl Ast for CompUnit {}
impl Ast for CompUnitItem {}
impl Ast for Decl {}
impl Ast for ConstDecl {}
impl Ast for ConstDef {}
impl Ast for VarDecl {}
impl Ast for VarDef {}
impl Ast for FuncDef {}
impl Ast for FuncFParams {}
impl Ast for Block {}
impl Ast for BlockItem {}
impl Ast for Stmt {}
impl Ast for InitVal {}
impl Ast for FuncType {}
impl Ast for FuncFParam {}
impl Ast for LVal {}
impl Ast for ExpEval {}
impl Ast for ExpInside {}
impl Ast for UnaryOp {}
impl Ast for BinaryOp {}
impl Ast for Number {}
