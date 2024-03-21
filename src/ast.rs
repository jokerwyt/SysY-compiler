use uuid::Uuid;

pub struct AstNode {
  pub id: Uuid, 
  pub ast: AstData,
  pub parent: Option<Uuid>,
}

impl AstNode {
  // pub fn build(ast: AstData) -> Self {
  //   AstNode {
  //     ast,
  //     parent: None,
  //   }
  // }
}

pub enum AstData {
  CompUnit(CompUnit),
  FuncDef(FuncDef),
  Decl(Decl),
  ConstDecl(ConstDecl),
  VarDecl(VarDecl),
  ConstDef(ConstDef),
  VarDef(VarDef),
  FuncFParam(FuncFParam),
  Block(Block),
  BlockItem(BlockItem),
  Stmt(Stmt),
  ExpEval(ExpEval),
  InitVal(InitVal),
}

pub type Ident = String;

pub type CompUnit = Vec<CompUnitItem>;

pub enum CompUnitItem {
  FuncDef(FuncDef),
  Decl(Decl),
}

pub enum Decl {
  Const(ConstDecl),
  Var(VarDecl),
}

pub struct ConstDecl {
  pub const_defs: Vec<ConstDef>,
}

pub struct ConstDef {
  pub ident: Ident,
  pub idx: Vec<ExpEval>, // alternative array index
  pub const_init_val: InitVal
}

pub struct VarDecl {
  pub var_defs: Vec<VarDef>,
}

pub struct VarDef {
  pub ident: Ident,
  pub idx: Vec<ExpEval>, // alternative array index
  pub init_val: Option<InitVal>
}

pub struct FuncDef {
  /// void or int
  pub has_retval: bool, 

  pub ident: String,
  pub func_f_params: FuncFParams,
  pub block: Block,
}

pub type FuncFParams = Vec<FuncFParam>;

pub struct Block {
  pub items: Vec<BlockItem>,
}

impl Block {
  pub fn new(items: Vec<BlockItem>) -> Self {
    Block {
      items, 
    }
  }
}

pub enum BlockItem {
  Decl(Decl),
  Stmt(Stmt),
}

pub enum Stmt {
  Assign(LVal, ExpEval),
  Exp (Option<ExpEval>),
  Block(Block),
  IfElse(ExpEval, Box<Stmt>, Option<Box<Stmt>>),
  While(ExpEval, Box<Stmt>),
  Break,
  Continue,
  Return(Option<ExpEval>),
  Empty, // ;
}

pub enum InitVal {
  Single(ExpEval),
  Sequence(Vec<InitVal>)
}

pub enum FuncType {
  Void,
  Int
}

pub struct FuncFParam {
  pub ident: Ident,

  /// A formal parameter array will omit the first dim
  pub shape_exclude_first_dimension: Option<Vec<ExpEval>>,
}

pub struct LVal {
  pub name: Ident, 
  pub idx: Vec<ExpEval>,
}

pub type Number = i32;

pub struct ExpEval {
  pub exp: ExpInside,
  pub const_value: Option<i32>
}

impl ExpEval {
  pub fn new_lval(lval: LVal) -> Self {
    ExpEval {
      exp: ExpInside::LVal(lval),
      const_value: None
    }
  }

  pub fn new_number(n: Number) -> Self {
    ExpEval {
      exp: ExpInside::Number(n),
      const_value: Some(n)
    }
  }

  pub fn new_binary(exp1: ExpEval, op: BinaryOp, exp2: ExpEval) -> Self {
    let const_value = match (exp1.const_value, exp2.const_value) {
      (Some(v1), Some(v2)) => {
        Some(BinaryOp::eval(v1, op, v2))
      },
      _ => None,
    };
    ExpEval {
      exp: ExpInside::Binary(Box::new(exp1), op, Box::new(exp2)),
      const_value,
    }
  }

  pub fn new_unary(op: UnaryOp, exp: ExpEval) -> Self {
    let const_value = match exp.const_value {
      Some(v) => {
        Some(UnaryOp::eval(op, v))
      },
      None => None,
    };
    ExpEval {
      exp: ExpInside::Unary(op, Box::new(exp)),
      const_value,
    }
  }

  pub fn new_call(ident: Ident, exps: Vec<ExpEval>) -> Self {
    ExpEval {
      exp: ExpInside::Call(ident, exps),
      const_value: None,
    }
  }
}

pub enum ExpInside {
  LVal(LVal), 
  Number(Number),
  Binary(Box<ExpEval>, BinaryOp, Box<ExpEval>),
  Unary(UnaryOp, Box<ExpEval>),
  Call(Ident, Vec<ExpEval>),
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
