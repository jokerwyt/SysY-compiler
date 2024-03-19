/*
Program-realted elements of AST.
*/

use super::basic::*;
use super::expr::*;

pub type CompUnit = Vec<CompUnitItem>;

#[derive(Debug)]
pub enum CompUnitItem {
  FuncDef(FuncDef),
  Decl(Decl),
}

#[derive(Debug)]
pub enum Decl {
  Const(ConstDecl),
  Var(VarDecl),
}

#[derive(Debug)]
pub struct ConstDecl {
  pub btype: BType,
  pub const_defs: Vec<ConstDef>,
}

#[derive(Debug)]
pub struct ConstDef {
  pub ident: Ident,
  pub idx: Vec<ConstExp>, // alternative array index
  pub const_init_val: ConstInitVal
}


#[derive(Debug)]
pub struct VarDecl {
  pub btype: BType,
  pub var_defs: Vec<VarDef>,
}

#[derive(Debug)]
pub struct VarDef {
  pub ident: Ident,
  pub idx: Vec<ConstExp>, // alternative array index
  pub init_val: Option<InitVal>
}

#[derive(Debug)]
pub struct FuncDef {
  pub func_type: BType,
  pub ident: String,
  pub func_f_params: FuncFParams,
  pub block: Block,
}

pub type FuncFParams = Vec<FuncFParam>;

pub type Block = Vec<BlockItem>;

#[derive(Debug)]
pub enum BlockItem {
  Decl(Decl),
  Stmt(Stmt),
}

#[derive(Debug)]
pub enum Stmt {
  Assign(LVal, Exp),
  Exp (Option<Exp>),
  Block(Block),
  IfElse(Exp, Box<Stmt>, Option<Box<Stmt>>),
  While(Exp, Box<Stmt>),
  Break,
  Continue,
  Return(Option<Exp>),
  Empty, // ;
}
