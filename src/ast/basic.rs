//! misc elements of AST

use super::expr::*;

pub type Ident = String;

#[derive(Debug)]
pub enum BType {
  Void = 0,
  Int = 1,
}

#[derive(Debug)]
pub enum ConstInitVal {
  Single(ConstExp),
  Sequence(Vec<ConstInitVal>)
}

#[derive(Debug)]
pub enum InitVal {
  Single(Exp),
  Sequence(Vec<InitVal>)
}

#[derive(Debug)]
pub enum FuncType {
  Void,
  BType(BType),
}

#[derive(Debug)]
pub struct FuncFParam {
  pub btype: BType,
  pub ident: Ident,
  pub shape_except_first_dimension: Option<Vec<ConstExp>>,
}

#[derive(Debug)]
pub struct LVal {
  pub name: Ident, 
  pub idx: Vec<Exp>,
}
pub type Number = i32;
