/*
Expression-related elements of AST.
We usually do not translate EBNF directly when processing expressions since such
tree structure can contains information such as priority.
*/

use super::basic::*;



#[derive(Debug)]
pub enum Exp {
  LVal(LVal), 
  Number(Number),
  Binary(Box<Exp>, BinaryOp, Box<Exp>),
  Unary(UnaryOp, Box<Exp>),
  Call(Ident, Vec<Exp>),
}

pub type ConstExp = Exp;

#[derive(Debug)]
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
}

#[derive(Debug)]
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
}
