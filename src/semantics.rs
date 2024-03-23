//! Semantics analysis
//! - Symbol tables
//! Symbol tables are associated with an AST node, and indexed by the AST node's AstNodeId.
//! 
//! - Constant folding

use uuid::Uuid;

use crate::utils::dfs::{DfsVisitor, TreeId};
use crate::{ast, ast_is, ast::ast_nodes_read, ast::ast_nodes_write};
use crate::ast::{AstNodeId, BinaryOp, UnaryOp};
use crate::utils::uuid_mapper::UuidOwner;
use crate::{ast_into, ast_node_into, ast_data_write_as, define_wrapper, global_mapper};
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

pub struct SymbolTable {
  /// id of the associate AstNode
  pub id: SymTableId, 
  pub entries: HashMap<SymIdent, SymTableEntry>,
}

#[derive(Clone, PartialEq, Eq)]
pub enum SymIdent {
  Func(String),

  /// Including (constant | variable) (single value | arrays).
  /// Sys-y allows a function and a value to have the same name.
  Value(String)
}

impl Display for SymIdent {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {
      SymIdent::Func(s) => write!(f, "Func: {}", s),
      SymIdent::Value(s) => write!(f, "Value: {}", s),
    }
  }
}

impl std::hash::Hash for SymIdent {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    match self {
      SymIdent::Func(s) => {
        "Func".hash(state);
        s.hash(state);
      }
      SymIdent::Value(s) => {
        "Value".hash(state);
        s.hash(state);
      }
    }
  }
}

// impl Eq for SymIdent {}

impl SymbolTable {
  pub fn insert_entry(&mut self, entry: SymTableEntry) -> SemaRes {
    if self.entries.contains_key(&entry.symbol) {
      return Err(format!("SymbolTable: symbol {} already exists", entry.symbol));
    }
    self.entries.insert(entry.symbol.clone(), entry);
    Ok(())
  }
}


impl UuidOwner for SymbolTable {
  fn id(&self) -> Uuid {
    self.id.inner().inner().clone()
  }
} 

pub struct SymTableEntry {
  pub symbol: SymIdent,
  pub ast: AstNodeId,
  pub kind: SymTableEntryKind,
}

impl SymTableEntry {
  /// Insert the entry into the last level symbol table of the given ast node.
  fn into_llt(self, id: &AstNodeId) -> SemaRes {
    let table_id = id.last_level_sym_table();
    sym_tables_write(&table_id.inner().inner(), |table| {
      table.insert_entry(self)
    })?
  }
}

pub enum SymTableEntryKind {
  FuncDef(ast::FuncDef),
  FuncParam(ast::FuncFParam),
  Var(ast::VarDef),
  Const(ast::ConstDef),
}

impl SymTableEntryKind {
  pub fn is_array(&self) -> bool {
    match self {
      SymTableEntryKind::FuncDef(_) => false,
      SymTableEntryKind::Var(var_def) => var_def.is_array(),
      SymTableEntryKind::Const(const_def) => const_def.is_array(),
      SymTableEntryKind::FuncParam(fparam) => fparam.is_array()
    }
  }

  pub fn get_array_shape(&self) -> Vec<i32> {
    todo!()
  }
}

global_mapper!(SYMBOLS, sym_tables_read, sym_tables_write, sym_tables_register, SymbolTable);

define_wrapper!(SymTableId, AstNodeId);

pub trait SymTableOwner { 
  fn create_symbol_table(&self); 
  fn get_sym_table(&self) -> Option<SymTableId>;
  fn all_sym_tables(&self) -> Vec<SymTableId>;
  fn last_level_sym_table(&self) -> SymTableId;
  fn global_sym_table(&self) -> SymTableId;
}

impl SymTableOwner for AstNodeId {
  fn create_symbol_table(&self) {
    let table = SymbolTable {
      id: SymTableId(self.clone()),
      entries: HashMap::new(),
    };
    SYMBOLS.with_borrow_mut(|sym_tables| {
      sym_tables.register(table);
    })
  }

  
  fn get_sym_table(&self) -> Option<SymTableId> {
    sym_tables_read(self.inner(), |sym_tables| {
      sym_tables.id.clone()
    }).ok()
  }

  /// Get all tables on the stack. 
  /// The first one is the global table, and the last one is the current table
  /// Therefore, the return length is at least one.
  fn all_sym_tables(&self) -> Vec<SymTableId> {
    let mut tables = Vec::new();
    let mut cur = Some(self.clone());
    while let Some(node) = cur {
      tables.extend(node.get_sym_table());
      cur = node.get_parent();
    } 
    tables.reverse();
    tables
  }

  fn last_level_sym_table(&self) -> SymTableId {
    let tables = self.all_sym_tables();
    tables.last().unwrap().clone()
  }

  fn global_sym_table(&self) -> SymTableId {
    let tables = self.all_sym_tables();
    tables.first().unwrap().clone()
  }
}

pub type SemaRes = Result<(), String>;

pub trait Semantics {
  fn const_eval(&self) -> SemaRes;
  fn children_ty_sanify_check(&self) -> SemaRes;
  fn semantics_analyze(&self) -> SemaRes;
  fn sema_preprocess(&self) -> SemaRes;
  fn sema_postprocess(&self) -> SemaRes;
}

impl AstNodeId {
  fn should_own_sym_table(&self) -> bool {
    let ast_data = self.get_ast_data();
    match ast_data {
        ast::AstData::CompUnit(_) => true, // the global sym table
        ast::AstData::FuncDef(_) => true, // stores all formal parameters
        ast::AstData::Block(_) => true, 
        _ => false
    }
  }
}

impl Semantics for AstNodeId {
  fn semantics_analyze(&self) -> SemaRes {
    assert!(ast_is!(self, CompUnit));
    let visitor = DfsVisitor::<_, _, AstNodeId>::new(
      |node| {
        node.sema_preprocess()
      },
      |node| {
        node.sema_postprocess()
      }
    );
    visitor.dfs(self)?;
    Ok(())
  }

  /// Eval all compile-time constant single value.
  /// Called in [Semantics::ty_irrelevant_sema_postprocess]
  fn const_eval(&self) -> SemaRes {
    // implement logics:
    // 1. check if the current node has a constant slot by multiple match
    // 2. if yes, get value_gathered from the children
    // 3. submit a write to cur_data

    let ast_data = self.get_ast_data();
    match ast_data {
      ast::AstData::CompUnit(_) => { }
      ast::AstData::Decl(_) => { }
      ast::AstData::ConstDecl(_) => { }
      ast::AstData::BType => { }
      ast::AstData::ConstDef(_) => { }
      ast::AstData::ConstInitVal(c_init_val) => {
        match c_init_val {
          ast::ConstInitVal::Single(sub_const_exp, _) => {
            let value_gathered = sub_const_exp.const_single_value();
            ast_data_write_as!(self, ConstInitVal, |cur_data| {
              *cur_data.const_mut().unwrap() = value_gathered;
            });
          },
          ast::ConstInitVal::Sequence(_) => ()
        };
      }
      ast::AstData::VarDecl(_) => { }
      ast::AstData::VarDef(_) => { }
      ast::AstData::InitVal(init_val) => {
        match init_val {
            ast::InitVal::Single(sub_exp, _) => {
              let value_gathered = sub_exp.const_single_value();
              ast_data_write_as!(self, InitVal, |cur_data| {
                *cur_data.const_mut().unwrap() = value_gathered;
              });
            }
            ast::InitVal::Sequence(_) => ()
        }
      }
      ast::AstData::FuncDef(_) => { }
      ast::AstData::FuncFParams(_) => { }
      ast::AstData::FuncFParam(_) => { }
      ast::AstData::Block(_) => { }
      ast::AstData::BlockItem(_) => { }
      ast::AstData::Stmt(_) => { }
      ast::AstData::Exp(exp) => {
        let value_gathered = exp.l_or_exp.const_single_value();
        ast_data_write_as!(self, Exp, |data| {
          data.const_value = value_gathered
        });
      }
      ast::AstData::LVal(_) => { }
      ast::AstData::PrimaryExp(exp) => {
        match exp {
          ast::PrimaryExp::Exp(sub_exp, _) => {
            let value_gathered = sub_exp.const_single_value();
            ast_data_write_as!(self, PrimaryExp, |data| {
              *data.const_mut().unwrap() = value_gathered;
            });
          }
          ast::PrimaryExp::LVal(_) => { }
          ast::PrimaryExp::Number(_) => { }
        }
      }
      ast::AstData::UnaryExp(uexp) => {
        match uexp {
          ast::UnaryExp::PrimaryExp { pexp, .. } => {
            let value_gathered = pexp.const_single_value();
            ast_data_write_as!(self, UnaryExp, |data| {
              *data.const_mut().unwrap() = value_gathered;
            });
          }
          ast::UnaryExp::Call { .. } => { }
          ast::UnaryExp::Unary { exp: sub_exp, op, .. } => {
            let value = if let Some(v) = sub_exp.const_single_value() {
              Some(UnaryOp::eval(op, v))
            } else {
              None
            };

            ast_data_write_as!(self, UnaryExp, |data| {
              *data.const_mut().unwrap() = value;
            });
          }
        }
      }
      ast::AstData::FuncRParams(_) => { }
      ast::AstData::BinaryExp(bexp) => {
        match bexp {
          // For binary exp, there must be a const slot.
          // But we still need to match since there are two kinds of method to 
          // evaluate: (unary | binary)
          ast::BinaryExp::Unary { exp: sub_exp, .. } => {
            let value = sub_exp.const_single_value();
            ast_data_write_as!(self, BinaryExp, |data| {
              *data.const_mut() = value;
            });
          }
          ast::BinaryExp::Binary { lhs, op, rhs, .. } => {
            let lhs_value = lhs.const_single_value();
            let rhs_value = rhs.const_single_value();
            let value = if let (Some(lhs), Some(rhs)) = (lhs_value, rhs_value) {
              Some(BinaryOp::eval(lhs, op, rhs))
            } else {
              None
            };

            ast_data_write_as!(self, BinaryExp, |data| {
              *data.const_mut() = value;
            });
          
          }
        }
      }
      ast::AstData::ConstExp(const_exp) => {
        let value = const_exp.0.const_single_value();
        ast_data_write_as!(self, ConstExp, |data| {
          data.1 = value;
        });
      }
    }
    Ok(())
  }

  /// Check if the children of the node have the correct type.
  fn children_ty_sanify_check(&self) -> SemaRes {
    return Ok(()); // TODO: future work.


    let ast_data = self.get_ast_data();
    match ast_data {
      ast::AstData::CompUnit(_) => todo!(),
      ast::AstData::Decl(_) => todo!(),
      ast::AstData::ConstDecl(_) => todo!(),
      ast::AstData::BType => todo!(),
      ast::AstData::ConstDef(_) => todo!(),
      ast::AstData::ConstInitVal(_) => todo!(),
      ast::AstData::VarDecl(_) => todo!(),
      ast::AstData::VarDef(_) => todo!(),
      ast::AstData::InitVal(_) => todo!(),
      ast::AstData::FuncDef(_) => todo!(),
      ast::AstData::FuncFParams(_) => todo!(),
      ast::AstData::FuncFParam(_) => todo!(),
      ast::AstData::Block(_) => todo!(),
      ast::AstData::BlockItem(_) => todo!(),
      ast::AstData::Stmt(_) => todo!(),
      ast::AstData::Exp(_) => todo!(),
      ast::AstData::LVal(_) => todo!(),
      ast::AstData::PrimaryExp(_) => todo!(),
      ast::AstData::UnaryExp(_) => todo!(),
      ast::AstData::FuncRParams(_) => todo!(),
      ast::AstData::BinaryExp(_) => todo!(),
      ast::AstData::ConstExp(_) => todo!(),
    }
  }
  
  /// Preprocess the node before the children are processed.
  /// Specific to the node type.\
  /// Things we handle here: 
  /// - symbol table creation
  /// - symbol table entry insertion for FuncDef
  fn sema_preprocess(&self) -> SemaRes {

    self.children_ty_sanify_check()?;
    if self.should_own_sym_table() {
      self.create_symbol_table();
    }

    let ast_data = self.get_ast_data();
    match ast_data {
      ast::AstData::CompUnit(_) => { }, 
      ast::AstData::Decl(_) => { }, 
      ast::AstData::ConstDecl(_) => { }, 
      ast::AstData::BType => { }, 
      ast::AstData::ConstDef(_) => { }, 
      ast::AstData::ConstInitVal(_) => { }, 
      ast::AstData::VarDecl(_) => { }, 
      ast::AstData::VarDef(_) => { },
      ast::AstData::InitVal(_) => { }, 
      ast::AstData::FuncDef(func_def) => {
        // For recursive calls, we must add the function to the symbol 
        // table before we resolve the function body.
        let entry = SymTableEntry {
          symbol: SymIdent::Func(func_def.ident.clone()),
          ast: self.clone(),
          kind: SymTableEntryKind::FuncDef(func_def),
        };

        // FuncDef owns a symbol table. Skip it.
        entry.into_llt(&self.get_parent().unwrap())?;
      }
      ast::AstData::FuncFParams(_) => { }
      ast::AstData::FuncFParam(f_param) => {
        let entry = SymTableEntry {
          symbol: match f_param {
            ast::FuncFParam::Single {ref ident , ..} 
            | ast::FuncFParam::Array {ref ident, ..} 
              => SymIdent::Value(ident.clone())
          }, 
          ast: self.clone(),
          kind: SymTableEntryKind::FuncParam(f_param),
        };

        // This will be added into FuncDef's symbol table.
        entry.into_llt(self)?;
      }
      ast::AstData::Block(_) => { }
      ast::AstData::BlockItem(_) => { }
      ast::AstData::Stmt(_) => { }
      ast::AstData::Exp(_) => { }
      ast::AstData::LVal(_) => { }
      ast::AstData::PrimaryExp(_) => { }
      ast::AstData::UnaryExp(_) => { }
      ast::AstData::FuncRParams(_) => { }
      ast::AstData::BinaryExp(_) => { }
      ast::AstData::ConstExp(_) => { }
    }
    Ok(())
  }

  /// sema_Postprocess the node before the children are processed.
  /// Specific to the node type.
  /// Things we handle here:
  /// - constant folding
  /// - symbol table entry insertion for ConstDef and VarDef
  fn sema_postprocess(&self) -> SemaRes {
    self.const_eval()?;

    let ast_data = self.get_ast_data();
    match ast_data {
      ast::AstData::CompUnit(_) => { }
      ast::AstData::Decl(_) => { }
      ast::AstData::ConstDecl(_) => { }
      ast::AstData::BType => { }
      ast::AstData::ConstDef(const_def) => {
        // Add the const to the symbol table
        let entry = SymTableEntry {
          symbol: SymIdent::Value(const_def.ident.clone()),
          ast: self.clone(),
          kind: SymTableEntryKind::Const(const_def),
        };
        entry.into_llt(self)?;
      }
      ast::AstData::ConstInitVal(_) => { }
      ast::AstData::VarDecl(_) => { }
      ast::AstData::VarDef(var_def) => {
        let entry = SymTableEntry {
          symbol: SymIdent::Value(var_def.ident.clone()),
          ast: self.clone(),
          kind: SymTableEntryKind::Var(var_def),
        };
        entry.into_llt(self)?;
      }
      ast::AstData::InitVal(_) => { }
      ast::AstData::FuncDef(_) => { }
      ast::AstData::FuncFParams(_) => { }
      ast::AstData::FuncFParam(_) => { }
      ast::AstData::Block(_) => { }
      ast::AstData::BlockItem(_) => { }
      ast::AstData::Stmt(_) => { }
      ast::AstData::Exp(_) => { }
      ast::AstData::LVal(_) => { }
      ast::AstData::PrimaryExp(_) => { }
      ast::AstData::UnaryExp(_) => { }
      ast::AstData::FuncRParams(_) => { }
      ast::AstData::BinaryExp(_) => { }
      ast::AstData::ConstExp(_) => { }
    }
    Ok(())
  }
  
}