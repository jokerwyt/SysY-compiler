// use std::collections::HashMap;

use uuid::Uuid;

use crate::ast;
use crate::ast::AstNodeId;
use crate::utils::{UuidOwner, UuidMapper};
use core::panic;
use std::cell::RefCell;
use crate::global_mapper;
use std::collections::HashMap;

pub struct SymbolTable {
  /// id of the associate AstNode
  pub id: Uuid, 
  pub entries: HashMap<String, SymTableEntry>,
}

impl SymbolTable {
  pub fn insert_entry(&mut self, entry: SymTableEntry) -> SemaRes {
    if self.entries.contains_key(&entry.symbol) {
      return Err(format!("Symbol {} already defined", entry.symbol));
    }
    self.entries.insert(entry.symbol.clone(), entry);
    Ok(())
  }
}


impl UuidOwner for SymbolTable {
  fn id(&self) -> Uuid {
    self.id
  }
} 

pub struct SymTableEntry {
  pub symbol: String, 
  pub ast: AstNodeId,
  pub kind: SymTableEntryKind,
}

pub enum SymTableEntryKind {
  FuncDef(ast::FuncDef),
  VarDef(ast::VarDef),

  /// if const array then no const value.
  ConstDef(ast::ConstDef, Option<i32>)
}

global_mapper!(SYMBOLS, sym_tables_submit, SymbolTable);

pub type SymTableId = Uuid;

pub trait SymTableOwner { 
  fn create_symbol_table(&self); 
  fn sym_table_id(&self) -> Option<SymTableId>;
  fn all_sym_tables(&self) -> Vec<SymTableId>;
}

impl SymTableOwner for AstNodeId {
  fn create_symbol_table(&self) {
    let table = SymbolTable {
      id: *self, 
      entries: HashMap::new(),
    };
    SYMBOLS.with_borrow_mut(|sym_tables| {
      sym_tables.register(table);
    })
  }

  fn sym_table_id(&self) -> Option<SymTableId> {
    sym_tables_submit(*self, |table| 
      Some(table.id)
    )
  }

  /// Get all tables on the stack. 
  /// The first one is the global table, and the last one is the current table
  /// Therefore, the return length is at least one.
  fn all_sym_tables(&self) -> Vec<SymTableId> {
    let my_table = self.sym_table_id();

    let mut higher = if let Some(table) = ast::get_parent(*self) {
      table.all_sym_tables()
    } else {
      vec![]
    };

    higher.extend(my_table);
    higher
  }
}

pub type SemaRes = Result<(), String>;

pub trait Semantics {
  fn semantics_analyze(&self) -> SemaRes;
}

impl Semantics for AstNodeId {
    fn semantics_analyze(&self) -> SemaRes {
      let ast_data = ast::get_ast_data(*self);
      match ast_data {
        ast::AstData::CompUnit(comp_unit) => {
          self.create_symbol_table();
          for decl in comp_unit.0 {
            let child_data = ast::get_ast_data(decl);
            
            // register the decl in the global table
            let sym_entry = match child_data {
                ast::AstData::FuncDef(func_def) => {
                  SymTableEntry {
                    symbol: func_def.ident.clone(),
                    ast: decl,
                    kind: SymTableEntryKind::FuncDef(func_def),
                  }
                },
                _ => panic!("Invalid child in CompUnit"),
            };

            // func_def needs to insert before analyzing down, for possible recursive calling.
            // const_def and var_def should ** NOT ** insert before analyzing down
            // const_def needs to evaluate the value before inserting into symbol table
            
          }
          todo!()
        },
        ast::AstData::FuncDef(_) => todo!(),
        ast::AstData::ConstDecl(_) => todo!(),
        ast::AstData::VarDecl(_) => todo!(),
        ast::AstData::ConstDef(_) => todo!(),
        ast::AstData::VarDef(_) => todo!(),
        ast::AstData::FuncFParam(_) => todo!(),
        ast::AstData::Block(_) => todo!(),
        ast::AstData::BlockItem(_) => todo!(),
        ast::AstData::Stmt(_) => todo!(),
        ast::AstData::Exp(_) => todo!(),
        ast::AstData::InitVal(_) => todo!(),
        ast::AstData::ConstInitVal(_) => todo!(),
        ast::AstData::LVal(_) => todo!(),
      }
    }
}