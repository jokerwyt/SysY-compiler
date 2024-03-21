// use std::collections::HashMap;

use uuid::Uuid;

use crate::ast::*;
use crate::utils::{UuidOwner, UuidMapper};
use std::cell::RefCell;
use crate::global_mapper;
use std::collections::HashMap;

pub struct SymbolTable {
  pub id: Uuid, 
  pub entries: HashMap<String, SymTableEntry>,
}

impl UuidOwner for SymbolTable {
  fn id(&self) -> Uuid {
    self.id
  }
} 

pub struct SymTableEntry {
  pub ast: AstNodeId,
  pub kind: SymTableEntryKind,
}

pub enum SymTableEntryKind {
  FuncDef,
  ValueDef,
}

global_mapper!(SYMBOLS, SymbolTable);

pub type SymTableId = Uuid;

pub trait SymTableOwner { 
  fn sym_table_id(&self) -> Option<SymTableId>;
  fn all_sym_tables(&self) -> Vec<SymTableId>;
}

impl SymTableOwner for AstNodeId {
  fn sym_table_id(&self) -> Option<SymTableId> {
    submit(*self, |table| 
      Some(table.id)
    )
  }

  /// Get all tables on the stack. 
  /// The first one is the global table, and the last one is the current table
  /// Therefore, the return length is at least one.
  fn all_sym_tables(&self) -> Vec<SymTableId> {
    let my_table = self.sym_table_id();

    let mut higher = if let Some(table) = get_parent(*self) {
      table.all_sym_tables()
    } else {
      vec![]
    };

    higher.extend(my_table);
    higher
  }
}

pub trait Analyzable {
  fn semantics_analyze(&self);
}

