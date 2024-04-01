//! Symbol tables are associated with an AST node, and indexed by the AST node's AstNodeId.

use koopa::ir::{Function, Type, Value};
use uuid::Uuid;

use crate::ast;
use crate::ast::AstNodeId;
use crate::utils::dfs::TreeId;
use crate::utils::uuid_mapper::UuidOwner;
use crate::utils::Res;
use crate::{define_wrapper, global_mapper};
use core::panic;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

pub struct SymbolTable {
  /// id of the associate AstNode
  pub id: SymTableId,
  pub entries: HashMap<SymIdent, SymTableEntry>,
}

/// Sys-y allows a function and a value to have the same name.
#[derive(Hash, Clone, PartialEq, Eq)]
pub enum SymIdent {
  Func(String),

  /// Including (constant | variable) (single value | arrays).
  /// I.e. all in LVal.
  Value(String),
}

impl Display for SymIdent {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {
      SymIdent::Func(s) => write!(f, "Func: {}", s),
      SymIdent::Value(s) => write!(f, "Value: {}", s),
    }
  }
}

impl SymbolTable {
  pub fn insert_entry(&mut self, entry: SymTableEntry) -> Res {
    if self.entries.contains_key(&entry.symbol) {
      return Err(format!(
        "SymbolTable: symbol {} already exists",
        entry.symbol
      ));
    }
    self.entries.insert(entry.symbol.clone(), entry);
    Ok(())
  }

  pub fn get_entry(&self, symbol: &SymIdent) -> Option<&SymTableEntry> {
    self.entries.get(symbol)
  }

  pub fn get_value_entry(&self, val_symbol: &String) -> Option<&SymTableEntry> {
    return self.get_entry(&SymIdent::Value(val_symbol.clone()));
  }

  pub fn get_func_entry(&self, func_symbol: &String) -> Option<&SymTableEntry> {
    return self.get_entry(&SymIdent::Func(func_symbol.clone()));
  }

  /// Get the constant int inside the symbol table.
  pub fn find_const_int(&self, const_name: &String) -> Option<i32> {
    let entry = self.get_value_entry(&const_name)?;
    return match &entry.kind {
      SymTableEntryData::ConstIntDef(v) => Some(*v),
      _ => None,
    };
  }
}

impl UuidOwner for SymbolTable {
  fn id(&self) -> Uuid {
    (**self.id).clone()
  }
}

#[derive(Clone)]
pub struct SymTableEntry {
  pub symbol: SymIdent,

  /// The ast node that holds the AstData in self.kind field.
  pub kind: SymTableEntryData,

  /// The function that holds the Value in this entry, or None for global const/var
  /// def and func def.
  pub func: Option<Function>,
}

impl SymTableEntry {
  /// Insert the entry into the last level symbol table of the given ast node.
  pub fn into_llt(self, id: &AstNodeId) {
    let table_id = id.last_level_sym_table();
    sym_tables_write(&table_id, |table| table.insert_entry(self)).unwrap();
  }
}

#[derive(Clone)]
pub enum SymTableEntryData {
  FuncDef(Function),

  /// Value type:
  ///   variable: *i32 from Alloc
  VarIntDef(Value),

  /// Value type: Integer
  ConstIntDef(i32),

  /// We refer to local/global and variable/const array in a consistent way.
  /// The differences are how we declare it (GlobalAlloc or Alloc) and initialize it.
  /// Value type: *[[i32, 5], 3] for int[3][5]
  ArrayDef(Value),

  /// It's special because the shape misses its first dimension.
  /// Value type: *[i32, 3] for int[][3]
  FuncParamArrayDef(Value, Type),
}

impl SymTableEntryData {
  pub fn is_array(&self) -> bool {
    match self {
      SymTableEntryData::ArrayDef(_) => true,
      SymTableEntryData::FuncParamArrayDef(_, _) => true,

      SymTableEntryData::FuncDef(_) => false,
      SymTableEntryData::VarIntDef(_) => false,
      SymTableEntryData::ConstIntDef(_) => false,
    }
  }

  pub fn get_array_shape(&self) -> Vec<i32> {
    todo!()
  }
}

global_mapper!(
  SYMBOLS,
  sym_tables_read,
  sym_tables_write,
  sym_tables_register,
  SymbolTable
);

define_wrapper!(SymTableId, AstNodeId);

impl SymTableId {
  /// Get the constant value inside the symbol table.
  pub fn find_const_int(&self, const_name: &String) -> Option<i32> {
    sym_tables_read(self, |table| table.find_const_int(const_name))
  }
}

impl AstNodeId {
  pub fn create_symbol_table(&self) {
    let table = SymbolTable {
      id: SymTableId(self.clone()),
      entries: HashMap::new(),
    };
    SYMBOLS.with_borrow_mut(|sym_tables| {
      sym_tables.register(table);
    })
  }

  pub fn lookup_sym_table(&self, ident: &SymIdent) -> Option<SymTableEntry> {
    let tables = self.all_sym_tables();
    for table in tables {
      let entry = sym_tables_read(&table, |table| {
        let query = table.get_entry(ident);
        if let Some(entry) = query {
          return Some(entry.clone());
        } else {
          return None;
        }
      });
      if entry.is_some() {
        return entry;
      }
    }
    None
  }

  /// Get all tables on the stack.
  /// The last one is the global table, and the first one is the current table
  /// Therefore, the return length is at least one.
  fn all_sym_tables(&self) -> Vec<SymTableId> {
    let mut tables: Vec<SymTableId> = Vec::new();
    let mut cur = Some(self.clone());
    while let Some(node) = cur {
      cur = node.get_parent();
      tables.extend(node.should_own_sym_table().then_some(node.into()));
    }
    assert!(tables.len() > 0, "No global symbol table found");
    tables
  }

  fn last_level_sym_table(&self) -> SymTableId {
    let tables = self.all_sym_tables();
    tables.first().unwrap().clone()
  }

  #[allow(dead_code)]
  fn global_sym_table(&self) -> SymTableId {
    let tables = self.all_sym_tables();
    tables.last().unwrap().clone()
  }

  /// Try to get the constant value in the nodes symbol table stacks.
  pub fn find_const_int(&self, const_name: String) -> Option<i32> {
    let tables = self.all_sym_tables();
    for table in tables {
      // the order is important.
      let try_get = table.find_const_int(&const_name);
      if try_get.is_some() {
        return try_get;
      }
    }
    None
  }
}

impl AstNodeId {
  pub fn should_own_sym_table(&self) -> bool {
    let ast_data = self.get_ast_data();
    match ast_data {
      ast::AstData::CompUnit(_) => true, // the global sym table
      ast::AstData::FuncDef(_) => true,  // stores all formal parameters
      ast::AstData::Block(_) => true,
      _ => false,
    }
  }
}
