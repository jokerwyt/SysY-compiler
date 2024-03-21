use std::collections::HashMap;
use uuid::Uuid;

pub struct SymbolTable {
  pub id: Uuid, 

  /// uuid of parent symbol table
  pub parent: Option<Uuid>,

  pub entries: HashMap<String, SymTableEntry>,
}

pub struct SymTableEntry {
  pub ast_id: Uuid
}

