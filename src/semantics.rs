// use uuid::Uuid;

// use crate::utils::dfs::{Dfs, TreeId};
// use crate::{ast, ast_is, ast::ast_nodes_submit};
// use crate::ast::AstNodeId;
// use crate::utils::uuid_mapper::UuidOwner;
// use core::panic;
// use crate::global_mapper;
// use std::collections::HashMap;

// pub struct SymbolTable {
//   /// id of the associate AstNode
//   pub id: Uuid, 
//   pub entries: HashMap<String, SymTableEntry>,
// }

// impl SymbolTable {
//   pub fn insert_entry(&mut self, entry: SymTableEntry) -> SemaRes {
//     if self.entries.contains_key(&entry.symbol) {
//       return Err(format!("SymbolTable: symbol {} already exists", entry.symbol));
//     }
//     self.entries.insert(entry.symbol.clone(), entry);
//     Ok(())
//   }
// }


// impl UuidOwner for SymbolTable {
//   fn id(&self) -> Uuid {
//     self.id
//   }
// } 

// pub struct SymTableEntry {
//   pub symbol: String, 
//   pub ast: AstNodeId,
//   pub kind: SymTableEntryKind,
// }

// impl SymTableEntry {

//   /// Insert the entry into the last level symbol table of the given ast node.
//   fn into_llt(self, id: &AstNodeId) -> SemaRes {
//     let table_id = id.last_level_sym_table();
//     sym_tables_submit(&table_id, |table| {
//       table.insert_entry(self)
//     })?
//   }
// }

// pub enum SymTableEntryKind {
//   FuncDef(ast::FuncDef),
//   Var(ast::VarDef),
//   Const(ast::ConstDef),
// }

// impl SymTableEntryKind {
//   pub fn is_array(&self) -> bool {
//     match self {
//       SymTableEntryKind::FuncDef(_) => false,
//       SymTableEntryKind::Var(var_def) => var_def.is_array(),
//       SymTableEntryKind::Const(const_def) => const_def.is_array(),
//     }
//   }

//   pub fn get_array_shape(&self) -> Vec<i32> {
//     todo!()
//   }
// }

// global_mapper!(SYMBOLS, sym_tables_submit, sym_tables_register, SymbolTable);

// pub type SymTableId = Uuid;

// pub trait SymTableOwner { 
//   fn create_symbol_table(&self); 
//   fn sym_table_id(&self) -> Result<SymTableId, String>;
//   fn all_sym_tables(&self) -> Vec<SymTableId>;
//   fn last_level_sym_table(&self) -> SymTableId;
//   fn global_sym_table(&self) -> SymTableId;
// }

// impl SymTableOwner for AstNodeId {
//   fn create_symbol_table(&self) {
//     let table = SymbolTable {
//       id: *self, 
//       entries: HashMap::new(),
//     };
//     SYMBOLS.with_borrow_mut(|sym_tables| {
//       sym_tables.register(table);
//     })
//   }

//   fn sym_table_id(&self) -> Result<SymTableId, String> {
//     sym_tables_submit(self, |table| 
//       table.id
//     )
//   }

//   /// Get all tables on the stack. 
//   /// The first one is the global table, and the last one is the current table
//   /// Therefore, the return length is at least one.
//   fn all_sym_tables(&self) -> Vec<SymTableId> {
//     let my_table = self.sym_table_id();

//     let mut higher = if let Some(parent) = self.get_parent() {
//       parent.all_sym_tables()
//     } else {
//       vec![]
//     };

//     higher.extend(my_table);
//     higher
//   }

//   fn last_level_sym_table(&self) -> SymTableId {
//     let tables = self.all_sym_tables();
//     *tables.last().unwrap()
//   }

//   fn global_sym_table(&self) -> SymTableId {
//     let tables = self.all_sym_tables();
//     *tables.first().unwrap()
//   }
// }

// pub type SemaRes = Result<(), String>;

// pub trait Semantics {
//   fn const_eval(&self) -> SemaRes;
//   fn children_ty_sanify_check(&self) -> SemaRes;
// }

// // impl Semantics for AstNodeId {
// //   /// Analyze the semantics of the AST node.
// //   /// Any symbol generated will be added to the last level symbol table.
// //   fn semantics_analyze(&self) -> SemaRes {
// //     self.children_ty_sanify_check()?;

// //     let ast_data = ast::get_ast_data(*self);
// //     match ast_data {
// //       ast::AstData::CompUnit(comp_unit) => {
// //         self.create_symbol_table(); // This is the global symbol table.
// //         for item in comp_unit.items {
// //           let child_data = ast::get_ast_data(item);
// //           match child_data {
// //               ast::AstData::Decl(_) | ast::AstData::FuncDef(_) => item.semantics_analyze()?, 
// //               _ => panic!("Invalid child in CompUnit"),
// //           }
// //         }
// //       }
// //       ast::AstData::Decl(decl) => {
// //         match decl {
// //           ast::Decl::ConstDecl(sub_decl) => {
// //             sub_decl.semantics_analyze()?;
// //           }
// //           ast::Decl::VarDecl(sub_decl)=> {
// //             sub_decl.semantics_analyze()?;
// //           }
// //         }
// //       }
// //       ast::AstData::ConstDecl(const_decl) => {
// //         for const_def in const_decl.const_defs {
// //           const_def.semantics_analyze()?;
// //         }
// //       }
// //       ast::AstData::BType => (),
// //       ast::AstData::ConstIdxList(const_idx_list) => {
// //         for idx in const_idx_list.const_exps {
// //           idx.semantics_analyze()?;
// //         }
// //       }
// //       ast::AstData::ConstDef(const_def) => {
// //         const_def.idx.semantics_analyze()?;
// //         const_def.const_init_val.semantics_analyze()?;

// //         SymTableEntry {
// //           symbol: const_def.ident.clone(),
// //           ast: *self, 
// //           kind: SymTableEntryKind::Const(const_def.clone())
// //         }.into_llt(&self)?;
// //       }
// //       ast::AstData::ConstInitVal(c_init_val) => {
// //         match c_init_val {
// //           ast::ConstInitVal::Single(exp) => {
// //             exp.semantics_analyze()?;
// //           }
// //           ast::ConstInitVal::Sequence(vals) => {
// //             for val in vals {
// //               val.semantics_analyze()?;
// //             }
// //           }
// //         }
// //       }
// //       ast::AstData::VarDecl(var_decl) => {
// //         for var_def in var_decl.var_defs {
// //           var_def.semantics_analyze()?;
// //         }
// //       }
// //       ast::AstData::VarDef(var_def) => {
// //         var_def.idx.semantics_analyze()?;
// //         if var_def.has_init_val() {
// //           var_def.init_val.unwrap().semantics_analyze()?;
// //         }
// //         SymTableEntry {
// //           symbol: var_def.ident.clone(),
// //           ast: *self, 
// //           kind: SymTableEntryKind::Var(var_def.clone())
// //         }.into_llt(&self)?;
// //       }
// //       ast::AstData::InitVal(init_val) => {
// //         match init_val {
// //           ast::InitVal::Single{exp} => {
// //             exp.semantics_analyze()?;
// //           }
// //           ast::InitVal::Sequence{init_vals} => {
// //             for val in init_vals {
// //               val.semantics_analyze()?;
// //             }
// //           }
// //         }
// //       }, 
// //       ast::AstData::FuncDef(_) => todo!(),
// //       ast::AstData::FuncFParams(_) => todo!(),
// //       ast::AstData::FuncFParam(_) => todo!(),
// //       ast::AstData::Block(_) => todo!(),
// //       ast::AstData::BlockItem(_) => todo!(),
// //       ast::AstData::Stmt(_) => todo!(),
// //       ast::AstData::Exp(_) => todo!(),
// //       ast::AstData::LVal(_) => todo!(),
// //       ast::AstData::PrimaryExp(_) => todo!(),
// //       ast::AstData::UnaryExp(_) => todo!(),
// //       ast::AstData::FuncRParams(_) => todo!(),
// //       ast::AstData::BinaryExp(_) => todo!(),
// //       ast::AstData::ConstExp(_) => todo!(),
// //     }; 
// //     self.const_eval()?;
// //     Ok(())
// //   }

// //   fn const_eval(&self) -> SemaRes {
// //     let ast_data = ast::get_ast_data(*self);
// //     match ast_data {
// //         ast::AstData::CompUnit(_) => todo!(),
// //         ast::AstData::Decl(_) => todo!(),
// //         ast::AstData::ConstDecl(_) => todo!(),
// //         ast::AstData::BType => todo!(),
// //         ast::AstData::ConstIdxList(_) => todo!(),
// //         ast::AstData::ConstDef(_) => todo!(),
// //         ast::AstData::ConstInitVal(_) => todo!(),
// //         ast::AstData::VarDecl(_) => todo!(),
// //         ast::AstData::VarDef(_) => todo!(),
// //         ast::AstData::InitVal(_) => todo!(),
// //         ast::AstData::FuncDef(_) => todo!(),
// //         ast::AstData::FuncFParams(_) => todo!(),
// //         ast::AstData::FuncFParam(_) => todo!(),
// //         ast::AstData::Block(_) => todo!(),
// //         ast::AstData::BlockItem(_) => todo!(),
// //         ast::AstData::Stmt(_) => todo!(),
// //         ast::AstData::Exp(_) => todo!(),
// //         ast::AstData::LVal(_) => todo!(),
// //         ast::AstData::PrimaryExp(_) => todo!(),
// //         ast::AstData::UnaryExp(_) => todo!(),
// //         ast::AstData::FuncRParams(_) => todo!(),
// //         ast::AstData::BinaryExp(_) => todo!(),
// //         ast::AstData::ConstExp(_) => todo!(),
// //     }
// //   }

// //   /// Check if the children of the node have the correct type.
// //   fn children_ty_sanify_check(&self) -> SemaRes {
// //     let ast_data = ast::get_ast_data(*self);
// //     match ast_data {
// //         ast::AstData::CompUnit(_) => todo!(),
// //         ast::AstData::Decl(_) => todo!(),
// //         ast::AstData::ConstDecl(_) => todo!(),
// //         ast::AstData::BType => todo!(),
// //         ast::AstData::ConstIdxList(_) => todo!(),
// //         ast::AstData::ConstDef(_) => todo!(),
// //         ast::AstData::ConstInitVal(_) => todo!(),
// //         ast::AstData::VarDecl(_) => todo!(),
// //         ast::AstData::VarDef(_) => todo!(),
// //         ast::AstData::InitVal(_) => todo!(),
// //         ast::AstData::FuncDef(_) => todo!(),
// //         ast::AstData::FuncFParams(_) => todo!(),
// //         ast::AstData::FuncFParam(_) => todo!(),
// //         ast::AstData::Block(_) => todo!(),
// //         ast::AstData::BlockItem(_) => todo!(),
// //         ast::AstData::Stmt(_) => todo!(),
// //         ast::AstData::Exp(_) => todo!(),
// //         ast::AstData::LVal(_) => todo!(),
// //         ast::AstData::PrimaryExp(_) => todo!(),
// //         ast::AstData::UnaryExp(_) => todo!(),
// //         ast::AstData::FuncRParams(_) => todo!(),
// //         ast::AstData::BinaryExp(_) => todo!(),
// //         ast::AstData::ConstExp(_) => todo!(),
// //     }
// //   }
// // }