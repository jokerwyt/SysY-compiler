// use std::collections::HashMap;

// use crate::ast::*;
// use crate::utils::RcRef;
// use std::io::Result;

// pub struct SymbolTable {
//   pub parent: Option<RcRef<SymbolTable>>,
//   pub entries: HashMap<String, SymTableEntry>,
// }

// pub struct SymTableEntry {
//   pub ast: AstRcRef, 
//   pub koopa_id: Option<String>
// }

// pub trait Semantics {
//   fn analyze(&self, ast: AstRcRef, parent: Option<RcRef<SemaNode>>) -> Option<SemaNode>;
// }

// pub struct SemaNode {
//   pub ast: AstRcRef,
//   pub parent: Option<RcRef<SemaNode>>,
//   pub sym_table: Option<RcRef<SymbolTable>>,
//   pub childrens: Vec<RcRef<SemaNode>>,
// }

// // impl Semantics for SemaNode {
// //   fn analyze(&self, ast: AstRcRef, parent: Option<RcRef<SemaNode>>) -> Option<SemaNode> {
//     // let mut ret_node = SemaNode {
//     //   ast: ast.clone(),
//     //   parent,
//     //   sym_table: None,
//     //   childrens: vec![],
//     // };
    
//     // match ast {
//     //     AstRcRef::CompUnit(comp_unit) => {
//     //       // construct global symbol table
//     //       let mut sym_table = RcRef::new(SymbolTable {
//     //         parent: None,
//     //         entries: HashMap::new(),
//     //       });
//     //       ret_node.sym_table = Some(sym_table);

//     //       for item in comp_unit.borrow().iter() {
//     //         match *item.borrow() {
//     //           CompUnitItem::FuncDef(ref func_def) => {
//     //             let func_name = func_def.borrow().ident.clone();
//     //             let sym_table_entry = SymTableEntry {
//     //               ast: AstRcRef::FuncDef(func_def.clone()),
//     //               koopa_id: None,
//     //             };
//     //             ret_node.sym_table.as_ref().unwrap().borrow_mut().entries.insert(func_name, sym_table_entry);
//     //             ret_node.childrens.push(
//     //               SemaNode::analyze(AstRcRef::FuncDef(func_def.clone()), Some(ret_node.clone()), ret_node.sym_table.clone())
//     //             );
//     //           }, 
//     //           CompUnitItem::Decl(ref decl) => {
                
//     //           }
//     //         }
//     //       }
//     //     }, 
//     //     AstRcRef::FuncDef(_) => todo!(),
//     //     AstRcRef::Decl(_) => todo!(),
//     //     AstRcRef::ConstDecl(_) => todo!(),
//     //     AstRcRef::VarDecl(_) => todo!(),
//     //     AstRcRef::ConstDef(_) => todo!(),
//     //     AstRcRef::VarDef(_) => todo!(),
//     //     AstRcRef::FuncFParam(_) => todo!(),
//     //     AstRcRef::Block(_) => todo!(),
//     //     AstRcRef::BlockItem(_) => todo!(),
//     //     AstRcRef::Stmt(_) => todo!(),
//     //     AstRcRef::ExpEval(_) => todo!(),
//     //     AstRcRef::InitVal(_) => todo!(),
//     // }
//     // None
// //   }
// // }