use lalrpop_util::lalrpop_mod;
use sysy_compiler::koopa_gen::ast;
use sysy_compiler::koopa_gen::ast::ast_nodes_read;
use sysy_compiler::koopa_gen::ast::AstData;
use sysy_compiler::koopa_gen::ast::AstNodeId;
use sysy_compiler::{ast_data_read_as, ast_is, koopa_gen::gen::KoopaGen};
lalrpop_mod!(sysy);

/// Get the return value of the main function based on the whole symbol table.
/// The symbol table includes those defined later. So just for test.
///
fn get_return_const(ast: &AstNodeId) -> Option<i32> {
  let mut ret_val = None;

  ast_data_read_as!(ast, CompUnit, |comp_unit| {
    for item in &comp_unit.items {
      if ast_is!(item, FuncDef) {
        ast_data_read_as!(item, FuncDef, |func_def| {
          if func_def.ident == "main" {
            ast_data_read_as!(&func_def.block, Block, |block| {
              for item in &block.items {
                ast_data_read_as!(item, BlockItem, |block_item| {
                  if let ast::BlockItem::Stmt(stmt) = block_item {
                    ast_data_read_as!(stmt, Stmt, |return_stmt| {
                      match return_stmt {
                        ast::Stmt::Return(ret) => match ret {
                          Some(exp) => {
                            let val = KoopaGen::eval_const_int(&exp);
                            ret_val = Some(val);
                          }
                          None => panic!("Return statement should have no return expression"),
                        },
                        _ => (),
                      }
                    })
                  }
                })
              }
            })
          }
        })
      }
    }
  });
  return ret_val;
}

#[test]
fn can_fold_const_easy() {
  let progs = String::from(
    r#"
int main() {
  return (1 + 2) * 3 / 9 + 1000 % (123 + 0x00);
}
  "#,
  );

  let ast = sysy::_CompUnitParser::new().parse(&progs).unwrap();
  KoopaGen::gen_on_compile_unit(&ast);

  assert_eq!(
    get_return_const(&ast).unwrap(),
    (1 + 2) * 3 / 9 + 1000 % (123 + 0x00)
  );
}

#[test]
#[should_panic]
fn can_not_fold_variable() {
  let progs = String::from(
    r#"
int main() {
  int a;
  return 1 + a;
}
  "#,
  );

  let ast = sysy::_CompUnitParser::new().parse(&progs).unwrap();
  KoopaGen::gen_on_compile_unit(&ast);

  // it will panic.
  get_return_const(&ast);
}

#[test]
fn can_fold_const_hard() {
  let progs = String::from(
    r#"
const int b = 100;
int main() {
  const int c = 10, a = 100 + (+b) + c; // 210
  return a + b + c;
}
  "#,
  );

  let ast = sysy::_CompUnitParser::new().parse(&progs).unwrap();
  println!("{}", ast.tree_to_string(true));
  KoopaGen::gen_on_compile_unit(&ast);

  assert_eq!(get_return_const(&ast).unwrap(), 210 + 100 + 10);
}
