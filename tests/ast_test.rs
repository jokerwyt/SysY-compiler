use lalrpop_util::lalrpop_mod;
use sysy_compiler::ast::AstNodeId;

lalrpop_mod!(sysy);

#[test]
fn can_generate_ast_hello() {
  for path in vec!["tests/test_prog/hello.y"] {
    let input = std::fs::read_to_string(path).unwrap();
    let _ast: AstNodeId = sysy::_CompUnitParser::new().parse(&input).unwrap();
    // println!("{}", _ast.to_string(false));
  }
}

#[test]
fn can_generate_ast_complex() {
  for path in vec!["tests/test_prog/complex.y"] {
    let input = std::fs::read_to_string(path).unwrap();
    let _ast: AstNodeId = sysy::_CompUnitParser::new().parse(&input).unwrap();
    // println!("{}", _ast.to_string(false));
  }
}
