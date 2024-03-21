pub mod ast;
pub mod semantics;
pub mod utils;
mod pg;

use ast::AstData;
use clap::Parser;
use lalrpop_util::lalrpop_mod;
use std::fs::read_to_string;
use std::io::Result;
use std::sync::Arc;

use crate::ast::AstNode;

lalrpop_mod!(sysy);

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Cli {
  #[clap(short, help = "Compile sys-y into koopa. Default into riscv")]
  koopa: Option<String>,

  #[clap(short)]
  riscv: Option<String>,

  #[clap(short, long)]
  output: String,
  input: String,
}

fn main() -> Result<()> {
  let args = Cli::parse();

  let input = args.input;
  let output = args.output;

  let input = read_to_string(input)?;

  let ast: ast::CompUnit = sysy::_CompUnitParser::new().parse(&input).unwrap();
  let ast_root = Arc::new(AstNode::build(AstData::CompUnit(ast)));


  // ast.semantics_analyze();

  if args.koopa.is_some() {
    assert!(args.riscv.is_none());

    // compile my ast 
  } else {
    let mut prog = koopa::ir::Program::new();
    // let main = prog.new_func(FunctionData::with_param_names(
    //   "@main".into(),
    //   vec![],
    //   Type::get_i32(),
    // ));
    
    // // let main_data = prog.func_mut(main);
    // // let bb = main_data.dfg_mut().new_bb().basic_block(Some("%entry".into()));
    // // main_data.layout_mut().bbs_mut().extend(vec![bb]);
    
    // // let ret_val = main_data.dfg_mut().new_value().integer(ast.func_def.block.stmt.num);
    // // let ret_statement = main_data.dfg_mut().new_value().ret(Some(ret_val));
    // // main_data.layout_mut().bb_mut(bb).insts_mut().extend([ret_statement]);
    
    // // open the output file
    // let output_file = std::fs::File::create(output)?;
    // let mut generator = KoopaGenerator::new(output_file);
    // generator.generate_on(&prog)?;
    
  }
  Ok(())
}
