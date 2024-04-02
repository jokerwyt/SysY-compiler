mod pg;

use clap::Parser;
use koopa::back::KoopaGenerator;
use lalrpop_util::lalrpop_mod;
use std::fs::read_to_string;
use std::io::{stdout, Result, Write};
use sysy_compiler::ast::AstNodeId;
use sysy_compiler::koopa_gen::KoopaGen;

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

  let _ast: AstNodeId = sysy::_CompUnitParser::new().parse(&input).unwrap();
  // stdout().write(_ast.tree_to_string(true).as_bytes())?;

  // koopa IR generation
  let prog = KoopaGen::gen_on_compile_unit(&_ast);

  if args.koopa.is_some() {
    // Target Koopa
    assert!(args.riscv.is_none());

    let mut text_gen = KoopaGenerator::new(Vec::new());
    text_gen.generate_on(&prog)?;
    let text_form_ir = std::str::from_utf8(&text_gen.writer()).unwrap().to_string();

    // print to the output file
    std::fs::write(output, text_form_ir)?;
  } else {
    // Target Riscv
  }
  Ok(())
}
