mod pg;

use clap::Parser;
use lalrpop_util::lalrpop_mod;
use std::fs::read_to_string;
use std::io::Result;
use sysy_compiler::ast::AstNodeId;

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
  let _output = args.output;

  let input = read_to_string(input)?;

  let ast: AstNodeId = sysy::_CompUnitParser::new().parse(&input).unwrap();

  // koopa IR generation
  let _prog = koopa::ir::Program::new();

  if args.koopa.is_some() {
    assert!(args.riscv.is_none());

    // compile my ast
  } else {
  }
  Ok(())
}
