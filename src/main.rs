use clap::Parser;
use koopa::back::KoopaGenerator;
use lalrpop_util::lalrpop_mod;
use std::fs::read_to_string;
use std::io::Result;
use sysy_compiler::koopa_gen::ast::AstNodeId;
use sysy_compiler::koopa_gen::gen::KoopaGen;
use sysy_compiler::riscv_gen::gen::RiscvGen;

lalrpop_mod!(sysy);

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Cli {
  #[clap(short)]
  koopa: Option<String>,

  #[clap(short)]
  riscv: Option<String>,

  #[clap(short)]
  perf: Option<String>,

  #[clap(short, long)]
  output: String,
  input: String,
}

fn main() -> Result<()> {
  let args = Cli::parse();

  let input = args.input;
  let output = args.output;

  let input = read_to_string(input)?;

  let ast: AstNodeId = sysy::_CompUnitParser::new().parse(&input).unwrap();
  // stdout().write(ast.tree_to_string(true).as_bytes())?;

  // koopa IR generation
  let koopa_prog = KoopaGen::gen_on_compile_unit(&ast);

  if args.koopa.is_some() {
    // Target Koopa
    assert!(args.riscv.is_none());

    let mut text_gen = KoopaGenerator::new(Vec::new());
    text_gen.generate_on(&koopa_prog)?;
    let text_form_ir = std::str::from_utf8(&text_gen.writer()).unwrap().to_string();

    // print to the output file
    std::fs::write(output, text_form_ir)?;
  } else {
    {
      let mut text_gen = KoopaGenerator::new(Vec::new());
      text_gen.generate_on(&koopa_prog)?;
      let text_form_ir = std::str::from_utf8(&text_gen.writer()).unwrap().to_string();

      // print to the output file
      let _ = std::fs::write("debug/koopa.out", text_form_ir);
    }
    assert!(args.riscv.is_some() || args.perf.is_some());
    // Target Riscv

    let riscv_gen = RiscvGen::new(&koopa_prog);

    // print to the output file
    std::fs::write(output, riscv_gen.gen().dump().join("\n"))?;
  }
  Ok(())
}
