pub mod ast;

use ::koopa::ir::builder::ValueBuilder;
use lalrpop_util::lalrpop_mod;
use std::env::args;
use std::fs::read_to_string;
use std::io::Result;

use ::koopa::ir::*;
use ::koopa::back::*;
use:: koopa::ir::builder::BasicBlockBuilder;
use ::koopa::ir::builder::LocalInstBuilder;

// 引用 lalrpop 生成的解析器
// 因为我们刚刚创建了 sysy.lalrpop, 所以模块名是 sysy
lalrpop_mod!(sysy);

fn main() -> Result<()> {
  // 解析命令行参数
  let mut args = args();
  args.next();
  let mode = args.next().unwrap();
  assert_eq!(mode, "-koopa");
  let input = args.next().unwrap();
  args.next();
  let output = args.next().unwrap();

  // 读取输入文件
  let input = read_to_string(input)?;

  // 调用 lalrpop 生成的 parser 解析输入文件
  let ast: ast::CompUnit = sysy::CompUnitParser::new().parse(&input).unwrap();

  // 输出解析得到的 AST
  println!("{:#?}", ast);

  let mut prog = Program::new();
  let main = prog.new_func(FunctionData::with_param_names(
    "@main".into(),
    vec![],
    Type::get_i32(),
  ));

  let main_data = prog.func_mut(main);
  let bb = main_data.dfg_mut().new_bb().basic_block(Some("%entry".into()));
  main_data.layout_mut().bbs_mut().extend(vec![bb]);

  let ret_val = main_data.dfg_mut().new_value().integer(ast.func_def.block.stmt.num);
  let ret = main_data.dfg_mut().new_value().ret(Some(ret_val));
  main_data.layout_mut().bb_mut(bb).insts_mut().extend([ret]);

  // open the output file
  let output_file = std::fs::File::create(output)?;
  let mut generator = KoopaGenerator::new(output_file);
  generator.generate_on(&prog)?;
  
  Ok(())
}
