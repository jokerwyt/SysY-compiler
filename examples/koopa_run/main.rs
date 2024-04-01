use std::io::stdout;

fn main() {
  // the only arg is the koopa ir file name
  let args: Vec<String> = std::env::args().collect();
  let koopa_file = &args[1];

  let program = koopa::front::Driver::from_path(koopa_file)
    .unwrap()
    .generate_program()
    .unwrap();

  // open a file "debug/llvm.out", if there is no such file, create one
  let file = std::fs::OpenOptions::new()
    .write(true)
    .create(true)
    .truncate(true)
    .open("debug/llvm.out")
    .unwrap();

  // parse the koopa ir
  let mut llvm_gen = koopa::back::LlvmGenerator::new(file);
  llvm_gen.generate_on(&program).unwrap();

  // llvm-as debug/llvm.out
  // llc debug/llvm.out.bc
  // gcc debug/llvm.out.s -o koopa_to_binary.out
  // ./koopa_to_binary.out

  // run the above commands to generate the binary
  // and run the binary
  let _ = std::process::Command::new("sh")
        .arg("-c")
        .arg("llvm-as debug/llvm.out && llc debug/llvm.out.bc && gcc debug/llvm.out.s -o debug/koopa_to_binary.out && ./debug/koopa_to_binary.out")
        .stdout(std::process::Stdio::inherit())
        .stderr(std::process::Stdio::inherit())
        .output()
        .unwrap();
}
