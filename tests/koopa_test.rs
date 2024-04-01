use std::io::sink;

use koopa::{back::Generator, ir::Program};
use lalrpop_util::lalrpop_mod;
use sysy_compiler::{koopa_gen::KoopaGen, utils::interpreter::Interpreter};
lalrpop_mod!(sysy);

#[test]
fn all_kinds_of_init_will_not_panic() {
  let progs = String::from(
    r#"
int i32 = 1;
int t[3] = {1};
int i32_arr[3][5] = {{}, {1, 2, 3, 4, 5}, 2};
const int ci32 = 2; 
const int ci32_array[5] = {ci32, ci32, ci32 + ci32 * ci32};
int main() {
    const int c = 1;
    int d[5] = {i32 + i32_arr[0][0] + ci32_array[0]};
    int i32_arr[3][5] = {{}, {c, 2, 3, 4, 5}, d[1]};
    return d[0] + d[1] + d[2] + d[3] + d[4] + d[5] + i32_arr[1][1];
}
  "#,
  );

  let ast = sysy::_CompUnitParser::new().parse(&progs).unwrap();
  println!("{}", ast.tree_to_string(true));
  KoopaGen::gen_on_compile_unit(&ast);
}

#[test]
fn simple_while() {
  let progs = String::from(
    r#"

int main() {
    int i = 0;
    int c = 0;
    while (i < 100) {
        c = c + i;
        i = i + 1;
    }
    return c;
}

  "#,
  );

  let ast = sysy::_CompUnitParser::new().parse(&progs).unwrap();
  let prog = KoopaGen::gen_on_compile_unit(&ast);
  assert_eq!(koopa_run(prog), 4950);
}

#[test]
fn simple_if() {
  let progs = String::from(
    r#"

int main() {
    int i = 1234;
    if (i % 2) {
        // odd number
        return 1;
    } else {
        // even number
        return 0;
    }
}

  "#,
  );

  let ast = sysy::_CompUnitParser::new().parse(&progs).unwrap();
  let prog = KoopaGen::gen_on_compile_unit(&ast);
  assert_eq!(koopa_run(prog), 0);
}

#[test]
fn complex_control_flow() {
  let progs = String::from(
    r#"

int main() {
    int cnt_odd = 0;
    int cnt_even = 0;
    
    int i = 0;
    while (i < 100) {
        if (i % 2) {
            cnt_odd = cnt_odd + 1;
        } else {
            cnt_even = cnt_even + 1;
        }
        i = i + 1;
    }

    return cnt_odd + cnt_even;
}

  "#,
  );

  let ast = sysy::_CompUnitParser::new().parse(&progs).unwrap();
  println!("{}", ast.tree_to_string(true));
  let prog = KoopaGen::gen_on_compile_unit(&ast);
  assert_eq!(koopa_run(prog), 100);
}

/// Run the given koopa program and return the return value
fn koopa_run(prog: Program) -> i32 {
  let interpreter = Interpreter::new(vec![]);
  let retval = Generator::with_visitor(sink(), interpreter)
    .generate_on(&prog)
    .unwrap();
  retval
}
