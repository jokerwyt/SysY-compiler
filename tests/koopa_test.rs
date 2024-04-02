use std::io::sink;

use koopa::{back::Generator, ir::Program};
use lalrpop_util::lalrpop_mod;
use sysy_compiler::{koopa_gen::KoopaGen, utils::interpreter::Interpreter};
lalrpop_mod!(sysy);

#[test]
fn complex_init() {
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
    return d[0] + d[1] + d[2] + d[3] + d[4] + i32_arr[1][1];
}
  "#,
  );

  let ast = sysy::_CompUnitParser::new().parse(&progs).unwrap();
  let prog = KoopaGen::gen_on_compile_unit(&ast);
  assert_eq!(koopa_run(prog), 5);
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
        if (i == 50) {
            break;
        } else {
            continue;
        }
    }

    int a = 0, b = 0, c = 0;
    i = 0;
    while (1) {
        i = i + 1;
        if (i == 100)
            break;
        if (i % 2) {
            if (i % 5) {
                a = a + 1;
            } else {
                b = b + 1;
            }
        } else {
            c = c + 1;
        }
    }

    // cnt_odd + cnt_even = 50

    return cnt_odd + cnt_even + a + b + c;
}

  "#,
  );

  let ast = sysy::_CompUnitParser::new().parse(&progs).unwrap();
  let prog = KoopaGen::gen_on_compile_unit(&ast);
  assert_eq!(koopa_run(prog), 149);
}

#[test]
fn simple_function_call() {
  let progs = String::from(
    r#"

int a = 0;
void func(int i) {
    a = a + i;
    return;
}

int main() {
    int i = 0;
    while (i < 100) {
        i = i + 1;
        func(i);
    }
    return a;
}

  "#,
  );

  let ast = sysy::_CompUnitParser::new().parse(&progs).unwrap();
  let prog = KoopaGen::gen_on_compile_unit(&ast);
  assert_eq!(koopa_run(prog), 5050);
}

/// Run the given koopa program and return the return value
fn koopa_run(prog: Program) -> i32 {
  let interpreter = Interpreter::new(vec![]);
  let retval = Generator::with_visitor(sink(), interpreter)
    .generate_on(&prog)
    .unwrap();
  retval
}
