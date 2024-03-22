// Comments
/* Multiple Line Comments in one line */
/* 
Multiple Line Comments in 
Multiple
Line
*/

int global_var;
int global_array[3];

const int global_const0 = 0;
const int global_const = 3 + 3 + global_const0;
const int global_const_array[3][3] = {1, {2,2}, {3,3,3}};
const int array_0[0] = {};

void func_without_ret(int param, int param2[], int param3[][3]) {
  {
    {
      {

      }
    }
    if (0)
    {
      if (1) {

      } else {

      }
    }
    while (1) {
      break;
    }
  }
}

int func_ret() {
  return global_const;
}

int main() {
  int local_var_without_init;
  const int local_const = ((1 + 3 % 5) * 8 / 1 <= 0) * !998244353;
  int local_var_with_init = local_const + 1;

  local_var_without_init = 0x233;

  // dangling-else
  if (local_const)
    if (/* const expr */ 1 + func_ret()) 
      func_ret();
    else /* dangling else */
      func_without_ret(local_var_without_init, /* partial array */ global_const_array[1], global_const_array);

  while (1) {
    break;
    continue;
  }

  int local_array[3][3] = {};
  print(local_array[global_const0][1 - 1]);

}