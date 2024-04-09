#!/usr/bin/env python3
# copy all .sy, .c and .in files under the working directory into data/

import os
import multiprocessing
import subprocess

def copy_files():
    os.system('rm -rf data && mkdir data')
    for root, dirs, files in os.walk('.'):
        for file in files:
            if file.endswith('.sy') or file.endswith('.c') or file.endswith('.in'):
                # rename all .sy into .c
                if file.endswith('.sy'):
                    new_file = file[:-3] + '.c'
                else:
                    new_file = file
                os.system('cp ' + os.path.join(root, file) + ' data/' + new_file)
                print('Copying ' + file + ' to data/' + new_file)
    print('All files copied!')

def generate_output(root, file):
  print('======= Compiling and running ' + file + ' ...')
  elf_name = "data/" + file[:-2] + '.elf'
  cmd = 'clang -x c ' + os.path.join(root, file) + ' -L$CDE_LIBRARY_PATH/native -lsysy -o ' + elf_name
  output_file = os.path.join(root, file[:-2] + '.out')
  if os.system(cmd) != 0:
    return (file, "clang failed to compile")
    
  # if there is an input file, redirect the input to the program
  # if not, just run the program
  if os.path.exists(os.path.join(root, file[:-2] + '.in')):
    # retval = os.system(elf_name + ' < ' + os.path.join(root, file[:-2] + '.in') + ' > ' + output_file,)
    result = subprocess.run([elf_name], stdin=open(os.path.join(root, file[:-2] + '.in'), 'r'), stdout=open(output_file, 'w'))
    retval = result.returncode
  else:
    result = subprocess.run([elf_name], stdout=open(output_file, 'w'))
    retval = result.returncode
  # append the return value to the output file
  with open(output_file, 'a+') as f:
    # see if it's an empty file
    if f.tell() == 0:
      f.write(str(retval))
    else:
      # see if there is still a newline at the end of the file
      f.seek(0, os.SEEK_END)
      f.seek(f.tell() - 1, os.SEEK_SET)
      if f.read(1) != '\n':
        f.write('\n')
      f.write(str(retval))


if __name__ == '__main__':
  copy_files()

  # for all .c file, use the following command to make .out
  # clang -x c $file -L$CDE_LIBRARY_PATH/native -lsysy -o $file.clang.elf > /dev/null 2>&1
  # ./$file.clang.elf < $input_file > $file.clang.out
  # remember to check if clang and clang.elf run successfully and report error if not

  error_list = []
  pool = multiprocessing.Pool(processes=16) 
  for root, dirs, files in os.walk('data'):
    for file in files:
      # if file != '000_main.c':
      #   continue
      # breakpoint()
      if file.endswith('.c'):
        #  generate_output(root, file)
         error = pool.apply_async(generate_output, (root, file))
         error_list.append(error)
  pool.close()
  pool.join()
  error_list = [error.get() for error in error_list if error.get() is not None]
  for root, dirs, files in os.walk('data'):
    for file in files:
      if file.endswith('.elf'):
        os.system('rm ' + os.path.join(root, file))

  if len(error_list) == 0:
    print('All files compiled and run successfully!')
  else:
    print('There are some errors:')
    for error in error_list:
      print(error)