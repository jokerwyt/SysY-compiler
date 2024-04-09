#!/bin/bash

# get those repo via the following link.
# Some cases need to support integer literal -2147483648, which is not included in PKU lab. We can edit them manually.
# https://pku-minic.github.io/online-doc/#/misc-app-ref/environment?id=%e4%bd%bf%e7%94%a8%e5%85%b6%e4%bb%96%e6%b5%8b%e8%af%95%e7%94%a8%e4%be%8b

# find all files whose name include space, and replace those space into "_"
find . -name "* *" -type f | rename 's/ /_/g'

list=()

# get the list of all .c file in "minic-test-cases-2021f" "minic-test-cases-2021s" 
list=$(find minic-test-cases-2021f minic-test-cases-2021s -name "*.c")

# get the list of .sy file in "lava-test" and "TrivialCompiler"
list="$list $(find lava-test TrivialCompiler -name "*.sy")"

# sort the list
list=$(echo $list | tr " " "\n" | sort | tr "\n" " ")
fail_list=()

for file in $list
do
    echo "Testing $file"
    rm -f $file.S $file.o $file.elf $file.elf.sysy.out $file.clang.out $file.clang.elf

    cargo run -- -riscv $file -o $file.S > /dev/null 2>&1
    # make sure it return 0
    if [ $? -ne 0 ]; then
        echo "Error in cargo run"
        fail_list+=($file)
        continue
    fi
    clang $file.S -c -o $file.o -target riscv32-unknown-linux-elf -march=rv32im -mabi=ilp32 
    # make sure it return 0
    if [ $? -ne 0 ]; then
        echo "Error in clang"
        fail_list+=($file)
        continue
    fi
    ld.lld $file.o -L$CDE_LIBRARY_PATH/riscv32 -lsysy -o $file.elf
    # make sure it return 0
    if [ $? -ne 0 ]; then
        echo "Error in ld.lld"
        fail_list+=($file)
        continue
    fi

    # build $file.out with clang, with linking
    clang -x c $file -L$CDE_LIBRARY_PATH/native -lsysy -o $file.clang.elf > /dev/null 2>&1
    # make sure it return 0
    if [ $? -ne 0 ]; then
        echo "Error in clang directly"
        fail_list+=($file)
        continue
    fi


    input_file=${file%.c}.in
    if [ ! -f $input_file ]; then
        input_file=/dev/null
    fi

    qemu-riscv32-static $file.elf < $input_file > $file.elf.sysy.out
    sysy_retval=$?

    ./$file.clang.elf < $input_file > $file.clang.out
    gcc_retval=$?

    # It cannot identify both segmentation fault.
    # But it does not matter...

    if [ $sysy_retval -ne $gcc_retval ]; then
        echo "Error: return value not match"
        fail_list+=($file)
        continue
    fi

    # compare the output
    diff $file.elf.sysy.out $file.clang.out
    if [ $? -ne 0 ]; then
        echo "Error: output not match"
        fail_list+=($file)
        continue
    fi

    echo "Test $file passed"
    
done

echo "Failed test cases:"
for file in ${fail_list[@]}
do
    echo $file
done
