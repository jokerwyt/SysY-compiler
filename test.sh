#!/bin/bash

# find all files whose name include space, and replace those space into "_"
find . -name "* *" -type f | rename 's/ /_/g'

list=()

# # get the list of all .c file in "minic-test-cases-2021f" "minic-test-cases-2021s" 
list=$(find minic-test-cases-2021f minic-test-cases-2021s -name "*.c")

# get the list of .sy file in "lava-test" and "TrivialCompiler"
list="$list $(find lava-test TrivialCompiler -name "*.sy")"

# sort the list
list=$(echo $list | tr " " "\n" | sort | tr "\n" " ")

for file in $list
do
    echo "Testing $file"

    cargo run -- -riscv $file -o $file.S > /dev/null 2>&1
    # make sure it return 0
    if [ $? -ne 0 ]; then
        echo "Error in cargo run"
        exit 1
    fi
    clang $file.S -c -o $file.o -target riscv32-unknown-linux-elf -march=rv32im -mabi=ilp32 
    # make sure it return 0
    if [ $? -ne 0 ]; then
        echo "Error in clang"
        exit 1
    fi
    ld.lld $file.o -L$CDE_LIBRARY_PATH/riscv32 -lsysy -o $file.elf
    # make sure it return 0
    if [ $? -ne 0 ]; then
        echo "Error in ld.lld"
        exit 1
    fi

    # build $file.out with clang, with linking
    clang -x c $file -L$CDE_LIBRARY_PATH/native -lsysy -o $file.clang.buildout > /dev/null 2>&1
    # make sure it return 0
    if [ $? -ne 0 ]; then
        echo "Error in clang directly"
        exit 1
    fi


    input_file=${file%.c}.in
    if [ ! -f $input_file ]; then
        input_file=/dev/null
    fi

    qemu-riscv32-static $file.elf < $input_file > $file.elf.sysy.out
    sysy_retval=$?

    ./$file.clang.buildout < $input_file > $file.clang.out
    gcc_retval=$?

    if [ $sysy_retval -ne $gcc_retval ]; then
        echo "Error: return value not match"
        exit 1
    fi

    # compare the output
    diff $file.elf.sysy.out $file.clang.out
    if [ $? -ne 0 ]; then
        echo "Error: output not match"
        exit 1
    fi

    echo "Test $file passed"
    
done