#/bin/bash

rm debug/*

clang $1 -c -o $1.o -target riscv32-unknown-linux-elf -march=rv32im -mabi=ilp32 \
&& echo "clang done" \
&& ld.lld $1.o -L$CDE_LIBRARY_PATH/riscv32 -lsysy -o $1.elf \
&& echo "ld.lld done" \
&& qemu-riscv32-static $1.elf

echo $?