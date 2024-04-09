#/bin/bash

find debug/ ! -name '*.c' -type f -delete

cargo run --release -- -riscv $1 -o $1.S\
&& clang $1.S -c -o $1.o -target riscv32-unknown-linux-elf -march=rv32im -mabi=ilp32 \
&& echo "clang done" \
&& ld.lld $1.o -L$CDE_LIBRARY_PATH/riscv32 -lsysy -o $1.elf \
&& echo "ld.lld done" \
&& qemu-riscv32-static $1.elf

echo $?