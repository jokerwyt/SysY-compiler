cargo run -- -koopa $1 -o $1.koopa\
&& koopac $1.koopa | llc --filetype=obj -o $1.o\
&& clang $1.o -L$CDE_LIBRARY_PATH/native -lsysy -o $1.out
./$1.out

echo "retval=$?"