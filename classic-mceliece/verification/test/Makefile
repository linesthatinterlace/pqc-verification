
# Build commands for bitcode

.SUFFIXES: .c .bc

%.bc : %.c
	clang -g -O1 -c -emit-llvm $< -o $@