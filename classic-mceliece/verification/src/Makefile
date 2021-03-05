
# Build commands for bitcode

.SUFFIXES: .c .bc

%.bc : %.c
	clang -g -O1 -c -emit-llvm $< -o $@ -march=native -mtune=native -Wall -I. -Isubroutines -DKAT -DKATNUM=`cat KATNUM` "-DCRYPTO_NAMESPACE(x)=x" "-D_CRYPTO_NAMESPACE(x)=_##x"

linked.bc : gf.bc root.bc
	llvm-link gf.bc root.bc -o linked.bc

clean:
	rm -f *.bc