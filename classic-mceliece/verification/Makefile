
# Build commands for bitcode

.SUFFIXES: .c .bc

artifacts/linked.bc : artifacts/gf.bc artifacts/root.bc artifacts/util.bc artifacts/synd.bc artifacts/transpose.bc artifacts/bm.bc artifacts/encrypt.bc artifacts/controlbits.bc
	llvm-link artifacts/gf.bc artifacts/root.bc artifacts/util.bc artifacts/synd.bc artifacts/transpose.bc artifacts/bm.bc artifacts/encrypt.bc artifacts/controlbits.bc -o artifacts/linked.bc

artifacts/synd.bc : imp-custom/synd.c
	clang -g -O1 -c -emit-llvm $< -o $@ -march=native -mtune=native -Wall -I. -Isubroutines -DKAT -DKATNUM=`cat imp/KATNUM` "-DCRYPTO_NAMESPACE(x)=x" "-D_CRYPTO_NAMESPACE(x)=_##x"

artifacts/bm.bc : imp-custom/bm.c
	clang -g -O1 -c -emit-llvm $< -o $@ -march=native -mtune=native -Wall -I. -Isubroutines -DKAT -DKATNUM=`cat imp/KATNUM` "-DCRYPTO_NAMESPACE(x)=x" "-D_CRYPTO_NAMESPACE(x)=_##x"

artifacts/encrypt.bc : imp-custom/encrypt.c
	clang -g -O1 -c -emit-llvm $< -o $@ -march=native -mtune=native -Wall -I. -Isubroutines -DKAT -DKATNUM=`cat imp/KATNUM` "-DCRYPTO_NAMESPACE(x)=x" "-D_CRYPTO_NAMESPACE(x)=_##x"

artifacts/%.bc : imp/%.c
	clang -g -O1 -c -emit-llvm $< -o $@ -march=native -mtune=native -Wall -I. -Isubroutines -DKAT -DKATNUM=`cat imp/KATNUM` "-DCRYPTO_NAMESPACE(x)=x" "-D_CRYPTO_NAMESPACE(x)=_##x"

graph : graphs/graph.dot
	dot -Tpng $< > artifacts/graph.png

test-log: artifacts/linked.bc
	saw proofs/linked.saw > artifacts/proof_output

test: artifacts/linked.bc
	saw proofs/linked.saw

clean:
	rm -f artifacts/*

