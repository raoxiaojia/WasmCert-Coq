default:
	opam install .

test-fib-iter:
	for file in fib_test/fib_iter/*.wasm; \
	do \
		echo "Executing $$file"; \
		dune exec -- wasm_coq_interpreter $$file -r main; \
	done
