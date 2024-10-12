default:
	opam install .

test-fib-iter:
	for file in fib_test/fib_iter/*.wasm; \
	do \
		echo "Executing $$file"; \
		dune exec -- wasm_coq_interpreter $$file -r main; \
	done

test-fib-rec:
	for file in fib_test/fib_rec/*.wasm; \
	do \
		echo "Executing $$file"; \
		dune exec -- wasm_coq_interpreter $$file -r main; \
	done

loc:
	cloc theories/type_progress.v
	cloc theories/type_preservation.v
	cloc theories/interpreter_ppi.v
