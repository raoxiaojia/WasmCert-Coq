default:
	opam install .

test-fib-iter:
	for file in fib_test/fib_iter/*.wasm; \
	do \
		echo "Testing $$file"; \
		dune exec -- wasm_coq_interpreter $$file -r main; \
	done

test-fib-rec:
	for file in fib_test/fib_rec/*.wasm; \
	do \
		echo "Testing $$file"; \
		dune exec -- wasm_coq_interpreter $$file -r main; \
	done
	
loc:
	cloc theories/contexts.v theories/interpreter_ctx.v theories/type_progress.v
