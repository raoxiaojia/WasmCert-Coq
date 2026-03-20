default:
	opam install .

SHELL := bash

SCRIPT := ./run_wast.sh

FOLDER ?=
FILTER ?=

.PHONY: run_wast test clean
run_wast:
	$(SCRIPT) "$(FOLDER)" "$(FILTER)"

test:
	$(SCRIPT)

clean:
	dune clean
