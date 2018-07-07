.PHONY: build test

build: Makefile.coq
	make -f $<

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@
