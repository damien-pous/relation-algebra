all: Makefile.coq
	$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq

cleanall: Makefile.coq
	+make -f Makefile.coq cleanall
	rm -f Makefile.coq* depend.dot depend.svg

depgraph:
	coqdep *.v -dumpgraph depgraph.dot 1>/dev/null 2>/dev/null
	sed -i 's/\[label=\"\([^"]*\)\"]/[label="\1";URL=".\/html\/RelationAlgebra.\1.html"]/g' depgraph.dot
	dot depgraph.dot -Tsvg -o depgraph.svg

Makefile.coq: 
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

enable:
	sed -i '/fhrel\.v/d' _CoqProject
	echo "fhrel.v" >>_CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

disable:
	sed -i '/fhrel\.v/d' _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@

.PHONY: all clean enable disable
