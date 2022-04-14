-include Makefile.coq

Makefile.coq: 
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

cleanall:: clean
	rm -f Makefile.coq* depgraph.* */*.d

depgraph::
	coqdep *.v -dumpgraph depgraph.dot 1>/dev/null 2>/dev/null
	sed -i 's/\[label=\"\([^"]*\)\"]/[label="\1";URL=".\/html\/RelationAlgebra.\1.html"]/g' depgraph.dot
	dot depgraph.dot -Tsvg -o depgraph.svg

enable-ssr::
	sed -i '/theories\/fhrel\.v/d' _CoqProject
	echo "theories/fhrel.v" >>_CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

disable-ssr::
	sed -i '/theories\/fhrel\.v/d' _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

enable-aac::
	sed -i '/theories\/rewriting_aac\.v/d' _CoqProject
	echo "theories/rewriting_aac.v" >>_CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

disable-aac::
	sed -i '/theories\/rewriting_aac\.v/d' _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq
