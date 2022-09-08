-include Makefile.coq

Makefile.coq: 
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

cleanall:: clean
	rm -f Makefile.coq* depgraph.* */*.d

depgraph.dot::
	@echo building dependency graph
	@echo "digraph {" > $@
	@ls -1 theories/*.v | grep -v theories/all |sed 's#theories/\(.*\)\.v#\1 [URL=".\/html\/RelationAlgebra.\1.html"];#g' >> $@
	@coqdep -f _CoqProject -dyndep no -m src/META.coq-relation-algebra \
	| grep vio \
	| sed 's#: [^ ]*\.v #->{#g' \
	| sed 's#src/META.coq-relation-algebra[ ]*##g' \
	| sed 's/\.vio//g' \
	| sed 's/[ ]*$$/};/g' \
	| sed 's/ /;/g' \
	| sed 's#theories/##g' \
	| sed 's#examples/.*##g' \
	| sed 's#all.*##g' \
	>> $@;
	@echo "}" >> $@

%.svg: %.dot
	tred $< | dot -Tsvg -o $@

## used to use [coqdep -dumpgraph] as follows
# 	coqdep theories/*.v -dumpgraph depgraph.dot 1>/dev/null 2>/dev/null
# 	sed -i 's/\[label=\"\([^"]*\)\"]/[label="\1";URL=".\/html\/RelationAlgebra.\1.html"]/g' depgraph.dot
# 	dot depgraph.dot -Tsvg -o depgraph.svg

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
