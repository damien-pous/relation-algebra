KNOWNTARGETS := RocqMakefile
KNOWNFILES   := Makefile _RocqProject

.DEFAULT_GOAL := invoke-rocqmakefile

RocqMakefile: Makefile _RocqProject
	$(ROCQBIN)rocq makefile -f _RocqProject -docroot . -o RocqMakefile

invoke-rocqmakefile: RocqMakefile
	$(MAKE) --no-print-directory -f RocqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-rocqmakefile $(KNOWNFILES)

cleanall:: clean
	rm -f RocqMakefile* *.d *.log */*.glob */.*.aux */*.vo*

# TOFIX
depgraph.dot::
	@echo building dependency graph
	@echo "digraph {" > $@
	@ls -1 theories/*.v | grep -v theories/all |sed 's#theories/\(.*\)\.v#\1 [URL=".\/html\/RelationAlgebra.\1.html"];#g' >> $@
	@coqdep -f _RocqProject -dyndep no -m src/META.rocq-relation-algebra \
	| grep vio \
	| sed 's#: [^ ]*\.v #->{#g' \
	| sed 's#src/META.rocq-relation-algebra[ ]*##g' \
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

# This should be the last rule, to handle any targets not declared above
%: invoke-rocqmakefile
	@true
