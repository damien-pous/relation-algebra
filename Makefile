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

depgraph.dot::
	@echo building dependency graph
	@echo "digraph {" > $@
	@ls -1 theories/*.v | grep -v theories/all |sed 's#theories/\(.*\)\.v#\1 [URL=".\/html\/RelationAlgebra.\1.html"];#g' >> $@
	@$(ROCQBIN)rocq dep -f _RocqProject theories/fhrel.v theories/rewriting_aac.v -dyndep no \
	| sed -n 's/\.vo.*:.*\.v /->{/p' \
	| sed 's/[^ ]*rocqworker//g' \
	| sed 's/[^ ]*META[^ ]*//g' \
	| sed 's/\.vo//g' \
	| sed '/^^ *$$/d' \
	| sed 's/[ ]$$/};/g' \
	| sed 's/  */;/g' \
	| sed 's#theories/##g' \
	| sed 's#examples/.*##g' \
	| sed 's#all.*##g' \
	>> $@;
	@echo "}" >> $@

%.svg: %.dot
	tred $< | dot -Tsvg -o $@

# This should be the last rule, to handle any targets not declared above
%: invoke-rocqmakefile
	@true
