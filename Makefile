all: Makefile.coq
	$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq

cleanall: Makefile.coq
	+make -f Makefile.coq cleanall
	rm -f Makefile.coq

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
