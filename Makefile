all: Makefile.coq
	$(MAKE) -f Makefile.coq all

html: Makefile.coq
	$(MAKE) -f Makefile.coq html

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq*

cleanall: Makefile.coq
	+make -f Makefile.coq cleanall
	rm -f Makefile.coq*

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: all html install clean cleanall
