all: Makefile.coq
	+$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	+$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf *~ .*.aux .*.cache

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq *.v

%: Makefile.coq
	+$(MAKE) -f Makefile.coq $@

.PHONY: all clean _CoqProject Makefile
