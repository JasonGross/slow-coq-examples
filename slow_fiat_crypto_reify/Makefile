-include Makefile.coq

Makefile.coq: _CoqProject Makefile
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq.tmp && mv Makefile.coq.tmp Makefile.coq
