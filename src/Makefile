SOURCES = common.ml prog.mli prog.ml lang.mli lang.ml parser.mly lexer.mll $(APRON_ML) sparkling.ml
RESULT = sparkling

OCAMLDEP = ocamldep.opt
OCAMLOPT = ocamlopt.opt

DOC_FILES = common.ml prog.mli lang.mli
OCAMLDOCFLAGS = -sort -stars

APRON = no

ifneq "$(APRON)" "no"
APRON_ML = AI.ml
INCDIRS += +apron
LIBS += bigarray gmp apron
LIBDIRS += /usr/lib/ocaml/stublibs
CLIBS += boxMPQ_caml boxMPQ octMPQ_caml octMPQ mpfr itvMPQ apron_caml apron camlidl
endif

test: all
	OCAMLRUNPARAM=b ./sparkling
	-$(MAKE) ginsu.ps

kiss: all
	./sparkling kiss.sparkling

all: dnc

philosophers:
	$(OCAMLOPT) philosophers.ml -o philosophers
	./philosophers 4 > philo.sparkling
	./sparkling philo.sparkling

ci:
	svn ci -m ""

%.ps: %.dot
	dot -Tps2 $^ -o $@

%.pdf: %.ps
	ps2pdf $^

include OCamlMakefile

.PHONY: philosophers
