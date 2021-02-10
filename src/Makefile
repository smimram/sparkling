all:
	@dune build

test: all
	OCAMLRUNPARAM=b dune exec ./sparkling.exe

kiss: all
	dune exec ./sparkling.exe kiss.sparkling

philosophers:
	ocamlopt philosophers.ml -o philosophers
	./philosophers 4 > philo.sparkling
	rm philosophers
	dune exec ./sparkling.exe philo.sparkling

ci:
	svn ci -m "Worked on sparkling."

%.ps: %.dot
	dot -Tps2 $^ -o $@

%.pdf: %.ps
	ps2pdf $^
