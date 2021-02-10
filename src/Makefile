all:
	@dune build

test: all
	OCAMLRUNPARAM=b dune exec ./sparkling.exe

kiss: all
	dune exec ./sparkling.exe kiss.sparkling

philosophers:
	dune exec ./philosophers.exe 4 > philo.sparkling
	dune exec ./sparkling.exe philo.sparkling
	rm philo.sparkling

conflicts:
	menhir --explain parser.mly
	rm -f parser.ml parser.mli
	less parser.conflicts
	rm -f parser.conflicts

ci:
	svn ci -m "Worked on sparkling."

%.ps: %.dot
	dot -Tps2 $^ -o $@

%.pdf: %.ps
	ps2pdf $^
