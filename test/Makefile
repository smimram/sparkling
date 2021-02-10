TESTS = $(wildcard *.sparkling)
SPARKLING = dune exec ../src/sparkling.exe

all: sparkling
	for i in $(TESTS); do \
	  echo "Testing $$i..."; \
	  $(SPARKLING) $$i; \
	done

sparkling:
	@$(MAKE) -C ../src

