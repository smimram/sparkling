TESTS = $(wildcard *.sparkling)
SPARKLING = dune exec ../src/sparkling.exe

all: sparkling
	@for i in $(TESTS); do \
	  echo "\n===== Testing $$i =====\n"; \
	  $(SPARKLING) $$i; \
	done

sparkling:
	@$(MAKE) -C ../src

