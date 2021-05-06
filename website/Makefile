all: sparkling.js

examples.ml: ../test/*.sparkling
	echo "let list = List.sort compare [" > $@
	for i in $(wildcard ../test/*.sparkling); do \
	  echo "\"`basename $$i .sparkling`\", " >> $@; \
	  echo -n "\"" >> $@; \
	  echo "`cat $$i`" >> $@; \
	  echo "\";" >> $@; \
	done; \
	echo "]" >> $@

sparkling.js:
	@rm -f $@
	@dune build
	@cp ../_build/default/website/web.bc.js $@

.PHONY: sparkling.js
