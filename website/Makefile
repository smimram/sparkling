all: sparkling.js

examples.ml:
	echo "let list = [" > $@
	for i in $(wildcard ../test/*.sparkling); do \
	  echo "\"`basename $$i`\", " >> $@; \
	  echo "\"" >> $@; \
	  echo "`cat $$i`" >> $@; \
	  echo "\";" >> $@; \
	done; \
	echo "]" >> $@

sparkling.js:
	@rm -f $@
	@dune build
	@cp ../_build/default/website/web.bc.js $@

.PHONY: sparkling.js
