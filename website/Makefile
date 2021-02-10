all: sparkling.js

sparkling.js:
	@rm -f $@
	@dune build
	@cp ../_build/default/website/web.bc.js $@

.PHONY: sparkling.js
