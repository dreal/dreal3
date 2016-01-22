all: setup.ml setup.data build
	@if [ ! -L ../bin/bmc ]; then ln -s ../tools/bmc_main.native ../bin/bmc; fi

setup.ml: _oasis
	oasis setup

setup.data: _oasis setup.ml
	ocaml setup.ml -configure

build: setup.ml setup.data
	ocaml setup.ml -build

clean: setup.ml
	-ocaml setup.ml -clean

dist-clean: clean
	-rm -f setup.ml setup.data _tags myocamlbuild.ml

.PHONY: all build clean dist-clean
