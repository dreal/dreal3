all: setup.ml setup.data build
	@if [ ! -L ../bin/bmc ]; then ln -s ../tools/bmc_main.native ../bin/bmc; fi
	@if [ ! -L ../bin/inv ]; then ln -s ../tools/inv_main.native ../bin/inv; fi

setup.ml: _oasis
	oasis setup

setup.data: _oasis setup.ml
	ocaml setup.ml -configure

build:
	ocaml setup.ml -build

clean:
	-ocaml setup.ml -clean

dist-clean:
	-ocaml setup.ml -clean
	-rm setup.ml setup.data _tags myocamlbuild.ml
