all:
	oasis setup
	ocaml setup.ml -configure
	ocaml setup.ml -build
	@if [ ! -L ../bin/bmc ]; then ln -s ../tools/bmc_main.native ../bin/bmc; fi
	@if [ ! -L ../bin/inv ]; then ln -s ../tools/inv_main.native ../bin/inv; fi

configure:
	ocaml setup.ml -configure

build:
	ocaml setup.ml -build

update:
	oasis setup

clean:
	-ocaml setup.ml -clean

dist-clean:
	-ocaml setup.ml -clean
	-rm setup.ml setup.data _tags myocamlbuild.ml
