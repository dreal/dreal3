all:
	oasis setup
	ocaml setup.ml -configure
	ocaml setup.ml -build
	

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
