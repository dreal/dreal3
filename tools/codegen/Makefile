all: setup.ml setup.data
	ocaml setup.ml -build

setup.ml: _oasis
	oasis setup

setup.data: setup.ml
	ocaml setup.ml -configure

clean:
	-ocaml setup.ml -clean

demo: all
	./main.native tests/2.dl

dist-clean:
	-ocaml setup.ml -clean
	-rm -f setup.ml setup.data _tags myocamlbuild.ml
