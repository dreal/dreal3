all:
	oasis setup
	ocaml setup.ml -configure
	ocaml setup.ml -build

clean:
	ocaml setup.ml -clean
	rm setup.* _tags myocamlbuild.ml
