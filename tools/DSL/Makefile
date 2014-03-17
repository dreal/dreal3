all: setup
	ocaml setup.ml -configure
	ocaml setup.ml -build

setup:
	oasis setup

clean:
	ocaml setup.ml -clean

demo: all
	./main.native tests/2.dl
