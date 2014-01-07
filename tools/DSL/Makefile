all:
	ocaml setup.ml -configure
	ocaml setup.ml -build

clean:
	ocaml setup.ml -clean

demo: all
	./main.native tests/1.dl
