all:
	ocamlbuild -use-ocamlfind -classic-display -cflag -dtypes dr2smt2.native

doc:
	ocamlbuild -use-ocamlfind -classic-display main.docdir/index.html

clean:
	rm -rf _build *.native
