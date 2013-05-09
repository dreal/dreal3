all:
	ocamlbuild -use-ocamlfind -classic-display -no-links -cflag -annot bmc/main.native smt2_stat/main.native
	@cp -v _build/bmc/main.native bmc/main.native
	@cp -v _build/smt2_stat/main.native smt2_stat/main.native

clean:
	rm -rf _build
