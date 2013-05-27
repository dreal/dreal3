all:
	ocamlbuild -use-ocamlfind -classic-display -no-links -cflag -annot \
		bmc/main.native \
		smt2_stat/main.native \
		cppbmc/pass1.native \
		cppbmc/pass2.native

	@cp -v _build/bmc/main.native bmc/main.native
	@cp -v _build/smt2_stat/main.native smt2_stat/main.native
	@cp -v _build/cppbmc/pass1.native cppbmc/pass1.native
	@cp -v _build/cppbmc/pass2.native cppbmc/pass2.native


clean:
	rm -rf _build bmc/main.native smt2_stat/main.native cppbmc/pass[1,2].native
