all:
	@rm -rf bmc/main.native smt2_stat/main.native cppbmc/pass[1,2].native icp_vis/main.native
	ocamlbuild -use-ocamlfind -classic-display -no-links -cflag -annot \
		bmc/main.native \
		smt2_stat/main.native \
		icp_vis/main.native \
		cppbmc/pass1.native \
		cppbmc/pass2.native

	@ln -sf ../_build/bmc/main.native bmc/main.native
	@ln -sf ../_build/smt2_stat/main.native smt2_stat/main.native
	@ln -sf ../_build/icp_vis/main.native icp_vis/main.native
	@ln -sf ../_build/cppbmc/pass1.native cppbmc/pass1.native
	@ln -sf ../_build/cppbmc/pass2.native cppbmc/pass2.native

clean:
	rm -rf _build bmc/main.native smt2_stat/main.native cppbmc/pass[1,2].native icp_vis/main.native
