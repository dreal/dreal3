all:
	@rm -rf bmc/main.native smt2_stat/main.native cppbmc/pass[1,2].native icp_vis/main.native
	ocamlbuild -use-ocamlfind -classic-display -no-links -cflag -annot \
		bmc/main.native \
		smt2_stat/main.native \
		icp_vis/main.native
#
# The following modules are disabled to due to the current issue of
# cil-1.7.2 package on OPAM. The author of cil recognized this problem
# and is working on this: https://github.com/kerneis/cil/issues/3
#
#		cppbmc/pass1.native \
#		cppbmc/pass2.native
#
	@ln -sf ../_build/bmc/main.native bmc/main.native
	@ln -sf ../_build/smt2_stat/main.native smt2_stat/main.native
	@ln -sf ../_build/icp_vis/main.native icp_vis/main.native
#	@ln -sf ../_build/cppbmc/pass1.native cppbmc/pass1.native
#	@ln -sf ../_build/cppbmc/pass2.native cppbmc/pass2.native

clean:
	rm -rf _build bmc/main.native smt2_stat/main.native cppbmc/pass[1,2].native icp_vis/main.native
