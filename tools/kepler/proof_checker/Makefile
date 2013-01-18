all: error.cmx intv.cmx env.cmx func.cmx constraint.cmx ptree.cmx parser.cmx lexer.cmx main.cmx
	ocamlfind ocamlopt -linkpkg -package batteries \
	../INTERVAL/interval.cmxa -I ../INTERVAL \
	error.cmx intv.cmx env.cmx func.cmx constraint.cmx ptree.cmx parser.cmx lexer.cmx main.cmx \
	../INTERVAL/libinterval.a -annot -o main.native

error.cmx: error.ml
	ocamlfind ocamlopt -I ../INTERVAL -annot -c error.ml 

intv.cmx: intv.ml
	ocamlfind ocamlopt -I ../INTERVAL -annot -package batteries -c intv.ml 

env.cmx: intv.ml env.ml
	ocamlfind ocamlopt -I ../INTERVAL -annot -package batteries -c env.ml 

func.cmx: intv.ml env.ml func.ml
	ocamlfind ocamlopt -I ../INTERVAL -annot -package batteries -c func.ml 

constraint.cmx: constraint.ml env.ml func.ml
	ocamlfind ocamlopt -I ../INTERVAL -annot -package batteries -c constraint.ml 

ptree.cmx: intv.ml env.ml func.ml ptree.ml
	ocamlfind ocamlopt -I ../INTERVAL -annot -package batteries -c ptree.ml 

main.cmx: intv.ml env.ml func.ml ptree.ml main.ml
	ocamlfind ocamlopt -I ../INTERVAL -annot -package batteries -c main.ml 

lexer.ml: lexer.mll
	ocamllex.opt -q lexer.mll

lexer.cmx: lexer.ml
	ocamlfind ocamlopt -c -package batteries -package threads -thread -o lexer.cmx lexer.ml

parser.ml: parser.mly
	ocamlyacc -v parser.mly

parser.cmi: parser.mli
	ocamlfind ocamlc -c -dtypes -package batteries -package threads -thread -o parser.cmi parser.mli

parser.cmx: parser.ml parser.cmi
	ocamlfind ocamlopt -c -package batteries -package threads -thread -o parser.cmx parser.ml

clean:
	-rm -f lexer.ml parser.ml parser.output
	-rm -f parser.mli
	-rm -f *.cmi *.cmx *.o *.annot
	-rm -f main.native
