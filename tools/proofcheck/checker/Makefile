all: error.cmx intv.cmx basic.cmx smt2_cmd.cmx smt2.cmx env.cmx func.cmx ptree.cmx parser.cmx lexer.cmx failhandler.cmx  main.cmx INTERVAL/interval.cmxa
	ocamlfind ocamlopt -linkpkg -package batteries \
	INTERVAL/interval.cmxa -I INTERVAL \
	-annot \
	error.cmx intv.cmx env.cmx basic.cmx func.cmx  smt2_cmd.cmx smt2.cmx failhandler.cmx ptree.cmx parser.cmx lexer.cmx main.cmx \
	INTERVAL/libinterval.a -annot -o main.native

INTERVAL/interval.cmxa:
	make -C INTERVAL/

error.cmx: error.ml
	ocamlfind ocamlopt -annot -c error.ml

intv.cmx: intv.ml INTERVAL/interval.cmxa
	ocamlfind ocamlopt -I INTERVAL -annot -package batteries -c intv.ml

basic.cmx: basic.ml
	ocamlfind ocamlopt -annot -package batteries -c basic.ml

smt2_cmd.cmx: basic.cmx  smt2_cmd.ml
	ocamlfind ocamlopt -annot -package batteries -c smt2_cmd.ml

smt2.cmx: smt2.ml smt2_cmd.cmx
	ocamlfind ocamlopt -annot -package batteries -c smt2.ml

env.cmx: intv.cmx env.ml INTERVAL/interval.cmxa
	ocamlfind ocamlopt -I INTERVAL -annot -package batteries -c env.ml

func.cmx: env.cmx intv.cmx basic.cmx func.ml  INTERVAL/interval.cmxa
	ocamlfind ocamlopt -I INTERVAL -annot -package batteries -c func.ml

ptree.cmx: intv.cmx env.cmx func.cmx smt2.cmx smt2_cmd.cmx basic.cmx ptree.ml failhandler.cmx
	ocamlfind ocamlopt -annot -package batteries -c ptree.ml

failhandler.cmx: intv.cmx env.cmx func.cmx smt2.cmx smt2_cmd.cmx basic.cmx failhandler.ml INTERVAL/interval.cmxa
	ocamlfind ocamlopt -I INTERVAL  -annot -package batteries -c failhandler.ml

main.cmx: ptree.cmx  env.cmx func.cmx main.ml parser.cmx lexer.cmx
	ocamlfind ocamlopt -annot -package batteries -c main.ml

lexer.ml: lexer.mll parser.ml
	ocamllex -q lexer.mll

lexer.cmx: lexer.ml
	ocamlfind ocamlopt -c -package batteries -package threads -thread -o lexer.cmx lexer.ml

parser.ml: parser.mly ptree.ml basic.ml func.ml env.ml
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
	make clean -C INTERVAL
