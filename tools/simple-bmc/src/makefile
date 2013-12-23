build:
	ocamlbuild -use-ocamlfind -classic-display -no-links -cflag -annot main.native
	@ln -sf _build/main.native sbmc

install: 
	cp _build/main.native ~/.opam/system/bin/sbmc

all: build

clean:
	rm -rf _build
	@rm -rf sbmc

demo: build
	./sbmc -k 3 data_file/bouncing_ball_with_drag.drh
