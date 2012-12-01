REQUIREMENT:
============
1. OCaml 3.12.1
2. OCaml Batteries Included 1.4.1
3. OCaml Findlib 1.2.7

BUILDING:
=========

1. Build interval computation library for ocaml

		$ cd INTERVAL
		$ make
		$ cd ..

2. Build proof checker

		$ cd proof_checker
		$ make

3. Try it on a simple example

		$ ./main.native test_trace/1.tr
