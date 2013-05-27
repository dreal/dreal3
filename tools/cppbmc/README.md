Requirements
============
1. Ocamlbrew

   URL: https://github.com/hcarty/ocamlbrew
   Dependency: `curl`, `m4`, `libev-dev`

2. CIL

   URL: https://github.com/kerneis/cil

   It is recommended to install CIL via `odb.ml`:

   - Download https://raw.github.com/thelema/odb/master/packages and
   copy it to ~/.odb/packages

   - Install CIL via odb.ml by typing

   $ odb.ml cil


Compile
=======

   $ make

Run
===

1. Preprocess the input C file

   $ gcc -E `input.c` > `input.i`

2. Run `pass1.native` with the preprocessed file

   $ ./pass1.native `input.i` > `output.txt`

3. Annotate `output.txt` and save it as `output_annotated.txt`

   Generated `output.txt` contains 1) a list of program variables which
   appeared in the given C program and 2) a logical formula which
   represents the semantics of the given loop body.

   We ask users to annotate `output.txt` with the following
   information and save the it as `output_annotated.txt`.

   2.1. Possible range of each variable.
   For instance, for the following incomplete ranges

       [, ]                              ActualGap_m: 0;
       [, ]                              DesiredGap_m: 2;
       [, ]                              K: 0;
       [, ]                              OnComingGap_m: 0;
       ...

   can be annotated as follows:

       [0, 10000]                        ActualGap_m: 0;
       [0, 10000]                        DesiredGap_m: 2;
       [-1000, 1000]                     K: 0;
       [0,10000]                         OnComingGap_m: 0;

   2.2. Invariant
   Users have to provide an inductive invariant for the given loop.
   For example,

       // Invariant
       (v0_cmd > 10)

4. Run `pass2.native`

   $ ./pass2.native `output_annotated.txt` > `output.dr`

5. Run `dReal` over the generated formula `output.dr`

   $ dReal `output.dr`
