#!/usr/bin/env bash
# Author: Soonho Kong (soonhok@cs.cmu.edu)

########################################################################
# Find oasis, opam, and ocaml
#######################################################################
for OCAMLTOOL in oasis opam ocamlc ocaml
do
    PATHNAME=`which $OCAMLTOOL`
    if [ ! -e "${PATHNAME}" ]; then
        echo Ocaml Tool: ${OCAMLTOOL} is not found. Please install ${OCAMLTOOL}.
        exit 1
    fi
done

########################################################################
# Build Tools (Ocaml)
########################################################################
cd tools
make
cd ..
