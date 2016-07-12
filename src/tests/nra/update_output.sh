#!/usr/bin/env bash
DREAL=../../../bin/dReal
for SMT2 in *.smt2
do
    echo Running... ${SMT2}
    if [ -e "${SMT2}.option" ] ; then
        ${DREAL} --suppress-warning `cat ${SMT2}.option` ${SMT2} | tail -n 1 | tee ${SMT2}.expected
    else
        ${DREAL} --suppress-warning ${SMT2} | tail -n 1 | tee ${SMT2}.expected
    fi
done
