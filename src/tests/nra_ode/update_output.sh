#!/usr/bin/env bash
DREAL=../../../bin/dReal
for SMT2 in *.smt2
do
    echo Running... ${SMT2}
    if [ -e "${SMT2}.option" ] ; then
        timeout3 -t 300 ${DREAL} `cat ${SMT2}.option` ${SMT2} 2>&1 | tail -n 1 | tee ${SMT2}.expected
    else
        timeout3 -t 300 ${DREAL} ${SMT2} 2>&1 | tail -n 1 | tee ${SMT2}.expected
    fi
done
