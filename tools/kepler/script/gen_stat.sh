#!/bin/bash
FAIL=`cat result/*.result | grep "^Fail" | wc -l`
SAT=`cat result/*.result | grep "^sat" | wc -l`
UNSAT=`cat result/*.result | grep "^unsat" | wc -l`
echo "<h2>"
echo "UNSAT : $UNSAT,"
echo "SAT : $SAT,"
echo "FAIL : $FAIL."
echo "</h2>"
