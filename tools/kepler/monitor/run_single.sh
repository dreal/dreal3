#!/bin/bash
RANGE_FILE=$1
FORMULA_FILE=$2
DREAL=~/work/dReal/opensmt/dReal
CHECKER=~/work/kepler-soohnok/src/proof_checker/main.native
INPUT_FILE="./input.dr"
TRACE_FILE="./trace"

echo $1 $2
echo $RANGE_FILE $FORMULA_FILE

echo 0. Combine RANGE and FORMULA, make an INPUT to dReal
cat $RANGE_FILE $FORMULA_FILE | tee $INPUT_FILE

echo 1. Run dReal, generate TRACE
$DREAL $INPUT_FILE | head -n -6 | tail -n +5 | tee $TRACE_FILE

echo 2. Check trace, possibily generates other ranges
$CHECKER $TRACE_FILE

echo =================================================

# 3. Delete this range
rm $1
#rm $INPUT_FILE
#rm $TRACE_FILE

