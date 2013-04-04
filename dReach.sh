#!/bin/bash
BMC=~/work/dreal2/tools/bmc/main.native
DREAL=~/work/dreal2/dReal
PRECISION=0.1
DREAL_OPTION="--visualize --precision=$PRECISION"
DRH=$1
SMT2=${DRH%.drh}.smt2

for K in {1..5}
do
    echo `date`: "Unroll $DRH => $SMT2 with K = $K"
    $BMC -k $K $DRH > $SMT2 || exit 1
    echo `date`: "Run dReal $SMT2 with $DREAL_OPTION"
    $DREAL $DREAL_OPTION $SMT2 || exit 2
done
