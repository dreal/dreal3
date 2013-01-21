#!/bin/bash
INEQDIR=$1
RESULTDIR=$2
MAX=30
RUN_SINGLE=~/work/dreal2/tools/kepler/script/run_single.sh

find $INEQDIR -name "*.smt2" | grep -v "minismt" | parallel --max-procs=$MAX "echo {}; $RUN_SINGLE {} $RESULTDIR"
