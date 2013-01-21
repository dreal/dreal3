#!/bin/bash
INEQDIR=$1
RESULTDIR=$2
MAX=1

find $INEQDIR -name "*.smt2" | grep -v "minismt" | parallel --max-procs=$MAX "echo {}; ./run_single.sh {} $RESULTDIR"
