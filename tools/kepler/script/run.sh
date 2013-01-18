#!/bin/bash
INEQDIR=$1
RESULTDIR=./result
MAX=25

find $INEQDIR -name "*.smt2" -newer $RESULTDIR/lastrun | parallel --max-procs=$MAX 'echo {}; ./run_single.sh {}'
touch $RESULTDIR/lastrun
