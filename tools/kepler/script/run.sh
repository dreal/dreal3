#!/bin/bash
INEQDIR=./flyspeck_ineqs/
RESULTDIR=./result
MAX=16

find $INEQDIR -name "*.dr" -newer $RESULTDIR/lastrun | parallel --max-procs=$MAX 'echo {}; ./run_single.sh {}'
touch $RESULTDIR/lastrun
