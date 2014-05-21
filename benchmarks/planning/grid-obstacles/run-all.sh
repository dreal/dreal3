#!/bin/bash

ulimit -t 600

NUM=10
NINST=10
TIMEFORMAT="%U"

echo "Size Heuristic Orig" >> grid.out
for((i=1; i <=$NUM; i++)); do {
	f=`expr $i \* 2`
   	echo "DELTA = ${d} STEPS = ${f}"
	LEN=`expr $f - 1`
	LEN=`expr 2 \* $LEN`

	for((j=1; j <=$NINST; j++)); do {
	INST=grid${f}_${j}.drh
	echo $INST
	CMD="dReachD -k ${LEN} ${INST}"
	CMD1="dReach -k ${LEN} ${INST}"
	echo $CMD
	runtime=$( time ( $CMD ) 2>&1  1>/dev/null)
	echo $runtime
	echo $CMD1
	runtime1=$( time ( $CMD1 ) 2>&1  1>/dev/null)
	echo $runtime1
	echo $f $j $runtime $runtime1 >> grid.out
}; done
}; done
