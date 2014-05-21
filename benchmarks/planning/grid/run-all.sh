#!/bin/bash
LIMIT=1200
ulimit -t $LIMIT

NUM=10
#TIMEFORMAT="%U"
TIMEFORMAT="%R"

echo "Size Heuristic Disj Orig" >> grid.out
for((i=1; i <=10; i++)); do {
	f=`expr $i \* 2`
   	echo "DELTA = ${d} STEPS = ${f}"
	INST=grid${f}.drh
	LEN=`expr $f - 1`
	LEN=`expr 2 \* $LEN`

	LINE="${f}"
	for c in "-b" "-d" ""; do {
	CMD="dReach ${c} -k ${LEN} ${INST}"
	echo $CMD
	runtime=$( time ( $CMD ) 2>&1  1>/tmp/grid-sat.tmp)
	echo $runtime
	cat /tmp/grid-sat.tmp
	FAIL=`cat /tmp/grid-sat.tmp | grep "There is no" `
	if [ -n "${FAIL}" ]; then
	    runtime="?"
	fi
	LINE=${LINE}" "${runtime}
	
}; done
	echo $LINE >> grid.out
}; done
