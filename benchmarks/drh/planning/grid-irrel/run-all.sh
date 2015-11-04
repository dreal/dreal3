#!/bin/bash
LIMIT=1200
ulimit -t $LIMIT

NUM=10
#TIMEFORMAT="%U"
TIMEFORMAT="%R"

echo "Size Heuristic Reduced" >> grid.out
for((i=1; i <=10; i++)); do {
	f=`expr $i \* 5`
	for((j=0; j <=5; j++)); do {
	       	g=`expr $j \* 10`
   	echo "DELTA = ${d} STEPS = ${f} IRREL = ${g}"
	INST=grid${f}_${g}.drh
	LEN=`expr $f - 1`
	LEN=`expr 2 \* $LEN`

	LINE="${f} ${g}"
	for c in "-r" "-e"   ; do {
	CMD="dReach ${c} -k ${LEN} ${INST} --delta --delta_heuristic"
	echo $CMD
	runtime=$( time ( $CMD ) 2>&1  1>/tmp/grid-sat.tmp)
	echo $runtime
#	cat /tmp/grid-sat.tmp 
	SATNODES=`cat /tmp/grid-sat.tmp | grep "nodes:" | cut -f 2 -d " "`
	NRANODES=`cat /tmp/grid-sat.tmp | grep "nodes:" | cut -f 3 -d " "`
	FAIL=`cat /tmp/grid-sat.tmp | grep "There is no" `
	if [ -n "${FAIL}" ]; then
	    runtime="?"
	    SATNODES="?"
	    NRANODES="?"
	fi
	LINE=${LINE}" "${runtime}" "${SATNODES}" "${NRANODES}
	
}; done
	echo $LINE >> grid.out
}; done
}; done

