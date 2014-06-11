#!/bin/bash

ulimit -t 600

NUM=10
NINST=10
TIMEFORMAT="%U"

echo "Size Heuristic Orig" >> grid.out
for((i=1; i <=$NUM; i++)); do {
	f=`expr $i \* 5`
   	echo "DELTA = ${d} STEPS = ${f}"
	LEN=`expr $f - 1`
	LEN=`expr 2 \* $LEN`

	for((j=1; j <=$NINST; j++)); do {
	INST=grid${f}_${j}.drh
	echo $INST
	LINE="${f} ${j}"
	for c in "-b" "-r"   ; do {
	CMD="dReach ${c} -k ${LEN} ${INST} --delta --delta_heuristic"
	echo $CMD
	runtime=$( time ( $CMD ) 2>&1  1>/tmp/grid-ob.tmp)
	echo $runtime
#	cat /tmp/grid-sat.tmp 
#	SATNODES=`cat /tmp/grid-ob.tmp | grep "nodes:" | cut -f 2 -d " "`
#	NRANODES=`cat /tmp/grid-ob.tmp | grep "nodes:" | cut -f 3 -d " "`
	FAIL=`cat /tmp/grid-ob.tmp | grep "There is no" `
	if [ -n "${FAIL}" ]; then
	    runtime="?"
#	    SATNODES="?"
#	    NRANODES="?"
	fi
	LINE=${LINE}" "${runtime} #" "${SATNODES}" "${NRANODES}
	
	
}; done
	echo $LINE >> grid.out

}; done
}; done
