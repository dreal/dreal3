#!/bin/bash
LIMIT=1200
ulimit -t $LIMIT

NUM=10
#TIMEFORMAT="%U"
TIMEFORMAT="%R"

#echo "Size Heuristic Disj Orig" >> grid.out
echo "Size Heuristic Reduced" >> grid.out
for((i=1; i <=10; i++)); do {
	f=`expr $i \* 5`
   	echo "DELTA = ${d} STEPS = ${f}"
	INST=grid${f}.drh
	LEN=`expr $f - 1`
	LEN=`expr 2 \* $LEN`

	LINE="${f}"
#	for c in "-b" "-d" ""; do {
	for c in "" "-d" "-b" "-r"  ; do {

	CMD="dReach ${c} -k ${LEN} ${INST} --delta --delta_heuristic"
	echo $CMD
	runtime=$( time ( $CMD ) 2>&1  1>/tmp/grid-unsat.tmp)
	echo $runtime
	cat /tmp/grid-unsat.tmp
	SATNODES=`cat /tmp/grid-unsat.tmp | grep "nodes:" | cut -f 2 -d " "`
	NRANODES=`cat /tmp/grid-unsat.tmp | grep "nodes:" | cut -f 3 -d " "`

	SUCC=`cat /tmp/grid-unsat.tmp | grep "unsat" `
	if [ -z "${SUCC}" ]; then
	    runtime="?"
	fi
	LINE=${LINE}" "${runtime}" "${SATNODES}" "${NRANODES}
	
}; done
	echo $LINE >> grid.out
}; done
