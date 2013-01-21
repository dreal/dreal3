#!/bin/bash
######################################
#
######################################

# dReal Path
DREAL=~/work/dreal2/dReal
TIMEOUT3=~/work/dreal2/tools/kepler/script/timeout3
TIMEUTIL=/usr/bin/time
INEQ_PATHNAME=$1
RESULTDIR=$2
INEQ=`basename $INEQ_PATHNAME`
BASE=${RESULTDIR}/${INEQ//.smt2/}
SMT=$BASE.smt2
OUTFILE=$BASE.out
TRACEFILE=$BASE.trace
TIMEFILE=$BASE.time
RESULTFILE=$BASE.result
TIMEOUT_TIME=1800 # 600 sec = 30 min

# Copy SMT to the Result DIR
if [ ! -f $SMT ]
then
	cp $INEQ_PATHNAME $SMT
fi

echo -n "Run dReal: $INEQ - "
$TIMEUTIL -f "%E" -o $TIMEFILE $TIMEOUT3 -t $TIMEOUT_TIME $DREAL $SMT 2> $OUTFILE > $TRACEFILE
EXITCODE=$?
if [ $EXITCODE -eq 137 ]
then
	echo "Timeout" | tee $RESULTFILE
else
	if [ $EXITCODE -eq 0 ]
	then
		echo -n "`cat $TIMEFILE` - "
		RESULT=`tail -n 1 $TRACEFILE`
		echo "$RESULT" | tee $RESULTFILE
	else
		echo "Fail" | tee $RESULTFILE
	fi
fi
