#!/bin/bash
######################################
#
######################################

# dReal Path
DREAL=../../../dReal
TIMEUTIL=/usr/bin/time
RESULTDIR=./result
INEQ_PATHNAME=$1
INEQ=`basename $INEQ_PATHNAME`
BASE=$RESULTDIR/${INEQ//.smt2/}
OUTFILE=$BASE.out
TRACEFILE=$BASE.trace
TIMEFILE=$BASE.time
RESULTFILE=$BASE.result
TIMEOUT_TIME=1800 # 600 sec = 30 min

echo -n "$INEQ - "
$TIMEUTIL -f "%E" -o $TIMEFILE timeout3 -t $TIMEOUT_TIME $DREAL $INEQ_PATHNAME 2> $OUTFILE > $TRACEFILE
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
