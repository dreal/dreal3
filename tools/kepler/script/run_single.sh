#!/bin/bash
DREAL=../../../dReal/opensmt/dReal
INEQDIR=../../../dReal/flyspeck_ineqs
TIMEUTIL=/usr/bin/time
RESULTDIR=./result
INEQ_PATHNAME=$1
INEQ=`basename $INEQ_PATHNAME`
BASE=$RESULTDIR/${INEQ}
OUTFILE=$BASE.out
TIMEFILE=$BASE.time
RESULTFILE=$BASE.result
IDFILE=$BASE.ID
ID=`head -n 3 $INEQ_PATHNAME | grep "ID" | sed 's/.*ID\[\([^]]\+\)\].*/\1/g'`
TIMEOUT_TIME=600 # 600 sec = 10 min

echo -n "$INEQ - $ID -"
echo $ID > $IDFILE
$TIMEUTIL -f "%E" -o $TIMEFILE ./timeout3 -t $TIMEOUT_TIME $DREAL $INEQ_PATHNAME &> $OUTFILE
EXITCODE=$?
if [ $EXITCODE -eq 137 ]
then
	echo "Timeout" | tee $RESULTFILE
else
	if [ $EXITCODE -eq 0 ]
	then
		RESULT=`tail -n 4 $OUTFILE | grep "The formula is " | cut -d ' ' -f 4`
		echo "$RESULT" | tee $RESULTFILE
	else
		echo "Fail" | tee $RESULTFILE
	fi
fi
