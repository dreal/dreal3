#!/bin/bash

# INPUT
# $1 = .smt pathname
# $2 = RESULTDIR
# $3 = DREAL pathname
# $4 = TIMEOUT

# OUTPUT
# RESULTDIR/nnn.smt2
# RESULTDIR/nnn.out    (dReal output)
# RESULTDIR/nnn.trace  (proof trace)
# RESULTDIR/nnn.time   (time)
# RESULTDIR/nnn.result (Timeout/unsat/sat/Fail)

TIMEOUT3=`dirname $0`/timeout3
TIMEUTIL="env time"
SMT_PATHNAME=$1
RESULTDIR=$2
DREAL=$3
SMT=`basename $SMT_PATHNAME`
BASE=${RESULTDIR}/${SMT/%.smt2/}
SMT=$BASE.smt2
OUTFILE=$BASE.out
TRACEFILE=$BASE.trace
TIMEFILE=$BASE.time
RESULTFILE=$BASE.result
TIMEOUT_TIME=$4

# Copy SMT to the Result DIR
if [ ! -f $SMT ]
then
	cp $SMT_PATHNAME $SMT
fi

echo -n "Run dReal: $SMT - "
$TIMEUTIL -f "%E" -o $TIMEFILE $TIMEOUT3 -t $TIMEOUT_TIME $DREAL --verbose --proof $SMT 2> $OUTFILE
EXITCODE=$?
if [ $EXITCODE -eq 137 ]
then
	echo "Timeout" | tee $RESULTFILE
else
	if [ $EXITCODE -eq 0 ]
	then
                mv $SMT.proof $TRACEFILE
		echo -n "`cat $TIMEFILE` - "
		RESULT=`tail -n 1 $TRACEFILE`
		echo "$RESULT" | tee $RESULTFILE
	else
		echo "Fail" | tee $RESULTFILE
	fi
fi
