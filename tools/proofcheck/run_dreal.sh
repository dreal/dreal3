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

function log_msg {
	echo -n "`date`: "
	printf "[%-30s]: " `basename $1`
	echo $2
}

# Copy SMT to the Result DIR
if [ ! -f $SMT ]
then
	cp $SMT_PATHNAME $SMT
fi

log_msg $SMT "dReal started"
$TIMEUTIL -f "%E" -o $TIMEFILE $TIMEOUT3 -t $TIMEOUT_TIME $DREAL --verbose --proof $SMT 2> $OUTFILE 1> $RESULTFILE
EXITCODE=$?
if [ $EXITCODE -eq 137 ]
then
	log_msg $SMT "dReal Timeout ($TIMEOUT_TIME sec)"
	echo "Timeout" > $RESULTFILE
else
	if [ $EXITCODE -eq 0 ]
	then
                mv $SMT.proof $TRACEFILE
		log_msg $SMT "dReal finished - `cat $TIMEFILE`"
	else
		log_msg $SMT "dReal failed - $EXITCODE"
		echo "Fail" > $RESULTFILE
	fi
fi
