#!/usr/bin/env bash
DREAL=$1
INSTANCE=$2
EXPECTED_OUT=$2.expected
TMP=$2.out

$DREAL --ode-grid=1024 $INSTANCE | tee $TMP
diff $TMP $EXPECTED_OUT
RESULT=$?
rm $TMP
exit $RESULT
