#!/usr/bin/env bash
DREAL=$1
INSTANCE=$2
INSTANCE_NAME=$3
EXPECTED_OUT=$2.expected
TMP=$2.out



$DREAL --short_sat $INSTANCE | tee $TMP
diff $TMP $EXPECTED_OUT
RESULT=$?
rm $TMP
exit $RESULT
