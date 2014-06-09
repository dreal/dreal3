#!/usr/bin/env bash
DREAL=$1
INSTANCE=$2
EXPECTED_OUT=$2.expected
TMP=$2.out
OPTIONS=--delta --delta_heuristic --short_sat

$DREAL $OPTIONS $INSTANCE | tee $TMP
diff $TMP $EXPECTED_OUT
RESULT=$?
rm $TMP
exit $RESULT
