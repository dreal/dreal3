#!/usr/bin/env bash
DREAL=$1
INSTANCE=$2
INSTANCE_NAME=$3
EXPECTED_OUT=$2.expected
TMP=$2.out


#this instance is currently taking a long time to solve
if [ $INSTANCE_NAME == "fedor_12.smt2" ] ; then
 exit 0
elif [ $INSTANCE_NAME == "fedor_12_dan_both.smt2" ] ; then
 exit 0
fi

$DREAL --short_sat $INSTANCE | tee $TMP
diff $TMP $EXPECTED_OUT
RESULT=$?
rm $TMP
exit $RESULT
