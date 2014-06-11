#!/usr/bin/env bash
DREAL=$1
INSTANCE=$2
INSTANCE_NAME=$3
EXPECTED_OUT=$2.expected
OPTION=
if [[ -e $2.option ]]
then
    OPTION=`cat $2.option`
fi
TMP=$2.out

echo $DREAL $OPTION $INSTANCE
$DREAL $OPTION --short_sat $INSTANCE | tee $TMP
diff $TMP $EXPECTED_OUT
RESULT=$?
rm $TMP
exit $RESULT
