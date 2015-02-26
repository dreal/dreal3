#!/usr/bin/env bash
DREAL=$1
INSTANCE=$2
shift 2
EXPECTED_OUT=${INSTANCE}.expected
TMP=${INSTANCE}.out
OPTIONS=$@
OPTION=
if [[ -e ${INSTANCE}.option ]]
then
    OPTION=`cat ${INSTANCE}.option`
fi
echo $DREAL $OPTIONS $OPTION -- "$INSTANCE"
$DREAL $OPTIONS $OPTION -- "$INSTANCE" | tee $TMP
diff $TMP $EXPECTED_OUT
RESULT=$?
rm $TMP
exit $RESULT
