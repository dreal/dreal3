#!/usr/bin/env bash
echo Input: $@
DREACH=$1
CWD=$2
INSTANCE=$3
shift 3
cd "${CWD}"
EXPECTED_OUT=${INSTANCE}.expected
TMP=${INSTANCE}.out
OPTIONS=$@
OPTION=
if [[ -e ${INSTANCE}.option ]]
then
    OPTION=`cat ${INSTANCE}.option`
fi
echo ${DREACH} ${OPTIONS} ${OPTION} "$INSTANCE"
${DREACH} ${OPTIONS} ${OPTION} "$INSTANCE" | tee $TMP
cat ${TMP}
cat ${EXPECTED_OUT}
diff ${TMP} ${EXPECTED_OUT}
RESULT=$?
rm $TMP
exit $RESULT
