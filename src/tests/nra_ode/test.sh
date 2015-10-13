#!/usr/bin/env bash
DREAL=$1
INSTANCE=$2
BASENAME=`basename ${INSTANCE}`
EXPECTED_OUT=${INSTANCE}.expected
shift 2
OPTION=$@
if [[ -e ${INSTANCE}.option ]]
then
    OPTION="${OPTION} `cat ${INSTANCE}.option`"
fi
TMP=`mktemp /tmp/${BASENAME}.out.XXXX`

echo "${DREAL} ${OPTION} ${INSTANCE} ==> ${TMP}"
"${DREAL}" ${OPTION} "${INSTANCE}" | tee "${TMP}"
diff "$TMP" "$EXPECTED_OUT"
RESULT=$?
rm -- "${TMP}"
exit ${RESULT}
