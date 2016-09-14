#!/usr/bin/env bash
DREAL=$1
INSTANCE=$2
BASENAME=`basename ${INSTANCE}`
shift 2
EXPECTED_OUT=${INSTANCE}.expected
TMP=`mktemp /tmp/${BASENAME}.out.XXXX`
OPTIONS=$@
OPTION=
if [[ -e ${INSTANCE}.option ]]
then
    OPTION=`cat "${INSTANCE}.option"`
fi
echo ${DREAL} ${OPTIONS} ${OPTION} "${INSTANCE}" "==>" "${TMP}"
"${DREAL}" --suppress-warning ${OPTIONS} ${OPTION} "${INSTANCE}" | tee "${TMP}"
diff "${TMP}" "${EXPECTED_OUT}"
RESULT=$?
rm -- "${TMP}"
exit ${RESULT}
