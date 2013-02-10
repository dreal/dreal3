#!/bin/bash

SMTDIR=$1
RESULTDIR=$2
DREAL=~/work/dreal2/dReal
RUN_DREAL=`dirname $0`/../proofcheck/run_dreal.sh
PROOFCHECK=`dirname $0`/../proofcheck/proofcheck.sh
TIMEOUT=1800

function log_msg {
	echo -n "`date`: "
	printf "[%-30s]: " `basename $1`
	echo $2
}

for SMT in `find $SMTDIR -name "*.smt2"`
do
	BASE=`basename ${SMT/%.smt2}`
	RESULT=$RESULTDIR/${BASE}.result
	TRACE=$RESULTDIR/${BASE}.trace
	PROOF=$RESULTDIR/${BASE}.smt2.proof
	# Run dReal (if necessary)
	if [[ ! -f $RESULT ]]
	then
		$RUN_DREAL $SMT $RESULTDIR $DREAL $TIMEOUT
	fi

	# Run Proof Check
	# if the result is unsat
	# if SMT doesn't contain ITE
	if [[ "`cat $RESULT`" == "unsat" ]]
	then
		if grep -q "ite" "$SMT"
		then
			log_msg $SMT "unsat but it containts ITE and we do not check its proof."
		else
			log_msg $SMT "unsat and we check its proof."
			mv $TRACE $PROOF
			$PROOFCHECK -t $TIMEOUT $PROOF
		fi
	else
		log_msg $SMT "`cat $RESULT`."
	fi
	# extract information and construct table
done
