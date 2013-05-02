#!/bin/bash
# Author: Soonho Kong <soonhok@cs.cmu.edu>

RESULTDIR=$1
FLYSPECK_REPO=~/work/dreal2/benchmarks/flyspeck_new
SMT_STAT=~/work/dreal2/tools/smt2_stat/main.native
COUNT_CHECK=`dirname $0`/count_check_stat.sh
DELIM=","

# Print Header
echo "filename,id,stime,num_vars,num_arith,num_poly,psize,result,pchecked,num_paxioms,num_subprob,ptime,pdepth"

# Print Content
for SMT in `find $RESULTDIR -maxdepth 1 -name "*.smt2"`
do
	BASE=`basename ${SMT/%.smt2}`
	ID=`cat $FLYSPECK_REPO/$BASE.id`
	RESULT=`cat $RESULTDIR/$BASE.result`
	TIME=`tail -n 1 $RESULTDIR/$BASE.time`
	if [[ "$RESULT" == "unknown" ]]
	then
		RESULT=Timeout
	fi
	if [[ "$RESULT" == "Fail" ]]
	then
		TIME="X"
	fi
		
	PROOF=$RESULTDIR/$BASE.trace
	PROOFDIR=$RESULTDIR/$BASE.smt2.proof.extra
	STAT=`$SMT_STAT $SMT | perl -ne 'chomp and print'`
	PROOF_SIZE="NO PROOF"
	if [[ -f $PROOF ]]
	then
		PROOF_SIZE=`stat --printf="%s" $PROOF`
	fi

	if [[ -f $PROOFDIR/$BASE.trace ]]
	then
		PROOF_SIZE=`stat --printf="%s" $PROOFDIR/$BASE.trace`
	fi

	if [[ -f $RESULTDIR/$BASE.smt2.proof ]]
	then
		PROOF_SIZE=`stat --printf="%s" $RESULTDIR/$BASE.smt2.proof`
	fi

	printf "%-10s${DELIM}%-40s${DELIM}%-10s${DELIM}%-15s${DELIM}%-10s${DELIM}%-10s" "$BASE" "$ID" "$TIME" "$STAT" "$PROOF_SIZE" "$RESULT"

	if [[ "$RESULT" == "unsat" ]]
	then
		if [[ -f $PROOFDIR/PROVED ]]
		then
			# 2. How many Proved Axioms?
			CHECK_STAT=`$COUNT_CHECK $PROOFDIR`
			PA=`echo $CHECK_STAT | cut -d '|' -f 2`
			FA=`echo $CHECK_STAT | cut -d '|' -f 1`
			TIME=`echo $CHECK_STAT | cut -d '|' -f 6`
			DEPTH=`echo $CHECK_STAT | cut -d '|' -f 7`
			printf "${DELIM}V${DELIM}%5d${DELIM}%5d${DELIM}%8s${DELIM}%2s" "$PA" "$FA" "$TIME" "$DEPTH"
		else
			printf "${DELIM}X${DELIM}     ${DELIM}     ${DELIM}       ${DELIM}"
		fi
	else
			printf "${DELIM}-${DELIM}     ${DELIM}     ${DELIM}       ${DELIM}"
	fi
	printf "\n"
done

exit 1

