#!/bin/bash
RESULTDIR=$1
FLYSPECK_REPO=~/work/dreal2/benchmarks/flyspeck_new
SMT_STAT=~/work/dreal2/tools/smt2_stat/main.native
COUNT_CHECK=`dirname $0`/count_check_stat.sh

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

	printf "%-10s|%-40s|%-10s|%-15s|%-10s|%-10s" "$BASE" "$ID" "$TIME" "$STAT" "$PROOF_SIZE" "$RESULT"

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
			printf "|V|%5d|%5d|%8s|%2s" "$PA" "$FA" "$TIME" "$DEPTH"
		else
			printf "|X|     |     |        |  "
		fi
	else
			printf "|-|     |     |        |  "
	fi
	printf "\n"
done

exit 1

