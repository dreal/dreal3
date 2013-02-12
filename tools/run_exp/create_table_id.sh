#!/bin/bash
RESULTDIR=$1
FLYSPECK_REPO=~/work/dreal2/benchmarks/flyspeck
SMT_STAT=~/work/dreal2/tools/smt2_stat/main.native
COUNT_CHECK=`dirname $0`/count_check_stat.sh

for SMT in `find $RESULTDIR -maxdepth 1 -name "*.smt2"`
do
	BASE=`basename ${SMT/%.smt2}`
	ID=`cat $FLYSPECK_REPO/$BASE.id`
	TIME=`cat $RESULTDIR/$BASE.time`
	PROOF=$RESULTDIR/$BASE.smt2.proof
	PROOFDIR=$RESULTDIR/$BASE.smt2.proof.extra
	STAT=`$SMT_STAT $SMT | perl -ne 'chomp and print'`
	PROOF_SIZE="NO PROOF"
	if [[ -f $PROOF ]]
	then
		PROOF_SIZE=`stat --printf="%s" $PROOF`
	fi
	RESULT=`cat $RESULTDIR/$BASE.result`
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

