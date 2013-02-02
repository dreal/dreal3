#!/bin/bash
SMT_STAT=~/work/dreal2/tools/smt2_stat/main.native
TEMP=`mktemp`
for CAT in `find result/ -maxdepth 1 -mindepth 1 -type d`
do
	for SMT in `ls $CAT/*.smt2`
	do
		CAT=`basename $CAT`
		grep -v "^(set-info :source .*)" $SMT > $TEMP
		mv $TEMP $SMT
		BASE=${SMT//.smt2/}
		if [ -f $BASE.id ] 
		then
			ID=`cat $BASE.id`
		else
			ID=""
		fi
		RESULT=`cat $BASE.result`
		TRACE=$BASE.trace
		TIME=`cat $BASE.time`


		if [ "$CAT" ==  "Timeout" ]
		then
			TIME="TIMEOUT"
		fi
		
		NUM_ARITH=`$SMT_STAT $SMT | grep "Arith" | cut -d ':' -f 2`
		NUM_MATH=`$SMT_STAT $SMT | grep "Math" | cut -d ':' -f 2`

		printf "%10s" `basename $BASE`
		printf "|%30s" "$ID"
		printf "|%7d|%4d" $NUM_ARITH $NUM_MATH
		printf "|%10s" $TIME
		if [ "$CAT" == "unsat" ]
		then
			if [ -f $TRACE ]
			then
				SIZE=`stat --printf="%s" $TRACE`
				printf "|%'15d" $SIZE
			else
				SIZE=0
			fi
		else
			printf "|%15s" ""
		fi
		printf "|%10s" $CAT

		# 1. Verified?
		UNSAT_DIR=`basename $BASE`
		if [ -f $UNSAT_DIR/PROVED ]
		then
			CHECK_STAT=`./count_check_stat.sh $UNSAT_DIR`
			
			# 2. How many Proved Axioms?
			PA=`echo $CHECK_STAT | cut -d '|' -f 2`
			FA=`echo $CHECK_STAT | cut -d '|' -f 1`
			TIME=`echo $CHECK_STAT | cut -d '|' -f 6`
			DEPTH=`echo $CHECK_STAT | cut -d '|' -f 7`

			printf "|V|%5d|%5d|%8s|%2s" "$PA" "$FA" "$TIME" "$DEPTH"
		else
			printf "| |     |     |        |  "
		fi

		printf "\n"
	done
done
