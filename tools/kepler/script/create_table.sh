#!/bin/bash
CATEGORY="sat unsat Timeout"
SMT_STAT=~/work/dreal2/tools/smt2_stat/main.native

for CAT in sat unsat Timeout
do
	for SMT in `ls $CAT/*.smt2`
	do
		BASE=${SMT//.smt2/}
		ID=`cat $BASE.id`
		RESULT=`cat $BASE.result`
		TRACE=$BASE.trace
		TIME=`cat $BASE.time`
		OUT=$BASE.out
		NUM_ARITH=`$SMT_STAT $SMT | grep "Arith" | cut -d ':' -f 2`
		NUM_MATH=`$SMT_STAT $SMT | grep "Math" | cut -d ':' -f 2`
		SIZE=`stat --printf="%s" $TRACE`
#		echo $CAT $ID $NUM_ARITH $NUM_MATH $TIME $RESULT $TRACE

		printf " %5s" `basename $BASE`
		printf "|%30s" "$ID"
		printf "|%7d|%4d" $NUM_ARITH $NUM_MATH
		if [ "$CAT" ==  "Timeout" ]
		then
			printf "|%10s" TIMEOUT
		else
			printf "|%10s" $TIME
		fi
		printf "|%10s" $CAT
		if [ "$CAT" == "unsat" ]
		then
			printf "|%'15d" $SIZE
		else
			printf "|%15s" ""
		fi
		printf "\n"
			
	done
done
