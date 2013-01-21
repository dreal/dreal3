#!/bin/bash
CATEGORY="sat unsat Timeout"
SMT_STAT=~/work/dreal2/tools/smt2_stat/main.native
TEMP=`mktemp`
for CAT in `find . -maxdepth 1 -mindepth 1 -type d`
do
	CAT=`basename $CAT`
	for SMT in `ls $CAT/*.smt2`
	do
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
		OUT=$BASE.out
		NUM_ARITH=`$SMT_STAT $SMT | grep "Arith" | cut -d ':' -f 2`
		NUM_MATH=`$SMT_STAT $SMT | grep "Math" | cut -d ':' -f 2`
		SIZE=`stat --printf="%s" $TRACE`
#		echo $CAT $ID $NUM_ARITH $NUM_MATH $TIME $RESULT $TRACE

		printf " %10s" `basename $BASE`
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
