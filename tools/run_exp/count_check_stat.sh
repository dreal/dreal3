#!/bin/bash
DIR=$1
TMP=`mktemp`

CHECK_STAT_COUNT=`find $DIR -name "*.check_stat" | wc -l`

if (( "$CHECK_STAT_COUNT" > "0" ))
then
	FA=`grep -h "Failed Axioms" $DIR/*.check_stat | cut -d ":" -f 2 | awk '{ SUM += $1} END { print SUM }'`
	PA=`grep -h "Proved Axioms" $DIR/*.check_stat | cut -d ":" -f 2 | awk '{ SUM += $1} END { print SUM }'`
	BR=`grep -h "Branches Axioms" $DIR/*.check_stat | cut -d ":" -f 2 | awk '{ SUM += $1} END { print SUM }'`
	TP=`grep -h "Trivial Prune" $DIR/*.check_stat | cut -d ":" -f 2 | awk '{ SUM += $1} END { print SUM }'`
	NP=`grep -h "non-trivial Prune" $DIR/*.check_stat | cut -d ":" -f 2 | awk '{ SUM += $1} END { print SUM }'`
else
	FA=0
	PA=0
	BR=0
	TP=0
	NP=0
fi

START_TIME=`cat $DIR/START_TIME`
END_TIME=`cat $DIR/END_TIME`

T_DIFF=$(echo "scale=2; ($END_TIME-$START_TIME) / 1000" | bc -l)

for smt in `find $DIR -name "*.smt2"`
do
	grep -o "_" <<< "$smt"  | wc -l
done | sort | uniq | tail -n 1 > $TMP

#printf "%10s %10s %10s %10s %10s %10s %10s\n"  "FA"  "PA"  "BR"  "TP"  "NP" "SEC" "DEPTH"
printf "%d|%d|%d|%d|%d|%.3f|%d\n" "$FA" "$PA" "$BR" "$TP" "$NP" "$T_DIFF" `cat $TMP`

rm $TMP



