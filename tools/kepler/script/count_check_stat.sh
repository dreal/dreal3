#!/bin/bash
FA=`grep "Failed Axioms" *.check_stat | cut -d ":" -f 3 | awk '{ SUM += $1} END { print SUM }'`
PA=`grep "Proved Axioms" *.check_stat | cut -d ":" -f 3 | awk '{ SUM += $1} END { print SUM }'`
BR=`grep "Branches Axioms" *.check_stat | cut -d ":" -f 3 | awk '{ SUM += $1} END { print SUM }'`
TP=`grep "Trivial Prune" *.check_stat | cut -d ":" -f 3 | awk '{ SUM += $1} END { print SUM }'`
NP=`grep "non-trivial Prune" *.check_stat | cut -d ":" -f 3 | awk '{ SUM += $1} END { print SUM }'`


START_TIME=`cat START_TIME`
END_TIME=`cat END_TIME`

T_DIFF=$(echo "scale=2; ($END_TIME-$START_TIME) / 1000" | bc -l)

printf "%10s %10s %10s %10s %10s %10s\n"  "FA"  "PA"  "BR"  "TP"  "NP" "SEC"
printf "%10d %10d %10d %10d %10d %10.3f\n" "$FA" "$PA" "$BR" "$TP" "$NP" "$T_DIFF"
