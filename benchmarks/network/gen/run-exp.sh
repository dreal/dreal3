#!/bin/bash

ulimit -t 1200
MIN=6
MAX=10

TIMEFORMAT='%2R'

OPT=--no-hybrid-clause-learning







echo "++++++++++++++++++ Flat nonLinear  +++++++++++++++"
for ((i=0; i <= $MAX; i++)); do {
     A=`expr 2 \* $i`
    ./gen-flat-nonlinear.sh $i > gen-$i-flat-nonlinear.drh
    time  dReach -u `expr 3 + $A` -l `expr 3 + $A` -d  gen-$i-flat-nonlinear.drh --precision 0.1 --stat     2>&1 > /dev/null
} ; done


echo "++++++++++++++++++ Flat nonLinear Heuristic +++++++++++++++"
for ((i=0; i <= $MAX; i++)); do {
     A=`expr 2 \* $i`
    ./gen-flat-nonlinear.sh $i > gen-$i-flat-nonlinear.drh
    time   dReach -u `expr 3 + $A` -l `expr 3 + $A` -r  gen-$i-flat-nonlinear.drh --precision 0.1 --stat     2>&1 > /dev/null
} ; done

echo "++++++++++++++++++ Flat nonLinear Heuristic no-cl +++++++++++++++"
for ((i=0; i <= $MAX; i++)); do {
     A=`expr 2 \* $i`
    ./gen-flat-nonlinear.sh $i > gen-$i-flat-nonlinear.drh
    time   dReach -u `expr 3 + $A` -l `expr 3 + $A` -r  gen-$i-flat-nonlinear.drh --precision 0.1 --stat  $OPT   2>&1 > /dev/null
} ; done


     echo "++++++++++++++++++ Composed Nonlinear  +++++++++++++++"


for ((i=0; i <= $MAX; i++)); do {
    ./gen-nonlinear-single.sh $i > gen-$i-single-nonlinear.drh
    A=`expr 4 \* $i`
     time dReach -u `expr 3 + $A` -l `expr 3 + $A` -d  -c gen-$i-single-nonlinear.drh --precision 0.1 --stat 2>&1 > /tmp/dan
}; done




echo "++++++++++++++++++ Composed Nonlinear Heuristic +++++++++++++++"


for ((i=0; i <= $MAX; i++)); do {
    ./gen-nonlinear-single.sh $i > gen-$i-single-nonlinear.drh
    A=`expr 4 \* $i`
     time dReach -u `expr 3 + $A` -l `expr 3 + $A` -r  -c gen-$i-single-nonlinear.drh --precision 0.1 --stat 2>&1 > /tmp/dan
}; done


echo "++++++++++++++++++ Composed Nonlinear Heuristic no-cl +++++++++++++++"


for ((i=0; i <= $MAX; i++)); do {
    ./gen-nonlinear-single.sh $i > gen-$i-single-nonlinear.drh
    A=`expr 4 \* $i`
     time dReach -u `expr 3 + $A` -l `expr 3 + $A` -r  -c gen-$i-single-nonlinear.drh --precision 0.1 --stat $OPT 2>&1 > /tmp/dan
}; done
     echo "++++++++++++++++++ Single Nonlinear  +++++++++++++++"


for ((i=0; i <= $MAX; i++)); do {
    ./gen-nonlinear-single.sh $i > gen-$i-single-nonlinear.drh
    A=`expr 4 \* $i`
     time dReach -u `expr 3 + $A` -l `expr 3 + $A` -d  -n gen-$i-single-nonlinear.drh --precision 0.1 --stat 2>&1 > /tmp/dan 
    } ; done



echo "++++++++++++++++++ Single Nonlinear Heuristic +++++++++++++++"


for ((i=0; i <= $MAX; i++)); do {
    ./gen-nonlinear-single.sh $i > gen-$i-single-nonlinear.drh
    A=`expr 4 \* $i`
    time dReach -u `expr 3 + $A` -l `expr 3 + $A` -r  -n gen-$i-single-nonlinear.drh --precision 0.1 --stat   2>&1 > /tmp/dan
} ; done
echo "++++++++++++++++++ Single Nonlinear Heuristic no-cl +++++++++++++++"


for ((i=0; i <= $MAX; i++)); do {
    ./gen-nonlinear-single.sh $i > gen-$i-single-nonlinear.drh
    A=`expr 4 \* $i`
    time dReach -u `expr 3 + $A` -l `expr 3 + $A` -r  -n gen-$i-single-nonlinear.drh --precision 0.1 --stat  $OPT 2>&1 > /tmp/dan
} ; done









echo "++++++++++++++++++ Composed Nonlinear  +++++++++++++++"


for ((i=0; i <= $MAX; i++)); do {
    ./gen-nonlinear-single.sh $i > gen-$i-single-nonlinear.drh
    A=`expr 4 \* $i`
     time dReach -u `expr 3 + $A` -l `expr 3 + $A` -d  -c gen-$i-single-nonlinear.drh --precision 0.1 --stat 2>&1 > /tmp/dan
} ; done

echo "++++++++++++++++++ Single Linear  +++++++++++++++"
for ((i=0; i <= $MAX; i++)); do {
    ./gen-linear-single.sh $i > gen-$i-single-linear.drh
    A=`expr 4 \* $i`
     time dReach -u `expr 3 + $A` -l `expr 3 + $A` -d  -n gen-$i-single-linear.drh --precision 0.1 --stat 2>&1 > /tmp/dan 
    } ; done



echo "++++++++++++++++++ Single Linear Heuristic +++++++++++++++"
for ((i=0; i <= $MAX; i++)); do {
    ./gen-flat-linear.sh $i > gen-$i-flat-linear.drh
    A=`expr 4 \* $i`
    time dReach -u `expr 3 + $A` -l `expr 3 + $A` -r  gen-$i-flat-linear.drh --precision 0.1 --stat $OPT 2>&1 > /tmp/dan 
} ; done


echo "++++++++++++++++++ Flat Linear Heuristic +++++++++++++++"
for ((i=0; i <= $MAX; i++)); do {
     A=`expr 2 \* $i`
    ./gen-flat-linear.sh $i > gen-$i-flat-linear.drh
    time   dReach -u `expr 3 + $A` -l `expr 3 + $A` -r  gen-$i-flat-linear.drh --precision 0.1 --stat     2>&1 > /dev/null
} ; done

echo "++++++++++++++++++ Flat Linear Heuristic, no learn +++++++++++++++"
for ((i=0; i <= $MAX; i++)); do {
     A=`expr 2 \* $i`
    ./gen-flat-linear.sh $i > gen-$i-flat-linear.drh
    time   dReach -u `expr 3 + $A` -l `expr 3 + $A` -r  gen-$i-flat-linear.drh --precision 0.1 --stat  $OPT   2>&1 > /dev/null
} ; done

echo "++++++++++++++++++ Flat Linear  +++++++++++++++"
for ((i=0; i <= $MAX; i++)); do {
     A=`expr 2 \* $i`
    ./gen-flat-linear.sh $i > gen-$i-flat-linear.drh
    time  dReach -u `expr 3 + $A` -l `expr 3 + $A` -d  gen-$i-flat-linear.drh --precision 0.1 --stat     2>&1 > /dev/null
} ; done

echo "++++++++++++++++++  Linear Heuristic, No learning +++++++++++++++"


for ((i=$MIN; i <= $MAX; i++)); do {
    ./gen-linear-multi.sh $i > gen-$i-multi-linear.drh
    A=`expr 4 \* $i`
     time dReach -u `expr 3 + $A` -l `expr 3 + $A` -r  -n gen-$i-multi-linear.drh --precision 0.1 --stat  $OPT 2>&1 > /tmp/dan
} ; done

echo "++++++++++++++++++  Linear Heuristic +++++++++++++++"


for ((i=$MIN; i <= $MAX; i++)); do {
    ./gen-linear-multi.sh $i > gen-$i-multi-linear.drh
    A=`expr 4 \* $i`
     time dReach -u `expr 3 + $A` -l `expr 3 + $A` -r  -n gen-$i-multi-linear.drh --precision 0.1 --stat   2>&1 > /tmp/dan
} ; done




echo "++++++++++++++++++ Composed Linear Heuristic, no learn +++++++++++++++"


for ((i=$MIN; i <= $MAX; i++)); do {
    ./gen-linear-single.sh $i > gen-$i-single-linear.drh
    A=`expr 4 \* $i`
     time dReach -u `expr 3 + $A` -l `expr 3 + $A` -r  -c gen-$i-single-linear.drh --precision 0.1 --stat $OPT  2>&1 > /tmp/dan
} ; done


echo "++++++++++++++++++ Composed Linear  +++++++++++++++"


for ((i=0; i <= $MAX; i++)); do {
    ./gen-linear-single.sh $i > gen-$i-single-linear.drh
    A=`expr 4 \* $i`
    time dReach -u `expr 3 + $A` -l `expr 3 + $A` -d  -c gen-$i-single-linear.drh --precision 0.1 --stat 2>&1 > /tmp/dan 
    } ; done


echo "++++++++++++++++++ Composed Linear Heuristic +++++++++++++++"


for ((i=0; i <= $MAX; i++)); do {
    ./gen-linear-single.sh $i > gen-$i-single-linear.drh
    A=`expr 4 \* $i`
     time dReach -u `expr 3 + $A` -l `expr 3 + $A` -r  -c gen-$i-single-linear.drh --precision 0.1 --stat   2>&1 > /tmp/dan
} ; done



echo "++++++++++++++++++  Linear  +++++++++++++++"


for ((i=0; i <= $MAX; i++)); do {
    ./gen-linear-multi.sh $i > gen-$i-multi-linear.drh
    A=`expr 4 \* $i`
     time dReach -u `expr 3 + $A` -l `expr 3 + $A` -d  -n gen-$i-multi-linear.drh --precision 0.1 --stat  $OPT 2>&1 > /tmp/dan
} ; done





