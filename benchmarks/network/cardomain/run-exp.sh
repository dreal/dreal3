#!/bin/bash

ulimit -t 1200

MAX=10

TIMEFORMAT='%2R'
OPT=--no-hybrid-clause-learning



echo "++++++++++++++++++ Single nonLinear heuristic  +++++++++++++++"
 ./gen-nonlinear-single.sh 1 > car-1-single-nonlinear.drh
time dReach -u 12 -l 12 -r -n car-1-single-nonlinear.drh --precision 0.1 --stat   2>&1 > /dev/null
for ((i=2; i <= $MAX; i++)); do {
    ./gen-nonlinear-single.sh $i > car-$i-single-nonlinear.drh
    time    dReach -u 10 -l 10 -r -n car-$i-single-nonlinear.drh --precision 0.1 --stat   2>&1 > /dev/null 
}    ; done


echo "++++++++++++++++++ Single nonLinear heuristic no-cl  +++++++++++++++"
 ./gen-nonlinear-single.sh 1 > car-1-single-nonlinear.drh
time dReach -u 12 -l 12 -r -n car-1-single-nonlinear.drh --precision 0.1 --stat $OPT   2>&1 > /dev/null
for ((i=2; i <= $MAX; i++)); do {
    ./gen-nonlinear-single.sh $i > car-$i-single-nonlinear.drh
    time    dReach -u 10 -l 10 -r -n car-$i-single-nonlinear.drh --precision 0.1 --stat $OPT   2>&1 > /dev/null 
}    ; done


echo "++++++++++++++++++ Single nonLinear   +++++++++++++++"
 ./gen-nonlinear-single.sh 1 > car-1-single-nonlinear.drh
time dReach -u 12 -l 12 -d -n car-1-single-nonlinear.drh --precision 0.1 --stat  $OPT  2>&1 > /dev/null
for ((i=2; i <= $MAX; i++)); do {
    ./gen-linear-single.sh $i > car-$i-single-nonlinear.drh
    time    dReach -u 10 -l 10 -d -n car-$i-single-nonlinear.drh --precision 0.1 --stat $OPT  2>&1 > /dev/null 
}    ; done


echo "++++++++++++++++++ Single Linear heuristic no-cl +++++++++++++++"
 ./gen-linear-single.sh 1 > car-1-single-linear.drh
time dReach -u 12 -l 12 -r -n car-1-single-linear.drh --precision 0.1 --stat  $OPT  2>&1 > /dev/null
for ((i=2; i <= $MAX; i++)); do {
    ./gen-linear-single.sh $i > car-$i-single-linear.drh
    time    dReach -u 10 -l 10 -r -n car-$i-single-linear.drh --precision 0.1 --stat $OPT  2>&1 > /dev/null 
}    ; done






echo "++++++++++++++++++ Flat nonLinear  +++++++++++++++"
time dReach -u 6 -l 6 -d  car-1-flat-nonlinear.drh --precision 0.1 --stat $OPT  2>&1 > /dev/null
for ((i=2; i <= $MAX; i++)); do {
    #./gen-linear-single.sh $i > car-$i-single-linear-no-acc-no-lock.drh
    time  dReach -u 5 -l 5 -d  car-$i-flat-nonlinear.drh --precision 0.1 --stat $OPT  2>&1 > /dev/null 
}    ; done

echo "++++++++++++++++++ Flat nonLinear Heuristic no-cl +++++++++++++++"
time dReach -u 6 -l 6 -r  car-1-flat-nonlinear.drh --precision 0.1 --stat   2>&1 > /dev/null
for ((i=2; i <= $MAX; i++)); do {
    #./gen-linear-single.sh $i > car-$i-single-linear-no-acc-no-lock.drh
    time  dReach -u 5 -l 5 -r  car-$i-flat-nonlinear.drh --precision 0.1 --stat   2>&1 > /dev/null 
}    ; done
echo "++++++++++++++++++ Flat nonLinear Heuristic +++++++++++++++"
time dReach -u 6 -l 6 -r  car-1-flat-nonlinear.drh --precision 0.1 --stat $OPT  2>&1 > /dev/null
for ((i=2; i <= $MAX; i++)); do {
    #./gen-linear-single.sh $i > car-$i-single-linear-no-acc-no-lock.drh
    time  dReach -u 5 -l 5 -r  car-$i-flat-nonlinear.drh --precision 0.1 --stat $OPT  2>&1 > /dev/null 
}    ; done


echo "++++++++++++++++++ Flat Linear Heuristic +++++++++++++++"
time dReach -u 6 -l 6 -r  car-1-flat-linear.drh --precision 0.1 --stat  2>&1 > /dev/null
for ((i=2; i <= $MAX; i++)); do {
    #./gen-linear-single.sh $i > car-$i-single-linear-no-acc-no-lock.drh
    time  dReach -u 5 -l 5 -r  car-$i-flat-linear.drh --precision 0.1 --stat   2>&1 > /dev/null 
}    ; done


echo "++++++++++++++++++ Flat Linear Heuristic no-cl +++++++++++++++"
time dReach -u 6 -l 6 -r  car-1-flat-linear.drh --precision 0.1 --stat $OPT 2>&1 > /dev/null
for ((i=2; i <= $MAX; i++)); do {
    #./gen-linear-single.sh $i > car-$i-single-linear-no-acc-no-lock.drh
    time  dReach -u 5 -l 5 -r  car-$i-flat-linear.drh --precision 0.1 --stat $OPT  2>&1 > /dev/null 
}    ; done

echo "++++++++++++++++++ Flat Linear  +++++++++++++++"
time dReach -u 6 -l 6 -r  car-1-flat-linear.drh --precision 0.1 --stat  $OPT 2>&1 > /dev/null
for ((i=2; i <= $MAX; i++)); do {
    #./gen-linear-single.sh $i > car-$i-single-linear-no-acc-no-lock.drh
    time  dReach -u 5 -l 5 -d  car-$i-flat-linear.drh --precision 0.1 --stat  $OPT 2>&1 > /dev/null 
}    ; done



echo "++++++++++++++++++ Composed Single Linear   +++++++++++++++"
 ./gen-linear-single.sh 1 > car-1-single-linear.drh
time dReach -u 12 -l 12 -d -c car-1-single-linear.drh --precision 0.1 --stat  $OPT  2>&1 > /dev/null
for ((i=2; i <= $MAX; i++)); do {
    ./gen-linear-single.sh $i > car-$i-single-linear.drh
    time    dReach -u 10 -l 10 -d -c car-$i-single-linear.drh --precision 0.1 --stat $OPT  2>&1 > /dev/null 
}    ; done


echo "++++++++++++++++++ Composed Single Linear heuristic  +++++++++++++++"
 ./gen-linear-single.sh 1 > car-1-single-linear.drh
time dReach -u 12 -l 12 -r -c car-1-single-linear.drh --precision 0.1 --stat  $OPT  2>&1 > /dev/null
for ((i=2; i <= $MAX; i++)); do {
    ./gen-linear-single.sh $i > car-$i-single-linear.drh
    time    dReach -u 10 -l 10 -r -c car-$i-single-linear.drh --precision 0.1 --stat $OPT  2>&1 > /dev/null 
}    ; done



 


echo "++++++++++++++++++ Flat nonLinear  +++++++++++++++"
time dReach -u 6 -l 6 -r  car-1-flat-nonlinear.drh --precision 0.1 --stat $OPT  2>&1 > /dev/null
for ((i=2; i <= $MAX; i++)); do {
    #./gen-linear-single.sh $i > car-$i-single-linear-no-acc-no-lock.drh
    time  dReach -u 5 -l 5 -d  car-$i-flat-nonlinear.drh --precision 0.1 --stat $OPT  2>&1 > /dev/null 
}    ; done


echo "++++++++++++++++++ Single Linear   +++++++++++++++"
 ./gen-linear-single.sh 1 > car-1-single-linear.drh
time dReach -u 12 -l 12 -d -n car-1-single-linear.drh --precision 0.1 --stat $OPT   2>&1 > /dev/null
for ((i=2; i <= 4; i++)); do {
    ./gen-linear-single.sh $i > car-$i-single-linear.drh
    time    dReach -u 10 -l 10 -d -n car-$i-single-linear.drh --precision 0.1 --stat $OPT  2>&1 > /dev/null 
}    ; done

