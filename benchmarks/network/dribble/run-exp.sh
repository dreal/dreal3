#!/bin/bash

ulimit -t 1200

MIN=21
MAX=30

TIMEFORMAT='%2R'
OPTS="--no-hybrid-clause-learning"










echo "++++++++++++++++++ Flat NonLinear Heuristic +++++++++++++++"


 
for ((i=$MIN; i <= $MAX; i++)); do {
    K=`expr $i \* 2`
    time dReach -u $K -l $K -r dribble-flat.drh --precision 0.1 --stat  2>&1 > /tmp/dan3
}    ; done

echo "++++++++++++++++++ Flat NonLinear Heuristic no-cl +++++++++++++++"


 
for ((i=$MIN; i <= $MAX; i++)); do {
    K=`expr $i \* 2`
    time dReach -u $K -l $K -r dribble-flat.drh --precision 0.1 --stat $OPTS 2>&1 > /tmp/dan3
}    ; done



echo "++++++++++++++++++ Single NonLinear Heuristic +++++++++++++++"


 
for ((i=$MIN; i <= $MAX; i++)); do {
    K=`expr $i \* 4`
    time dReach -u $K -l $K -r -n dribble-net.drh --precision 0.1 --stat  2>&1 > /tmp/dan3 
}    ; done



echo "++++++++++++++++++ Single NonLinear Heuristic no-cl +++++++++++++++"


 
for ((i=$MIN; i <= $MAX; i++)); do {
    K=`expr $i \* 4`
    time dReach -u $K -l $K -r -n dribble-net.drh --precision 0.1 --stat $OPTS 2>&1 > /tmp/dan3 
}    ; done


echo "++++++++++++++++++ Single NonLinear  +++++++++++++++"

 
for ((i=$MIN; i <= $MAX; i++)); do {
    K=`expr $i \* 4`
     time dReach -u $K -l $K -d -n dribble-net.drh --precision 0.1 --stat $OPTS 2>&1 > /tmp/dan3 
}    ; done






echo "++++++++++++++++++ Flat NonLinear  +++++++++++++++"

for ((i=$MIN; i <= $MAX; i++)); do {
    K=`expr $i \* 2`
     time dReach -u $K -l $K -d dribble-flat.drh --precision 0.1 --stat $OPTS 2>&1 > /tmp/dan3 
}    ; done


echo "++++++++++++++++++ Single NonLinear Heuristic Composed +++++++++++++++"


 
for ((i=$MIN; i <= $MAX; i++)); do {
    K=`expr $i \* 4`
     time dReach -u $K -l $K -r -c dribble-net.drh --precision 0.1 --stat  2>&1 > /tmp/dan3 
}    ; done


echo "++++++++++++++++++ Single NonLinear Heuristic Composed no-cl +++++++++++++++"


 
for ((i=$MIN; i <= $MAX; i++)); do {
    K=`expr $i \* 4`
     time dReach -u $K -l $K -r -c dribble-net.drh --precision 0.1 --stat $OPTS 2>&1 > /tmp/dan3 
}    ; done


echo "++++++++++++++++++ Single NonLinear Composed +++++++++++++++"


 
for ((i=$MIN; i <= $MAX; i++)); do {
    K=`expr $i \* 4`
     time dReach -u $K -l $K -d -c dribble-net.drh --precision 0.1 --stat $OPTS 2>&1 > /tmp/dan3 
}    ; done
