#--no-hybrid-clause-learning
MAX=10
TIMEFORMAT='%2R'


 ulimit -t 1200


 
echo "++++++++++++++++++ Single Nonlinear Heuristic No Acc No Lock (no-cl) +++++++++++++++"

./gen-nonlinear-single-no-acc-no-lock.sh 1 > car-1-single-nonlinear-no-acc-no-lock.drh
time dReach -u 6 -l 6 -r -n car-1-single-nonlinear-no-acc-no-lock.drh --precision 0.1 --stat --no-hybrid-clause-learning 2>&1 > /dev/null

for ((i=2; i <= $MAX; i++)); do {
    ./gen-nonlinear-single-no-acc-no-lock.sh $i > car-$i-single-nonlinear-no-acc-no-lock.drh
    time dReach -u 5 -l 5 -r -n car-$i-single-nonlinear-no-acc-no-lock.drh --precision 0.1 --stat --no-hybrid-clause-learning 2>&1 > /dev/null
}    ; done

echo "++++++++++++++++++ Single Nonlinear Heuristic No Acc No Lock  +++++++++++++++"

./gen-nonlinear-single-no-acc-no-lock.sh 1 > car-1-single-nonlinear-no-acc-no-lock.drh
time dReach -u 6 -l 6 -r -n car-1-single-nonlinear-no-acc-no-lock.drh --precision 0.1 --stat  2>&1 > /dev/null

for ((i=2; i <= $MAX; i++)); do {
     ./gen-nonlinear-single-no-acc-no-lock.sh $i > car-$i-single-nonlinear-no-acc-no-lock.drh
 time    dReach -u 5 -l 5 -r -n car-$i-single-nonlinear-no-acc-no-lock.drh --precision 0.1 --stat  2>&1 > /dev/null
    
}    ; done


echo "++++++++++++++++++ Single Nonlinear  No Acc No Lock  +++++++++++++++"

./gen-nonlinear-single-no-acc-no-lock.sh 1 > car-1-single-nonlinear-no-acc-no-lock.drh
time dReach -u 6 -l 6 -d -n car-1-single-nonlinear-no-acc-no-lock.drh --precision 0.1 --stat  2>&1 > /dev/null

for ((i=2; i <= $MAX; i++)); do {
    ./gen-nonlinear-single-no-acc-no-lock.sh $i > car-$i-single-nonlinear-no-acc-no-lock.drh
    time dReach -u 5 -l 5 -d -n car-$i-single-nonlinear-no-acc-no-lock.drh --precision 0.1 --stat 2>&1 > /dev/null
}    ; done

 

echo "++++++++++++++++++ Composed Linear  No Acc No Lock  +++++++++++++++"

./gen-linear-single-no-acc-no-lock.sh 1 > car-1-single-linear-no-acc-no-lock.drh
time dReach -u 6 -l 6 -d -c car-1-single-linear-no-acc-no-lock.drh --precision 0.1 --stat  2>&1 > /dev/null

for ((i=2; i <= $MAX; i++)); do {
    ./gen-linear-single-no-acc-no-lock.sh $i > car-$i-single-linear-no-acc-no-lock.drh
    time dReach -u 5 -l 5 -d -c car-$i-single-linear-no-acc-no-lock.drh --precision 0.1 --stat 2>&1 > /dev/null
}    ; done

 
echo "++++++++++++++++++ Composed Linear Heuristic No Acc No Lock (no-cl) +++++++++++++++"

./gen-linear-single-no-acc-no-lock.sh 1 > car-1-single-linear-no-acc-no-lock.drh
time dReach -u 6 -l 6 -r -c car-1-single-linear-no-acc-no-lock.drh --precision 0.1 --stat --no-hybrid-clause-learning 2>&1 > /dev/null

for ((i=2; i <= $MAX; i++)); do {
    ./gen-linear-single-no-acc-no-lock.sh $i > car-$i-single-linear-no-acc-no-lock.drh
    time dReach -u 5 -l 5 -r -c car-$i-single-linear-no-acc-no-lock.drh --precision 0.1 --stat --no-hybrid-clause-learning 2>&1 > /dev/null
}    ; done
 
  echo "++++++++++++++++++ Single Linear   +++++++++++++++"

 ./gen-linear-single.sh 1 > car-1-single-linear.drh
time dReach -u 12 -l 12 -r -n car-1-single-linear.drh --precision 0.1 --stat  2>&1 > /dev/null

for ((i=2; i <= $MAX; i++)); do {
    ./gen-linear-single.sh $i > car-$i-single-linear.drh
time    dReach -u 10 -l 10 -d -n car-$i-single-linear.drh --precision 0.1 --stat 2>&1 > /dev/null 

}    ; done

 echo "++++++++++++++++++ Single Linear Heuristic  +++++++++++++++"

 ./gen-linear-single.sh 1 > car-1-single-linear.drh
time dReach -u 12 -l 12 -r -n car-1-single-linear.drh --precision 0.1 --stat  2>&1 > /dev/null

for ((i=2; i <= $MAX; i++)); do {
    ./gen-linear-single.sh $i > car-$i-single-linear.drh
time    dReach -u 10 -l 10 -r -n car-$i-single-linear.drh --precision 0.1 --stat 2>&1 > /dev/null 

}    ; done


 echo "++++++++++++++++++ Single Linear Heuristic (no-cl) +++++++++++++++"

 ./gen-linear-single.sh 1 > car-1-single-linear.drh
time dReach -u 12 -l 12 -r -n car-1-single-linear.drh --precision 0.1 --stat --no-hybrid-clause-learning 2>&1 > /dev/null

for ((i=2; i <= $MAX; i++)); do {
    ./gen-linear-single.sh $i > car-$i-single-linear.drh
time     dReach -u 10 -l 10 -r -n car-$i-single-linear.drh --precision 0.1 --stat --no-hybrid-clause-learning 2>&1 > /dev/null && grep "Running time               =" /dev/null
     
}    ; done

exit

 
 echo "++++++++++++++++++ Single Linear Heuristic No Acc No Lock (no-cl) +++++++++++++++"

./gen-linear-single-no-acc-no-lock.sh 1 > car-1-single-linear-no-acc-no-lock.drh
time dReach -u 6 -l 6 -r -n car-1-single-linear-no-acc-no-lock.drh --precision 0.1 --stat --no-hybrid-clause-learning 2>&1 > /dev/null

for ((i=2; i <= $MAX; i++)); do {
    ./gen-linear-single-no-acc-no-lock.sh $i > car-$i-single-linear-no-acc-no-lock.drh
    time dReach -u 5 -l 5 -r -n car-$i-single-linear-no-acc-no-lock.drh --precision 0.1 --stat --no-hybrid-clause-learning 2>&1 > /dev/null
}    ; done

echo "++++++++++++++++++ Single Linear Heuristic No Acc No Lock  +++++++++++++++"

./gen-linear-single-no-acc-no-lock.sh 1 > car-1-single-linear-no-acc-no-lock.drh
time dReach -u 6 -l 6 -r -n car-1-single-linear-no-acc-no-lock.drh --precision 0.1 --stat  2>&1 > /dev/null

for ((i=2; i <= $MAX; i++)); do {
     ./gen-linear-single-no-acc-no-lock.sh $i > car-$i-single-linear-no-acc-no-lock.drh
 time    dReach -u 5 -l 5 -r -n car-$i-single-linear-no-acc-no-lock.drh --precision 0.1 --stat  2>&1 > /dev/null
    
}    ; done


echo "++++++++++++++++++ Single Linear  No Acc No Lock  +++++++++++++++"

./gen-linear-single-no-acc-no-lock.sh 1 > car-1-single-linear-no-acc-no-lock.drh
time dReach -u 6 -l 6 -d -n car-1-single-linear-no-acc-no-lock.drh --precision 0.1 --stat  2>&1 > /dev/null

for ((i=2; i <= $MAX; i++)); do {
    ./gen-linear-single-no-acc-no-lock.sh $i > car-$i-single-linear-no-acc-no-lock.drh
    time dReach -u 5 -l 5 -d -n car-$i-single-linear-no-acc-no-lock.drh --precision 0.1 --stat 2>&1 > /dev/null
}    ; done



echo "++++++++++++++++++ Composed Linear Heuristic No Acc No Lock  +++++++++++++++"

./gen-linear-single-no-acc-no-lock.sh 1 > car-1-single-linear-no-acc-no-lock.drh
time dReach -u 6 -l 6 -r -c car-1-single-linear-no-acc-no-lock.drh --precision 0.1 --stat  2>&1 > /dev/null

for ((i=2; i <= $MAX; i++)); do {
     ./gen-linear-single-no-acc-no-lock.sh $i > car-$i-single-linear-no-acc-no-lock.drh
 time    dReach -u 5 -l 5 -r -c car-$i-single-linear-no-acc-no-lock.drh --precision 0.1 --stat  2>&1 > /dev/null
    
}    ; done



 



 

 


 

 


 
 echo "++++++++++++++++++ Single Linear Heuristic No Acc (no-cl) +++++++++++++++"

./gen-linear-single-no-acc.sh 1 > car-1-single-linear-no-acc.drh
time dReach -u 12 -l 12 -r -n car-1-single-linear-no-acc.drh --precision 0.1 --stat --no-hybrid-clause-learning 2>&1 > /dev/null

for ((i=2; i <= $MAX; i++)); do {
    
    ./gen-linear-single-no-acc.sh $i > car-$i-single-linear-no-acc.drh
time     dReach -u 10 -l 10 -r -n car-$i-single-linear-no-acc.drh --precision 0.1 --stat --no-hybrid-clause-learning 2>&1 > /dev/null
    
}    ; done



echo "++++++++++++++++++ Single Linear Heuristic No Acc No Lock  +++++++++++++++"

./gen-linear-single-no-acc-no-lock.sh 1 > car-1-single-linear-no-acc-no-lock.drh
time dReach -u 6 -l 6 -r -n car-1-single-linear-no-acc-no-lock.drh --precision 0.1 --stat  2>&1 > /dev/null

for ((i=2; i <= $MAX; i++)); do {
     ./gen-linear-single-no-acc-no-lock.sh $i > car-$i-single-linear-no-acc-no-lock.drh
 time    dReach -u 5 -l 5 -r -n car-$i-single-linear-no-acc-no-lock.drh --precision 0.1 --stat  2>&1 > /dev/null
    
}    ; done

echo "++++++++++++++++++ Single Linear Heuristic No Acc  +++++++++++++++"

./gen-linear-single-no-acc.sh 1 > car-1-single-linear-no-acc.drh
time dReach -u 12 -l 12 -r -n car-1-single-linear-no-acc.drh --precision 0.1 --stat  2>&1 > /dev/null

for ((i=2; i <= $MAX; i++)); do {
        ./gen-linear-single-no-acc.sh $i > car-$i-single-linear-no-acc.drh
    time dReach -u 10 -l 10 -r -n car-$i-single-linear-no-acc.drh --precision 0.1 --stat  2>&1 > /dev/null
}    ; done

 
