#!/bin/bash

NUM=10
IRREL=5
for((i=1; i <=$NUM; i++)); do {
  f=`expr $i \* 5`
  for((j=0; j <=$IRREL; j++)); do {
   g=`expr $j \* 10`
  ./gen-instance.sh $f $g > grid${f}_${g}.drh
}; done
}; done
