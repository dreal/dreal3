#!/bin/bash

NUM=10
INST=10
for((i=1; i <=$NUM; i++)); do {
  f=`expr $i \* 5`
  for((j=1; j <=$INST; j++)); do {
  ./gen-instance.sh $f > grid${f}_${j}.drh
}; done
}; done
