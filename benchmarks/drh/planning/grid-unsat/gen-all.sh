#!/bin/bash

NUM=10
for((i=1; i <=$NUM; i++)); do {
  f=`expr $i \* 5`
  ./gen-instance.sh $f > grid${f}.drh
}; done
