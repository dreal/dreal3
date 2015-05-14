#!/bin/bash

NUM=2

for((i=2; i <=$NUM; i++)); do {
        if [ ${i} -lt 10 ]; then
            PREFIX="0"
         else
            PREFIX=""
         fi
        for d in 0.001 0.1; do {
        for j in "" "_delta_all"  "_delta_timeonly" "_delta_aim" ; do {
                INSTANCE=barn_door_${PREFIX}${i}_${i}${j}.smt2
                #echo delta=${d}, steps = ${i}, variation = ${j}
                echo $INSTANCE $d
                time ../../../../dReal --delta --precision ${d} --proof $INSTANCE
        }; done
    }; done
}; done
