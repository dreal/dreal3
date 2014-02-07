#!/bin/bash

NUM=10

for((i=1; i <=$NUM; i++)); do {
	if [ ${i} -lt 10 ]; then
	    PREFIX="0"
	 else
	    PREFIX=""
	 fi
	time ../../../../dReach.sh -d -p 1.0  -u ${i} -t 1000 barn_door_${PREFIX}${i}.drh 
}; done