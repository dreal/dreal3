#!/bin/bash

NUM=10

for((i=1; i <=$NUM; i++)); do {
	if [ ${i} -lt 10 ]; then
	    PREFIX="0"
	 else
	    PREFIX=""
	 fi
	./gen-instance.sh -s ${i} -o barn_door_${PREFIX}${i}.drh
}; done