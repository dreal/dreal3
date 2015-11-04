#!/bin/bash

NUM=5

for((i=1; i <=$NUM; i++)); do {
	f=$i #`expr $i \* 10`
	if [ ${f} -lt 10 ]; then
	    PREFIX="0"
	 else
	    PREFIX=""
	 fi
	for d in 0.001 0.1 1.0 2.0 4.0; do {	
		#for relaxTime in true false; do {
		for relaxTime in true; do {
			#for relaxJump in true false; do {
			for relaxJump in true; do {
				#for sat in "" "-u"; do {
				for sat in ""; do {
					./gen-instance.sh \
					-s ${f} \
					-o barn_door_${PREFIX}${f}_${d}_${relaxTime}_${relaxJump}${sat}.drh -d ${d} \
					-t $relaxTime \
					-j $relaxJump \
					$sat
				    }; done
			    }; done
		    }; done
            }; done
    }; done