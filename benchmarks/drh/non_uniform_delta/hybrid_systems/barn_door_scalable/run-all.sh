#!/bin/bash

ulimit -t 600

NUM=5

TIMEFORMAT="%U"
#/usr/bin/time -f "$fmt" -o $timefile command args...

for((i=1; i <=$NUM; i++)); do {
	f=$i #`expr $i \* 10`
	if [ ${f} -lt 10 ]; then
	    PREFIX="0"
	 else
	    PREFIX=""
	 fi
	for d in  4.0 2.0 1.0 0.1 0.001; do {
		#for relaxTime in true false; do {
		for relaxTime in true; do {
			#for relaxJump in true false; do {
			for relaxJump in true; do {
				for deltaH in "--delta-heuristic" ""; do {
					#for sat in "-u" ""; do {
					for sat in ""; do {
   						echo "DELTA = ${d} STEPS = ${f}"
						CMD="dReach -k ${i} barn_door_${PREFIX}${i}_${d}_${relaxTime}_${relaxJump}${sat}.drh ${deltaH} --delta"
						#CMD="../../../../dReach.sh -d ${deltaH} -u 1 -l 1 -t 600 barn_door_${PREFIX}${f}_${d}_${relaxTime}_${relaxJump}${sat}.drh"
						echo $CMD
						runtime=$( time ( $CMD ) 2>&1  1>/dev/null)
						echo $f $runtime >> barn_door_${d}_${relaxTime}_${relaxJump}${deltaH}${sat}.out
					    }; done
				    }; done
			    }; done
		    }; done
	    }; done
}; done
