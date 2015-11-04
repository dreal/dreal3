#!/bin/bash

ulimit -t 600

NUM=5
NONSENSE=5
TIMEFORMAT="%U"
#/usr/bin/time -f "$fmt" -o $timefile command args...

for((i=1; i <=$NUM; i++)); do {
	f=$i #`expr $i \* 10`
	if [ ${f} -lt 10 ]; then
	    PREFIX="0"
	 else
	    PREFIX=""
	 fi
	for((j=1; j <=$NONSENSE; j++)); do {
		for d in  4.0 2.0 1.0 0.1 0.001; do {
			for relaxTime in true ; do {
#			for relaxJump in true false; do {
				for deltaH in "--delta-heuristic" ""; do {
					#for sat in "-u" ""; do {
					for sat in ""; do {
   						echo "DELTA = ${d} STEPS = ${f}"
						CMD="dReach -k ${f} targeting_${PREFIX}${f}_${j}_${d}_${relaxTime}_${relaxJump}${sat}.drh  --delta ${deltaH}"
						echo $CMD
						runtime=$( time ( $CMD ) 2>&1  1>/dev/null)
						echo $f $j $runtime >> targeting_${d}_${relaxTime}_${relaxJump}${deltaH}${sat}.out
					    }; done
				    }; done
			    }; done
		    }; done
	    }; done
}; done
