NUM=5

TIMEFORMAT="%U"
#/usr/bin/time -f "$fmt" -o $timefile command args...

for deltaH in "--delta-heuristic" ""; do {
OUT="barn_door${deltaH}.out"
echo "" > $OUT 
for((i=1; i <=$NUM; i++)); do {
	f=$i #`expr $i \* 10`
	if [ ${f} -lt 10 ]; then
	    PREFIX="0"
	 else
	    PREFIX=""
	 fi
	LINE="$i"
	for d in  0.001 0.1 1.0 2.0 4.0 ; do {
		#for relaxTime in true false; do {
		for relaxTime in true; do {
			#for relaxJump in true false; do {
			for relaxJump in true; do {
					#for sat in "-u" ""; do {
					for sat in ""; do {
   						echo "DELTA = ${d} STEPS = ${f}"
						#CMD="../../../../dReach.sh -d ${deltaH} -u ${i} -l ${i} -t 600 barn_door_${PREFIX}${i}_${d}_${relaxTime}_${relaxJump}${sat}.drh"
						#CMD="../../../../dReach.sh -d ${deltaH} -u 1 -l 1 -t 600 barn_door_${PREFIX}${f}_${d}_${relaxTime}_${relaxJump}${sat}.drh"
						CMD="egrep -e \"${i}\s[0-9]+\" barn_door_${d}_${relaxTime}_${relaxJump}${deltaH}${sat}.out"
						echo $CMD
						#runtime=$( time ( $CMD ) 2>&1  1>/dev/null)
						t=`echo ${CMD} | bash | cut -f 2 -d " "`
						echo [$t]

						if [ -z $t ] ; then
						    LINE=$LINE" ?"
						else
						    LINE=$LINE" "$t
						fi
					    }; done
				    }; done
			    }; done
	    }; done
	echo $LINE >> $OUT
	    }; done
}; done
