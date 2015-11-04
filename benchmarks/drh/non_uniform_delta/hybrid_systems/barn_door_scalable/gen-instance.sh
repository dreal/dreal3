#!/bin/bash

SIZE=
OUT=
RELAXTIME=
RELAXJUMP=
UNSAT=
while getopts ":s:o:d:t:j:u" opt; do
  case $opt in
  s)
      SIZE=$OPTARG
      echo "Generating Instance of Size = ${SIZE}"
      ;;
  o)
      OUT=$OPTARG
      echo "Outfile = ${OUT}"
      ;;
  d)
      DELTA=$OPTARG
      echo "DELTA = ${DELTA}"
      ;;
  t)
      RELAXTIME=$OPTARG
      echo "RELAXTIME = ${RELAXTIME}"
      ;;
  j)
      RELAXJUMP=$OPTARG
      echo "RELAXJUMP = ${RELAXJUMP}"
      ;;
  u)
      UNSAT=1
      echo "UNSAT = 1"
      ;;
  \?)
      echo "Invalid option: -$OPTARG" >&2
      usage
      exit
      ;;
  esac
done

usage(){
 echo "./gen-instance -s <SIZE> -d <DELTA> -o <OUTFILE> -t [true|false]"
}



outputVariables(){
    MAX_HEIGHT=`expr $SIZE \* 6`
    echo "[-${MAX_HEIGHT}, ${MAX_HEIGHT}] aim_height;" >> $OUT
    echo "[0, 1] on;" >> $OUT
    echo "[0, 10] time;" >> $OUT
    for((i=0; i < $SIZE; i++)); do {
	echo "[-5, 5] x_${i};" >> $OUT
#	echo "[-10, 10] y_${i};" >> $OUT
    }; done
}

outputModes(){
    for((i=0; i < $SIZE; i++)); do {
	MODE=`expr $i + 1`
	NEXTMODE=`expr $MODE + 1`
	echo "{ mode ${MODE};"               >> $OUT
	if [ $RELAXTIME == "true" ]; then
	    echo "  timeprecision: ${DELTA};"       >> $OUT
	fi

	echo "  invt:"                       >> $OUT
	echo "        (on <= 0);"            >> $OUT
#	echo "        (<= -50 aim_height);"  >> $OUT
	if [ $RELAXJUMP == "false" ]; then
	    echo "        (50 >= aim_height);"   >> $OUT
	else
	    echo "        (50 >= [${DELTA}] aim_height);"   >> $OUT
	fi
	echo "  flow:"                       >> $OUT
	echo "        d/dt[aim_height] = 0;" >> $OUT
	echo "        d/dt[on] = 0;"         >> $OUT
	for((j=0; j < $SIZE; j++)); do {
		echo "        d/dt[x_${j}] = 0;"         >> $OUT
	    }; done
	
	echo "  jump:"                       >> $OUT
	if [ $RELAXJUMP == "false" ]; then
#	echo "        true ==> @${NEXTMODE} (= aim_height' (+ aim_height (- y_${i} (* x_${i} x_${i}))) [${DELTA}]);" >> $OUT
	    echo "        true ==> @${NEXTMODE} (aim_height' = (aim_height + x_${i}));" >> $OUT
#	echo "        true ==> @${NEXTMODE} (= aim_height' (- y_${i} (* x_${i} x_${i})) [${DELTA}]);" >> $OUT
	else
#	echo "        true ==> @${NEXTMODE} (= aim_height' (+ aim_height (- y_${i} (* x_${i} x_${i}))) [${DELTA}]);" >> $OUT
	    echo "        true ==> @${NEXTMODE} (aim_height' = [${DELTA}] (aim_height + x_${i}));" >> $OUT
#	echo "        true ==> @${NEXTMODE} (= aim_height' (- y_${i} (* x_${i} x_${i})) [${DELTA}]);" >> $OUT
	fi
	echo "}" >> $OUT
    }; done

}

outputLastMode(){
    MODE=`expr ${SIZE} + 1`
    echo "{mode ${MODE};"                  >> $OUT
    if [ $RELAXTIME == "true" ]; then
	echo "  timeprecision: ${DELTA};"       >> $OUT
    fi
    echo "  invt:"                         >> $OUT
    echo "        (on >= 1);"              >> $OUT
    if [ $RELAXJUMP == "false" ]; then
	echo "        (50 >= aim_height);"   >> $OUT
    else
	echo "        (50 >= [${DELTA}] aim_height);"   >> $OUT
    fi
    echo "  flow:"                         >> $OUT
    echo "        d/dt[aim_height] = 0;"   >> $OUT
    echo "        d/dt[on] = 0;"           >> $OUT
    for((j=0; j < $SIZE; j++)); do {
	    echo "        d/dt[x_${j}] = 0;"         >> $OUT
	}; done

    echo "  jump:"                         >> $OUT
    echo "        true ==> @${MODE} true;" >> $OUT
    echo "}"                               >> $OUT
}

outputInit(){
    echo "init:" >> $OUT
    echo "@1 (and  (aim_height = 0) (on = 0));" >> $OUT
}

outputGoal(){
    MODE=`expr ${SIZE} + 1`
    echo "goal:" >> $OUT
    if [ $UNSAT ]; then
	UNSAT_HEIGHT=`expr ${SIZE} \* 6`
	echo "@${MODE} (and (on = 1) (aim_height = ${UNSAT_HEIGHT}));" >> $OUT
    else
	SAT_HEIGHT=3
	echo "@${MODE} (and (on = 1) (aim_height <= (1 + ${SAT_HEIGHT})) (aim_height >= (${SAT_HEIGHT} - 1)));" >> $OUT
    fi
}


#echo "Barn door with ${SIZE} aiming step(s)" > $OUT
echo "" > $OUT #make sure old copies are gone


outputVariables 
outputModes
outputLastMode 
outputInit 
outputGoal 
