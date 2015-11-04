#!/bin/bash

SIZE=
OUT=
RELAXTIME=
RELAXJUMP="false"
UNSAT=
NUMNONSENSE=
while getopts ":s:o:d:t:j:u:n:" opt; do
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
  n)
      NUMNONSENSE=$OPTARG
      echo "NUMNONSENSE = ${NUMNONSENSE}"
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
	for((j=0; j < ${NUMNONSENSE}; j++)); do {
		echo "[-5, 5] y_${i}_${j};" >> $OUT
	    }; done
    }; done
    for((i=0; i < $NUMNONSENSE; i++)); do {
	echo "[-${MAX_HEIGHT}, ${MAX_HEIGHT}] nonsense_${i};" >> $OUT
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
	echo "        (50 >= aim_height);"   >> $OUT
	for((j=0; j < $NUMNONSENSE; j++)); do {
	    echo "        (50 >= [${DELTA}] nonsense_${j});"   >> $OUT
	    }; done

	echo "  flow:"                       >> $OUT
	echo "        d/dt[aim_height] = 0;" >> $OUT
	for((j=0; j < $NUMNONSENSE; j++)); do {
		echo "        d/dt[nonsense_${j}] = 0;" >> $OUT
	    }; done
	echo "        d/dt[on] = 0;"         >> $OUT
	for((j=0; j < $SIZE; j++)); do {
	    echo "        d/dt[x_${j}] = 0;"         >> $OUT
	    for((k=0; k < $NUMNONSENSE; k++)); do {
		    echo "        d/dt[y_${j}_${k}] = 0;"         >> $OUT
		}; done
	}; done

	echo "  jump:"                       >> $OUT

	JUMP="        true ==> @${NEXTMODE} (and (aim_height' = (aim_height + x_${i}))" 
	for((j=0; j < $NUMNONSENSE; j++)); do {
		JUMP=$JUMP" (nonsense_${j}' = [${DELTA}] (nonsense_${j} +  y_${i}_${j}) )"
	    }; done
	JUMP=$JUMP");"
	echo $JUMP >> $OUT
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
    echo "        (on <= 0);"              >> $OUT
    echo "        (50 >= aim_height);"   >> $OUT
    for((j=0; j < $NUMNONSENSE; j++)); do {
	    echo "        (50 >= [${DELTA}] nonsense_${j});"   >> $OUT
	}; done
    
    echo "  flow:"                         >> $OUT
    echo "        d/dt[aim_height] = 0;"   >> $OUT
    echo "        d/dt[on] = 0;"           >> $OUT
    for((j=0; j < $NUMNONSENSE; j++)); do {
	    echo "        d/dt[nonsense_${j}] = 0;" >> $OUT
	}; done
    for((j=0; j < $SIZE; j++)); do {
	    echo "        d/dt[x_${j}] = 0;"         >> $OUT
	    for((k=0; k < $NUMNONSENSE; k++)); do {
		    echo "        d/dt[y_${j}_${k}] = 0;"         >> $OUT
		}; done
	}; done

    echo "  jump:"                         >> $OUT
    echo "        true ==> @${MODE} true;" >> $OUT
    echo "}"                               >> $OUT
}

outputInit(){
    echo "init:" >> $OUT
    INIT="@1 (and  (aim_height = 0) (on = 0)"
    for((j=0; j < $NUMNONSENSE; j++)); do {
	    INIT=$INIT" (nonsense_${j} = 0)"
	}; done
    INIT=$INIT");"
    echo $INIT >> $OUT

}

outputGoal(){
    MODE=`expr ${SIZE} + 1`
    echo "goal:" >> $OUT
    if [ $UNSAT ]; then
	UNSAT_HEIGHT=`expr ${SIZE} \* 6`
	echo "@${MODE} (and (aim_height = ${UNSAT_HEIGHT}));" >> $OUT
    else
	SAT_HEIGHT=0
	echo "@${MODE} (and (aim_height = ${SAT_HEIGHT}));" >> $OUT
    fi
}


#echo "Targeting with ${SIZE} aiming step(s)" > $OUT
echo "" > $OUT #make sure old copies are gone


outputVariables 
outputModes
outputLastMode 
outputInit 
outputGoal 
