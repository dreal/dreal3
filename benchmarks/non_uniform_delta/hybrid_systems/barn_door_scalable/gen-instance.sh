#!/bin/bash

SIZE=
OUT=
while getopts ":s:o:" opt; do
  case $opt in
  s)
      SIZE=$OPTARG
      echo "Generating Instance of Size = ${SIZE}"
      ;;
  o)
      OUT=$OPTARG
      echo "Outfile = ${OUT}"
      ;;
  \?)
      echo "Invalid option: -$OPTARG" >&2
      usage
      exit
      ;;
  esac
done

usage(){
 echo "./gen-instance -s <SIZE> -o <OUTFILE>"
}



outputVariables(){
    echo "[-50, 50] aim_height;" >> $OUT
    echo "[0, 1] on;" >> $OUT
    echo "[0, 10] time;" >> $OUT
    for((i=0; i < $SIZE; i++)); do {
	echo "[-10, 10] x_${i};" >> $OUT
	echo "[-10, 10] y_${i};" >> $OUT
    }; done
}

outputModes(){
    for((i=0; i < $SIZE; i++)); do {
	MODE=`expr $i + 1`
	NEXTMODE=`expr $MODE + 1`
	echo "{ mode ${MODE};"               >> $OUT
	echo "  invt:"                       >> $OUT
	echo "        (<= on 0);"            >> $OUT
#	echo "        (<= -50 aim_height);"  >> $OUT
	echo "        (>= 50 aim_height);"   >> $OUT
	echo "  flow:"                       >> $OUT
	echo "        d/dt[aim_height] = 0;" >> $OUT
	echo "        d/dt[on] = 0;"         >> $OUT
	echo "  jump:"                       >> $OUT
	echo "        true ==> @${NEXTMODE} (= aim_height' (+ aim_height (- y_${i} (* x_${i} x_${i}))));" >> $OUT
	echo "}" >> $OUT
    }; done

}

outputLastMode(){
    MODE=`expr ${SIZE} + 1`
    echo "{mode ${MODE};"                  >> $OUT
    echo "  invt:"                         >> $OUT
    echo "        (<= on 0);"              >> $OUT
    echo "        (>= 50 aim_height);"   >> $OUT
    echo "  flow:"                         >> $OUT
    echo "        d/dt[aim_height] = 0;"   >> $OUT
    echo "        d/dt[on] = 0;"           >> $OUT
    echo "  jump:"                         >> $OUT
    echo "        true ==> @${MODE} true;" >> $OUT
    echo "}"                               >> $OUT
}

outputInit(){
    echo "init:" >> $OUT
    echo "@1 (and  (= aim_height 0) (= on 0));" >> $OUT
}

outputGoal(){
    MODE=`expr ${SIZE} + 1`
    echo "goal:" >> $OUT
    echo "@${MODE} (and (= aim_height 5));" >> $OUT
}


#echo "Barn door with ${SIZE} aiming step(s)" > $OUT
echo "" > $OUT #make sure old copies are gone


outputVariables 
outputModes
outputLastMode 
outputInit 
outputGoal 