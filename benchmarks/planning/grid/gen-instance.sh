#!/bin/bash

DIMENSION=$1



outputInit(){
    echo "init:"
    echo "@1 true;"
}

outputGoal(){
    END=`expr ${DIMENSION} \* ${DIMENSION}`
    echo "goal:"
    echo "@${END} true;"
}

convertXYtoMode(){
    i=$1
    j=$2
    MODE=`expr ${i} \* ${DIMENSION}`
    MODE=`expr ${MODE} + ${j}`
    MODE=`expr ${MODE} + 1`
    echo $MODE
}

outputMode(){
    i=$1
    j=$2
    MODE=`convertXYtoMode $i $j`
    echo "{ mode ${MODE};"
    echo "  invt:  true;"
    echo "  flow: d/dt[x]=0;"
    echo "  jump: "
    outputNJump $i $j
    outputSJump $i $j
    outputEJump $i $j
    outputWJump $i $j
    echo "}"
}

outputNJump(){
    i=$1
    j=$2
    BOUNDARY=`expr $j + 1`
    if [ ${BOUNDARY} == ${DIMENSION} ]; then
	echo "   //No North"
    else
	JP=`expr $j + 1`
	NEXT=`convertXYtoMode $i $JP`
	echo "   true ==> @${NEXT} true; //North"
     fi
}

outputEJump(){
    i=$1
    j=$2
    BOUNDARY=`expr $i + 1`
    if [ ${BOUNDARY} == ${DIMENSION} ]; then
	echo "   //No East"
    else
	JP=`expr $i + 1`
	NEXT=`convertXYtoMode $JP $j`
	echo "   true ==> @${NEXT} true; //East"
     fi
}

outputSJump(){
    i=$1
    j=$2
    BOUNDARY=$j
    if [ ${BOUNDARY} == 0 ]; then
	echo "   //No South"
    else
	JP=`expr $j - 1`
	NEXT=`convertXYtoMode $i $JP`
	echo "   true ==> @${NEXT} true; //South"
     fi
}

outputWJump(){
    i=$1
    j=$2
    BOUNDARY=$i
    if [ ${BOUNDARY} == 0 ]; then
	echo "   //No West"
    else
	JP=`expr $i - 1`
	NEXT=`convertXYtoMode $JP $j`
	echo "   true ==> @${NEXT} true; //West"
     fi
}

echo "[0, 1] x;"
echo "[0, 1] time;"

for((i=0;i<${DIMENSION};i++)); do {
    for((j=0;j<${DIMENSION};j++)); do {
	outputMode $i $j
    }; done
}; done


outputInit
outputGoal
