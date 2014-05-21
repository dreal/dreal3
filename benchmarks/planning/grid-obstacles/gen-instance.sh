#!/bin/bash

DIMENSION=$1

ADJACENCY="//set<pair<int, int>*> adjacent = {"


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
    getRandomBool
    if [ $boolResult = "TRUE" ]; then
    if [ ${BOUNDARY} == ${DIMENSION} ]; then
	echo "   //No North"
    else
	JP=`expr $j + 1`
	THIS=`convertXYtoMode $i $j`
	NEXT=`convertXYtoMode $i $JP`
	ADJACENCY=${ADJACENCY}"new pair<int, int>("${THIS}","${NEXT}"), "
	echo "   true ==> @${NEXT} true; //North"
     fi
    fi
}

outputEJump(){
    i=$1
    j=$2
    BOUNDARY=`expr $i + 1`
    getRandomBool
    if [ $boolResult = "TRUE" ]; then
    if [ ${BOUNDARY} == ${DIMENSION} ]; then
	echo "   //No East"
    else
	JP=`expr $i + 1`
	THIS=`convertXYtoMode $i $j`
	NEXT=`convertXYtoMode $JP $j`
	ADJACENCY=${ADJACENCY}"new pair<int, int>("${THIS}","${NEXT}"), "
	echo "   true ==> @${NEXT} true; //East"
     fi
    fi
}

outputSJump(){
    i=$1
    j=$2
    BOUNDARY=$j
    getRandomBool
    if [ $boolResult = "TRUE" ]; then
    if [ ${BOUNDARY} == 0 ]; then
	echo "   //No South"
    else
	JP=`expr $j - 1`
	THIS=`convertXYtoMode $i $j`
	NEXT=`convertXYtoMode $i $JP`
	ADJACENCY=${ADJACENCY}"new pair<int, int>("${THIS}","${NEXT}"), "
	echo "   true ==> @${NEXT} true; //South"
     fi
    fi
}

outputWJump(){
    i=$1
    j=$2
    BOUNDARY=$i
    getRandomBool
    if [ $boolResult = "TRUE" ]; then
    if [ ${BOUNDARY} == 0 ]; then
	echo "   //No West"
    else
	JP=`expr $i - 1`
	THIS=`convertXYtoMode $i $j`
	NEXT=`convertXYtoMode $JP $j`
	ADJACENCY=${ADJACENCY}"new pair<int, int>("${THIS}","${NEXT}"), "
	echo "   true ==> @${NEXT} true; //West"
     fi
     fi
}

getRandomBool(){
BINARY=2
T=1
number=$RANDOM

let "number %= $BINARY"
#  Note that    let "number >>= 14"    gives a better random distribution
#+ (right shifts out everything except last binary digit).
if [ "$number" -eq $T ]
then
  boolResult="TRUE"
else
  boolResult="FALSE"
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


ADJACENCY=${ADJACENCY}"};"
echo $ADJACENCY
