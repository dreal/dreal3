#!/bin/bash

DIMENSION=$1

ADJACENCY="//set<pair<int, int>*> adjacent = {"


outputInit(){
    echo "init:"
    echo "@1 (x = 1);"
}

outputGoal(){
    END=`expr ${DIMENSION} \* ${DIMENSION}`
    UNSAT=1
    echo "goal:"
    echo "@${END} (x = ${UNSAT});"
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
    echo "  flow: d/dt[x]=-1;"
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
	THIS=`convertXYtoMode $i $j`
	NEXT=`convertXYtoMode $i $JP`
	ADJACENCY=${ADJACENCY}"new pair<int, int>("${THIS}","${NEXT}"), "
	echo "   true ==> @${NEXT} (x' = x); //North"
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
	THIS=`convertXYtoMode $i $j`
	NEXT=`convertXYtoMode $JP $j`
	ADJACENCY=${ADJACENCY}"new pair<int, int>("${THIS}","${NEXT}"), "
	echo "   true ==> @${NEXT} (x' = x); //East"
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
	THIS=`convertXYtoMode $i $j`
	NEXT=`convertXYtoMode $i $JP`
	ADJACENCY=${ADJACENCY}"new pair<int, int>("${THIS}","${NEXT}"), "
	echo "   true ==> @${NEXT} (x' = x); //South"
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
	THIS=`convertXYtoMode $i $j`
	NEXT=`convertXYtoMode $JP $j`
	ADJACENCY=${ADJACENCY}"new pair<int, int>("${THIS}","${NEXT}"), "
	echo "   true ==> @${NEXT} (x' = x); //West"
     fi
}


echo "[0, 1] x;"
echo "[0.00001, 0.0001] time;"

for((i=0;i<${DIMENSION};i++)); do {
    for((j=0;j<${DIMENSION};j++)); do {
	outputMode $i $j
    }; done
}; done


outputInit
outputGoal


ADJACENCY=${ADJACENCY}"};"
echo $ADJACENCY
