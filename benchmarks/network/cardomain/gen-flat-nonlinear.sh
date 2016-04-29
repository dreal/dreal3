#!/bin/bash

DIMENSION=$1

accelModes=
decelModes=
accelResModes=
decelResModes=
endMode=

outputModeOff(){
    echo "{ mode 1;"
    echo "  flow: "
#    echo "        d/dt[a] = 0;"
    echo "        d/dt[v] = 0;"
    echo "        d/dt[d] = 0;"
 #   echo "        d/dt[clock] = 1;"
    echo "  jump: "
#    echo "        (clock >= epsilon)  ==> @"${accelModes[0]}" (clock' = 0);"
    echo "        true  ==> @"${accelModes[0]}" true;"
    echo "}"
}

getAccelMode(){
    #mode is accel value
    mode=$1
    modeAccel=`expr $mode + 1`
    if [ $modeAccel -lt 0 ] ; then
	decelIndex=`expr $modeAccel \* -1`
	echo ${decelModes[$decelIndex]}
    else
	echo ${accelModes[$modeAccel]}
    fi
}

getDecelMode(){
    #mode is accel value
    mode=$1
    modeAccel=`expr $mode - 1`
    if [ $modeAccel -lt 0 ] ; then
	decelIndex=`expr $modeAccel \* -1`
	echo ${decelModes[$decelIndex]}
    else
	echo ${accelModes[$modeAccel]}
    fi
}

getAccelResMode(){
    #mode is accel value
    mode=$1
    modeAccel=`expr $mode + 1`
    if [ $modeAccel -lt 0 ] ; then
	decelIndex=`expr $modeAccel \* -1`
	echo ${decelResModes[$decelIndex]}
    else
	echo ${accelResModes[$modeAccel]}
    fi
}

getDecelResMode(){
    #mode is accel value
    mode=$1
    modeAccel=`expr $mode - 1`
    if [ $modeAccel -lt 0 ] ; then
	decelIndex=`expr $modeAccel \* -1`
	echo ${decelResModes[$decelIndex]}
    else
	echo ${accelResModes[$modeAccel]}
    fi
}

outputModeOnAccel(){
    accel=$1
    mode=${accelModes[$accel]}
    resMode=${accelResModes[$accel]}

    echo "{ mode "$mode";"
    echo "  invt:"
#    echo "        (v <= 50);"
    echo "  flow: "
#    echo "        d/dt[a] = "$accel";"
    echo "        d/dt[v] = "$accel" - (0.1 * (v ^2));"
#    echo "        d/dt[v] = "$accel";"
    echo "        d/dt[d] = v;"
#    echo "        d/dt[clock] = 1;"
    echo "  jump: "

    accelMode=`getAccelMode $accel`
    decelMode=`getDecelMode $accel`
    if [ $accel -lt $DIMENSION ] ; then
#	echo "        (clock >= epsilon) ==> @"$accelMode" (clock' = 0);"
	echo "        true ==> @"$accelMode" true;"
    fi
#    echo "        (clock >= epsilon) ==> @"$decelMode" (clock' = 0);"
    echo "        true ==> @"$decelMode" true;"
#    echo "        (and (clock >= epsilon) (v >= 50)) ==> @"$resMode" (clock' = 0);"
#    echo "        (and true (v >= 50)) ==> @"$resMode" true;"
#    echo "        (clock >= epsilon) ==> @"$endMode" (clock' = 0);"
    echo "        true ==> @"$endMode" true;"
    echo "}"

}

outputModeOnAccelResist(){
    accel=$1
    mode=${accelResModes[$accel]}
    nonresMode=${accelModes[$accel]}

    echo "{ mode "$mode";"
    echo "  invt:"
    echo "        (v >= 50);"
    echo "  flow: "
#    echo "        d/dt[a] = "$accel";"
    echo "        d/dt[v] = "$accel" - (0.1 * (v ^2));"
    echo "        d/dt[d] = v;"
#    echo "        d/dt[clock] = 1;"
    echo "  jump: "

    accelMode=`getAccelResMode $accel`
    decelMode=`getDecelResMode $accel`
    if [ $accel -lt $DIMENSION ] ; then
#	echo "        (clock >= epsilon) ==> @"$accelMode" (clock' = 0);"
	echo "        true ==> @"$accelMode" true;"
    fi
#    echo "        (clock >= epsilon) ==> @"$decelMode" (clock' = 0);"
    echo "        true ==> @"$decelMode" true;"
#    echo "        (and (clock >= epsilon) (v <= 50)) ==> @"$nonresMode" (clock' = 0);"
#    echo "        (and true (v <= 50)) ==> @"$nonresMode" true;"
#    echo "        (clock >= epsilon) ==> @"$endMode" (clock' = 0);"
#    echo "        true ==> @"$endMode" true;"
    echo "}"

}

outputModeOnDecel(){
    accel=$1
    resMode=${decelResModes[$accel]}
    mode=${decelModes[$accel]}
    accel=`expr $accel \* -1`

    echo "{ mode "$mode";"
    echo "  invt:"
#    echo "        (v <= 50);"
    echo "  flow: "
#    echo "        d/dt[a] = "$accel";"
#    echo "        d/dt[v] = "$accel";"
    echo "        d/dt[v] ="$accel" - (0.1 * (v ^2));"
    echo "        d/dt[d] = v;"
#    echo "        d/dt[clock] = 1;"
    echo "  jump: "

    accelMode=`getAccelMode $accel`
    decelMode=`getDecelMode $accel`
#    echo "        (clock >= epsilon) ==> @"$accelMode" (clock' = 0);"
    echo "        true ==> @"$accelMode" true;"
    if [ $accel -lt `expr -1 \* $DIMENSION` ] ; then
#	echo "        (clock >= epsilon) ==> @"$decelMode" (clock' = 0);"
	echo "        true ==> @"$decelMode" true;"
    fi
#    echo "        (and (v >= 50) (clock >= epsilon)) ==> @"$resMode" (clock' = 0);"
#    echo "        (and (v >= 50) true) ==> @"$resMode" true;"
#    echo "        (clock >= epsilon) ==> @"$endMode" (clock' = 0);"
    echo "        true ==> @"$endMode" true;"
    echo "}"

}

outputModeOnDecelResist(){
    accel=$1
    nonresMode=${decelModes[$accel]}

    mode=${decelResModes[$accel]}
    accel=`expr $accel \* -1`
    
    echo "{ mode "$mode";"
    echo "  invt:"
    echo "        (v >= 50);"
    echo "  flow: "
#    echo "        d/dt[a] = "$accel";"
    echo "        d/dt[v] ="$accel" - (0.1 * (v ^2));"
    echo "        d/dt[d] = v;"
#    echo "        d/dt[clock] = 1;"
    echo "  jump: "

    accelMode=`getAccelResMode $accel`
    decelMode=`getDecelResMode $accel`
#    echo "        (clock >= epsilon) ==> @"$accelMode" (clock' = 0);"
    echo "        true ==> @"$accelMode" true;"
    if [ $accel -lt `expr -1 \* $DIMENSION` ] ; then
#	echo "        (clock >= epsilon) ==> @"$decelMode" (clock' = 0);"
	echo "        true ==> @"$decelMode" true;"
    fi
#    echo "        (and (v <= 50) (clock >= epsilon)) ==> @"$nonresMode" (clock' = 0);"
    echo "        (and (v <= 50)) ==> @"$nonresMode" true;"
#    echo "        (clock >= epsilon) ==> @"$endMode" (clock' = 0);"
 #   echo "        true ==> @"$endMode" true;"
    echo "}"

}

outputEndMode(){
    echo "{ mode "$endMode";"
    echo "  flow: "
#    echo "        d/dt[a] = 0;"
    echo "        d/dt[v] = 0;"
    echo "        d/dt[d] = 0;"
#    echo "        d/dt[clock] = 0;"
    echo "  jump: "
      echo "}"
}

outputInit(){
    echo "init:"
echo "@1 (and (d = 0)"
echo "	      (v = 0) "
#echo "	      (clock = 0) "
echo "   );"

}

outputGoal(){
    echo "goal:"
    echo " @"$endMode" (and (d = 30) (v = 0));"

}



#echo "#define epsilon 0.00001"
echo "[0, 10] v;"
#echo "[-"$DIMENSION", "$DIMENSION"] a;"
echo "[0, 30] d;"
echo "[0, 30] time;"
#echo "[0, 100] clock;"

count=2
accelModes[0]=$count
count=`expr $count + 1`
for((i=1; i<=$DIMENSION; i++)); do {
	accelModes[$i]=$count
	count=`expr $count + 1`
};done
for((i=1; i<=$DIMENSION; i++)); do {
	decelModes[$i]=$count
	count=`expr $count + 1`
};done
accelResModes[0]=$count
count=`expr $count + 1`
for((i=1; i<=$DIMENSION; i++)); do {
	accelResModes[$i]=$count
	count=`expr $count + 1`
};done
for((i=1; i<=$DIMENSION; i++)); do {
	decelResModes[$i]=$count
	count=`expr $count + 1`
};done
endMode=$count

outputModeOff

for((i=0; i<=$DIMENSION; i++)) do {
    outputModeOnAccel $i
    outputModeOnAccelResist $i
}; done

for((i=1; i<=$DIMENSION; i++)) do {
    outputModeOnDecel $i
    outputModeOnDecelResist $i
}; done

outputEndMode

outputInit
outputGoal
