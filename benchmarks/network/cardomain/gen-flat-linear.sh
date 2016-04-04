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
    echo "        (v <= 50);"
    echo "  flow: "
#    echo "        d/dt[a] = "$accel";"
#    echo "        d/dt[v] = "$accel" - (0.01 * ((v - 0) * ((v) - 0)));"
    echo "        d/dt[v] = "$accel";"
    echo "        d/dt[d] = v;"
#    echo "        d/dt[clock] = 1;"
    echo "  jump: "

    for ((j=0; j < $DIMENSION; j++)); do {
	accelRes=`expr $accel + $j`
	accelMode=`getAccelMode $accelRes`
    if [ $accelRes -lt $DIMENSION ] ; then
	echo "        true ==> @"$accelMode" true;"
    fi

    decelRes=`expr $accel - $j`
    decelMode=`getDecelMode $decelRes`
    nDIMENSION=`expr -1 \* $DIMENSION`
    if [ $decelRes -gt $nDIMENSION ] ; then
	echo "        true ==> @"$decelMode" true;"
    fi
    }; done
    if [ $accel -eq 0 ] ; then
	echo "        (v = 0) ==> @1 true;"
    fi
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
    echo "        d/dt[v] = "$accel";"
#    echo "        d/dt[v] = "$accel" - (0.01 * ((v - 0) * ((v) - 0)));"
    echo "        d/dt[d] = v;"
#    echo "        d/dt[clock] = 1;"
    echo "  jump: "

    for ((j=0; j < $DIMENSION; j++)); do {
	accelRes=`expr $accel + $j`
	accelMode=`getAccelResMode $accelRes`

    if [ $accelRes -lt $DIMENSION ] ; then
#	echo "        (clock >= epsilon) ==> @"$accelMode" (clock' = 0);"
	echo "        true ==> @"$accelMode" true;"
    fi
#    echo "        (clock >= epsilon) ==> @"$decelMode" (clock' = 0);"
	decelRes=`expr $accel - $j`
	decelMode=`getDecelResMode $decelRes`
	nDIMENSION=`expr -1 \* $DIMENSION`
    if [ $decelRes -gt $nDIMENSION ] ; then
	echo "        true ==> @"$decelMode" true;"
    fi
    }; done
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
    echo "        (v <= 50);"
    echo "  flow: "
#    echo "        d/dt[a] = "$accel";"
    echo "        d/dt[v] = "$accel";"
#    echo "        d/dt[v] ="$accel" - (0.01 * ((v - 0) * ((v) - 0)));"
    echo "        d/dt[d] = v;"
#    echo "        d/dt[clock] = 1;"
    echo "  jump: "

    for ((j=0; j < $DIMENSION; j++)); do {
	accelRes=`expr $accel + $j`
	accelMode=`getAccelMode $accelRes`
    if [ $accelRes -lt $DIMENSION ] ; then
	echo "        true ==> @"$accelMode" true;"
    fi

    decelRes=`expr $accel - $j`
    decelMode=`getDecelMode $decelRes`
    nDIMENSION=`expr -1 \* $DIMENSION`
    if [ $decelRes -gt $nDIMENSION ] ; then
	echo "        true ==> @"$decelMode" true;"
    fi
    }; done
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
    echo "        d/dt[v] = "$accel";"
#    echo "        d/dt[v] ="$accel" - (0.01 * ((v - 0) * ((v) - 0)));"
    echo "        d/dt[d] = v;"
#    echo "        d/dt[clock] = 1;"
    echo "  jump: "

    for ((j=0; j < $DIMENSION; j++)); do {
	accelRes=`expr $accel + $j`
	accelMode=`getAccelResMode $accelRes`

    if [ $accelRes -lt $DIMENSION ] ; then
#	echo "        (clock >= epsilon) ==> @"$accelMode" (clock' = 0);"
	echo "        true ==> @"$accelMode" true;"
    fi
#    echo "        (clock >= epsilon) ==> @"$decelMode" (clock' = 0);"
	decelRes=`expr $accel - $j`
	decelMode=`getDecelResMode $decelRes`
	nDIMENSION=`expr -1 \* $DIMENSION`
    if [ $decelRes -gt $nDIMENSION ] ; then
	echo "        true ==> @"$decelMode" true;"
    fi
    }; done
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
    echo "     true ==> @1 (true);"
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
    echo " @1 (and (d = 30) (v = 0));"

}



echo "#define epsilon 0.00001"
echo "[0, 100] v;"
#echo "[-"$DIMENSION", "$DIMENSION"] a;"
echo "[0, 300] d;"
echo "[0, 300] time;"
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
#     outputModeOnAccelResist $i
}; done

for((i=1; i<=$DIMENSION; i++)) do {
    outputModeOnDecel $i
#    outputModeOnDecelResist $i
}; done

#outputEndMode

outputInit
outputGoal
