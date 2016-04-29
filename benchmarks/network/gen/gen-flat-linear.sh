#!/bin/bash

DIMENSION=$1


NUMVARS=`expr 2 \* $DIMENSION`
NUMVARS=`expr $NUMVARS + 1`


currentstate=
states=

indexToBitArray(){
    index=$1
    for((i=0;i<$NUMVARS;i++)); do {
	    currentstate[$i]=`expr $index % 2`
	    #echo ${currentstate[$i]}
	    let "index >>= 1"
	}; done

}

currentStateOfTanki(){
    using=$1
    used=`expr $DIMENSION + $using`
    is_using=${currentstate[$using]}
    is_used=${currentstate[$used]}
    #illegal if is_using and not is_used

    if [ $is_using -eq "1" ]; then
	if [ $is_used -eq "0" ]; then
	    echo "3" #illegal
	else
	    echo "2" #used using
	fi
    else
	if [ $is_used -eq "1" ]; then
	    echo "1" #used not using
	else
	    echo "0" #not used not using
	fi
    fi
}

isIllegalState(){
    illegal="F"
    for((i=1; i <=$DIMENSION; i++)); do {
	    if [ ${currentstate[$i]} -eq "1" ] ; then
		twoi=`expr $DIMENSION + $i`
		if [ ${currentstate[$twoi]} -eq "0" ] ; then
		    illegal="T"
		fi
	    fi
	} ; done
    echo $illegal
}

currentStateOfGenerator(){
    echo ${currentstate[0]}
}

encodeStateFlip(){
    i1=$1
    i2=$2
    result=0
    for((j=`expr 2 \* $DIMENSION`; j>=0; j--)); do {
	    bit=${currentstate[$j]}
	    if [ $j == $i1 ]; then
		bit=`expr 1 - $bit`
	    fi
	    if [ -n "$i2" ] ; then
		if [ $j == $i2 ]; then
		    bit=`expr 1 - $bit`
		fi
	    fi
	    let "result |= bit"
	    let "result <<= 1"
	    #result=$result$bit
	} ;done
    let "result >>= 1"
    result=`expr $result + 1`
    echo $result
}




outputMode(){
    bitstate=$1
    indexToBitArray $bitstate

    illegal=`isIllegalState`
    MODE=`expr $bitstate + 1`
    if [ $illegal == "F" ]; then

   
    
   
    let "GEN_ON=`currentStateOfGenerator`"
    
    tanks_pouring=0
    for((i=1; i<=$DIMENSION; i++)) do {
	if [ `currentStateOfTanki $i` -eq "2" ] ; then
	    tank_pouring=1
	else
	    tank_pouring=0
	fi
       
	tank_rate=`expr $tank_pouring \* 2`
	tanks_pouring=`expr $tanks_pouring + $tank_rate`
    };done
    

    echo "{ mode ${MODE};"
    echo "  invt: "
    for((i=1; i<=$DIMENSION; i++)) do {
#	if [ `currentStateOfTanki $i` -eq "2" ]; then
	    echo "        (tank"$i"_refuel_time <= TANK_DURATION);"
#	fi
    }; done
#    if [ $GEN_ON -eq "1" ]; then
	    echo "        (generator_time <= GENERATOR_DURATION);"
#    fi
    echo "        (fuel_level >= 0);"

    echo "  flow: "
#    echo "        d/dt[clock] = 1;"
    if [ $GEN_ON -eq "0" ]; then
	echo "        d/dt[fuel_level] = "$tanks_pouring";"
	echo "        d/dt[generator_time] = 0;"
    else
	if [ $tanks_pouring -eq "0" ] ; then
	  echo "        d/dt[fuel_level] = -1;"
	else
	    echo "        d/dt[fuel_level] = "$tanks_pouring" - 1;"
	fi
	  echo "        d/dt[generator_time] = 1;"
    fi
    for((i=1; i<=$DIMENSION; i++)) do {
	tank_state=`currentStateOfTanki $i`
	if [ $tank_state -eq "2" ] ; then
	    echo "        d/dt[tank"$i"_refuel_time] = 1;"
	else
	    echo "        d/dt[tank"$i"_refuel_time] = 0;"
	fi
    }; done
    echo "  jump: "
    allTanksOff="T"
    for((i=1; i<=$DIMENSION; i++)) do {
	#stop or start pouring
	tank_state=`currentStateOfTanki $i`
#	echo "Tank State = "$tank_state
#	if [ $tank_state -eq "0" ] ; then
	    #tank is not used and is not available
	    #No transition
	if [ $tank_state -eq "0" ] ; then
	    #tank is not used and is available
	    #transition to on, flip avail and using
	    #pour at any time
	    j=`expr $DIMENSION + $i`
	    flip_tank_i=`encodeStateFlip $i $j`
#	    echo "        (and (tank"$i"_refuel_time <= TANK_DURATION) (clock >= epsilon)) ==> @"$flip_tank_i" (clock' = 0);"
	    echo "        (and (tank"$i"_refuel_time <= TANK_DURATION) ) ==> @"$flip_tank_i" true;"
	fi
         
	if [ $tank_state -eq "2" ] ; then
	    #tank is being used and not available
	    #transition to off, flip using
	    #end pour when done
	    flip_tank_i=`encodeStateFlip $i`
#	    echo "        (and (tank"$i"_refuel_time = TANK_DURATION) (clock >= epsilon)) ==> @"$flip_tank_i" (clock' = 0);"
	    echo "        (and (tank"$i"_refuel_time = TANK_DURATION) ) ==> @"$flip_tank_i" true;"
	    allTanksOff="F"
#	else
#	    echo "ILLEGAL state for tank $i"
	fi
	


    }; done
    
    gen=0
    generator_flip=`encodeStateFlip $gen`
    if [ $GEN_ON -eq "0" ]; then
	if [ $allTanksOff == "T" ] ; then
	#finish if all actions done
#	    echo "        (and (clock >= epsilon) (generator_time = GENERATOR_DURATION)) ==> @"`expr $states + 1`" (clock' = 0);"
	    echo "        (and  (generator_time = GENERATOR_DURATION)) ==> @"`expr $states + 1`" true;"
	fi
	#can turn on generator at any time
#	echo "        (and (clock >= epsilon) (generator_time <= GENERATOR_DURATION)) ==> @"$generator_flip" (clock' = 0);"
	echo "        (and (generator_time <= GENERATOR_DURATION)) ==> @"$generator_flip" true;"
    else
#	echo "        (and (clock >= epsilon) (generator_time = GENERATOR_DURATION)) ==> @"$generator_flip" (clock' = 0);"
	echo "        (and (generator_time = GENERATOR_DURATION)) ==> @"$generator_flip" true;"
#	echo "        (and (generator_time = GENERATOR_DURATION)) ==> @"`expr $states + 1`" true;"
#	echo "        (and (clock >= epsilon) (generator_time = GENERATOR_DURATION)) ==> @"`expr $states + 1`" (clock' = 0);"
    fi
    echo "}"
else
	echo "{ mode "$MODE";"
	echo "  flow:"
#	echo "        d/dt[clock] = 0;"
	echo "        d/dt[fuel_level] = 0;"
	echo "        d/dt[generator_time] = 0;"
	for((i=1; i<=$DIMENSION; i++)) do {
	    echo "        d/dt[tank"$i"_refuel_time] = 0;"
	}; done	
	echo "  jump:"
	echo "}"
fi
}



outputInit(){
    echo "init:"
echo "@1 (and (fuel_level          = STARTING_FUEL)"
echo "	      (generator_time      = 0) "
#echo "	      (clock      = 0) "
for((i=1; i<=$DIMENSION; i++)) do {
    echo "	      (tank"$i"_refuel_time   = 0)"
}; done
echo "   );"

}

outputGoalMode(){
echo "{ mode "`expr $states + 1`";"
echo "  flow: "
#echo "        d/dt[clock] = 0;"
echo "        d/dt[fuel_level] = 0;"
echo "        d/dt[generator_time] = 0;"
for((i=1; i<=$DIMENSION; i++)) do {
    echo "        d/dt[tank"$i"_refuel_time] = 0;"
}; done
echo "  jump: "
echo "}"
  
}


outputGoal(){
    echo "goal:"
    echo " @"`expr $states + 1`" (and (generator_time = GENERATOR_DURATION));"

}


TANK_DURATION=`expr 40 \* $DIMENSION`
START_FUEL=`expr 1000 - $TANK_DURATION`

echo "#define STARTING_FUEL "$START_FUEL
echo "#define GENERATOR_CAPACITY 1600"
echo "#define TANK_DURATION 20"
echo "#define GENERATOR_DURATION 1000"
#echo "#define epsilon 0.00001"


echo "[0, GENERATOR_CAPACITY] fuel_level;"
for((i=1; i<=$DIMENSION; i++)) do {
echo "[0, TANK_DURATION] tank"$i"_refuel_time;"
}; done
echo "[0, GENERATOR_DURATION] generator_time;"
echo "[0, 1000] time;"
#echo "[0, 1001] clock;"

let "states=1"
let "shift=`expr 2 \* $DIMENSION`"
let "states<<=`expr $shift + 1`"

for((s=0;s<$states;s++)); do { #generator on?
	outputMode $s 
}; done
outputGoalMode


outputInit
outputGoal
