#!/bin/bash

DIMENSION=$1

header(){
    printf "#define capacity_gen 1600\n\
#define eps 0.001\n\
[0, 1000] time;\n"
    }


component_fuellevel() {
    printf "(component fuellevel_gen;\n\
[0, 1600] fuellevel_gen;\n"
    for((i = 0; i < $DIMENSION; i++)); do {
	printf "label do_start_refuel$i;\n\
	label do_stop_refuel$i;\n"
    }; done

   printf "label do_stop_gen;\n\
	label do_start_gen;\n"

   #no generator running, but refilling
   for((i = 0; i <= $DIMENSION; i++)); do {
       RATE=`expr 2 \* $i`
       UP_ONE=`expr $i + 1`
       DOWN_ONE=`expr $i - 1`
       printf "(mode fuellevel_nogen_t$i;\n\
 invt:\n\
 flow:\n\
   d/dt[fuellevel_gen] = $RATE;
 jump:\n"
       if [ $UP_ONE -le $DIMENSION ] ; then
	   for((j = 0; j < $DIMENSION; j++)); do {
	       printf "(do_start_refuel$j) : true ==> @fuellevel_nogen_t$UP_ONE true;\n"
	   };done
       fi
       if [ $DOWN_ONE -ge 0 ] ; then
	   for((j = 0; j < $DIMENSION; j++)); do {
	       printf "(do_stop_refuel$j) : true ==> @fuellevel_nogen_t$DOWN_ONE true;\n"
	   };done
       fi
       printf " (do_start_gen) : true ==> @fuellevel_gen_t$i true;\n"
       printf ")\n"
   }; done

   #generator running, but refilling
   for((i = 0; i <= $DIMENSION; i++)); do {
       RATE=`expr 2 \* $i`
       UP_ONE=`expr $i + 1`
       DOWN_ONE=`expr $i - 1`
       printf "(mode fuellevel_gen_t$i;\n\
 invt:\n\
 flow:\n\
   d/dt[fuellevel_gen] = ($RATE - 1);
 jump:\n"
       if [ $UP_ONE -le $DIMENSION ] ; then
	   for((j = 0; j < $DIMENSION; j++)); do {
	       printf "(do_start_refuel$j) : true ==> @fuellevel_gen_t$UP_ONE true;\n"
	   };done
       fi
       if [ $DOWN_ONE -ge 0 ] ; then
	   for((j = 0; j < $DIMENSION; j++)); do {
	       printf "(do_stop_refuel$j) : true ==> @fuellevel_gen_t$DOWN_ONE true;\n"
	   };done
       fi
       printf " (do_stop_gen) : true ==> @fuellevel_nogen_t$i true;\n"
       printf ")\n"
       }; done
   printf ")\n"
    }

component_generator_ran() {
    printf "(component generator_ran;\n\
label do_stop_gen;\n\
(mode ran_false;\n\
 invt:\n\
 flow:\n\
 jump:\n\
 (do_stop_gen) : true ==> @ran_true true;\n\
)\n\
(mode ran_true;\n\
 invt:\n\
 flow:\n\
 jump:\n\
\n\
)\n\
)\n\
"
}

component_available_tank() {
    printf "(component available_tank;\n\
label used_tank;\n\
(mode available_false;\n\
 invt:\n\
 flow:\n\
 jump:\n\
)\n\
(mode available_true;\n\
 invt:\n\
 flow:\n\
 jump:\n\
 (used_tank) : true ==> @available_false true;\n\
)\n\
)\n "
}

component_refueling_gen() {
    printf "(component refueling_gen;\n\
label start;\n\
label stop;\n\
(mode refueling_false;\n\
 invt:\n\
 flow:\n\
 jump:\n\
 (start) : true ==> @refueling_true true;\n\
)\n\
(mode refueling_true;\n\
 invt:\n\
 flow:\n\
 jump:\n\
 (stop) : true ==> @refueling_false true;\n\
)\n\
)\n "
}

component_generate_gen() {
    printf "(component generate_gen_automaton;\n\
[0, 1000] T_generate_gen_automaton; \n\
label do_stop_gen; \n\
label did_start_gen; \n\
label did_stop_gen; \n\
label do_start_gen; \n\
(mode running_generate_gen_automaton; \n\
invt:\n\
(T_generate_gen_automaton <= 1000); \n\
flow:\n\
d/dt[T_generate_gen_automaton] = 1; \n\
jump:\n\
(do_stop_gen): (and (T_generate_gen_automaton = 1000)) ==> @running_to_non_active_generate_gen_automaton (and (T_generate_gen_automaton' = 0) ); \n\
)\n\
(mode non_active_generate_gen_automaton; \n\
invt:\n\
flow:\n\
d/dt[T_generate_gen_automaton] = 0; \n\
jump:\n\
(do_start_gen): (true) ==> @interm_to_running_generate_gen_automaton (and (T_generate_gen_automaton' = 0)); \n\
)\n\
(mode interm_to_running_generate_gen_automaton; \n\
invt:\n\
(T_generate_gen_automaton <= 0); \n\
flow:\n\
d/dt[T_generate_gen_automaton] = 1; \n\
jump:\n\
(did_start_gen): true ==> @running_generate_gen_automaton (and (T_generate_gen_automaton' = 0)); \n\
)\n\
(mode running_to_non_active_generate_gen_automaton; \n\
invt:\n\
(T_generate_gen_automaton <= 0); \n\
flow:\n\
d/dt[T_generate_gen_automaton] = 1; \n\
jump: \n\
(did_stop_gen): (and (T_generate_gen_automaton = 0)) ==> @non_active_generate_gen_automaton (and (T_generate_gen_automaton' = 0)); \n\
)\n\
)\n "
}

component_refuel_gen_tank (){
    INSTANCE=$1
    TANK_DURATION=20
    RATE="2"
    printf "(component refuel_gen_tank1_automaton;\n\
[0, $TANK_DURATION] T_refuel_gen_tank1_automaton;\n\
[0, capacity_gen] fuellevel_gen;\n\

label do_stop_refuel;\n\
label did_start_refuel;\n\
label did_stop_refuel;\n\
label do_start_refuel;\n\
(mode running_refuel_gen_tank1_automaton;\n\
invt:\n\
(T_refuel_gen_tank1_automaton <= $TANK_DURATION);\n\
(fuellevel_gen<capacity_gen);\n\
flow:\n\
d/dt[T_refuel_gen_tank1_automaton] = 1;\n\
jump:\n\
(do_stop_refuel): (and (T_refuel_gen_tank1_automaton = $TANK_DURATION)) ==> @running_to_non_active_refuel_gen_tank1_automaton (and (T_refuel_gen_tank1_automaton' = 0));\n\
)\n\
(mode non_active_refuel_gen_tank1_automaton;\n\
invt:\n\
flow:\n\
d/dt[T_refuel_gen_tank1_automaton] = 0;\n\
jump:\n\
(do_start_refuel): true ==> @interm_to_running_refuel_gen_tank1_automaton (and (T_refuel_gen_tank1_automaton' = 0) );\n\
)\n\
(mode interm_to_running_refuel_gen_tank1_automaton;\n\
invt:\n\
(T_refuel_gen_tank1_automaton <= 0);\n\
flow:\n\
d/dt[T_refuel_gen_tank1_automaton] = 1;\n\
jump:\n\
(did_start_refuel): (and (T_refuel_gen_tank1_automaton = 0)) ==> @running_refuel_gen_tank1_automaton (and (T_refuel_gen_tank1_automaton' = 0));\n\
)\n\
(mode running_to_non_active_refuel_gen_tank1_automaton;\n\
invt:\n\
(T_refuel_gen_tank1_automaton <= 0);\n\
flow:\n\
d/dt[T_refuel_gen_tank1_automaton] = 1;\n\
jump:\n\
(did_stop_refuel): (and (T_refuel_gen_tank1_automaton = 0)) ==> @non_active_refuel_gen_tank1_automaton (and (T_refuel_gen_tank1_automaton' = 0));\n\
)\n\
)\n " 
}

component_lock() {
    
    printf "(component lock_automaton;\n"
   for((i = 0; i < $DIMENSION; i++)); do {
       printf "	label do_start_refuel$i;\n\
	label did_start_refuel$i;\n\
	label do_stop_refuel$i;\n\
        label did_stop_refuel$i;\n "
    }; done

   printf "label do_stop_gen;\n\
	label did_start_gen;\n\
	label do_start_gen;\n\
	label did_stop_gen;\n\
	
	(mode locked;\n\
	invt:\n\
	flow:\n\
	jump:\n "
   for((i = 0; i < $DIMENSION; i++)); do {
       printf "	(did_start_refuel$i): (true) ==> @unlocked (true);\n\
	(did_stop_refuel$i): (true) ==> @unlocked (true);\n "
       }; done
   printf "(did_start_gen): (true) ==> @unlocked (true);\n\
	(did_stop_gen): (true) ==> @unlocked (true);\n\
	)\n\
	
	(mode unlocked;\n\
	invt:\n\
	flow:\n\
	jump:\n "
   for((i = 0; i < $DIMENSION; i++)); do {
       printf "(do_start_refuel$i): (true) ==> @unlocked (true);\n\
	(do_stop_refuel$i): (true) ==> @unlocked (true);\n "
       }; done
   printf "(do_stop_gen): (true) ==> @unlocked (true);\n\
	(do_start_gen): (true) ==> @locked (true);\n\
	)\n\
)\n "
    }

components(){
    component_fuellevel
    component_generator_ran
    component_available_tank
    component_refueling_gen
    component_generate_gen
    for((i = 0; i < $DIMENSION; i++)); do {
	component_refuel_gen_tank $i
    }; done
    component_lock 
    
}

analyze() {
    TANK_DURATION=`expr 40 \* $DIMENSION`
    START_FUEL=`expr 1000 - $TANK_DURATION`
    
   printf "analyze: \n 
fuellevel_gen = fuellevel_gen[[], @fuellevel_nogen_t0 (fuellevel_gen = $START_FUEL)];\n"
    printf "lock_automaton0 = lock_automaton[[], @unlocked (true)];\n"

        printf "generate_gen_automaton0 = generate_gen_automaton[[T_generate_gen_automaton/time_generate_gen_automaton], @non_active_generate_gen_automaton (and  (fuellevel_gen = $START_FUEL) (T_generate_gen_automaton = 0))];\n"
       for((i = 0; i < $DIMENSION; i++)); do {
	   printf "refuel_gen_tank1_automaton$i = refuel_gen_tank1_automaton[[T_refuel_gen_tank1_automaton/time_rt$i,do_stop_refuel/do_stop_refuel$i,did_start_refuel/did_start_refuel$i,did_stop_refuel/did_stop_refuel$i,do_start_refuel/do_start_refuel$i], @non_active_refuel_gen_tank1_automaton (T_refuel_gen_tank1_automaton = 0)];\n"
       }; done
       
       printf "generator_ran0 = generator_ran[[], @ran_false true];\n"

       for((i = 0; i < $DIMENSION; i++)); do {
	   printf "available_tank$i = available_tank[[used_tank/do_start_refuel$i], @available_true true];\n\
refueling_gen$i = refueling_gen[[stop/do_stop_refuel$i, start/do_start_refuel$i], @refueling_false true];\n"
       }; done
       
       printf "( "
       for((i = 0; i < $DIMENSION; i++)); do {
	   printf "refuel_gen_tank1_automaton$i || available_tank$i  || refueling_gen$i || "
       }; done
  
       printf "lock_automaton0 || generate_gen_automaton0 || generator_ran0 || fuellevel_gen);\n\
goal: (@generator_ran0.ran_true): (true);\n\
" 


}

header
components
analyze
