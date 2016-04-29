#!/bin/bash

DIMENSION=$1

header () {
    printf "[0, 1000] time;\n"
}

acceleration() {
    
   printf "(component acceleration;
 [-1000, 1000] a;
(mode a_zero;
invt:
flow:
d/dt[a] = 0;
jump:
)
)\n"
}

distance() {
    printf "(component distance;
 [-1000, 1000] d;
 [-1000, 1000] v;	
label do_start;
label do_stop;
(mode d_zero;
invt:
flow:
d/dt[d] = 0;
jump:
(do_start) : true ==> @d_v true;
)

(mode d_v;
invt:
flow:
d/dt[d] = v;
jump:
(do_stop) : true ==> @d_zero true;
)

)\n"
}

velocity() {
    printf "(component velocity;
 [-1000, 1000] a;
 [-1000, 1000] v;	
label do_start;
label do_stop;
(mode v_zero;
invt:
flow:
d/dt[v] = 0;
jump:
(do_start) : true ==> @v_a true;
(do_stop) : true ==> @v_zero true;
)

(mode v_a;
invt:
flow:
d/dt[v] = a;
jump:
(do_stop) : true ==> @v_zero true;
)
)\n"
    }

moving() {
    printf "(component moving_automaton;
label do_stop;
label do_start;
(mode on_moving_automaton;
invt:
flow:
jump:
(do_stop) : true ==> @off_moving_automaton true;
)

(mode off_moving_automaton;
invt:
flow:
jump:
(do_start) : true ==> @on_moving_automaton true;
)

)\n"
}

start() {
    printf "(component start_automaton;
 [-1000, 1000] v;
label do_start;

(mode off_start_automaton;
invt:
flow:
jump:
(do_start): true ==> @off_start_automaton true;

)
)\n"
}

stop() {
        printf "(component stop_automaton;
 [-1000, 1000] v;
[-1000, 1000] a;
label do_stop;

(mode off_stop_automaton;
invt:
flow:
jump:
(do_stop): (and (v = 0) (a = 0)) ==> @off_stop_automaton true;

)
)\n"
}

accelerate() {
    INSTANCE=$1
        printf "(component accelerate_automaton$INSTANCE;
label do_accel$INSTANCE;

(mode off_accelerate_automaton;
invt:
flow:
jump:
(do_accel$INSTANCE): true ==> @off_accelerate_automaton (and (a' = a + $INSTANCE));

)
)\n"
}

decelerate() {
    INSTANCE=$1
        printf "(component decelerate_automaton$INSTANCE;
label do_decel$INSTANCE;

(mode off_decelerate_automaton;
invt:
flow:
jump:
(do_decel$INSTANCE): true ==> @off_decelerate_automaton (and (a' = a - $INSTANCE));
)
)\n"
}

running() {
        printf "(component running;
label do_stop;
label do_start;\n"
	for((i = 1; i <= $DIMENSION; i++)); do {
	    printf "label do_accel$i;
label do_decel$i;\n"
}; done

	printf "(mode running_true;
invt:
flow:
jump:
(do_stop): true ==> @running_false true;\n"
	for((i = 1; i <= $DIMENSION; i++)); do {
	    printf "(do_accel$i): true ==> @running_true true;
(do_decel$i): true ==> @running_true true;\n"
	}; done
	printf ")
(mode running_false;
invt:
flow:
jump:
(do_start): true ==> @running_true true;
)
)\n"
}


lock() {
        printf "(component lock_automaton;
\n"
	for((i = 1; i <= $DIMENSION; i++)); do {
	    printf "label do_accel$i;
label do_decel$i;\n"
}; done

printf "label do_start;
label do_stop;



(mode lock_released;
invt:
flow:
jump:\n"

	for((i = 1; i <= $DIMENSION; i++)); do {
	    printf "(do_accel$i): (true) ==> @lock_released true;
(do_decel$i): (true) ==> @lock_released true;\n"
	}; done
	printf "(do_start): (true) ==> @lock_released true;
(do_stop): (true) ==> @lock_released true;
)
)\n"
    }

components() {
    acceleration
    distance
    velocity
    moving
    start
    stop
    for((j = 1; j <= $DIMENSION; j++)); do {
	accelerate $j
	decelerate $j
    }; done
    running
    lock
}


analyze() {
    printf "analyze: 
moving_automaton0 = moving_automaton[[], @off_moving_automaton true];\n"
	for((i = 1; i <= $DIMENSION; i++)); do {
	printf "accelerate_automaton$i = accelerate_automaton$i[[], @off_accelerate_automaton true];
decelerate_automaton$i = decelerate_automaton$i[[], @off_decelerate_automaton true];\n"
    }; done
    printf "running_automaton0 = running[[], @running_false true];
start_automaton0 = start_automaton[[], @off_start_automaton true];
stop_automaton0 = stop_automaton[[], @off_stop_automaton true];
lock_automaton0 = lock_automaton[[], @lock_released true];
acceleration0 = acceleration[[], @a_zero (a = 0)];
velocity0 = velocity[[], @v_zero (v = 0)];
distance0 = distance[[], @d_zero (d = 0)];

(
acceleration0 ||
velocity0 ||
distance0 ||
moving_automaton0\n"
	for((i = 1; i <= $DIMENSION; i++)); do {
	printf "accelerate_automaton$i ||
decelerate_automaton$i ||\n"
    }; done
printf "start_automaton0 ||
stop_automaton0 ||
lock_automaton0 ||
running_automaton0
);

goal:
(@running_automaton0.running_false) : (and (d =30) );\n"
}

header
components
analyze

