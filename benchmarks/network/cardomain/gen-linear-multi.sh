#!/bin/bash

DIMENSION=$1

header () {
    printf "[0, 1000] time;\n"
}

moving() {
    printf "(component moving_automaton;
[-1000, 1000] a;
[-1000, 1000] d;
[-1000, 1000] v;
label do_stop;
label do_start;
(mode on_moving_automaton;
invt:
flow:
d/dt[d] = v;
d/dt[v] = a;
d/dt[a] = 0;
jump:
(do_stop) : true ==> @off_moving_automaton true;
)

(mode off_moving_automaton;
invt:
flow:
d/dt[d] = 0;
d/dt[v] = 0;
d/dt[a] = 0;
jump:
(do_start) : true ==> @on_moving_automaton true;
)

)\n"
}

start() {
    printf "(component start_automaton;

label did_start;
label do_start;
(mode on_start_automaton;
invt:
flow:
jump:
(did_start): true ==> @off_start_automaton true;
)
(mode off_start_automaton;
invt:
flow:
jump:
(do_start): true ==> @on_start_automaton true;

)
)\n"
}

stop() {
        printf "(component stop_automaton;

label did_stop;
label do_stop;
(mode on_stop_automaton;
invt:
flow:
jump:
(did_stop): true ==> @off_stop_automaton true;
)
(mode off_stop_automaton;
invt:
flow:
jump:
(do_stop): (and (v = 0) (a = 0)) ==> @on_stop_automaton true;

)
)\n"
}

accelerate() {
    INSTANCE=$1
        printf "(component accelerate_automaton$INSTANCE;
label did_accel$INSTANCE;
label do_accel$INSTANCE;
(mode on_accelerate_automaton;
invt:
flow:
jump:
(did_accel$INSTANCE): true ==> @off_accelerate_automaton true;
)
(mode off_accelerate_automaton;
invt:
flow:
jump:
(do_accel$INSTANCE): true ==> @on_accelerate_automaton (and (a' = a + $INSTANCE));

)
)\n"
}

decelerate() {
    INSTANCE=$1
        printf "(component decelerate_automaton$INSTANCE;
label did_decel$INSTANCE;
label do_decel$INSTANCE;
(mode on_decelerate_automaton;
invt:
flow:
jump:
(did_decel$1): true ==> @off_decelerate_automaton true;
)
(mode off_decelerate_automaton;
invt:
flow:
jump:
(do_decel$INSTANCE): true ==> @on_decelerate_automaton (and (a' = a - $INSTANCE));
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
[0,1] lock_timer;\n"
	for((i = 1; i <= $DIMENSION; i++)); do {
	    printf "label did_accel$i;
label do_accel$i;
label did_decel$i;
label do_decel$i;\n"
}; done

printf "label do_start;
label did_start;
label do_stop;
label did_stop;

(mode lock_enabled;
invt:
(lock_timer <= 0);
flow:
d/dt[lock_timer] = 1;
jump:\n"
	for((i = 1; i <= $DIMENSION; i++)); do {
	    printf "(did_accel$i): (lock_timer >= 0) ==> @lock_released (true);
(did_decel$i): (lock_timer >= 0) ==> @lock_released (true);\n"
}; done

	printf "(did_start): (lock_timer >= 0) ==> @lock_released (true);
(did_stop): (lock_timer >= 0) ==> @lock_released (true);
)
(mode lock_released;
invt:
flow:
d/dt[lock_timer] = 0;
jump:\n"

	for((i = 1; i <= $DIMENSION; i++)); do {
	    printf "(do_accel$i): (true) ==> @lock_enabled (lock_timer' = 0);
(do_decel$i): (true) ==> @lock_enabled (lock_timer' = 0);\n"
	}; done
	printf "(do_start): (true) ==> @lock_enabled (lock_timer' = 0);
(do_stop): (true) ==> @lock_enabled (lock_timer' = 0);
)
)\n"
    }

components() {
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
moving_automaton0 = moving_automaton[[], @off_moving_automaton (and (a = 0) (d = 0) (v = 0))];
\n"
    for((i = 1; i <= $DIMENSION; i++)); do {
	printf "accelerate_automaton$i = accelerate_automaton$i[[], @off_accelerate_automaton true];
decelerate_automaton$i = decelerate_automaton$i[[], @off_decelerate_automaton true];\n"
    }; done
    printf "running_automaton0 = running[[], @running_false true];
start_automaton0 = start_automaton[[], @off_start_automaton true];
stop_automaton0 = stop_automaton[[], @off_stop_automaton true];
lock_automaton0 = lock_automaton[[lock_timer/time_lock], @lock_released (lock_timer=0)];

(
moving_automaton0 ||\n"
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

