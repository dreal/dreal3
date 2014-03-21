#!/usr/bin/gnuplot

set terminal postscript color
set style data  linespoints

set xlabel "Number of Adjustment Steps" 
set ylabel "Total Time (s)"
set key top left


set output "barn_door_delta.ps"
set title "Barn Door Solving Time (s), Delta Heuristic, Various Delta"

plot 'barn_door_0.001_true_true--delta-heuristic.out' t "delta, 0.001", \
     'barn_door_0.1_true_true--delta-heuristic.out' t "delta, 0.1", \
     'barn_door_1.0_true_true--delta-heuristic.out' t "delta, 1.0", \
     'barn_door_2.0_true_true--delta-heuristic.out' t "delta, 2.0", \
     'barn_door_4.0_true_true--delta-heuristic.out' t "delta, 4.0"

set title "Barn Door Solving Time (s),Epsilon Heuristic, Various Delta"
set output "barn_door_epsilon.ps"
plot 'barn_door_0.001_true_true.out' t "epsilon, 0.001", \
     'barn_door_0.1_true_true.out' t "epsilon, 0.1", \
     'barn_door_1.0_true_true.out' t "epsilon, 1.0", \
     'barn_door_2.0_true_true.out' t "epsilon, 2.0", \
     'barn_door_4.0_true_true.out' t "epsilon, 4.0"

set ylabel "Runtime Improvement Factor"

set title "Barn Door Solving Time (s), Delta  Heuristic, Various Delta"
set output "barn_door_improve-delta.ps"
plot 'barn_door--delta-heuristic.out' using 1:($2/$3) t "delta, 0.001/0.1" ls 2, \
     'barn_door--delta-heuristic.out' using 1:($2/$4) t "delta, 0.001/1.0" ls 3, \
     'barn_door--delta-heuristic.out' using 1:($2/$5) t "delta, 0.001/2.0" ls 4, \
     'barn_door--delta-heuristic.out' using 1:($2/$6) t "delta, 0.001/4.0" ls 5

set title "Barn Door Solving Time (s), Epsilon Heuristic, Various Delta"
set output "barn_door_improve-epsilon.ps"
plot 'barn_door.out' using 1:($2/$3) t "epsilon, 0.001/0.1" ls 2 , \
     'barn_door.out' using 1:($2/$4) t "epsilon, 0.001/1.0" ls 3, \
     'barn_door.out' using 1:($2/$5) t "epsilon, 0.001/2.0" ls 4, \
     'barn_door.out' using 1:($2/$6) t "epsilon, 0.001/4.0" ls 5

