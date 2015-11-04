#!/usr/bin/gnuplot

set terminal postscript color
set style data  linespoints

set xlabel "Instance" 
set ylabel "Total Time (s)"
set key top left
set logscale y

set output "barn_door_delta.ps"
set title "Barn Door Solving Time (s), 5 nonsense, Delta Heuristic, various Delta"
plot 'barn_door_0.001_true_--delta-heuristic.out' using 3  t "0.001", \
     'barn_door_0.1_true_--delta-heuristic.out' using 3 t "0.1", \
     'barn_door_1.0_true_--delta-heuristic.out' using 3  t "1.0", \
     'barn_door_2.0_true_--delta-heuristic.out' using 3  t "2.0", \
     'barn_door_4.0_true_--delta-heuristic.out' using 3 t "4.0"



set output "barn_door_comparo.ps"
set title "Barn Door Solving Time (s),  5 nonsense, Delta Heuristic vs Epsilon Heuristic,Delta = 1.0"
plot 'barn_door_1.0_true_--delta-heuristic.out'  using 3  t "delta, 1.0", \
     'barn_door_1.0_true_.out'  using 3  t "epsilon, 1.0"
     
set output "barn_door_epsilon.ps"
set title "Barn Door Solving Time (s), 5 nonsense, Epsilon Heuristic, various Delta"
plot [0:16] 'barn_door_0.001_true_.out' using 3  t "0.001", \
     'barn_door_0.1_true_.out' using 3 t "0.1", \
     'barn_door_1.0_true_.out' using 3  t "1.0", \
     'barn_door_2.0_true_.out' using 3  t "2.0", \
     'barn_door_4.0_true_.out' using 3 t "4.0"


set xlabel "Jumps"
set ylabel "Irrel"
set zlabel "Total Time (s)"
set grid x y z back
set xyplane 0
set view 30,110,1,1.5
set xrange [*:4] reverse
set yrange [1:5] 
set xtics 1
set ytics 1
unset logscale y

set output "targeting_delta3d.ps"
set title "Targeting Solving Time (s), Delta Heuristic"
splot 'barn_door_0.001_true_--delta-heuristic.out' using 1:2:3 every  :::0::0  t "0.001" ls 1, \
      'barn_door_0.001_true_--delta-heuristic.out' using 1:2:3 every  :::1::1  notit ls 1, \
      'barn_door_0.001_true_--delta-heuristic.out' using 1:2:3 every  :::2::2  notit ls 1, \
      'barn_door_0.1_true_--delta-heuristic.out'  using 1:2:3 every  :::0::0 t "0.1" ls 2, \
      'barn_door_0.1_true_--delta-heuristic.out' using 1:2:3 every  :::1::1  notit ls 2, \
      'barn_door_0.1_true_--delta-heuristic.out' using 1:2:3 every  :::2::2  notit ls 2, \
      'barn_door_1.0_true_--delta-heuristic.out' using 1:2:3 every  :::0::0 t "1.0" ls 3, \
      'barn_door_1.0_true_--delta-heuristic.out' using 1:2:3 every  :::1::1 notit ls 3, \
      'barn_door_1.0_true_--delta-heuristic.out' using 1:2:3 every  :::2::2 notit ls 3, \
      'barn_door_1.0_true_--delta-heuristic.out' using 1:2:3 every  :::3::3 notit ls 3, \
      'barn_door_2.0_true_--delta-heuristic.out' using 1:2:3 every  :::0::0 t "2.0" ls 4, \
      'barn_door_2.0_true_--delta-heuristic.out' using 1:2:3 every  :::1::1 notit ls 4, \
      'barn_door_2.0_true_--delta-heuristic.out' using 1:2:3 every  :::2::2 notit ls 4, \
      'barn_door_2.0_true_--delta-heuristic.out' using 1:2:3 every  :::3::3 notit ls 4, \
      'barn_door_4.0_true_--delta-heuristic.out' using 1:2:3 every  :::0::0 t "4.0" ls 5, \
      'barn_door_4.0_true_--delta-heuristic.out' using 1:2:3 every  :::1::1 notit ls 5, \
      'barn_door_4.0_true_--delta-heuristic.out' using 1:2:3 every  :::2::2 notit ls 5, \
      'barn_door_4.0_true_--delta-heuristic.out' using 1:2:3 every  :::3::3 notit ls 5

set output "targeting_epsilon3d.ps"
set title "Targeting Solving Time (s), Epsilon Heuristic"

splot 'barn_door_0.001_true_.out' using 1:2:3 every  :::0::0  t "0.001" ls 1, \
      'barn_door_0.001_true_.out' using 1:2:3 every  :::1::1  notit ls 1, \
      'barn_door_0.001_true_.out' using 1:2:3 every  :::2::2  notit ls 1, \
      'barn_door_0.1_true_.out'  using 1:2:3 every  :::0::0 t "0.1" ls 2, \
      'barn_door_0.1_true_.out' using 1:2:3 every  :::1::1  notit ls 2, \
      'barn_door_0.1_true_.out' using 1:2:3 every  :::2::2  notit ls 2, \
      'barn_door_1.0_true_.out' using 1:2:3 every  :::0::0 t "1.0" ls 3, \
      'barn_door_1.0_true_.out' using 1:2:3 every  :::1::1 notit ls 3, \
      'barn_door_1.0_true_.out' using 1:2:3 every  :::2::2 notit ls 3, \
      'barn_door_1.0_true_.out' using 1:2:3 every  :::3::3 notit ls 3, \
      'barn_door_2.0_true_.out' using 1:2:3 every  :::0::0 t "2.0" ls 4, \
      'barn_door_2.0_true_.out' using 1:2:3 every  :::1::1 notit ls 4, \
      'barn_door_2.0_true_.out' using 1:2:3 every  :::2::2 notit ls 4, \
      'barn_door_2.0_true_.out' using 1:2:3 every  :::3::3 notit ls 4, \
      'barn_door_4.0_true_.out' using 1:2:3 every  :::0::0 t "4.0" ls 5, \
      'barn_door_4.0_true_.out' using 1:2:3 every  :::1::1 notit ls 5, \
      'barn_door_4.0_true_.out' using 1:2:3 every  :::2::2 notit ls 5, \
      'barn_door_4.0_true_.out' using 1:2:3 every  :::3::3 notit ls 5

set zlabel "Runtime Improvement Factor"
set view 30,290,1,1.5
set yrange [1:5] reverse


set output "targeting_delta3d_improvement.ps"
set title "Targeting Improvement Factor (over delta=0.001), Delta Heuristic"
splot 'barn_door_delta_all.out' using 1:2:($3/$4) every  :::0::0  t "0.1" ls 2, \
      'barn_door_delta_all.out' using 1:2:($3/$4) every  :::1::1  notit ls 2, \
      'barn_door_delta_all.out' using 1:2:($3/$4) every  :::2::2  notit ls 2, \
      'barn_door_delta_all.out' using 1:2:($3/$5) every  :::0::0 t "1.0" ls 3, \
      'barn_door_delta_all.out' using 1:2:($3/$5) every  :::1::1  notit ls 3, \
      'barn_door_delta_all.out' using 1:2:($3/$5) every  :::2::2  notit ls 3, \
      'barn_door_delta_all.out' using 1:2:($3/$5) every  :::3::3  notit ls 3, \
      'barn_door_delta_all.out' using 1:2:($3/$6) every  :::0::0 t "2.0" ls 4, \
      'barn_door_delta_all.out' using 1:2:($3/$6) every  :::1::1 notit ls 4, \
      'barn_door_delta_all.out' using 1:2:($3/$6) every  :::2::2 notit ls 4, \
      'barn_door_delta_all.out' using 1:2:($3/$6) every  :::3::3 notit ls 4, \
      'barn_door_delta_all.out' using 1:2:($3/$7) every  :::0::0 t "4.0" ls 5, \
      'barn_door_delta_all.out' using 1:2:($3/$7) every  :::1::1 notit ls 5, \
      'barn_door_delta_all.out' using 1:2:($3/$7) every  :::2::2 notit ls 5, \
      'barn_door_delta_all.out' using 1:2:($3/$7) every  :::3::3 notit ls 5

set output "targeting_epsilon3d_improvement.ps"
set title "Targeting Improvement Factor (over delta=0.001), Epsilon Heuristic"

splot 'barn_door_epsilon_all.out' using 1:2:($3/$4) every  :::0::0  t "0.1" ls 2, \
      'barn_door_epsilon_all.out' using 1:2:($3/$4) every  :::1::1  notit ls 2, \
      'barn_door_epsilon_all.out' using 1:2:($3/$4) every  :::2::2  notit ls 2, \
      'barn_door_epsilon_all.out' using 1:2:($3/$5) every  :::0::0 t "1.0" ls 3, \
      'barn_door_epsilon_all.out' using 1:2:($3/$5) every  :::1::1  notit ls 3, \
      'barn_door_epsilon_all.out' using 1:2:($3/$5) every  :::2::2  notit ls 3, \
      'barn_door_epsilon_all.out' using 1:2:($3/$5) every  :::3::3  notit ls 3, \
      'barn_door_epsilon_all.out' using 1:2:($3/$6) every  :::0::0 t "2.0" ls 4, \
      'barn_door_epsilon_all.out' using 1:2:($3/$6) every  :::1::1 notit ls 4, \
      'barn_door_epsilon_all.out' using 1:2:($3/$6) every  :::2::2 notit ls 4, \
      'barn_door_epsilon_all.out' using 1:2:($3/$6) every  :::3::3 notit ls 4, \
      'barn_door_epsilon_all.out' using 1:2:($3/$7) every  :::0::0 t "4.0" ls 5, \
      'barn_door_epsilon_all.out' using 1:2:($3/$7) every  :::1::1 notit ls 5, \
      'barn_door_epsilon_all.out' using 1:2:($3/$7) every  :::2::2 notit ls 5, \
      'barn_door_epsilon_all.out' using 1:2:($3/$7) every  :::3::3 notit ls 5