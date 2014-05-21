#!/usr/bin/gnuplot

set terminal postscript color
set style data  linespoints

set xlabel "Grid Dimension" 
set ylabel "Total Time (s)"
set key top left


set output "grid-sat.ps"
set title "Grid Solving Time (s) -- SAT problem"

plot 'grid.out' using 1:2 t "BMC Heuristic, All Paths", \
     'grid.out' using 1:3 t "All Paths", \
     'grid.out' using 1:4 t "Iterate Single Path"
