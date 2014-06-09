#!/usr/bin/gnuplot

set terminal postscript color
set style data  linespoints

set xlabel "Grid Dimension" 

set key top left
set logscale y

set ylabel "Total Time (s)"
set output "grid-sat.ps"
set title "Grid Solving Time (s) -- SAT problem"
plot 'grid.out' using 1:2 t "Full Encoding", \
     'grid.out' using 1:5 t "Reduced Encoding"


set ylabel "MiniSat Nodes"
set output "grid-sat-nodes.ps"
set title "Grid SAT solver nodes -- SAT problem"
plot 'grid.out' using 1:3 t "Full Encoding", \
     'grid.out' using 1:6 t "Reduced Encoding"

set ylabel "ICP Nodes"
set output "grid-icp-nodes.ps"
set title "Grid ICP solver nodes -- SAT problem"
plot 'grid.out' using 1:4 t "Full Encoding", \
     'grid.out' using 1:7 t "Reduced Encoding"
