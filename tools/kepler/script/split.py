#!/usr/bin/python
import sys
import os
trace_name = sys.argv[1]
base_name, ext = os.path.splitext(trace_name)
input = open(trace_name)
counter = 0

def get_newname():
    global counter
    counter = counter + 1
    return base_name + "_" + str(counter) + ".trace"

# Create a init out
output = sys.stdout

for line in input:
    if line.startswith("Precision:"):
        output = open(get_newname(), "w")
    output.write(line)
