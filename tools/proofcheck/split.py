#!/usr/bin/python
import sys
import os
import shutil

trace_name = sys.argv[1]
base_name, ext = os.path.splitext(trace_name)
input = open(trace_name)
counter = 0

def touch(fname, times=None):
    with file(fname, 'a'):
        os.utime(fname, times)

def get_newname():
    global counter
    counter = counter + 1
    return base_name + "_" + str(counter) + ".trace"

# Create a init out
output = sys.stdout

#print "Split " + trace_name,

for line in input:
    if line.startswith("Precision:"):
        output = open(get_newname(), "w")
    output.write(line)

#print " into " + str(counter) + " traces."

if counter == 1:
    touch(trace_name)
    os.remove(base_name + "_1.trace")
else:
    os.remove(trace_name)

