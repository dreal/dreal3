#!/usr/bin/env python

"""
Convert JSON data to human-readable form.

Usage:
  prettyJSON.py inputFile [outputFile]
"""

import sys
import simplejson as json

def main(args):
    try:
    	inputFile = open(args[1])
    	input = json.load(inputFile)
    	inputFile.close()
    except IndexError:
    	usage()
    	return False
    if len(args) < 3:
    	print json.dumps(input, sort_keys = False, indent = 4)
    else:
    	outputFile = open(args[2], "w")
    	json.dump(input, outputFile, sort_keys = False, indent = 4)
    	outputFile.close()
    return True

def usage():
    print __doc__

if __name__ == "__main__":
    sys.exit(not main(sys.argv))
