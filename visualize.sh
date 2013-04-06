#!/bin/bash
##################################################################
# Usage:
# $ ./visualize.sh "<SEQ_OF_MODES>" <NUM_OF_MODES> <JSON_FILE>
#
# Example:
# $ ./visualize.sh "[1,2,1,2,1,2,1,2,1]" 2 data.json
#
# Author: Soonho Kong <soonhok@cs.cmu.edu>
##################################################################

function new_text {
python << END
import sys
x = $1
num_of_modes = int($2)
sys.stdout.write("[")
for i in range(0, len(x)):
    if i != 0:
        sys.stdout.write(",")
    sys.stdout.write(str(i * num_of_modes + x[i]))
sys.stdout.write("]")
END


}

TEXT=$1
NUM_OF_MODES=$2
NEW_TEXT=`new_text $1 $2`
JSON=$3
JSON_OLD=$3.old

echo "$TEXT => $NEW_TEXT"
mv $JSON $JSON_OLD
sed s/\"groups\":\ .\*/\"groups\":\ $NEW_TEXT/ $JSON_OLD > $JSON
