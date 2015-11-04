#!/bin/bash

NUM=5
NONSENSE=5
for((i=1; i <=$NUM; i++)); do {
	f=$i #`expr $i \* 10`
	if [ ${f} -lt 10 ]; then
	    PREFIX="0"
	 else
	    PREFIX=""
	 fi
	for((j=1; j <=$NONSENSE; j++)); do {
		for d in 0.001 0.1 1.0 2.0 4.0; do {	
			for relaxTime in true ; do {
#		for relaxJump in true false; do {
				for sat in "" ; do {
					./gen-instance.sh -s ${f} -o targeting_${PREFIX}${f}_${j}_${d}_${relaxTime}_${relaxJump}${sat}.drh -d ${d} -t $relaxTime $sat -n ${j}
				    }; done
			    }; done
		    }; done
            }; done
    }; done
