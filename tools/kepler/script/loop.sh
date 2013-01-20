#!/bin/bash

########################################
# TIME STAMP
SMT_TIMESTAMP=./SMT_TIMESTAMP
CHECK_TIMESTAMP=./CHECK_TIMESTAMP

# TODO
TODO=./TODO

# QUEUE
SMT_QUEUE=./SMT_QUEUE
CHECK_QUEUE=./CHECK_QUEUE

# MAX (NUM of Processors to Use)
MAX=25

RUN_SINGLE=~/work/dreal2/tools/kepler/script/run_single.sh
PCHECKER=~/work/dreal2/tools/kepler/proof_checker/main.native
SPLIT=~/work/dreal2/tools/kepler/script/split.py

if [ ! -f $SMT_TIMESTAMP ]
then
    touch $SMT_TIMESTAMP -d "2000-01-01 00:00:00"
fi

if [ ! -f $CHECK_TIMESTAMP ]
then
    touch $CHECK_TIMESTAMP -d "2000-01-01 00:00:00"
fi

########################################

touch $TODO

while [ -f $TODO ]
do
    # INITIALIZE QUEUES
    rm -rf $SMT_QUEUE $CHECK_QUEUE
    touch $SMT_QUEUE $CHECK_QUEUE

    # TODO will be re-created if we need more things TO DO
    rm $TODO

    # Find SMT2 files and add to SMT QUEUE
    # 1) Newer than SMT_TIMESTAMP
    # 2) Do not have the result, yet
    for SMT2 in `find ./ -name "*.smt2" -newer $SMT_TIMESTAMP`
    do
        BASE=${SMT2//.smt2/}
        if [ ! -f $BASE.result ]
        then
            echo $BASE >> $SMT_QUEUE
            echo `date`: "Adding ${BASE}.smt2 to the SMT Queue"
        fi
    done

    # UPDATE: SMT TIMESTAMP
    touch $SMT_TIMESTAMP

    # RUN in Parallel: dReal2 to generate results (.result, .time, .trace)
    if [ -s $SMT_QUEUE ]
    then
        echo `date`: "RUN DREAL2:"
        cat $SMT_QUEUE | parallel --max-procs=$MAX "$RUN_SINGLE {}.smt2"
    fi

    # UPDATE: CHECK TIMESTAMP
    touch $CHECK_TIMESTAMP

    # RUN: split.py
    if [ -s $SMT_QUEUE ]
    then
	echo `date`: "RUN SPLIT:"
        cat $SMT_QUEUE | parallel --max-procs=$MAX "$SPLIT {}.trace"
    fi

    # Find trace files and add to CHECK QUEUE
    # - Newer than CHECK_TIMESTAMP
    for TRACE in `find ./ -name "*.trace" -newer $CHECK_TIMESTAMP`
    do
        BASE=${TRACE//.trace/}
        echo $BASE >> $CHECK_QUEUE
        echo "Adding ${BASE}.trace to the CHECK Queue"
    done

    # RUN in Parallel: proof_checker to generate result (possibly sub_problems)

    if [ -s $CHECK_QUEUE ]
    then
        echo `date`: "RUN Check"
        cat $CHECK_QUEUE | parallel --max-procs=$MAX "$PCHECKER {}.trace"
#        touch $TODO # We may need to have more things TO DO
    fi

    # UPDATE: CHECK TIMESTAMP
    touch $CHECK_TIMESTAMP
done
