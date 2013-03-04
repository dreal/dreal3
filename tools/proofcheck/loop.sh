#!/bin/bash
TIMEOUT=$1
DREAL=$2
MAX=$3
RESULTDIR=$4
MAX_QUEUE=50000

TODO=${RESULTDIR}/TODO
SMT_QUEUE=${RESULTDIR}/SMT_QUEUE
CHECK_QUEUE=${RESULTDIR}/CHECK_QUEUE
NOT_PROVED_YET=${RESULTDIR}/NOT_YET
PROVED=${RESULTDIR}/PROVED
WRONG=${RESULTDIR}/WRONG
START_TIME=${RESULTDIR}/START_TIME
END_TIME=${RESULTDIR}/END_TIME

PROOFCHECK_PATH=`dirname $0`
RUN_DREAL=${PROOFCHECK_PATH}/run_dreal.sh
PCHECKER=${PROOFCHECK_PATH}/checker/main.native
SPLIT=${PROOFCHECK_PATH}/split.py

function log_msg {
	echo -n "`date`: "
	printf "[%-30s]: " `basename $1`
	echo $2
}

touch $NOT_PROVED_YET
touch $TODO

date +%s%N | cut -b1-13 > $START_TIME
DEADLINE="`cat $START_TIME` + ( $TIMEOUT * 1000 )"
DEADLINE=`echo "$DEADLINE" | bc`

while [ -f $TODO ]
do
    # CHECK THE TIME, TERMINATE IF TIMEOUT
    CURTIME=`date +%s%N | cut -b1-13`
    if [ "$CURTIME" -gt "$DEADLINE" ]
    then
            log_msg ${BASE}.smt2 "ProofChecking: Timeout"
            touch ${RESULTDIR}/TIMEOUT
            exit 1
    fi

    # INITIALIZE QUEUES
    rm -rf $SMT_QUEUE $CHECK_QUEUE
    touch $SMT_QUEUE $CHECK_QUEUE

    # TODO will be re-created if we need more things TO DO
    rm $TODO

    # Find SMT2 files and add to SMT QUEUE
    # 1) Do not have the result, yet
    for SMT2 in `find $RESULTDIR -name "*.smt2"`
    do
        BASE=${SMT2/%.smt2/}
        if [ ! -f $BASE.result ]
        then
            echo $BASE >> $SMT_QUEUE
            log_msg ${BASE}.smt2 "ProofChecking: Adding to the SMT Queue"
        fi
    done

    if [ "`wc $SMT_QUEUE -l | cut -d ' ' -f 1`" -gt $MAX_QUEUE ]
    then
            log_msg ${BASE}.smt2 "ProofChecking: Too many files"
            touch ${RESULTDIR}/TOOMANY
            exit 2
    fi
    

    # RUN in Parallel: dReal2 to generate results (.result, .time, .trace)
    if [ -s $SMT_QUEUE ]
    then
	log_msg $SMT_QUEUE "ProofChecking: Run dReal"
        cat $SMT_QUEUE | parallel --max-procs=$MAX "$RUN_DREAL {}.smt2 $RESULTDIR $DREAL $TIMEOUT"
    fi

    # RUN: split.py
    if [ -s $SMT_QUEUE ]
    then
	log_msg $SMT_QUEUE "ProofChecking: Split Traces"
        cat $SMT_QUEUE | parallel --max-procs=$MAX "$SPLIT {}.trace"
    fi

    # Find trace files and add to CHECK QUEUE
    for TRACE in `find $RESULTDIR -name "*.trace"`
    do
        BASE=${TRACE/%.trace/}
        if [ ! -f $BASE.checked ]
        then
	    echo $BASE >> $CHECK_QUEUE
            log_msg ${BASE}.trace "ProofChecking: Adding to the Check Queue"
	fi
    done

    # RUN in Parallel: proof_checker to generate result (possibly sub_problems)

    if [ -s $CHECK_QUEUE ]
    then
	log_msg $CHECK_QUEUE "ProofChecking: Check traces in the queue."
        cat $CHECK_QUEUE | parallel --max-procs=$MAX "$PCHECKER {}.trace > {}.check_stat"

        for ID in `cat $CHECK_QUEUE`
        do
            if grep -q "Failed Axioms" $ID.check_stat
            then
                touch $ID.checked
                # Check was run.
                if grep -q "Failed Axioms     #: 0" $ID.check_stat
                then
                    touch $ID.trace.PROVED
                else
                    touch $ID.trace.not_proved
                fi
            else
                # Check was not run properly. ABORT!
                touch $ID.trace.WRONG
                touch $WRONG
                date +%s%N | cut -b1-13 > $END_TIME
                exit 2
            fi
        done
        touch $TODO # We may need to have more things TO DO
    fi
done

rm $NOT_PROVED_YET
touch $PROVED

date +%s%N | cut -b1-13 > $END_TIME
exit 0
