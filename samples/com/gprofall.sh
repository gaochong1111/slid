#!/bin/bash

if [ "$#" -ne 1 ]; then
	echo "usage: $0 <bench-dir>"
	exit 1
fi

BENCH=$1

SHARED_MAKE="make -f ../Makefile"

cd ${BENCH}
echo "========================== Profiling benchmark \"${BENCH}\" =========================="

for i in `ls *.smt`
do
        FNAME=`basename ${i}`
	LOG_FILE="${i}.log"
	RESULT_FILE="${FNAME}.prof"

	echo "==== Testing file \"${i}\""
	${SHARED_MAKE} --always-make ${LOG_FILE}
	if [ $? -ne "0" ] ; then
		echo "INTERNAL ERROR"
		echo -e "result for ${i}:                                              \e[1;33mFAILED\e[0m"
		continue
	fi
        gprof -b ../spen > ${RESULT_FILE}
	RUN_TIME=$(grep "Total time" ${LOG_FILE} | sed 's/^.*:\(.*\)$/\1/')
	echo -e "result for ${i}:                                              \e[1;32mOK\e[0m       in time ${RUN_TIME} sec"
	${SHARED_MAKE} --quiet clean
done

