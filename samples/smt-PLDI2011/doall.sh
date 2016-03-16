#!/bin/bash

if [ "$#" -ne 1 ]; then
	echo "usage: $0 <benchmark>"
	exit 1
fi

BENCH=$1

SHARED_MAKE="make -f ../Makefile"

cd ${BENCH}
echo "========================== Testing suite \"${BENCH}\" =========================="

for i in `ls ${BENCH}-*.tptp.smt`
do
	LOG_FILE="${i}.log"
	RESULT_FILE="${i}.res"
	EXPECTED_FILE="expected/${i}.exp"

	echo "==== Testing file \"${i}\""
	${SHARED_MAKE} --always-make ${LOG_FILE}
	if [ $? -ne "0" ] ; then
		echo "INTERNAL ERROR"
		echo -e "result for ${i}:                   \033[33mFAILED\033[30m"
		continue
	fi
	tail -1 ${LOG_FILE} > ${RESULT_FILE}
	RUN_TIME=$(grep "Total time" ${LOG_FILE} | sed 's/^.*:\(.*\)$/\1/')
	tail -1 ${EXPECTED_FILE} > exp.txt
	diff exp.txt ${RESULT_FILE} >/dev/null
	if [ $? -ne "0" ] ; then
		echo -e "==== received \"$(cat ${RESULT_FILE})\" while expecting \"$(cat exp.txt)\""
		echo -e "result for ${i}:                   \033[31mERROR\033[30m"
	else
		echo "==== received expected result:    $(cat ${RESULT_FILE})"
		echo -e "result for ${i}:                   \033[32mOK\033[30m     in time ${RUN_TIME} sec"
	fi
        mv ${LOG_FILE} log/.
	${SHARED_MAKE} --quiet clean
	rm ${RESULT_FILE}
done

