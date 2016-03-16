#!/bin/bash

if [ "$#" -lt 1 ]; then
	echo "usage: $0 <predicate> [-<procedure>]"
	exit 1
fi

PRED=$1

PROC=$2

SHARED_MAKE="make -f ../Makefile"

cd ${PRED}
echo "========================== Testing predicate \"${PRED}\" =========================="

for i in `ls ${PRED}${PROC}*-vc??.smt`
do
        BN_FILE=`basename -s .smt ${i}`
	LOG_FILE="${i}.slog"
	RESULT_FILE="${i}.res"
	EXPECTED_FILE="${i}.exp"

	echo "==== Testing file \"${i}\""
	${SHARED_MAKE} --always-make ${LOG_FILE}
	if [ $? -ne "0" ] ; then
		echo "INTERNAL ERROR"
		echo -e "result for ${i}:                                              \e[1;33mFAILED\e[0m"
		continue
	fi
	tail -1 ${LOG_FILE} > ${RESULT_FILE}
	RUN_TIME=$(grep "Total time" ${LOG_FILE} | sed 's/^.*:\(.*\)$/\1/')
	diff ${EXPECTED_FILE} ${RESULT_FILE} >/dev/null
	if [ $? -ne "0" ] ; then
		echo "==== received \"$(cat ${RESULT_FILE})\" while expecting \"$(cat ${EXPECTED_FILE})\""
		echo -e "result for ${i}:                                              \e[1;31mERROR\e[0m"
	else
		echo "==== received expected result:    $(cat ${RESULT_FILE})"
		echo -e "result for ${i}:                                              \e[1;32mOK\e[0m       in time ${RUN_TIME} sec"
	fi

 	echo "---- move data entailments to z3"
         for df in `ls df-*.txt`
         do
 		DENTL=${BN_FILE}-${df}
 		mv ${df} ../z3/${DENTL} 
 		echo "    generate z3/${DENTL}"
 	done

	${SHARED_MAKE} --quiet clean
	rm ${RESULT_FILE}
done

# stats
echo "****** Statistics *****"
BOK=`grep OK ../*${PRED}${PROC}_slog | wc -l`
BERR=`grep ERROR ../*${PRED}${PROC}_slog | wc -l`
BALL=`grep "Testing file" ../*${PRED}${PROC}_slog | wc -l`
echo "(OK=${BOK}, NOK=${BERR}) over ${BALL}"


