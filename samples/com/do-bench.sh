#!/bin/bash

if [ "$#" -ne 1 ]; then
	echo "usage: $0 <dir>"
	exit 1
fi

if test -f log; then
  mv log log-old
else
  mkdir log
fi

BENCHDIR=$1
RUN=./starexec_run_spen.sh

for i in `ls ${BENCHDIR}/*.smt2`
do
	echo "**** Testing file \"${i}\""
	RES=`${RUN} ${i}`
	echo ",,,, ${RES}"
	ERES=$(grep :status ${i} | grep -c \ ${RES}\))
	echo ",,,, ${ERES}"
	if [ "${ERES}" -eq "0" ] ; then
                echo "==== received \"${RES}\" while expecting \"$(grep status ${i})\""
                echo -e "result for ${i}: \033[31mERROR\033[30m"
        else
                echo "==== received expected result: ${RES}"
        fi
done

