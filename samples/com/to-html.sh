#!/bin/sh

if [ "$#" -ne 1 ]; then
        echo "usage: $0 <pred>"
        exit 1
fi

PRED=$1

GITHUBDIR="https://github.com/mihasighi/spen/tree/master/samples/"

echo "<tr>"
echo "<td rowspan=3>${PRED}</td>"
OLDPROC=""
for i in `ls ${PRED}/${PRED}*-vc??.smt`
do
	FNAME=`basename -s .smt ${i}`
	PROC=`echo ${FNAME} | cut -f2 -d-`
	VCN=`echo ${FNAME} | cut -f3 -d-`
	if [ -z "${VCN}" ]
	then
		VCN="${PROC}"
		PROC="${OLDPROC}"
	fi

	if [ "${OLDPROC}" != "${PROC}" ] 
	then
		echo "</td>"
		echo "</tr>"
		echo "<tr>"
		echo "<td>${PROC}</td><td>"
		OLDPROC=${PROC}
	else
		echo ", "
	fi
	echo "<a href=\"${GITHUBDIR}${i}\">${VCN}</a>"
done

echo "</td>"
echo "</tr>"
