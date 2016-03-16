#!/bin/bash

if [ "$#" -ne 1 ]; then
	echo "usage: $0 <file>"
	exit 1
fi

FILE=$1
SED="sed -i "

# replace 'QF_S' by 'QF_SLRDI'
${SED} 's/QF_S /QF_SLRDI /g' ${FILE}
${SED} 's/QF_S)/QF_SLRDI)/g' ${FILE}

# replace 'singleton' by 'bag'
${SED} 's/singleton /bag /g' ${FILE}

# replace 'bag-lt' by <
${SED} 's/bag-lt /< /g' ${FILE}

# replace 'bag-gt' by >
${SED} 's/bag-gt /> /g' ${FILE}

# replace 'bag-le' by <=
${SED} 's/bag-le /<= /g' ${FILE}

# replace 'bag-ge' by >=
${SED} 's/bag-ge />= /g' ${FILE}

# replace 'bag-union' by 'bagunion'
${SED} 's/bag-union /bagunion /g' ${FILE}

# replace 'bag-sub' by 'subset'
${SED} 's/bag-sub /subset /g' ${FILE}

# replace 'bag-diff' by 'bagminus'
${SED} 's/bag-diff /bagminus /g' ${FILE}

# replace '(data ' by '(ref data '
${SED} 's/(data /(ref data /g' ${FILE}

# replace '(or (not ...)' by '(=> \1'
${SED} 's/or (not /=> /g' ${FILE}
${SED} 's/)) (subset /) (subset /g' ${FILE}
${SED} 's/) ) (subset /) (subset /g' ${FILE}


