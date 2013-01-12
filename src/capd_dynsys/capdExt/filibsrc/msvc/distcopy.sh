#! /bin/sh
if [ $# -lt 1 ] ; then 
	echo "Need an argument. Try \"wininst\""
	exit 0
fi

HEADERS=`find . | perl -p -e "s/^\.\///" | egrep "(\.icc|\.hpp|\.h)$" | egrep "^(rounding_control|interval|fp_traits|ieee)"`
PREFIX=$1

for i in $HEADERS ; do
	DIR=`dirname $i`
	FILE=`basename $i`
	INSTDIR=${PREFIX}/include/${DIR}
	mkdir -p $INSTDIR
	cp -p $i ${INSTDIR}/${FILE}
done

for i in `find msvc -name \*.exe | grep "/release/"` ; do
	mkdir -p ${PREFIX}/bin
	BN="`basename ${i}`"
	cp -p "${i}" "${PREFIX}/bin/filib_release_${BN}"
done

for i in `find msvc -name \*.exe | grep "/debug/"` ; do
	mkdir -p ${PREFIX}/bin
	BN="`basename ${i}`"
	cp -p "${i}" "${PREFIX}/bin/filib_debug_${BN}"
done

for i in `find msvc -name \*.lib | grep "/release/"` ; do
	mkdir -p ${PREFIX}/lib
	BN="`basename ${i}`"
	cp -p "${i}" "${PREFIX}/lib/${BN}"
done

for i in `find msvc -name \*.lib | grep "/debug/"` ; do
	mkdir -p ${PREFIX}/lib
	BN="`basename ${i} | perl -p -e "s/\.lib/d.lib/"`"
	cp -p "${i}" "${PREFIX}/lib/${BN}"
done
