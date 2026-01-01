#!/bin/sh

EFIPROGS="acpidump"

EFIDIR=`(cd \`dirname $0\`; pwd)`
TOPDIR=`(cd ${EFIDIR}/../..; pwd)`

usage() {
	echo "Usage: `basename $0` [-c]"
	echo "Where:"
	echo "     -c: Use EDK standard C-library - StdLib."
	exit 1
}

while getopts "c" opt
do
	case $opt in
	c) EDKSTDLIB=yes;;
	?) echo "Invalid option: $1"
	   usage;;
	esac
done

if [ -z ${EDKSTDLIB} ]; then
   EFISUFFIX=nostdlib
else
   EFISUFFIX=stdlib
fi

echo "Copying AcpiPkg package files..."
cp -f ${EFIDIR}/AcpiPkg.dec ${TOPDIR}/AcpiPkg.dec
cp -f ${EFIDIR}/AcpiPkg_${EFISUFFIX}.dsc ${TOPDIR}/AcpiPkg.dsc

for p in ${EFIPROGS}; do
	EFIINF=${p}_${EFISUFFIX}.inf
	echo "Copying $p build file: ${EFIINF}..."
	if [ ! -f ${EFIDIR}/$p/${EFIINF} ]; then
		echo "Invalid build file: ${EFIINF}"
		exit 1
	else
		cp -f ${EFIDIR}/$p/${EFIINF} ${TOPDIR}/source/${p}.inf
	fi
done
