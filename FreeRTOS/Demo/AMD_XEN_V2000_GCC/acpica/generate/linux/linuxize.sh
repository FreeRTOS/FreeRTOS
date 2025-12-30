#!/bin/bash
#
# NAME:
#         linuxize.sh - create linuxized ACPICA source
#
# SYNOPSIS:
#         linuxize.sh [-s] <file>
#
# DESCRIPTION:
#         Convert ACPICA source to Linux format.
#         Parameters:
#          file     Path of file to be linuxized.
#         Options:
#          -s       Force regeneration of acpisrc.
#

usage()
{
	echo "Usage:"
	echo "`basename $0` [-s] <file>"
	echo "Where:"
	echo "        -s: generate acpisrc"
	echo "      file: path of file to be linuxized"
	exit -1
}

while getopts "s" opt
do
	case $opt in
	s) FORCE_ACPISRC=force;;
	?) echo "Invalid argument $opt"
	   usage;;
	esac
done
shift $(($OPTIND - 1))

if [ -z "$1" ] ; then
	usage
fi

SCRIPT=`(cd \`dirname $0\`; pwd)`
. $SCRIPT/libacpica.sh

ACPICADIR=`getdir $1`
ACPICAFILE=`getfile $1`
LINUXDIR=$CURDIR/linux/${ACPICADIR#${SRCDIR}/}
LINUXFILE=$CURDIR/linux/${ACPICAFILE#${SRCDIR}/}

# Generate latest version of the acpisrc utility
echo "[linuxize.sh] Generating tool (acpisrc)..."
make_acpisrc $SRCDIR $FORCE_ACPISRC > /dev/null

echo "[linuxize.sh] Converting format (acpisrc)..."
mkdir -p $LINUXDIR
rm -f $LINUXFILE
$ACPISRC -ldqy $ACPICAFILE $LINUXFILE > /dev/null

# indent all .c and .h files
echo "[linuxize.sh] Converting format (lindent)..."
lindent $CURDIR/linux
