#!/bin/bash
#
# NAME:
#         divergence.sh - find divergences between Linux and ACPICA
#
# SYNOPSIS:
#         divergence.sh [-s] <path>
#
# DESCRIPTION:
#         Find the divergences between these sets of source code:
#          1) The current ACPICA source from the ACPICA git tree
#          2) The version of ACPICA that is integrated into Linux
#         The goal is to eliminate as many differences as possible between
#         these two sets of code.
#         Parameters:
#          path     Path of directory to the Linux source tree.
#         Options:
#          -s       Single direction
#                   (indent on Linux rather than both of Linux and ACPICA)
#

usage()
{
	echo "Usage: `basename $0` [-s] <path>"
	echo "Where:"
	echo "  -s: indent on (Linux) rather than on (Linux and ACPICA)"
	echo "  path is path to root of Linux source code."
	exit 1
}

while getopts "s" opt
do
	case $opt in
	s) LINDENT_DIR=single;;
	?) echo "Invalid argument $opt"
	   usage;;
	esac
done
shift $(($OPTIND - 1))

SCRIPT=`(cd \`dirname $0\`; pwd)`
. $SCRIPT/libacpica.sh

LINUX_ACPICA=$CURDIR/linux-acpica
ACPICA_LINUXIZED=$CURDIR/acpica-linuxized
LINUX=`fulldir $1`

# Parameter validation

if [ -z $1 ] ; then
	echo "Usage: $0 <Linux>"
	echo "  Linux: Path of Linux source"
	exit 1
fi
if [ ! -e $1 ] ; then
	echo "$1, Linux source directory does not exist"
	exit 1
fi
if [ ! -d $1 ] ; then
	echo "$1, Not a directory"
	exit 1
fi

if [ -z $LINDENT_DIR ] ; then
	LINDENT_DIR=multiple
fi

echo "[divergence.sh] Generating tool (acpisrc)..."
make_acpisrc $SRCDIR force > /dev/null

#
# Copy the actual Linux ACPICA files locally (from the Linux tree)
#
echo "[divergence.sh] Converting hierarchy..."
copy_linux_hierarchy $LINUX $LINUX_ACPICA
linuxize_hierarchy_ref $LINUX_ACPICA $SRCDIR $ACPICA_LINUXIZED

#
# Lindent both sets of files
#
echo "[divergence.sh] Converting format (lindent-acpica)..."
linuxize_format $ACPICA_LINUXIZED

if [ "x$LINDENT_DIR" = "xmultiple" ] ; then
	echo "[divergence.sh] Converting format (lindent-linux)..."
	lindent $LINUX_ACPICA
fi

#
# Now we can finally do the big diff
#
echo "[divergence.sh] Generating divergences ($LINDENT_DIR)..."
diff -E -b -w -B -rpuN linux-acpica acpica-linuxized > divergence-$LINDENT_DIR.diff
diffstat divergence-$LINDENT_DIR.diff > diffstat-$LINDENT_DIR.txt
echo "=========="
ls -s1 divergence-$LINDENT_DIR.diff diffstat-$LINDENT_DIR.txt
echo "=========="

#
# Cleanup
#
rm -rf $LINUX_ACPICA
rm -rf $ACPICA_LINUXIZED
