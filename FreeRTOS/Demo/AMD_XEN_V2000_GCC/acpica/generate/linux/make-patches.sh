#!/bin/bash
#
# NAME:
#         make-patches.sh - extract a set of linuxized patches from the
#                           ACPICA git repository
#
# SYNOPSIS:
#         make-patches.sh [-n hash] [-r release] [-u] <old_commit> [new_commit]
#
# DESCRIPTION:
#         Creates the linuxized patch set from old_commit to new_commit in
#         ACPICA git repository.
#         Parameters:
#          old_commit The old commit ID.
#          new_commit The new commit ID.  If this parameter is not specified,
#                     the new commit ID is default to HEAD.
#         Options:
#          -n hash    Specify number of digits from commit hash to form a name.
#          -r release Specify a release ID, it will turn out to be the name of
#                     the patch files.  If this option is not specified, the
#                     default name of the patch files will be the current month
#                     in YYYYmm date format.
#          -u         Generate upstream commit IDs in the linuxized patches.
#

RELEASE=`date +%Y%m`
HASH=8

usage()
{
	echo "Usage: `basename $0` [-n hash] [-r release] [-u] <old_commit> [new_commit]"
	echo "Where:"
	echo "  -n: Specify number of digits from commit hash to form a name"
	echo "      (default to 8)."
	echo "  -r: Set release ID, default is $RELEASE in YYYYmm- date format"
	echo "  -u: Generate upstream commit IDs"
	echo "  old_commit: The old commit id\n";
	echo "  new_commit: Optional, the new commit id, default to HEAD";
	exit 0
}

SCRIPT=`(cd \`dirname $0\`; pwd)`
. $SCRIPT/libacpica.sh

ACPICA_DIR=$CURDIR/patches.acpica.$RELEASE
LINUX_DIR=$CURDIR/patches.linux.$RELEASE
NEW_RELEASE="HEAD"
OLD_RELEASE="HEAD"
ACPICA_CNT=0
LINUX_CNT=0
MAINTAINER="Bob Moore <robert.moore@intel.com>"
GIT_EXTRACT="$SCRIPT/gen-patch.sh"
RELEASE="${RELEASE}-"

while getopts "dn:r:u" opt
do
	case $opt in
	d) DRYRUN="yes";;
	n) HASH=$OPTARG;;
	r) RELEASE=$OPTARG;;
	u) GIT_EXTRACT="${GIT_EXTRACT} -u -m '${MAINTAINER}'";;
	?) echo "Invalid argument $opt"
	   usage;;
	esac
done
shift $(($OPTIND - 1))

if [ -z $1 ]; then
	echo "old_commit is not specified"
	usage
fi
OLD_RELEASE=$1
if [ ! -z $2 ]; then
	NEW_RELEASE=$2
fi

COMMITS=`git rev-list --reverse $OLD_RELEASE..$NEW_RELEASE`

for c in $COMMITS; do
	ACPICA_CNT=`expr $ACPICA_CNT + 1`
done

generate_patch()
{
	local cid aid lid
	local COMMIT SUBJECT

	cid=$1
	aid=$2
	lid=$3

	COMMIT=`git log -1 $cid --format=%H`
	COMMIT_NAME=`git log -1 $cid --format=%H | cut -c 1-${HASH}`
	SUBJECT=`git log -1 $cid --format=%s`

	echo "[make-patches.sh] Generating patch ($aid:$lid:$COMMIT_NAME: $SUBJECT)..."
	(
		cd $SCRIPT

		if [ "x$DRYRUN" = "xyes" ]; then
			echo $GIT_EXTRACT -i $lid -n $HASH $COMMIT
		else
			eval $GIT_EXTRACT -i $lid -n $HASH $COMMIT
			echo "[make-patches.sh]  Copying ACPICA patch ($RELEASE$aid.patch)..."
			mv acpica-$COMMIT_NAME.patch $ACPICA_DIR/$RELEASE$aid.patch
			echo $RELEASE$aid.patch >> $ACPICA_DIR/series
		fi


		if [ -f linux-$COMMIT_NAME.patch ]; then
			if [ "x$DRYRUN" != "xyes" ]; then
				echo "[make-patches.sh] Copying Linux patch ($RELEASE$lid.patch)..."
				mv linux-$COMMIT_NAME.patch $LINUX_DIR/$RELEASE$lid.patch
				echo $RELEASE$lid.patch >> $LINUX_DIR/series
			fi
		fi
	)
}

rm -rf $ACPICA_DIR
rm -rf $LINUX_DIR
mkdir -p $ACPICA_DIR
mkdir -p $LINUX_DIR

ACPICA_IDX=1
LINUX_IDX=1
make_acpisrc $SRCDIR force > /dev/null

for c in $COMMITS; do
	generate_patch $c $ACPICA_IDX $LINUX_IDX

	LINUX_TO=$LINUX_DIR/$RELEASE$LINUX_IDX.patch
	if [ -f $LINUX_TO ]; then
		echo "[make-patches.sh] Generated $LINUX_TO."
		LINUX_IDX=`expr $LINUX_IDX + 1`
	fi

	ACPICA_IDX=`expr $ACPICA_IDX + 1`
done

LINUX_CNT=`expr $LINUX_IDX - 1`

echo "[make-patches.sh] Generated $ACPICA_CNT raw patches and $LINUX_CNT linuxized patches."
