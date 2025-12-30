#!/bin/bash
#
# NAME:
#         gen-patch.sh - extract linuxized patches from the ACPICA git
#                        repository
#
# SYNOPSIS:
#         gen-patch.sh [-f from] [-i index] [-l link] [-m maintainer] [-n hash] [-u] [commit]
#
# DESCRIPTION:
#         Extract linuxized patches from the git repository.
#         Options:
#          -i: Specify patch index.
#          -l: Specify a URL prefix that can be used to link the commit.
#          -m: Specify maintainer name <email> for Signed-off-by field.
#          -n: Specify number of digits from commit hash to form a name.
#          -u: Specify whether the commit is in an upstream repository.
#          commit: GIT commit (default to HEAD).
#

usage() {
	echo "Usage: `basename $0` [-f from] [-i index] [-l link] [-m maintainer] [-n hash] [-u] <commit>"
	echo "Where:"
	echo "     -i: Specify patch index (default to 0)."
	echo "     -l: Specify a URL prefix that can be used to link the commit."
	echo "     -m: Specify maintainer name <email> for Signed-off-by field."
	echo "     -n: Specify number of digits from commit hash to form a name"
	echo "         (default to 8)."
	echo "     -u: Specify whether the commit is in an upstream repository."
	echo " commit: GIT commit (default to HEAD)."
	exit 1
}

COMMITTER="`git config user.name` <`git config user.email`>"
INDEX=0
UPSTREAM=no
HASH=8

while getopts "i:l:m:n:u" opt
do
	case $opt in
	i) INDEX=$OPTARG;;
	l) LINK=$OPTARG;;
	n) HASH=$OPTARG;;
	m) MAINTAINER=$OPTARG;;
	u) UPSTREAM=yes
	   if [ "x${LINK}" = "x" ]; then
		LINK=https://github.com/acpica/acpica/commit/
	   fi;;
	?) echo "Invalid argument $opt"
	   usage;;
	esac
done
shift $(($OPTIND - 1))

COMMIT=$1
if [ "x${COMMIT}" = "x" ]; then
	COMMIT=HEAD
fi

after=`git log -1 ${COMMIT} --format=%H`
after_name=`git log -1 ${COMMIT} --format=%H | cut -c 1-${HASH}`
before=`git log -1 ${COMMIT}^1 --format=%H`
before_name=`git log -1 ${COMMIT}^1 --format=%H | cut -c 1-${HASH}`

SCRIPT=`(cd \`dirname $0\`; pwd)`
. $SCRIPT/libacpica.sh

GP_acpica_repo=$CURDIR/acpica.repo
GP_linux_before=$CURDIR/linux.before_name
GP_linux_after=$CURDIR/linux.after_name
GP_acpica_patch=$CURDIR/acpica-$after_name.patch
GP_linux_patch=$CURDIR/linux-$after_name.patch

echo "[gen-patch.sh] Extracting GIT ($SRCDIR)..."
# Cleanup
rm -rf $GP_linux_before
rm -rf $GP_linux_after
rm -rf $GP_acpica_repo
git clone $SRCDIR $GP_acpica_repo > /dev/null || exit 2

# Preset environments: LINK
# Arg 1: commit ID
generate_refs()
{
	if [ "x${LINK}" != "x" ]; then
		echo "Link: ${LINK}$1"
	fi
}

# Preset environments: AUTHOR, MAINTAINER, COMMITTER
# Arg 1: commit ID
generate_sobs()
{
	split_desc $1 1
	echo "Signed-off-by: ${AUTHOR}"
	if [ "x${MAINTAINER}" != "x" ]; then
		echo "Signed-off-by: ${MAINTAINER}"
	fi
	echo "Signed-off-by: ${COMMITTER}"
}

# Preset environments: UPSTREAM, INDEX, COMMITTER
# Arg 1: commit ID
generate_acpica_desc()
{
	AUTHOR_NAME=`git log -1 $1 --format="%aN"`
	AUTHOR_EMAIL=`git log -1 $1 --format="%aE"`
	if [ "x${AUTHOR_NAME}" = "xRobert Moore" ]; then
		AUTHOR_NAME="Bob Moore"
	fi
	if [ "x${AUTHOR_EMAIL}" = "xRobert.Moore@intel.com" ]; then
		AUTHOR_EMAIL="robert.moore@intel.com"
	fi
	AUTHOR="${AUTHOR_NAME} <${AUTHOR_EMAIL}>"
	FORMAT="From %H Mon Sep 17 00:00:00 2001%nFrom: $COMMITTER%nDate: %aD%nFrom: $AUTHOR%nSubject: [PATCH $INDEX] ACPICA: %s%n%n%b"
	if [ "x$UPSTREAM" = "xyes" ]; then
		FORMAT="From %H Mon Sep 17 00:00:00 2001%nFrom: $COMMITTER%nDate: %aD%nFrom: $AUTHOR%nSubject: [PATCH $INDEX] ACPICA: %s%n%nACPICA commit %H%n%n%b"
	fi
	GIT_LOG_FORMAT=`echo $FORMAT`
	eval "git log -1 $1 --format=\"$GIT_LOG_FORMAT\""
}

# Arg 1: patch description file
# Arg 2: 1=dump SOB block, 0=dump other text
split_desc()
{
	tac $1 | DOSOB=$2 awk '
	BEGIN { SOB=1 }
	{
		if (SOB==1) {
			if (match($0, /^Signed-off-by:.*/)) {
				if (ENVIRON["DOSOB"]==1)
					print $0
			} else if (match($0, /^Fixed-by:.*/)) {
				if (ENVIRON["DOSOB"]==1)
					print $0
			} else if (match($0, /^Original-by:.*/)) {
				if (ENVIRON["DOSOB"]==1)
					print $0
			} else if (match($0, /^Acked-by:.*/)) {
				if (ENVIRON["DOSOB"]==1)
					print $0
			} else if (match($0, /^Reviewed-by:.*/)) {
				if (ENVIRON["DOSOB"]==1)
					print $0
			} else if (match($0, /^Reported-by:.*/)) {
				if (ENVIRON["DOSOB"]==1)
					print $0
			} else if (match($0, /^Tested-by:.*/)) {
				if (ENVIRON["DOSOB"]==1)
					print $0
			} else if (match($0, /^Reported-and-tested-by:.*/)) {
				if (ENVIRON["DOSOB"]==1)
					print $0
			} else if (match($0, /^Link:.*/)) {
				if (ENVIRON["DOSOB"]==1)
					print $0
			} else if (match($0, /^Reference:.*/)) {
				if (ENVIRON["DOSOB"]==1)
					print $0
			} else if (match($0, /^$/)) {
			} else {
				SOB=0
				if (ENVIRON["DOSOB"]==0)
					print $0
			}
		} else {
			if (ENVIRON["DOSOB"]==0)
				print $0
		}
	}
	' | tac
}

# Preset environments: LINK, AUTHOR, MAINTAINER, COMMITTER
# Arg 1: commit ID
# Arg 2: patch description file
generate_linux_desc()
{
	split_desc $2 0
	echo ""
	generate_refs $1
	generate_sobs $2 | awk '
	{
		if (printed[$0]==0) {
			print $0
			printed[$0]=1;
		}
	}
	'
}

echo "[gen-patch.sh] Creating ACPICA repository ($after_name)..."
(
	cd $GP_acpica_repo
	git reset $after --hard >/dev/null 2>&1
)

echo "[gen-patch.sh] Creating ACPICA patch (acpica-$after_name.patch)..."
(
	cd $GP_acpica_repo
	git format-patch -1 --stdout >> $GP_acpica_patch
)

echo "[gen-patch.sh] Creating Linux repository ($after_name)..."
(
	cd $GP_acpica_repo/generate/linux
	if [ ! -f ./gen-repo.sh ]; then
		cp $SRCDIR/generate/linux/gen-repo.sh ./
	fi
	./gen-repo.sh -c -n $HASH $after
)
mv -f $GP_acpica_repo/generate/linux/linux-$after_name $GP_linux_after

echo "[gen-patch.sh] Creating ACPICA repository ($before_name)..."
(
	cd $GP_acpica_repo
	git reset $before --hard >/dev/null 2>&1
)

echo "[gen-patch.sh] Creating Linux repository ($before_name)..."
(
	cd $GP_acpica_repo/generate/linux
	if [ ! -f ./gen-repo.sh ]; then
		cp $SRCDIR/generate/linux/gen-repo.sh ./
	fi
	./gen-repo.sh -c -n $HASH $before
)
mv -f $GP_acpica_repo/generate/linux/linux-$before_name $GP_linux_before

(
	echo "[gen-patch.sh] Creating Linux patch (linux-$after_name.patch)..."
	cd $CURDIR
	tmpdiff=`mktemp -u`
	tmpdesc=`mktemp -u`
	diff -Nurp linux.before_name linux.after_name >> $tmpdiff

	if [ $? -ne 0 ]; then
		generate_acpica_desc $after > $tmpdesc
		generate_linux_desc $after_name $tmpdesc > $GP_linux_patch
		$ACPISRC -ldqy $GP_linux_patch $GP_linux_patch > /dev/null
		echo "---" >> $GP_linux_patch
		diffstat $tmpdiff >> $GP_linux_patch
		echo >> $GP_linux_patch
		cat $tmpdiff >> $GP_linux_patch
	else
		echo "Warning: Linux version is empty, skipping $after_name..."
	fi
	rm -f $tmpdiff
	rm -f $tmpdesc
)

# Cleanup temporary directories
rm -rf $GP_linux_before
rm -rf $GP_linux_after
rm -rf $GP_acpica_repo
