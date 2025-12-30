#!/bin/bash
#
# NAME:
#         libacpica.sh - ACPICA release script library
#
#

if [ -z $SCRIPT ]; then
	echo "SCRIPT is empty, please invoking libacpica.sh from release scripts."
	exit 1
fi

CURDIR=`pwd`
TOOLDIR=$SCRIPT/bin
ACPISRC=$TOOLDIR/acpisrc
ACPI_TYPES=

linux_dirs()
{
	local dirs

	dirs="\
		drivers/acpi/acpica \
		include/acpi \
		include/acpi/platform \
		tools/power/acpi/common \
		tools/power/acpi/os_specific/service_layers \
		tools/power/acpi/tools/acpidump \
	"
	echo $dirs
}

acpica_privs()
{
	local incs

	incs="\
		acapps.h \
		accommon.h acconvert.h \
		acdebug.h acdispat.h \
		acevents.h \
		acglobal.h \
		achware.h \
		acinterp.h \
		aclocal.h \
		acmacros.h \
		acnamesp.h \
		acobject.h acopcode.h \
		acparser.h acpredef.h \
		acresrc.h \
		acstruct.h \
		actables.h \
		acutils.h \
		amlcode.h amlresrc.h \
	"
	echo $incs
}

acpica_drivers_paths()
{
	local paths incs inc

	paths="\
		components/debugger \
		components/dispatcher \
		components/events \
		components/executer \
		components/hardware \
		components/namespace \
		components/parser \
		components/resources \
		components/tables \
		components/utilities \
	"
	incs=`acpica_privs`
	for inc in $incs; do
		paths="$paths include/$inc"
	done
	echo $paths
}

acpica_tools_paths()
{
	local paths incs inc

	paths="\
		common/getopt.c \
		common/cmfsize.c \
		os_specific/service_layers/oslibcfs.c \
		os_specific/service_layers/oslinuxtbl.c \
		os_specific/service_layers/osunixdir.c \
		os_specific/service_layers/osunixmap.c \
		os_specific/service_layers/osunixxf.c \
		tools/acpidump \
	"
	echo $paths
}

acpica_exclude_paths()
{
	local paths

	paths="\
		include/acpi/acclib.h \
		include/acpi/acdisasm.h \
		include/acpi/actbinfo.h \
		include/acpi/platform/accygwin.h \
		include/acpi/platform/acefi.h \
		include/acpi/platform/acefiex.h \
		include/acpi/platform/acfreebsd.h \
		include/acpi/platform/achaiku.h \
		include/acpi/platform/acmacosx.h \
		include/acpi/platform/acmsvc.h \
		include/acpi/platform/acmsvcex.h \
		include/acpi/platform/acnetbsd.h \
		include/acpi/platform/acos2.h \
		include/acpi/platform/acqnx.h \
		include/acpi/platform/acwin.h \
		include/acpi/platform/acwinex.h \
		include/acpi/platform/acwin64.h \
		include/acpi/platform/acdragonfly.h \
		include/acpi/platform/acdragonflyex.h \
		drivers/acpi/acpica/utclib.c \
	"
	echo $paths
}

fulldir()
{
	( cd $1; pwd )
}

getdir()
{
	local lpath

	lpath=`dirname $1`
	fulldir $lpath
}

getfile()
{
	local d f

	d=`getdir $1`
	f=`basename $1`
	echo $d/$f
}

identify_bits()
{
	local arch no64

	arch=`uname -m`
	no64=`echo ${arch%64}`

	if [ "x$arch" != "x$no64" ] ; then
		echo 64
	else
		echo 32
	fi
}

make_tool()
{
	local srcdir acpi_tool tooldir bits

	srcdir=$1
	acpi_tool=$2

	tooldir=$srcdir/generate/unix
	bits=`identify_bits`

	mkdir -p $TOOLDIR
	make -C $srcdir $acpi_tool

	if [ ! -f $tooldir/bin$bits/$acpi_tool ]; then
		bits=
	fi

	cp $tooldir/bin$bits/$acpi_tool $TOOLDIR
}

clean_tool()
{
	local srcdir acpi_tool tooldir bits

	srcdir=$1
	acpi_tool=$2

	tooldir=$srcdir/generate/unix
	bits=`identify_bits`

	if [ -f $tooldir/bin$bits/$acpi_tool ]; then
		rm -f $tooldir/bin$bits/$acpi_tool
		rm -rf $tooldir/$acpi_tool/obj$bits
	fi
	if [ -f $tooldir/bin/$acpi_tool ]; then
		rm -f $tooldir/bin/$acpi_tool
		rm -rf $tooldir/$acpi_tool/obj
	fi

	rm -f $tooldir/bin$bits/$acpi_tool
}

clean_acpisrc()
{
	clean_tool $1 acpisrc
}

make_acpisrc()
{
	if [ "x$2" = "xforce" ]; then
		clean_tool $1 acpisrc
	fi
	make_tool $1 acpisrc
}

find_typedefs()
{
	cat $1 | awk '
	{
		if (match($0, /^typedef[_a-zA-Z0-9\* \t]+;/)) {
			s1=substr($0, RSTART, RLENGTH)
			if (match(s1, /^typedef[ \t]+/)) {
				s2=substr(s1, RLENGTH+1)
				if (match(s2, /(signed|unsigned)[ \t]+/)) {
					s3=substr(s2, RLENGTH+1)
				} else {
					s3=s2
				}
				if (match(s3, /[_a-zA-Z0-9]+[ \t]+/)) {
					s4=substr(s3, RLENGTH+1)
					if (match(s4, /\*[ \t]*/)) {
						s5=substr(s4, RLENGTH+1)
					} else {
						s5=s4
					}
					if (match(s5, /[_a-zA-Z0-9]+/)) {
						def=substr(s5, RSTART, RLENGTH)
						print def
					}
				}
			}
		}
	}
	'
}

find_all_typedefs()
{
	local f files

	files=`find . -name "*.h"`
	for f in $files; do
		find_typedefs $f
	done
}

lindent_find_typedefs()
{
	ACPI_TYPES=`find_all_typedefs | sort | uniq`
}

lindent_single()
{
	local t indent_flags

	indent_flags="-npro -kr -i8 -ts8 -sob -l80 -ss -ncs -il0"
	for t in $ACPI_TYPES; do
		if [ "x$2" = "xtrue" ]; then
			echo " Adding type $t"
		fi
		indent_flags="$indent_flags -T $t"
	done

	dos2unix $1 > /dev/null 2>&1
	indent $indent_flags $1
}

lindent()
{
	local files f verbose=true

	(
		cd $1
		lindent_find_typedefs
		files=`find . -name "*.[ch]" | cut -c3-`
		for f in $files; do
			lindent_single $f $verbose
			verbose=false
		done
		find . -name "*~" | xargs rm -f
	)
}

linuxize_format()
{
	echo " Converting (acpisrc -l)..."
	$ACPISRC -ldqy $1 $1 > /dev/null

	echo " Converting (indent)..."
	lindent $1

	echo " Converting (acpisrc -i)..."
	$ACPISRC -idqy $1 $1 > /dev/null
}

copy_linux_hierarchy()
{
	local from to dirs dir

	from=$1
	to=$2

	rm -rf $to
	dirs=`linux_dirs`

	for dir in $dirs; do
		echo " Copying ($dir)..."
		mkdir -p $to/$dir
		cp $from/$dir/*.[ch] $to/$dir/
	done
}

linuxize_hierarchy_ref()
{
	local linux acpica to
	local all_files
	local t n d f
	local private_includes inc

	linux=$1
	acpica=$2
	to=$3

	rm -rf $to
	mkdir -p $to

	#
	# Ensure that the files in the two directories
	# (native ACPICA and Linux ACPICA) match
	#

	all_files=`find $linux`

	for t in $all_files ; do
		if [ -f $t ] ; then
			n=${t#${linux}/}
			d=$to/`dirname $n`
			f=`find $acpica/source -name \`basename $t\``
			if [ ! -z $f ] ; then
				mkdir -p $d
				cp -f $f $d
			else
				echo " Removing ($n)..."
				rm -f $t
			fi
		fi
	done

	private_includes=`acpica_privs`

	# Do we need to perform things on private_includes?
	for inc in $private_includes ; do
		if [ -f $to/include/acpi/$inc ] ; then
			echo "Warning: private include file $inc is now public.  Please check the linuxize.sh"
		elif [ ! -f $to/drivers/acpi/acpica/$inc ] ; then
			echo "Warning: private include file $inc does not exist.  Please check the linuxize.sh."
		fi
	done
}

linuxize_hierarchy_noref()
{
	local repo_linux paths path

	repo_linux=$1

	(
		cd $repo_linux

		# Making hierarchy

		# Making source files
		mkdir -p drivers/acpi/acpica
		paths=`acpica_drivers_paths`
		for path in $paths; do
			if [ -d source/$path ]; then
				echo " Moving directory $path..."
				mv source/$path/*.[ch] drivers/acpi/acpica/
			fi
			if [ -f source/$path ]; then
				echo " Moving file $path..."
				mv source/$path drivers/acpi/acpica/
			fi
		done

		# Making include files
		mkdir -p include/acpi
		mv -f source/include/* include/acpi

		# Making tools/power/acpi files
		paths=`acpica_tools_paths`
		for path in $paths; do
			if [ -d source/$path ]; then
				echo " Moving directory $path..."
				mkdir -p tools/power/acpi/$path
				mv source/$path/*.[ch] tools/power/acpi/$path/
			fi
			if [ -f source/$path ]; then
				echo " Moving file $path..."
				mkdir -p `dirname tools/power/acpi/$path`
				mv source/$path tools/power/acpi/$path
			fi
		done

		# Removing non-Linux files
		paths=`acpica_exclude_paths`
		for path in $paths; do
			if [ -d $path ]; then
				echo " Removing directory $path..."
				rm -rf $path
			fi
			if [ -f $path ]; then
				echo " Removing file $path..."
				rm -f $path
			fi
		done

		rm -rf source
	)
}

SRCDIR=`fulldir $SCRIPT/../..`
