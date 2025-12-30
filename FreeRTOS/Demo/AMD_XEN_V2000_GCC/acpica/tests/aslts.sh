#!/bin/bash
#
# aslts - execute ASL test suite
#

# Will build temporary versions of iASL and acpiexec
postfix=`date +%H%M%S`
tmp_iasl=/tmp/iasl-$postfix
tmp_acpiexec=/tmp/acpiexec-$postfix
tmp_acpibin=/tmp/acpibin-$postfix

TEST_CASES=
TEST_MODES=
REBUILD_TOOLS=yes
BINCOMPONLY=no
DATATABLEONLY=no
EXECONLY=no

usage() {

	echo "Usage:"
	echo "`basename $0` [-c case] [-m mode] [-u]"
	echo "Where:"
	echo "  -c:	Specify individual test cases (can be used multiple times)"
	echo "  -m:	Specify individual test modes (can be used multiple times)"
	echo "  -u:	Do not force rebuilding of ACPICA utilities (acpiexec, iasl)"
	echo "  -e:     Perform the execution of aml files and omit binary comparison of regular aml and disassembled aml file."
	echo "  -b:     Only perform binary comparison of regular aml and disasssembled aml file"
	echo "  -d:     Only execute data table compiler/disassembler test"
	echo ""

	echo "Available test modes:"
	echo "  n32	32-bit unoptimized code (tests are compiled with iasl -oa -r 1 and other flags)"
	echo "  n64	64-bit unoptimized code (tests are compiled with iasl -oa -r 2 and other flags)"
	echo "  o32	32-bit optimized code (tests are compiled with iasl -r 1 and other flags)"
	echo "  o64	64-bit optimized code (tests are compiled with iasl -r 2 and other flags)"
	echo ""

	Do 3
	exit 1
}

# Setup environment and variables.
# Need a path to ASLTS and iasl,acpiexec generation dir
setup_environment() {

	aslts_dir=$1
	generation_dir=$2

	if [ -z "$generation_dir" ] ; then
		echo "missing generation directory argument"
		exit
	elif [ -z "$aslts_dir" ] ; then
		echo "missing aslts directory argument"
		exit
	elif [ ! -d "$generation_dir" ] ; then
		echo $generation_dir is not a dir
		exit
	elif [ ! -d "$aslts_dir" ] ; then
		echo $aslts_dir is not a dir
		exit
	fi

	# Variables required by ASLTS
	unset ASL
	unset acpiexec
	unset ASLTSDIR

	export ASL=$tmp_iasl
	export acpiexec=$tmp_acpiexec
	export acpibin=$tmp_acpibin
	export ASLTSDIR=$aslts_dir
	export PATH=$ASLTSDIR/bin:$PATH
}


# Generate both iASL and acpiexec from source
build_acpi_tools() {

	restore_dir=$PWD
	cd ${generation_dir}
	rm -f $tmp_iasl $tmp_acpiexec $tmp_acpibin

	# Build native-width iASL compiler and acpiexec
	if [ ! -e bin/iasl -o ! -e bin/acpiexec ]; then
		REBUILD_TOOLS=yes
	fi
	if [ "x$REBUILD_TOOLS" = "xyes" ]; then
		jobs=`nproc`
		make clean
		make iasl ASLTS=TRUE -j$jobs
		make acpibin ASLTS=TRUE -j$jobs
		make acpiexec ASLTS=TRUE -j$jobs
	fi

	if [ -d "bin" ] && [ -f "bin/iasl" ]; then
		echo "Installing ACPICA tools"
		cp bin/iasl $tmp_iasl
		cp bin/acpiexec $tmp_acpiexec
		cp bin/acpibin $tmp_acpibin
	else
		echo "Could not find iASL/acpiexec tools"
		exit
	fi

	# Ensure that the tools are available
	if [ ! -f $tmp_iasl ] ; then
		echo "iasl compiler not found"
		exit
	elif [ ! -f $tmp_acpiexec ] ; then
		echo "acpiexec utility not found"
		exit
	elif [ ! -f $tmp_acpibin ] ; then
		echo "acpibin utility not found"
		exit
	fi

	cd $restore_dir
}

# Run a simple compiler test.
# This test does the following:
# 1 generate all sample tables in the compiler
# 2 compile all tables (.asl -> .aml)
# 3 disassembles all tables (.aml -> .dsl)
# 4 recompiles all all tables (.dsl -> recomp.aml)
# 5 runs binary comparison between .aml and recomp.aml
run_compiler_template_test()
{
	pushd templates

	rm -f *.asl *.aml *.dsl

	$ASL -T all 2> /dev/null
	for filename in *.asl
	do
		make -s NAME=$(basename "$filename" .asl)
	done

	rm -f *.asl *.aml *.dsl
	popd
}


# Compile and run the ASLTS suite
run_aslts() {

	# Remove a previous version of the AML test code
	version=`$ASL | grep version | awk '{print $5}'`
	rm -rf $ASLTSDIR/tmp/aml/$version

	# run templates test

	run_compiler_template_test

	if [ "x$DATATABLEONLY" = "xyes" ]; then
		return 0
	fi;

	if [ "x$TEST_MODES" = "x" ]; then
		TEST_MODES="n32 n64 o32 o64"
	fi
	Do 0 $TEST_MODES $TEST_CASES $EXECONLY
	if [ $? -ne 0 ]; then
		echo "ASLTS Compile Failure"
		exit 1
	fi

	# Execute the test suite
	if [ "x$BINCOMPONLY" = "xno" ]; then
		echo ""
		echo "ASL Test Suite Started: `date`"
		start_time=$(date)

		if [ "x$TEST_MODES" = "x" ]; then
			TEST_MODES="n32 n64 o32 o64"
		fi
		Do 1 $TEST_MODES $TEST_CASES

		echo ""
		echo "ASL Test Suite Finished: `date`"
		echo "                Started: $start_time"

		rm -f $tmp_iasl $tmp_acpiexec $tmp_acpibin
	fi;
}

SRCDIR=`(cd \`dirname $0\`; cd ..; pwd)`
setup_environment $SRCDIR/tests/aslts $SRCDIR/generate/unix

# To use common utilities
. $SRCDIR/tests/aslts/bin/common
. $SRCDIR/tests/aslts/bin/settings
RESET_SETTINGS
INIT_ALL_AVAILABLE_CASES
INIT_ALL_AVAILABLE_MODES

while getopts "c:m:uebd" opt
do
	case $opt in
	b)
		BINCOMPONLY=yes
		echo "Running only binary comparisons"
	;;
	c)
		get_collection_opcode "$OPTARG"
		if [ $? -eq $COLLS_NUM ]; then
			echo "Invalid test case: $OPTARG"
			usage
		else
			TEST_CASES="$OPTARG $TEST_CASES"
		fi
	;;
	d)
		DATATABLEONLY=yes
		echo "Running only data table test"
	;;
	e)
		EXECONLY=yes
		echo "Running tests without binary comparisons"
	;;
	m)
		check_mode_id "$OPTARG"
		if [ $? -eq 1 ]; then
			echo "Invalid test mode: $OPTARG"
			usage
		else
			TEST_MODES="$OPTARG $TEST_MODES"
		fi
	;;
	u)
		REBUILD_TOOLS=no
	;;
	?)
		echo "Invalid argument: $opt"
		usage
	;;
	esac
done
shift $(($OPTIND - 1))

build_acpi_tools
run_aslts
