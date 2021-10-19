#!/usr/bin/env python3
###############################################################################
# FreeRTOS
# Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.
#
# https://www.FreeRTOS.org
# https://github.com/FreeRTOS
###############################################################################
import argparse
import gzip
import json
import os
import re
import sys


def main():
    arg_parser = argparse.ArgumentParser(
        description="Filter the contents of a gov intermediate coverage file"
    )
    arg_parser.add_argument(
        "-i", "--in", required=True, help="input .gcov.json.gz file to be filtered"
    )
    arg_parser.add_argument(
        "-m",
        "--map",
        required=True,
        help="Json file containing a callmap for the files under test",
    )
    arg_parser.add_argument(
        "-t",
        "--test",
        required=True,
        help="The unit test .c file which contains @coverage flags.",
    )
    arg_parser.add_argument(
        "-f", "--format", required=True, help="The output format to use (json|lcov)"
    )
    arg_parser.add_argument(
        "-o",
        "--out",
        required=False,
        help="output file path (otherwise stdout out is used)",
    )

    args = arg_parser.parse_args()
    # Validate arguments
    if not os.path.isfile(vars(args)["in"]):
        print("The input file path does not exist.", file=sys.stderr)
        sys.exit(1)

    if vars(args)["out"] and not os.path.isdir(os.path.dirname(vars(args)["out"])):
        print("The output directory does not exist.", file=sys.stderr)
        sys.exit(1)

    if not os.path.isfile(args.map):
        print("The callmap file path does not exist.", file=sys.stderr)
        sys.exit(1)

    if not os.path.isfile(args.test):
        print("The test file path does not exist.", file=sys.stderr)
        sys.exit(1)

    skip_target_filtering = False
    tagged_functions = get_tagged_functions_in_file(args.test)
    if len(tagged_functions) == 0:
        print("WARNING: No target functions found in test file.")
        skip_target_filtering = True

    print("Target functions from UT: " + str(tagged_functions), file=sys.stderr)

    cov_functions_deps = get_function_deps(args.map, tagged_functions)
    print(
        "Target functions and dependencies: " + str(cov_functions_deps), file=sys.stderr
    )

    if vars(args)["in"] and (".gz" in vars(args)["in"]):
        covfile_handle = gzip.open(vars(args)["in"], "rb")
    else:
        covfile_handle = open(vars(args)["in"], "r")

    if skip_target_filtering:
        print("WARNING: Skipping coverage filtering.")
        covdata_out = json.load(covfile_handle)
    else:
        covdata_out = filter_coverage_file(covfile_handle, cov_functions_deps)

    covfile_handle.close()

    filter_excluded_lines(covdata_out)

    # default to lcov output format
    out_format = "lcov"
    if vars(args)["format"]:
        out_format = args.format

    if vars(args)["out"]:
        if ".gz" in args.out:
            outfile = gzip.open(args.out, "wb", encoding="ascii")
        else:
            outfile = open(args.out, "w")
    else:
        outfile = sys.stdout
    if out_format == "json":
        json.dump(covdata_out, outfile)
    elif out_format == "lcov":
        convert_to_lcov_info(args, covdata_out, outfile)

    if outfile is not sys.stdout:
        outfile.close()


def get_tagged_functions_in_file(filename):
    """Given a filename, return a set of the target function names tagged with
    @coverage in that file."""
    token_regex = r"^.*@coverage(( (\w+))+).*$"
    token_pattern = re.compile(token_regex, re.IGNORECASE)

    cov_functions = set()

    line = ""
    with open(filename, "r") as f:
        while True:
            line = f.readline()
            if not line:
                break
            match = re.match(token_pattern, line)
            if match:
                loc = match.group(1).strip().split()
                for i in loc:
                    cov_functions.add(i)
    return cov_functions


def get_function_deps(call_map_file, cov_functions):
    """Return a set of functions and the functions called by those functions.
    Given a set of function names, return a set containing those functions and
    any dependent functions defined by the callmap."""
    cov_functions_deps = set()
    with open(call_map_file, "r") as callmap_f:
        callmap = json.load(callmap_f)
        for function in cov_functions:
            # Check callgraph and add dependent functions in this project
            if function in callmap:
                cov_functions_deps.add(function)
                for dep in callmap[function]:
                    cov_functions_deps.add(dep)
            else:
                print(
                    "WARN: function specified in unit test file ({}) was not "
                    "found in {}.\nCheck that the function name is correct and"
                    " that the specified coverage target is not a macro.".format(
                        function, call_map_file
                    ),
                    file=sys.stderr,
                )
    return cov_functions_deps


def filter_coverage_file(covfile_handle, cov_functions):
    """Given an input coverage json file and a set of functions that the test
    is targeting, filter the coverage file to only include data generated
    by running the given functions."""
    covdata_out = dict()
    covdata = json.load(covfile_handle)
    # copy basic info
    assert covdata["format_version"] == "1"
    covdata_out["format_version"] = covdata["format_version"]
    covdata_out["current_working_directory"] = covdata["current_working_directory"]
    covdata_out["data_file"] = covdata["data_file"]
    covdata_out["gcc_version"] = covdata["gcc_version"]
    # handle per proj file data
    covdata_out["files"] = list()
    for targetfile in covdata["files"]:
        cur_file = dict()
        cur_file["file"] = targetfile["file"]
        cur_functions = list()
        for function in targetfile["functions"]:
            if function["name"] in cov_functions:
                cur_functions.append(function)
        cur_file["functions"] = cur_functions
        cur_lines = list()
        for line in targetfile["lines"]:
            if "function_name" in line and line["function_name"] in cov_functions:
                cur_lines.append(line)
        cur_file["lines"] = cur_lines
        covdata_out["files"].append(cur_file)
    return covdata_out


def get_excluded_lines(c_file):
    """Read a .c file and determine which lines should be excluded based on
    LCOV_EXCL comments"""
    excl_lines = set()
    excl_br_lines = set()
    excl_line_flag = False
    excl_br_line_flag = False
    with open(c_file, "r") as cfile:
        line_number = 1
        while True:
            line = cfile.readline()
            if not line:
                break
            if "LCOV_EXCL" in line:
                if "LCOV_EXCL_LINE" in line:
                    excl_lines.add(line_number)
                if "LCOV_EXCL_BR_LINE" in line:
                    excl_br_lines.add(line_number)
                if "LCOV_EXCL_START" in line:
                    excl_line_flag = True
                if "LCOV_EXCL_STOP" in line:
                    excl_line_flag = False
                if "LCOV_EXCL_BR_START" in line:
                    excl_br_line_flag = True
                if "LCOV_EXCL_BR_STOP" in line:
                    excl_br_line_flag = False
                if excl_line_flag:
                    excl_lines.add(line_number)
                if excl_br_line_flag:
                    excl_br_lines.add(line_number)
            line_number += 1
    return excl_lines, excl_br_lines


def filter_excluded_lines(covdata):
    """ Remove coverage data for lines excluded with LCOV_EXCL_* comments """
    for target_file in covdata["files"]:
        excl_lines, excl_br_lines = get_excluded_lines(target_file["file"])
        target_lines_excl = list()
        for target_line in target_file["lines"]:
            if not ("line_number" in target_line and "count" in target_line):
                continue
            if int(target_line["line_number"]) in excl_br_lines:
                target_line["branches"] = list()
            if int(target_line["line_number"]) not in excl_lines:
                target_lines_excl.append(target_line)
        target_file["lines"] = target_lines_excl


# Based on lcov's geninfo perl script
def convert_to_lcov_info(args, covdata, outfile):
    """ Convert a given gcov intermediate format json file to lcov .info format """
    outfile.write("TN:{}\n".format(os.path.basename(args.test.replace(".c", ""))))
    for target_file in covdata["files"]:
        functions_found = 0
        functions_hit = 0
        outfile.write("SF:{}\n".format(target_file["file"]))

        # Handle function data
        for target_func in target_file["functions"]:
            # validate stanza and skip
            if not (
                "name" in target_func
                and "start_line" in target_func
                and "execution_count" in target_func
            ):
                continue
            outfile.write(
                "FN:{},{}\n".format(target_func["start_line"], target_func["name"])
            )

            outfile.write(
                "FNDA:{},{}\n".format(
                    target_func["execution_count"], target_func["name"]
                )
            )
            functions_found += 1
            if target_func["execution_count"] > 0:
                functions_hit += 1
        if functions_found > 0:
            outfile.write("FNF:{}\n".format(functions_found))
            outfile.write("FNH:{}\n".format(functions_hit))

        lines_found = 0
        lines_hit = 0
        branches_found = 0
        branches_hit = 0
        # Handle line data
        for target_line in target_file["lines"]:
            if not ("line_number" in target_line and "count" in target_line):
                continue
            outfile.write(
                "DA:{},{}\n".format(target_line["line_number"], target_line["count"])
            )
            lines_found += 1
            if target_line["count"] > 0:
                lines_hit += 1
            # Branch number within each line
            branch_number = 0
            # Handle branch data
            for target_branch in target_line["branches"]:
                branch_count = "-"
                if target_line["unexecuted_block"] and target_line["count"] == 0:
                    branch_count = "-"
                elif "count" in target_branch:
                    branch_count = target_branch["count"]
                # Note: block number is not needed.
                outfile.write(
                    "BRDA:{},0,{},{}\n".format(
                        target_line["line_number"], branch_number, branch_count
                    )
                )
                branch_number += 1
                branches_found += 1
                if branch_count != "-":
                    branches_hit += 1
        if branches_found > 0:
            outfile.write("BRF:{}\n".format(branches_found))
            outfile.write("BRH:{}\n".format(branches_hit))
        outfile.write("LF:{}\n".format(lines_found))
        outfile.write("LH:{}\n".format(lines_hit))
        outfile.write("end_of_record\n")


if __name__ == "__main__":
    main()
