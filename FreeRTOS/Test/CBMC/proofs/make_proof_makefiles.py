#!/usr/bin/env python3
#
# Generation of Makefiles for CBMC proofs.
#
# Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.


import argparse
import ast
import collections
import json
import logging
import operator
import os
import os.path
import platform
import re
import sys
import textwrap
import traceback


# ______________________________________________________________________________
# Compatibility between different python versions
# ``````````````````````````````````````````````````````````````````````````````

# Python 3 doesn't have basestring
try:
    basestring
except NameError:
    basestring = str

# ast.Num was deprecated in python 3.8
_plat = platform.python_version().split(".")
if _plat[0] == "3" and int(_plat[1]) > 7:
    ast_num = ast.Constant
else:
    ast_num = ast.Num
# ______________________________________________________________________________


def prolog():
    return textwrap.dedent("""\
        This script generates Makefiles that can be used either on Windows (with
        NMake) or Linux (with GNU Make). The Makefiles consist only of variable
        definitions; they are intended to be used with a common Makefile that
        defines the actual rules.

        The Makefiles are generated from JSON specifications. These are simple
        key-value dicts, but can contain variables and computation, as
        well as comments (lines whose first character is "#"). If the
        JSON file contains the following information:

                {
                    # 'T was brillig, and the slithy toves
                    "FOO": "BAR",
                    "BAZ": "{FOO}",

                    # Did gyre and gimble in the wabe;
                    "QUUX": 30
                    "XYZZY": "__eval 5 if {QUUZ} < 5 else min({QUUX}, 60)"
                }

        then the resulting Makefile will look like

                H_FOO = BAR
                H_BAZ = BAR
                H_QUUX = 30
                H_XYZZY = 30

        The language used for evaluation is highly restricted; arbitrary
        python is not allowed.  JSON values that are lists will be
        joined with whitespace:

                { "FOO": ["BAR", "BAZ", "QUX"] }

                ->

                H_FOO = BAR BAZ QUX

        As a special case, if a key is equal to "DEF", "INC" (and maybe more,
        read the code) the list of values is treated as a list of defines or
        include paths. Thus, they have -D or /D, or -I or /I, prepended to them
        as appropriate for the platform.


                { "DEF": ["DEBUG", "FOO=BAR"] }

                on Linux ->

                H_DEF = -DDEBUG -DFOO=BAR

        Pathnames are written with a forward slash in the JSON file. In
        each value, all slashes are replaced with backslashes if
        generating Makefiles for Windows. If you wish to generate a
        slash even on Windows, use two slashes---that will be changed
        into a single forward slash on both Windows and Linux.

                {
                    "INC": [ "my/cool/directory" ],
                    "DEF": [ "HALF=//2" ]
                }

                On Windows ->

                H_INC = /Imy\cool\directory
                H_DEF = /DHALF=/2

        When invoked, this script walks the directory tree looking for files
        called "Makefile.json". It reads that file and dumps a Makefile in that
        same directory. We assume that this script lives in the same directory
        as a Makefile called "Makefile.common", which contains the actual Make
        rules. The final line of each of the generated Makefiles will be an
        include statement, including Makefile.common.
    """)

def load_json_config_file(file):
    with open(file) as handle:
        lines = handle.read().splitlines()
    no_comments = "\n".join([line for line in lines
                             if line and not line.lstrip().startswith("#")])
    try:
        data = json.loads(no_comments,
                          object_pairs_hook=collections.OrderedDict)
    except json.decoder.JSONDecodeError:
        traceback.print_exc()
        logging.error("parsing file %s", file)
        sys.exit(1)
    return data


def dump_makefile(dyr, system):
    data = load_json_config_file(os.path.join(dyr, "Makefile.json"))

    makefile = collections.OrderedDict()

    # Makefile.common expects a variable called OBJS_EXCEPT_HARNESS to be
    # set to a list of all the object files except the harness.
    if "OBJS" not in data:
        logging.error(
            "Expected a list of object files in %s/Makefile.json" % dyr)
        exit(1)
    makefile["OBJS_EXCEPT_HARNESS"] = " ".join(
        o for o in data["OBJS"] if not o.endswith("_harness.goto"))

    so_far = collections.OrderedDict()
    for name, value in data.items():
        if isinstance(value, list):
            new_value = []
            for item in value:
                new_value.append(compute(item, so_far, system, name, dyr, True))
            makefile[name] = " ".join(new_value)
        else:
            makefile[name] = compute(value, so_far, system, name, dyr)

    if (("EXPECTED" not in makefile.keys()) or
            str(makefile["EXPECTED"]).lower() == "true"):
        makefile["EXPECTED"] = "SUCCESSFUL"
    elif str(makefile["EXPECTED"]).lower() == "false":
        makefile["EXPECTED"] = "FAILURE"
    makefile = ["H_%s = %s" % (k, v) for k, v in makefile.items()]

    # Deal with the case of a harness being nested several levels under
    # the top-level proof directory, where the common Makefile lives
    common_dir_path = "..%s" % _platform_choices[system]["path-sep"]
    common_dir_path = common_dir_path * len(dyr.split(os.path.sep)[1:])

    with open(os.path.join(dyr, "Makefile"), "w") as handle:
        handle.write(("""{contents}

{include} {common_dir_path}Makefile.common""").format(
            contents="\n".join(makefile),
            include=_platform_choices[system]["makefile-inc"],
            common_dir_path=common_dir_path))


def compute(value, so_far, system, key, harness, appending=False):
    if not isinstance(value, (basestring, float, int)):
        logging.error(wrap("""\
                        in file %s, the key '%s' has value '%s',
                        which is of the wrong type (%s)"""),
                      os.path.join(harness, "Makefile.json"), key,
                      str(value), str(type(value)))
        exit(1)

    value = str(value)
    try:
        var_subbed = value.format(**so_far)
    except KeyError as e:
        logging.error(wrap("""\
                        in file %s, the key '%s' has value '%s', which
                        contains the variable %s, but that variable has
                        not previously been set in the file"""),
                      os.path.join(harness, "Makefile.json"), key,
                      value, str(e))
        exit(1)

    if var_subbed[:len("__eval")] != "__eval":
        tmp = re.sub("//", "__DOUBLE_SLASH__", var_subbed)
        tmp = re.sub("/", _platform_choices[system]["path-sep-re"], tmp)
        evaluated = re.sub("__DOUBLE_SLASH__", "/", tmp)
    else:
        to_eval = var_subbed[len("__eval"):].strip()
        logging.debug("About to evaluate '%s'", to_eval)
        evaluated = eval_expr(to_eval,
                              os.path.join(harness, "Makefile.json"),
                              key, value)

    if key == "DEF":
        final_value = "%s%s" % (_platform_choices[system]["define"],
                                evaluated)
    elif key == "INC":
        final_value = "%s%s" % (_platform_choices[system]["include"],
                                evaluated)
    else:
        final_value = evaluated

    # Allow this value to be used for future variable substitution
    if appending:
        try:
            so_far[key] = "%s %s" % (so_far[key], final_value)
        except KeyError:
            so_far[key] = final_value
        logging.debug("Appending final value '%s' to key '%s'",
                      final_value, key)
    else:
        so_far[key] = final_value
        logging.info("Key '%s' set to final value '%s'", key, final_value)

    return final_value


def eval_expr(expr_string, harness, key, value):
    """
    Safe evaluation of purely arithmetic expressions
    """
    try:
        tree = ast.parse(expr_string, mode="eval").body
    except SyntaxError:
        traceback.print_exc()
        logging.error(wrap("""\
            in file %s at key '%s', value '%s' contained the expression
            '%s' which is an invalid expression"""), harness, key,
                      value, expr_string)
        exit(1)

    def eval_single_node(node):
        logging.debug(node)
        if isinstance(node, ast_num):
            return node.n
        # We're only doing IfExp, which is Python's ternary operator
        # (i.e. it's an expression). NOT If, which is a statement.
        if isinstance(node, ast.IfExp):
            # Let's be strict and only allow actual booleans in the guard
            guard = eval_single_node(node.test)
            if guard is not True and guard is not False:
                logging.error(wrap("""\
                    in file %s at key '%s', there was an invalid guard
                    for an if statement."""), harness, key)
                exit(1)
            if guard:
                return eval_single_node(node.body)
            return eval_single_node(node.orelse)
        if isinstance(node, ast.Compare):
            left = eval_single_node(node.left)
            # Don't allow expressions like (a < b) < c
            right = eval_single_node(node.comparators[0])
            op = eval_single_node(node.ops[0])
            return op(left, right)
        if isinstance(node, ast.BinOp):
            left = eval_single_node(node.left)
            right = eval_single_node(node.right)
            op = eval_single_node(node.op)
            return op(left, right)
        if isinstance(node, ast.Call):
            valid_calls = {
                "max": max,
                "min": min,
            }
            if node.func.id not in valid_calls:
                logging.error(wrap("""\
                    in file %s at key '%s', there was an invalid
                    call to %s()"""), harness, key, node.func.id)
                exit(1)
            left = eval_single_node(node.args[0])
            right = eval_single_node(node.args[1])
            return valid_calls[node.func.id](left, right)
        try:
            return {
                ast.Eq: operator.eq,
                ast.NotEq: operator.ne,
                ast.Lt: operator.lt,
                ast.LtE: operator.le,
                ast.Gt: operator.gt,
                ast.GtE: operator.ge,

                ast.Add: operator.add,
                ast.Sub: operator.sub,
                ast.Mult: operator.mul,
                # Use floordiv (i.e. //) so that we never need to
                # cast to an int
                ast.Div: operator.floordiv,
            }[type(node)]
        except KeyError:
            logging.error(wrap("""\
                in file %s at key '%s', there was expression that
                was impossible to evaluate"""), harness, key)
            exit(1)

    return eval_single_node(tree)


_platform_choices = {
    "linux": {
        "platform": "linux",
        "path-sep": "/",
        "path-sep-re": "/",
        "define": "-D",
        "include": "-I",
        "makefile-inc": "include",
    },
    "windows": {
        "platform": "win32",
        "path-sep": "\\",
        "path-sep-re": re.escape("\\"),
        "define": "/D",
        "include": "/I",
        "makefile-inc": "!INCLUDE",
    },
}
# Assuming macos is the same as linux
_mac_os = dict(_platform_choices["linux"])
_mac_os["platform"] = "darwin"
_platform_choices["macos"] = _mac_os


def default_platform():
    for arg_string, os_data in _platform_choices.items():
        if sys.platform == os_data["platform"]:
            return arg_string
    return "linux"


_args = [{
    "flags": ["-s", "--system"],
    "metavar": "OS",
    "choices": _platform_choices,
    "default": str(default_platform()),
    "help": textwrap.dedent("""\
                which operating system to generate makefiles for.
                Defaults to the current platform (%(default)s);
                choices are {choices}""").format(
                    choices="[%s]" % ", ".join(_platform_choices)),
}, {
    "flags": ["-v", "--verbose"],
    "help": "verbose output",
    "action": "store_true",
}, {
    "flags": ["-w", "--very-verbose"],
    "help": "very verbose output",
    "action": "store_true",
    }]


def get_args():
    pars = argparse.ArgumentParser(
        description=prolog(),
        formatter_class=argparse.RawDescriptionHelpFormatter)
    for arg in _args:
        flags = arg.pop("flags")
        pars.add_argument(*flags, **arg)
    return pars.parse_args()


def set_up_logging(args):
    fmt = "{script}: %(levelname)s %(message)s".format(
        script=os.path.basename(__file__))
    if args.very_verbose:
        logging.basicConfig(format=fmt, level=logging.DEBUG)
    elif args.verbose:
        logging.basicConfig(format=fmt, level=logging.INFO)
    else:
        logging.basicConfig(format=fmt, level=logging.WARNING)

def wrap(string):
    return re.sub(r"\s+", " ", re.sub("\n", " ", string))

def main():
    args = get_args()
    set_up_logging(args)

    for root, _, fyles in os.walk("."):
        if "Makefile.json" in fyles:
            dump_makefile(root, args.system)


if __name__ == "__main__":
    main()
