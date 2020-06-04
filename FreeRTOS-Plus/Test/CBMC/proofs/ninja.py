#!/usr/bin/env python3

"""
Write a ninja build file to generate reports for cbmc proofs.

Given a list of folders containing cbmc proofs, write a ninja build
file the generate reports for these proofs.  The list of folders may
be given on the command line, in a json file, or found in the file
system.
"""

# Add task pool

import sys
import os
import platform
import argparse
import json

################################################################
# The command line parser

def argument_parser():
    """Return the command line parser."""

    parser = argparse.ArgumentParser(
        description='Generate ninja build file for cbmc proofs.',
        epilog="""
            Given a list of folders containing cbmc proofs, write a ninja build
            file the generate reports for these proofs.  The list of folders may
            be given on the command line, in a json file, or found in the file
            system.
            In the json file, there should be a dict mapping the key "proofs"
            to a list of folders containing proofs.
            The file system, all folders folders under the current directory
            containing a file named 'cbmc-batch.yaml' is considered a
            proof folder.
            This script assumes that the proof is driven by a Makefile
            with targets goto, cbmc, coverage, property, and report.
            This script does not work with Windows and Visual Studio.
        """
    )
    parser.add_argument('folders', metavar='PROOF', nargs='*',
                        help='Folder containing a cbmc proof')
    parser.add_argument('--proofs', metavar='JSON',
                        help='Json file listing folders containing cbmc proofs')
    return parser

################################################################
# The list of folders containing proofs
#
# The list of folders will be taken from
# 1. the list PROOFS defined here or
# 2. the command line
# 3. the json file specified on the command line containing a
#    dict mapping the key JSON_KEY to a list of folders
# 4. the folders below the current directory containing
#    a file named FS_KEY
#

PROOFS = [
]

JSON_KEY = 'proofs'
FS_KEY = 'cbmc-batch.yaml'

def find_proofs_in_json_file(filename):
    """Read the list of folders containing proofs from a json file."""

    if not filename:
        return []
    try:
        with open(filename) as proofs:
            return json.load(proofs)[JSON_KEY]
    except (FileNotFoundError, KeyError):
        raise UserWarning("Can't find key {} in json file {}".format(JSON_KEY, filename))
    except json.decoder.JSONDecodeError:
        raise UserWarning("Can't parse json file {}".format(filename))

def find_proofs_in_filesystem():
    """Locate the folders containing proofs in the filesystem."""

    proofs = []
    for root, _, files in os.walk('.'):
        if FS_KEY in files:
            proofs.append(os.path.normpath(root))
    return proofs

################################################################
# The strings used to write sections of the ninja file

NINJA_RULES = """
################################################################
# task pool to force sequential builds of goto binaries

pool goto_pool
  depth = 1

################################################################
# proof target rules

rule build_goto
  command = make -C ${folder} goto
  pool = goto_pool

rule build_cbmc
  command = make -C ${folder} cbmc

rule build_coverage
  command = make -C ${folder} coverage

rule build_property
  command = make -C ${folder} property

rule build_report
  command = make -C ${folder} report

rule clean_folder
  command = make -C ${folder} clean

rule veryclean_folder
  command = make -C ${folder} veryclean

rule open_proof
  command = open ${folder}/html/index.html

"""

NINJA_BUILDS = """
################################################################
# {folder} proof targets

build {folder}/{entry}.goto: build_goto
  folder={folder}

build {folder}/cbmc.txt: build_cbmc {folder}/{entry}.goto
  folder={folder}

build {folder}/coverage.xml: build_coverage {folder}/{entry}.goto
  folder={folder}

build {folder}/property.xml: build_property {folder}/{entry}.goto
  folder={folder}

build {folder}/html/index.html: build_report {folder}/{entry}.goto {folder}/cbmc.txt {folder}/coverage.xml {folder}/property.xml
  folder={folder}

build clean_{folder}: clean_folder
  folder={folder}

build veryclean_{folder}: veryclean_folder
  folder={folder}

build open_{folder}: open_proof
  folder={folder}

build {folder}: phony {folder}/html/index.html

default {folder}

"""

NINJA_GLOBALS = """
################################################################
# global targets

build clean: phony {clean_targets}

build veryclean: phony {veryclean_targets}

build open: phony {open_targets}
"""

################################################################
# The main function

def get_entry(folder):
    """Find the name of the proof in the proof Makefile."""

    with open('{}/Makefile'.format(folder)) as makefile:
        for line in makefile:
            if line.strip().lower().startswith('entry'):
                return line[line.find('=')+1:].strip()
            if line.strip().lower().startswith('h_entry'):
                return line[line.find('=')+1:].strip()
    raise UserWarning("Can't find ENTRY in {}/Makefile".format(folder))

def write_ninja_build_file():
    """Write a ninja build file to generate proof results."""

    if platform.system().lower() == 'windows':
        print("This script does not run on Windows.")
        sys.exit()

    args = argument_parser().parse_args()

    proofs = (PROOFS or
              args.folders or
              find_proofs_in_json_file(args.proofs) or
              find_proofs_in_filesystem())

    with open('build.ninja', 'w') as ninja:
        ninja.write(NINJA_RULES)
        for proof in proofs:
            entry = get_entry(proof)
            ninja.write(NINJA_BUILDS.format(folder=proof, entry=entry))
        targets = lambda kind, folders: ' '.join(
            ['{}_{}'.format(kind, folder) for folder in folders]
        )
        ninja.write(NINJA_GLOBALS.format(
            clean_targets=targets('clean', proofs),
            veryclean_targets=targets('veryclean', proofs),
            open_targets=targets('open', proofs)
        ))

################################################################

if __name__ == "__main__":
    write_ninja_build_file()
