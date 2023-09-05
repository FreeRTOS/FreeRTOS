#!/usr/bin/env python3
#
# Creating the CBMC proofs from Configurations.json.
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

import collections
import json
import logging
import os
import pathlib
import shutil
import textwrap

from make_proof_makefiles import load_json_config_file

LOGGER = logging.getLogger("ComputeConfigurations")

def prolog():
    return textwrap.dedent("""\
        This script Generates Makefile.json from Configrations.json.

        Starting in the current directory, it walks down every subdirectory
        looking for Configurations.json files. Every found Configurations.json
        file is assumed to look similar to the following format:

        {
          "ENTRY": "ARPProcessPacket",
          "CBMCFLAGS":
          [
              "--unwind 1",
              "--unwindset vARPRefreshCacheEntry.0:7,memcmp.0:17",
              "--nondet-static"
          ],
          "OBJS":
          [
            "$(ENTRY)_harness.goto",
            "$(FREERTOS)/lib/FreeRTOS-Plus-TCP/source/FreeRTOS_ARP.goto"
          ],
          "DEF":
          [
            {"disableClashDetection": ["ipconfigARP_USE_CLASH_DETECTION=0"]},
            {"enableClashDetection": ["ipconfigARP_USE_CLASH_DETECTION=1"]}
          ]
        }

        The format is mainly taken from the Makefile.json files.
        The only difference is that it expects a list of json object in the DEF
        section. This script will generate a Makefile.json in a subdirectory and
        copy the harness to each subdirectory.
        The key is later taken as the name for the configuration subdirectory
        prexied by 'config_'.

        So for the above script, we get two subdirectories:
        -config_disableClashDetection
        -config_enableClashDetection

        As an example, the resulting Makefile.json for the
        config_disableClashDetection directory will be:

        {
          "ENTRY": "ARPProcessPacket",
          "CBMCFLAGS": [
            "--unwind 1",
            "--unwindset vARPRefreshCacheEntry.0:7,memcmp.0:17",
            "--nondet-static"
          ],
          "OBJS": [
            "$(ENTRY)_harness.goto",
            "$(FREERTOS)/lib/FreeRTOS-Plus-TCP/source/FreeRTOS_ARP.goto"
          ],
          "DEF": [
            "ipconfigARP_USE_CLASH_DETECTION=0"
          ]
        }

        These Makefile.json files then can be turned into Makefiles for running
        the proof by executing the make-proof-makefiles.py script.
        """)


def process(folder, files):
    json_content = load_json_config_file(os.path.join(folder,
                                                      "Configurations.json"))
    try:
        def_list = json_content["DEF"]
    except KeyError:
        LOGGER.error("Expected DEF as key in a Configurations.json files.")
        return
    for config in def_list:
        logging.debug(config)
        try:
            configname = [name for name in config.keys()
                          if name != "EXPECTED"][0]
            configbody = config[configname]
        except (AttributeError, IndexError) as e:
            LOGGER.error(e)
            LOGGER.error(textwrap.dedent("""\
            The expected layout for an entry in the Configurations.json
            file is a dictonary. Here is an example of the expected format:

            "DEF":
            [
              {"disableClashDetection": ["ipconfigARP_USE_CLASH_DETECTION=0"]},
              {"enableClashDetection": ["ipconfigARP_USE_CLASH_DETECTION=1"]}
            ]
                """))
            LOGGER.error("The offending entry is %s", config)
            return
        new_config_folder = os.path.join(folder, "config_" + configname)
        pathlib.Path(new_config_folder).mkdir(exist_ok=True, parents=True)
        harness_copied = False
        for file in files:
            # Copy cbmc proof harness into configuration directory
            if file.endswith("harness.c"):
                shutil.copy(os.path.join(folder, file),
                            os.path.join(new_config_folder, file))
                harness_copied = True
            # Copy cbmc-viewer configuration file into configuration directory
            if file == "cbmc-viewer.json":
                shutil.copy(os.path.join(folder, file),
                            os.path.join(new_config_folder, file))

        if not harness_copied:
            LOGGER.error("Could not find a harness in folder %s.", folder)
            LOGGER.error("This folder is not processed do the end!")
            return
        # The order of keys must be maintained as otherwise the
        # make_proof_makefiles script might fail.
        current_config = collections.OrderedDict(json_content)
        current_config["DEF"] = configbody
        if "EXPECTED" in config.keys():
            current_config["EXPECTED"] = config["EXPECTED"]
        else:
            current_config["EXPECTED"] = True
        with open(os.path.join(new_config_folder, "Makefile.json"),
                  "w") as output_file:
            json.dump(current_config, output_file, indent=2)


def main():
    for fldr, _, fyles in os.walk("."):
        if "Configurations.json" in fyles:
            process(fldr, fyles)


if __name__ == '__main__':
    logging.basicConfig(format="{script}: %(levelname)s %(message)s".format(
        script=os.path.basename(__file__)))
    main()
