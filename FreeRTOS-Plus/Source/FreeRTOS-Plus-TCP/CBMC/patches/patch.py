#!/usr/bin/env python3

import logging
import os
import subprocess
import sys
from glob import glob

from patches_constants import PATCHES_DIR

def patch():
    if os.path.isfile("patched"):
        sys.exit()

    applied_patches = []
    failed_patches = []
    for tmpfile in glob(os.path.join(PATCHES_DIR, "*.patch")):
        print("patch", tmpfile)
        result = subprocess.run(["git", "apply", "--ignore-space-change", "--ignore-whitespace", tmpfile],
                                cwd=os.path.join("..", "..", "..", ".."))
        if result.returncode:
            failed_patches.append(tmpfile)
            logging.error("patching failed: %s", tmpfile)
        else:
            applied_patches.append(tmpfile)

    with open(os.path.join(PATCHES_DIR, "patched"), "w") as outp:
        print("Success:", file=outp)
        print("\n".join(map(lambda x: "\t" + x, applied_patches)), file=outp)

        print("Failure:", file=outp)
        print("\n".join(map(lambda x: "\t" + x, failed_patches)), file=outp)


if __name__ == "__main__":
    patch()
