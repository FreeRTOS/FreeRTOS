#!/bin/bash -eu

NO_COVERAGE=1 EXTRA_VERIFAST_ARGS=-stats make list queue | grep overhead: | sort | uniq
