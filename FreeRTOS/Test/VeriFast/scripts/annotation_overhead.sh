#!/bin/bash -eu

NO_COVERAGE=1 EXTRA_VERIFAST_ARGS=-stats make queue list | grep overhead: | sort | uniq
