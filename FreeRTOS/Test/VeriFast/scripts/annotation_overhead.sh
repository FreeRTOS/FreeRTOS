#!/bin/bash -eu

NO_COVERAGE=1 EXTRA_VERIFAST_ARGS=-stats make queue | grep overhead: | sort | uniq
