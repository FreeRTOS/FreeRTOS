# Indent with spaces
.RECIPEPREFIX := $(.RECIPEPREFIX) $(.RECIPEPREFIX)
# Do not move this line below the include
MAKEFILE_ABSPATH     := $(abspath $(lastword $(MAKEFILE_LIST)))
include ../makefile.in

# SUITES lists the suites contained in subdirectories of this directory
SUITES	+=	single_priority_no_timeslice
SUITES	+=	single_priority_timeslice
SUITES	+=	multiple_priorities_no_timeslice
SUITES	+=	multiple_priorities_timeslice

# SUITS mock dependency source for coverage test
SUITES	+=	multiple_priorities_no_timeslice_mock

# SUITS for configASSERT
SUITES	+=	config_assert

# PROJECT and SUITE variables are determined based on path like so:
#   $(UT_ROOT_DIR)/$(PROJECT)/$(SUITE)
PROJECT :=  $(lastword $(subst /, ,$(dir $(abspath $(MAKEFILE_ABSPATH)))))

include ../subdir.mk
