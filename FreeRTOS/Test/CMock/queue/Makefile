# Indent with spaces
.RECIPEPREFIX := $(.RECIPEPREFIX) $(.RECIPEPREFIX)
# Do not move this line below the include
MAKEFILE_ABSPATH     := $(abspath $(lastword $(MAKEFILE_LIST)))
include ../makefile.in

# SUITES lists the suites contained in subdirectories of this directory
SUITES	+=	generic
SUITES	+=	dynamic
SUITES	+=	static
SUITES	+=	semaphore
SUITES	+=	sets
SUITES	+=	tracing

# PROJECT and SUITE variables are determined based on path like so:
#   $(UT_ROOT_DIR)/$(PROJECT)/$(SUITE)
PROJECT :=  $(lastword $(subst /, ,$(dir $(abspath $(MAKEFILE_ABSPATH)))))

include ../subdir.mk
