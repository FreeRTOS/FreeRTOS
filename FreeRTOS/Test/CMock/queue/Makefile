# Indent with spaces
.RECIPEPREFIX := $(.RECIPEPREFIX) $(.RECIPEPREFIX)
# Do not move this line below the include
MAKEFILE_ABSPATH     := $(abspath $(lastword $(MAKEFILE_LIST)))
include ../makefile.in

# SUITES lists the suites contained in subdirectories
SUITES          +=  two_tests

# Project / Suite are determined based on path: $(UT_ROOT_DIR)/$(PROJECT)/$(SUITE)
PROJECT         :=  $(lastword $(subst /, ,$(dir $(abspath $(MAKEFILE_ABSPATH)))))

# Define directory paths
SCRATCH_DIR     :=  $(GENERATED_DIR)/$(PROJECT)

LCOV_LIST       :=  $(foreach suite,$(SUITES),$(SCRATCH_DIR)/$(PROJECT)_$(suite).info)
COVINFO         :=  $(GENERATED_DIR)/$(PROJECT).info

.PHONY: all clean libs run bin lcov zerocoverage

all: run

clean:
    rm -rf $(SCRATCH_DIR)
    rm -f $(BIN_DIR)/$(PROJECT)*_utest
    rm -f $(COVINFO)

libs:
    make -C $(UT_ROOT_DIR) libs

lcov : $(COVINFO)

# run each suite and leave gcda / gcov files in place
run:
    $(foreach suite,$(SUITES),\
        make -C $(suite) run;)

bin: $(EXEC_LIST)

zerocoverage:
    $(LCOV_BIN_DIR)/lcov --zerocounters --directory $(SCRATCH_DIR)

# Combine lcov
$(SCRATCH_DIR)/$(COVINFO): $(LCOV_LIST)
    $(LCOV_BIN_DIR)/lcov $(foreach cov,$(LCOV_LIST),--add-tracefile $(cov) ) \
    --rc lcov_branch_coverage=1 --rc genhtml_branch_coverage=1 \
    -o $@
    $(LCOV_BIN_DIR)/lcov --summary --rc lcov_branch_coverage=1 --rc genhtml_branch_coverage=1 $@

# Generate lcov for each suite
$(LCOV_LIST) :
    $(foreach suite,$(SUITES),\
        make -C $(suite) lcov;)

# Combine lcov from each subdirectory into one lcov info file for the project
$(COVINFO) : $(LCOV_LIST)
    lcov $(LCOV_OPTS) -o $@ $(foreach cov,$(LCOV_LIST),--add-tracefile $(cov) )
