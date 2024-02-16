# Indent with spaces
.RECIPEPREFIX := $(.RECIPEPREFIX) $(.RECIPEPREFIX)

# Define directory paths
SCRATCH_DIR     :=  $(GENERATED_DIR)/$(PROJECT)

LCOV_LIST       :=  $(foreach suite,$(SUITES),$(SCRATCH_DIR)/$(PROJECT)_$(suite).info)
COVINFO         :=  $(GENERATED_DIR)/$(PROJECT).info
COV_REPORT_DIR  :=  $(SCRATCH_DIR)/coverage

.PHONY: all clean libs run bin lcov zerocoverage lcovhtml

all: run

clean :
    rm -rf $(SCRATCH_DIR)
    rm -f $(BIN_DIR)/$(PROJECT)*_utest
    rm -f $(COVINFO)

libs :
    make -C $(UT_ROOT_DIR) libs

lcov : $(COVINFO)

# run each suite and leave gcda / gcov files in place
run: libs
    $(foreach suite,$(SUITES),\
        make -C $(suite) run;)

bin: $(EXEC_LIST)

zerocoverage:
    $(LCOV_BIN_DIR)/lcov --zerocounters --directory $(SCRATCH_DIR)

# Generate lcov for each suite
$(LCOV_LIST) :
    $(foreach suite,$(SUITES),\
        make -C $(suite) lcov;)

# Combine lcov from each subdirectory into one lcov info file for the project
$(COVINFO) : $(LCOV_LIST)
    lcov $(LCOV_OPTS) -o $@ $(foreach cov,$(LCOV_LIST),--add-tracefile $(cov) )

lcovhtml : $(COVINFO)
    mkdir -p $(COV_REPORT_DIR)
    genhtml $(COVINFO) $(LCOV_OPTS) --output-directory $(COV_REPORT_DIR)
