# Indent with spaces
.RECIPEPREFIX := $(.RECIPEPREFIX) $(.RECIPEPREFIX)

# define the name for this test's output files
ifdef SUITE
EXEC_PREFIX     :=  $(PROJECT)_$(SUITE)
else
EXEC_PREFIX     :=  $(PROJECT)
endif

# Define directory paths

ifdef SUITE
PROJECT_DIR     :=  $(abspath ../)
else
PROJECT_DIR     :=  $(abspath .)
endif

SUITE_DIR       :=  $(abspath .)

ifdef SUITE
SCRATCH_DIR     :=  $(GENERATED_DIR)/$(PROJECT)/$(SUITE)
else
SCRATCH_DIR     :=  $(GENERATED_DIR)/$(PROJECT)
endif

MOCKS_DIR       :=  $(SCRATCH_DIR)/mocks
PROJ_DIR        :=  $(SCRATCH_DIR)/proj

# Define mock details
MOCK_FILES      :=  $(notdir $(MOCK_FILES_FP))
MOCK_HDR        :=  $(addprefix mock_,$(MOCK_FILES))
MOCK_SRC        :=  $(addprefix mock_,$(MOCK_FILES:.h=.c))
MOCK_OBJ        :=  $(addprefix mock_,$(MOCK_FILES:.h=.o))
MOCK_HDR_LIST   :=  $(addprefix $(MOCKS_DIR)/,$(MOCK_HDR))
MOCK_SRC_LIST   :=  $(addprefix $(MOCKS_DIR)/,$(MOCK_SRC))
MOCK_OBJ_LIST   :=  $(addprefix $(SCRATCH_DIR)/,$(MOCK_OBJ))
CFLAGS          +=  -I$(MOCKS_DIR)

# Kernel files under test
PROJ_SRC_LIST   :=  $(addprefix $(KERNEL_DIR)/,$(PROJECT_SRC))
PROJ_PP_LIST    :=  $(addprefix $(PROJ_DIR)/,$(PROJECT_SRC:.c=.i))
PROJ_OBJ_LIST   :=  $(addprefix $(PROJ_DIR)/,$(PROJECT_SRC:.c=.o))
PROJ_GCDA_LIST  :=  $(PROJ_OBJ_LIST:.o=.gcda)

# Unit test files
SUITE_OBJ_LIST  :=  $(addprefix $(SCRATCH_DIR)/,$(SUITE_UT_SRC:.c=.o))
RUNNER_SRC_LIST :=  $(addprefix $(SCRATCH_DIR)/,$(SUITE_UT_SRC:_utest.c=_utest_runner.c))
RUNNER_OBJ_LIST :=  $(addprefix $(SCRATCH_DIR)/,$(SUITE_UT_SRC:_utest.c=_utest_runner.o))

# Support files
SF_OBJ_LIST     :=  $(addprefix $(SCRATCH_DIR)/sf_,$(SUITE_SUPPORT_SRC:.c=.o))
DEPS_OBJ_LIST   :=  $(addprefix $(SCRATCH_DIR)/dep_,$(PROJECT_DEPS_SRC:.c=.o))
EXECS           :=  $(addprefix $(EXEC_PREFIX)_,$(SUITE_UT_SRC:.c=))
EXEC_LIST       :=  $(addprefix $(BIN_DIR)/,$(EXECS))
LCOV_LIST       :=  $(addsuffix .info,$(addprefix $(SCRATCH_DIR)/,$(SUITE_UT_SRC:.c=)))
COVINFO_INITIAL :=  $(SCRATCH_DIR)/$(EXEC_PREFIX)_initial.info
COVINFO_COMBINE :=  $(SCRATCH_DIR)/$(EXEC_PREFIX)_combined.info
COVINFO         :=  $(abspath $(SCRATCH_DIR)/..)/$(EXEC_PREFIX).info
LIBS_LIST       :=  $(foreach lib, $(LIBS), $(LIB_DIR)/$(lib).so)

# Coverage related options
GCC_COV_OPTS    :=  -fprofile-arcs -ftest-coverage -fprofile-generate
GCOV_OPTS       :=  --unconditional-branches --branch-probabilities
COV_REPORT_DIR  :=  $(SCRATCH_DIR)/coverage

.PHONY: all clean run gcov bin lcov lcovhtml libs

# Prevent deletion of intermediate files
NO_DELETE : $(MOCK_HDR_LIST) $(MOCK_SRC_LIST) $(MOCK_OBJ_LIST)      \
            $(DEPS_OBJ_LIST) $(SF_OBJ_LIST) $(EXEC_LIST)            \
            $(PROJ_PP_LIST) $(PROJ_OBJ_LIST) $(PROJ_GCDA_LIST)      \
            $(SUITE_OBJ_LIST) $(RUNNER_SRC_LIST) $(RUNNER_OBJ_LIST) \
            $(COVINFO) $(LCOV_LIST)

# Cases that run test binaries cannot be run in parallel.
.NOTPARALLEL : $(COVINFO) $(LCOV_LIST) $(PROJ_GCDA_LIST)

.DEFAULT_GOAL := run

# Generate gcov files by default
run : gcov

gcov : $(PROJ_GCDA_LIST)

clean:
    rm -rf $(SCRATCH_DIR)
    rm -rf $(EXEC_LIST)
    rm -rf $(COVINFO)

$(LIBS_LIST) :
    make -C $(UT_ROOT_DIR) libs

define run-test
$(1)

endef

# Run and append to gcov data files
$(PROJ_GCDA_LIST) : $(EXEC_LIST)
    rm -f $(PROJ_DIR)/*.gcda
    mkdir -p $(BIN_DIR)
    # run each test case
    $(foreach bin,$^,$(call run-test,$(bin)))

# Run and generate lcov
lcov: $(COVINFO)

lcovhtml : $(COVINFO)
    mkdir -p $(COV_REPORT_DIR)
    genhtml $(COVINFO) $(LCOV_OPTS) --output-directory $(COV_REPORT_DIR)

bin: $(EXEC_LIST)

# Generate _mock.c / .h files
$(MOCK_HDR_LIST) $(MOCK_SRC_LIST) : $(PROJECT_DIR)/$(PROJECT).yml $(MOCK_FILES_FP)
    mkdir -p $(SCRATCH_DIR) $(MOCKS_DIR)
    cd $(SCRATCH_DIR) && \
        ruby $(CMOCK_EXEC_DIR)/cmock.rb -o$(PROJECT_DIR)/$(PROJECT).yml \
        $(MOCK_FILES_FP)

# Generate callgraph for coverage filtering
$(PROJ_DIR)/callgraph.json : $(PROJ_SRC_LIST)
    mkdir -p $(PROJ_DIR)
    python3 $(UT_ROOT_DIR)/tools/callgraph.py --out $@ $^

# preprocess proj files to expand macros for coverage
$(PROJ_DIR)/%.i : $(KERNEL_DIR)/%.c
    mkdir -p $(PROJ_DIR)
    $(CC) -E $< $(CPPFLAGS) $(CFLAGS) -o $@

# compile the project objects with coverage instrumented
$(PROJ_DIR)/%.o : $(PROJ_DIR)/%.i
    $(CC) -c $< $(CPPFLAGS) $(CFLAGS) $(INCLUDE_DIR) $(GCC_COV_OPTS) -o $@

# Build mock objects
$(SCRATCH_DIR)/mock_%.o : $(MOCKS_DIR)/mock_%.c
    $(CC) -c $< $(CPPFLAGS) $(CFLAGS) -o $@

# compile unit tests
$(SCRATCH_DIR)/%_utest.o : $(SUITE_DIR)/%_utest.c $(MOCK_HDR_LIST) $(LIBS_LIST)
    mkdir -p $(SCRATCH_DIR)
    $(CC) -c $< $(CPPFLAGS) $(CFLAGS) -o $@

# compile support files
$(SCRATCH_DIR)/sf_%.o : $(PROJECT_DIR)/%.c $(MOCK_HDR_LIST)
    mkdir -p $(SCRATCH_DIR)
    $(CC) -c $< $(CPPFLAGS) $(CFLAGS) -o $@

# compile c files that are needed by PROJ but not mocked
$(SCRATCH_DIR)/dep_%.o : $(KERNEL_DIR)/%.c
    mkdir -p $(SCRATCH_DIR)
    $(CC) -c $< $(CPPFLAGS) $(CFLAGS) -o $@

# generate a test runner for each test file
$(SCRATCH_DIR)/%_utest_runner.c : $(SUITE_DIR)/%_utest.c
    mkdir -p $(SCRATCH_DIR)
    ruby $(UNITY_BIN_DIR)/generate_test_runner.rb\
        $(PROJECT_DIR)/$(PROJECT).yml $< $@

# compile test runner
$(SCRATCH_DIR)/%_utest_runner.o : $(SCRATCH_DIR)/%_utest_runner.c
    mkdir -p $(SCRATCH_DIR)
    $(CC) -c $< $(CPPFLAGS) $(CFLAGS) -o $@

# Link the _utest binary
$(EXEC_LIST) : $(BIN_DIR)/$(EXEC_PREFIX)_%_utest : $(SCRATCH_DIR)/%_utest.o         \
                                                   $(SCRATCH_DIR)/%_utest_runner.o  \
                                                   $(SF_OBJ_LIST) $(MOCK_OBJ_LIST)  \
                                                   $(PROJ_OBJ_LIST) $(LIBS_LIST)    \
                                                   $(DEPS_OBJ_LIST)
    mkdir -p $(BIN_DIR)
    $(CC) $< $(subst .o,_runner.o,$<) $(SF_OBJ_LIST) $(DEPS_OBJ_LIST) \
        $(MOCK_OBJ_LIST) $(PROJ_OBJ_LIST) $(LDFLAGS) -o $@

# Generate baseline inital coverage data from .gcno file
$(SCRATCH_DIR)/$(EXEC_PREFIX)_initial.info : $(PROJ_OBJ_LIST)
    lcov $(LCOV_OPTS) --capture --initial --directory $(PROJ_DIR) -o $@

# Run the test runner and genrate a filtered gcov.json.gz file
$(SCRATCH_DIR)/%_utest.info : $(BIN_DIR)/$(EXEC_PREFIX)_%_utest \
                              $(PROJ_DIR)/callgraph.json
    # Remove any existing coverage data
    rm -f $(PROJ_DIR)/*.gcda

    # run the testrunner
    $<

    # Gather coverage into a json.gz file
    gcov $(GCOV_OPTS) $(foreach src,$(PROJECT_SRC),$(PROJ_DIR)/$(src:.c=.gcda)) \
         --json-format --stdout | gzip > $(subst .info,.json.gz,$@)

    # Filter coverage based on tags in unit test file
    $(TOOLS_DIR)/filtercov.py --in $(subst .info,.json.gz,$@)   \
                              --map $(PROJ_DIR)/callgraph.json  \
                              --test $(SUITE_DIR)/$*_utest.c    \
                              --format lcov                     \
                              --out $@
    -lcov $(LCOV_OPTS) --summary $@

    # Remove temporary files
    rm -f $(subst .info,.json.gz,$@)
    rm -f $(PROJ_GCDA_LIST)

# Combine lcov from each test bin into one lcov info file for the suite
$(COVINFO_COMBINE) : $(LCOV_LIST)
    lcov $(LCOV_OPTS) -o $@ $(foreach cov,$(LCOV_LIST),--add-tracefile $(cov) )

# Add baseline / initial coverage generated by gcc to point out untagged functions
$(COVINFO) : $(COVINFO_COMBINE) $(COVINFO_INITIAL)
    lcov $(LCOV_OPTS) -o $@ --add-tracefile $(COVINFO_INITIAL) --add-tracefile $(COVINFO_COMBINE)
