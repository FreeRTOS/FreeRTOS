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
CPPFLAGS        +=  -I$(MOCKS_DIR)

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
            $(SUITE_OBJ_LIST) $(RUNNER_SRC_LIST) $(RUNNER_OBJ_LIST)

.DEFAULT_GOAL := run

# preprocess proj files to expand macros for coverage
$(PROJ_DIR)/%.i : $(KERNEL_DIR)/%.c
    mkdir -p $(PROJ_DIR)
    $(CC) -E $< $(CPPFLAGS) -o $@

# compile the project objects with coverage instrumented
$(PROJ_DIR)/%.o : $(PROJ_DIR)/%.i
    $(CC) -c $< $(CPPFLAGS) $(CFLAGS) $(INCLUDE_DIR) $(GCC_COV_OPTS) -Wall -Wextra -Werror -pedantic -std=c89 -o $@

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

# Generate _mock.c / .h files
$(MOCK_HDR_LIST) $(MOCK_SRC_LIST) : $(PROJECT_DIR)/$(PROJECT).yml $(MOCK_FILES_FP)
    mkdir -p $(SCRATCH_DIR) $(MOCKS_DIR)
    cd $(SCRATCH_DIR) && \
        ruby $(CMOCK_EXEC_DIR)/cmock.rb -o$(PROJECT_DIR)/$(PROJECT).yml \
        $(MOCK_FILES_FP)


$(LIBS_LIST) :
    make -C $(UT_ROOT_DIR) libs

include $(UT_ROOT_DIR)/coverage.mk
