# Do not move this line below the include
MAKEFILE_ABSPATH	:=	$(abspath $(lastword $(MAKEFILE_LIST)))
include ../makefile.in

# PROJECT_SRC lists the .c files under test
PROJECT_SRC			:=	list.c

# PROJECT_DEPS_SRC list the .c file that are dependencies of PROJECT_SRC files
# Files in PROJECT_DEPS_SRC are excluded from coverage measurements
PROJECT_DEPS_SRC	:=

# PROJECT_HEADER_DEPS: headers that should be excluded from coverage measurements.
PROJECT_HEADER_DEPS	:=	FreeRTOS.h

# SUITE_UT_SRC: .c files that contain test cases (must end in _utest.c)
SUITE_UT_SRC		:=	list_utest.c

# SUITE_SUPPORT_SRC: .c files used for testing that do not contain test cases.
# Paths are relative to PROJECT_DIR
SUITE_SUPPORT_SRC	:=

# List the headers used by PROJECT_SRC that you would like to mock
MOCK_FILES_FP		:=

# List any addiitonal flags needed by the preprocessor
CPPFLAGS			+=	-DportUSING_MPU_WRAPPERS=0

# List any addiitonal flags needed by the compiler
CFLAGS				+=

# Try not to edit beyond this line unless necessary.

# Project is determined based on path: $(UT_ROOT_DIR)/$(PROJECT)
PROJECT			:=	$(lastword $(subst /, ,$(dir $(abspath $(MAKEFILE_ABSPATH)))))

# Define directory paths
SCRATCH_DIR		:=	$(GENERATED_DIR)/$(PROJECT)
MOCKS_DIR		:=	$(SCRATCH_DIR)/mocks
PROJ_DIR		:=	$(SCRATCH_DIR)/proj
PROJECT_DIR		:=	$(abspath .)
SUITE_DIR		:=	$(abspath .)

# Define mock details
MOCK_FILES		:=	$(notdir $(MOCK_FILES_FP))
MOCK_SRC		:=	$(addprefix mock_,$(MOCK_FILES:.h=.c))
MOCK_OBJ		:=	$(addprefix mock_,$(MOCK_FILES:.h=.o))
MOCK_SRC_LIST	:=	$(addprefix $(MOCKS_DIR)/,$(MOCK_SRC))
MOCK_OBJ_LIST	:=	$(addprefix $(SCRATCH_DIR)/,$(MOCK_OBJ))
CFLAGS			+=	-I$(MOCKS_DIR)/
PROJ_SRC_LIST	:=	$(addprefix $(KERNEL_DIR)/,$(PROJECT_SRC))
PROJ_PP_LIST	:=	$(addprefix $(PROJ_DIR)/,$(PROJECT_SRC:.c=.i))
PROJ_OBJ_LIST	:=	$(addprefix $(PROJ_DIR)/,$(PROJECT_SRC:.c=.o))
PROJ_GCDA_LIST	:=	$(PROJ_OBJ_LIST:.o=.gcda)
SUITE_OBJ_LIST	:=	$(addprefix $(SCRATCH_DIR)/,$(SUITE_UT_SRC:.c=.o))
RUNNER_SRC_LIST	:=	$(addprefix $(SCRATCH_DIR)/,$(SUITE_UT_SRC:_utest.c=_utest_runner.c))
RUNNER_OBJ_LIST	:=	$(addprefix $(SCRATCH_DIR)/,$(SUITE_UT_SRC:_utest.c=_utest_runner.o))
SF_OBJ_LIST		:= 	$(addprefix $(SCRATCH_DIR)/sf_,$(SUITE_SUPPORT_SRC:.c=.o))
DEPS_OBJ_LIST	:= 	$(addprefix $(SCRATCH_DIR)/dep_,$(PROJECT_DEPS_SRC:.c=.o))
EXECS			:=	$(addprefix $(PROJECT)_,$(SUITE_UT_SRC:.c=))
EXEC_LIST		:=	$(addprefix $(BIN_DIR)/,$(EXECS))
COV_LIST		:=	$(addsuffix .info,$(addprefix $(SCRATCH_DIR)/,$(SUITE_UT_SRC:.c=)))
COVINFO			:=	$(PROJECT)_utest.info
LIBS			:=	$(foreach lib, $(LIBS), $(LIB_DIR)/$(lib).so)

# Coverage related options
GCC_COV_OPTS	:=	-fprofile-arcs -ftest-coverage -fprofile-generate
LCOV_OPTS		:=	--config-file $(UT_ROOT_DIR)/lcovrc
GCOV_OPTS		:=	--unconditional-branches --branch-probabilities

.PHONY: all clean run gcov bin lcov lcovhtml

# Prevent deletion of intermediate files
NO_DELETE :	$(MOCK_SRC_LIST) $(MOCK_OBJ_LIST) $(SF_OBJ_LIST) $(EXEC_LIST) \
			$(DEPS_OBJ_LIST) $(PROJ_PP_LIST) $(PROJ_OBJ_LIST) $(PROJ_GCDA_LIST) \
			$(SUITE_OBJ_LIST) $(RUNNER_SRC_LIST) $(RUNNER_OBJ_LIST) $(COV_LIST)	\
			# $(COVINFO)

# Rules that run test binaries cannot be run in parallel.
.NOTPARALLEL 	:= 	$(SCRATCH_DIR)/$(COVINFO) $(COV_LIST) $(PROJ_GCDA_LIST)

.DEFAULT_GOAL 	:= 	all
all: gcov

clean:
	rm -rf $(SCRATCH_DIR)
	rm -rf $(EXEC_LIST)
	rm -rf $(COVERAGE_DIR)/$(PROJECT)

$(LIBS)&:
	make -C $(UT_ROOT_DIR) libs

# Generate gcov files by default
run : gcov

gcov : $(PROJ_GCDA_LIST)

define run-test
$(1)

endef

# Run and append to gcov data files
$(PROJ_GCDA_LIST) &: $(EXEC_LIST)
	rm -f $(PROJ_DIR)/*.gcda
	# run each test case
	$(foreach bin,$^,$(call run-test,$(bin)))

# Run and generate lcov
lcov: $(SCRATCH_DIR)/$(COVINFO)

lcovhtml : $(SCRATCH_DIR)/$(COVINFO)
	mkdir -p $(COVERAGE_DIR)/$(PROJECT)
	genhtml $(SCRATCH_DIR)/$(COVINFO) $(LCOV_OPTS)  \
			--output-directory $(COVERAGE_DIR)/$(PROJECT)

bin: $(EXEC_LIST)

# Generate _mock.c / .h files
# $(MOCK_SRC_LIST) &: $(PROJECT_DIR)/$(PROJECT).yml $(MOCK_FILES_FP)
# 	mkdir -p $(SCRATCH_DIR) $(MOCKS_DIR)
# 	cd $(SCRATCH_DIR) && \
# 		ruby $(CMOCK_EXEC_DIR)/cmock.rb -o$(PROJECT_DIR)/$(PROJECT).yml \
# 		$(MOCK_FILES_FP)

# preprocess proj files to expand macros for coverage
$(PROJ_DIR)/%.i : $(KERNEL_DIR)/%.c $(MOCK_SRC_LIST)
	mkdir -p $(PROJ_DIR)
	$(CC) -E $< $(CPPFLAGS) $(CFLAGS) -o $@

# Generate callgraph for coverage filtering later on
$(SCRATCH_DIR)/callgraph.json : $(PROJ_SRC_LIST)
	mkdir -p $(SCRATCH_DIR)
	python3 $(UT_ROOT_DIR)/tools/callgraph.py $^ > $@

COVERAGE_EXCLUDE := $(foreach excl,$(PROJECT_HEADER_DEPS), -fprofile-exclude-files=$(excl))
# compile the project objects with coverage instrumented
$(PROJ_DIR)/%.o : $(PROJ_DIR)/%.i
	$(CC) -c $< $(CPPFLAGS) $(INCLUDE_DIR) $(GCC_COV_OPTS) $(COVERAGE_EXCLUDE) -o $@

# Build mock objects
$(SCRATCH_DIR)/mock_%.o : $(MOCKS_DIR)/mock_%.c
	$(CC) -c $< $(CPPFLAGS) $(CFLAGS) -o $@

# compile unit tests
$(SCRATCH_DIR)/%_utest.o : $(SUITE_DIR)/%_utest.c $(MOCK_SRC_LIST)
	mkdir -p $(SCRATCH_DIR)
	$(CC) -c $< $(CPPFLAGS) $(CFLAGS) -o $@

# compile support files
$(SCRATCH_DIR)/sf_%.o : $(PROJECT_DIR)/%.c $(MOCK_SRC_LIST)
	mkdir -p $(SCRATCH_DIR)
	$(CC) -c $< $(CPPFLAGS) $(CFLAGS) -o $@

# compile c files that are needed by PROJ but not mocked
$(SCRATCH_DIR)/dep_%.o : $(KERNEL_DIR)/%.c $(MOCK_SRC_LIST)
	mkdir -p $(SCRATCH_DIR)
	$(CC) -c $< $(CPPFLAGS) $(CFLAGS) -o $@

# generate a test runner for each test file
$(SCRATCH_DIR)/%_utest_runner.c : $(SUITE_DIR)/%_utest.c
	mkdir -p $(SCRATCH_DIR)
	ruby $(UNITY_BIN_DIR)/generate_test_runner.rb\
		$(PROJECT_DIR)/$(PROJECT).yml $< $@

# compile test runner
$(SCRATCH_DIR)/%_utest_runner.o : $(SCRATCH_DIR)/%_utest_runner.c
	$(CC) -c $< $(CPPFLAGS) $(CFLAGS) -o $@

# Link the _utest binary $(SCRATCH_DIR)/%_utest_runner.o
$(BIN_DIR)/$(PROJECT)_%_utest : $(SCRATCH_DIR)/%_utest.o \
								$(SCRATCH_DIR)/%_utest_runner.o \
								$(SF_OBJ_LIST) $(MOCK_OBJ_LIST) \
								$(PROJ_OBJ_LIST) $(LIBS)	\
								$(DEPS_OBJ_LIST)
	mkdir -p $(BIN_DIR)
	$(CC) $< $(subst .o,_runner.o,$<) $(SF_OBJ_LIST) $(DEPS_OBJ_LIST) $(MOCK_OBJ_LIST) $(PROJ_OBJ_LIST) $(LDFLAGS) -o $@

# Run the test runner and genrate a filtered gcov.json.gz file
$(SCRATCH_DIR)/%_utest.info : $(BIN_DIR)/$(PROJECT)_%_utest $(SCRATCH_DIR)/callgraph.json
	# Remove any existing coverage data
	rm -f $(PROJ_DIR)/*.gcda

	# run the testrunner
	$<

	# Gather coverage into a json.gz file
	gcov $(GCOV_OPTS) $(foreach src,$(PROJECT_SRC),$(PROJ_DIR)/$(src:.c=.gcda)) \
		 --json-format --stdout | gzip > $(subst .info,.json.gz,$@)

	# Filter coverage based on tags in unit test file
	$(TOOLS_DIR)/filtercov.py --in $(subst .info,.json.gz,$@) \
							  --map $(SCRATCH_DIR)/callgraph.json \
							  --test $(SUITE_DIR)/$*_utest.c \
							  --format lcov \
							  --out $@
	-lcov $(LCOV_OPTS) --summary $@

	# Remove temporary files
	rm -f $(PROJ_DIR)/*.gcda
	rm -f  $(subst .info,.json.gz,$@)

# # Combine lcov from each test bin into one lcov info file for the suite
# $(SCRATCH_DIR)/$(COVINFO) : $(COV_LIST)
# 	lcov $(LCOV_OPTS) -o $@ $(foreach cov,$(COV_LIST),--add-tracefile $(cov) )
# 	-lcov $(LCOV_OPTS) --summary $@
