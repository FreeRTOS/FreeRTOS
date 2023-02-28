# indent with spaces
.RECIPEPREFIX := $(.RECIPEPREFIX) $(.RECIPEPREFIX)
include makefile.in

# Change to match installed location
export CC ?= /usr/local/bin/gcc
export LD ?= /usr/local/bin/ld

# Add units here when adding a new unit test directory with the same name
UNITS       :=  timers
UNITS       +=  tasks
UNITS       +=  list
UNITS       +=  queue
UNITS       +=  stream_buffer
UNITS       +=  message_buffer
UNITS       +=  event_groups
UNITS       +=  smp

.PHONY: makefile.in

UNITY_OPTIONS    :=  -DUNITY_USE_COMMAND_LINE_ARGS
UNITY_OPTIONS    +=  -DUNITY_OUTPUT_COLOR -DUNITY_INCLUDE_PRINT_FORMATTED
COVINFO     :=  $(BUILD_DIR)/cmock_test.info
LCOV_LIST   :=  $(foreach unit,$(UNITS),$(GENERATED_DIR)/$(unit).info )

.PHONY: all doc clean $(UNITS) directories coverage zero_coverage              \
        run run_formatted run_col_formatted run_col libs execs lcov            \
        help

include makefile.in

all: doc coverage | directories
execs: $(UNITS) | directories

$(UNITS) : libs | directories
    $(MAKE) -C $@

Makefile : ;

makefile.in : ;

SHARED_LIBS := $(addprefix $(LIB_DIR)/,$(addsuffix .so,$(LIBS)))

libs : $(SHARED_LIBS)

doc:
    $(MAKE) -C doc all

clean:
    rm -rf $(BUILD_DIR)

help:
    @echo -e 'Usage: $$ make <target>\n '
    @echo -e ' where <target> is one of: $(UNITS) doc all run run_formatted run_col run_col_formatted coverage'
    @echo -e ''
    @echo -e '$(UNITS) : will build the corresponding test including all its configuration'
    @echo -e 'doc               : will generate doxygen docs in $(BUILD_DIR)/doc/index.html'
    @echo -e 'run               : will build and run all $(UNITS) and their various configurations.'
    @echo -e '                    It will also generate a test report in the JUnit format in $(BUILD_DIR)/report.xml'
    @echo -e 'run_col           : same as run but the results are in colors(pass: green, fail: red)'
    @echo -e 'run_formatted     : will show test case results in a formatted way'
    @echo -e 'run_col_formatted : same as formatted but will show the results in colors'
    @echo -e 'coverage          : will run code coverage and generate html docs in $(BUILD_DIR)/coverage/index.html'
    @echo -e 'all               : will build documentations and coverage, which builds and runs all tests'

$(LIB_DIR)/libcmock.so : $(CMOCK_SRC_DIR)/cmock.c                              \
                         $(CMOCK_SRC_DIR)/cmock.h                              \
                         $(LIB_DIR)/libunity.so                                \
                         Makefile | directories
    $(CC) -o $@ -shared -fPIC $<  $(INCLUDE_DIR)


$(LIB_DIR)/libunity.so : $(UNITY_SRC_DIR)/unity.c                              \
                         $(UNITY_SRC_DIR)/unity.h                              \
                         Makefile | directories
    ${CC} -o $@ $(UNITY_OPTIONS) -shared -fPIC  $<

$(LIB_DIR)/libunitymemory.so: ${UNITY_MEM_DIR}/unity_memory.c                  \
                              ${UNITY_MEM_DIR}/unity_memory.h                  \
                              ${LIB_DIR}/libunity.so                           \
                              Makefile | directories
    ${CC} -o $@ -shared -fPIC $< ${INCLUDE_DIR}

$(LIB_DIR)/libcexception.so: ${C_EXCEPTION_SRC_DIR}/CException.c               \
                             ${C_EXCEPTION_SRC_DIR}/CException.h               \
                             Makefile | directories
   ${CC} -o $@ -shared -fPIC $< ${INCLUDE_DIR}

run : $(UNITS) | directories
    -rm -f $(BUILD_DIR)/unit_test_report.txt
    for f in $(BIN_DIR)/*; do                                                  \
        $${f} | tee -a $(BUILD_DIR)/unit_test_report.txt ;                     \
    done
    cd $(BUILD_DIR) &&                                                         \
    ruby $(UNITY_BIN_DIR)/parse_output.rb                                      \
        -xml $(BUILD_DIR)/unit_test_report.txt

run_col : $(UNITS) zero_coverage | directories
    for f in $(BIN_DIR)/*; do \
        ruby -r $(UNITY_BIN_DIR)/colour_reporter.rb  -e "report('`$${f}`')";   \
    done

run_formatted :  $(UNITS) zero_coverage | directories
    for f in $(BIN_DIR)/*; do                                                  \
        $${f} > $(BUILD_DIR)/output;                                           \
        ruby  $(UNITY_BIN_DIR)/parse_output.rb $(BUILD_DIR)/output ;           \
    done

run_col_formatted :  $(UNITS) zero_coverage | directories
    for f in $(BIN_DIR)/*; do                                                  \
        $${f} > $(BUILD_DIR)/output;                                           \
        ruby -r $(UNITY_BIN_DIR)/colour_reporter.rb                            \
             -e "report('$$(ruby $(UNITY_BIN_DIR)/parse_output.rb              \
              $(BUILD_DIR)/output)')";                                         \
    done
directories:
    -mkdir -p $(BUILD_DIR)
    -mkdir -p $(LIB_DIR)
    -mkdir -p $(COVERAGE_DIR)
    -mkdir -p $(BIN_DIR)

zero_coverage :
        lcov --zerocounters --directory $(BUILD_DIR) --config-file $(UT_ROOT_DIR)/lcovrc

coverage : run_col
    lcov --base-directory $(KERNEL_DIR) --directory $(BUILD_DIR) --capture     \
        --config-file $(UT_ROOT_DIR)/lcovrc -o $(COVINFO)
    genhtml $(COVINFO) --branch-coverage                                       \
        --config-file $(UT_ROOT_DIR)/lcovrc --output-directory $(COVERAGE_DIR)

lcov : $(COVINFO)

# Combine lcov from each test bin into one lcov info file for the suite
$(COVINFO) : $(LCOV_LIST)
    lcov $(LCOV_OPTS) -o $@ $(foreach cov,$(LCOV_LIST),--add-tracefile $(cov) )

# Generate lcov for each suite
$(LCOV_LIST) : zero_coverage
    make -C $(subst .info,,$(@F)) lcov

lcovhtml : $(COVINFO) | directories
    genhtml $(COVINFO) $(LCOV_OPTS) --output-directory $(COVERAGE_DIR) --quiet
