# indent with spaces
.RECIPEPREFIX := $(.RECIPEPREFIX) $(.RECIPEPREFIX)
include makefile.in

# Change to match installed location
export CC ?= /usr/local/bin/gcc
export LD ?= /usr/local/bin/ld

# Add units here when adding a new unit test directory with the same name
UNITS       +=  list
UNITS       +=  queue
#UNITS       +=  timers
UNITS       +=  stream_buffer
UNITS       +=  message_buffer
UNITS       +=  event_groups

COVINFO     :=  $(BUILD_DIR)/cmock_test.info
LCOV_LIST   :=  $(foreach unit,$(UNITS),$(GENERATED_DIR)/$(unit).info )

.PHONY: all doc clean $(UNITS) directories coverage zero_coverage \
        run run_formatted run_col_formatted run_col libs execs lcov \
        help

all: doc coverage
execs: $(UNITS)

$(UNITS) : libs | directories
    $(MAKE) -C $@

SHARED_LIBS := $(addprefix $(LIB_DIR)/,$(addsuffix .so,$(LIBS)))

libs : $(SHARED_LIBS)

doc:
    $(MAKE) -C doc all

clean:
    rm -rf build

help:
    @echo -e 'Usage: $$ make <unit>\n '
    @echo -e ' where <unit> is one of: $(UNITS) doc all run run_formatted run_col run_col_formatted coverage'

$(LIB_DIR)/libcmock.so : ${CMOCK_SRC_DIR}/cmock.c   \
                         ${CMOCK_SRC_DIR}/cmock.h   \
                         ${LIB_DIR}/libunity.so     \
                         Makefile
    mkdir -p $(LIB_DIR)
    ${CC} -o $@ -shared -fPIC $< ${INCLUDE_DIR}

$(LIB_DIR)/libunity.so : ${UNITY_SRC_DIR}/unity.c   \
                         ${UNITY_SRC_DIR}/unity.h   \
                         Makefile
    mkdir -p $(LIB_DIR)
    ${CC} -o $@ -shared -fPIC $<

$(LIB_DIR)/libunitymemory.so: ${UNITY_MEM_DIR}/unity_memory.c   \
                              ${UNITY_MEM_DIR}/unity_memory.h   \
                              ${LIB_DIR}/libunity.so            \
                              Makefile
    mkdir -p $(LIB_DIR)
    ${CC} -o $@ -shared -fPIC $< ${INCLUDE_DIR}

$(LIB_DIR)/libcexception.so: ${C_EXCEPTION_SRC_DIR}/CException.c    \
                             ${C_EXCEPTION_SRC_DIR}/CException.h
    mkdir -p $(LIB_DIR)
    ${CC} -o $@ -shared -fPIC $< ${INCLUDE_DIR}

run : $(UNITS)
    mkdir -p $(BUILD_DIR)
    rm -f $(BUILD_DIR)/unit_test_report.txt
    for f in $(BIN_DIR)/*; do                               \
        $${f} | tee -a $(BUILD_DIR)/unit_test_report.txt;   \
    done
    cd $(BUILD_DIR) &&                              \
        ruby $(UNITY_BIN_DIR)/parse_output.rb -xml  \
        $(BUILD_DIR)/unit_test_report.txt

run_col : $(UNITS) zero_coverage
    for f in $(BIN_DIR)/*; do \
        ruby -r $(UNITY_BIN_DIR)/colour_reporter.rb -e "report('`$${f}`')"; done

run_formatted : $(UNITS) zero_coverage
    for f in $(BIN_DIR)/*; do                                       \
        $${f} > $(BUILD_DIR)/output;                                \
        ruby $(UNITY_BIN_DIR)/parse_output.rb $(BUILD_DIR)/output ; \
    done

run_col_formatted : $(UNITS) zero_coverage
    for f in $(BIN_DIR)/*; do                                       \
        $${f} > $(BUILD_DIR)/output;                                \
        ruby -r $(UNITY_BIN_DIR)/colour_reporter.rb                 \
            -e "report('$$(ruby $(UNITY_BIN_DIR)/parse_output.rb    \
        $(BUILD_DIR)/output)')";                                    \
    done

zero_coverage :
    lcov --zerocounters --directory $(BUILD_DIR) --config-file $(UT_ROOT_DIR)/lcovrc

coverage : run_col
    lcov --base-directory $(KERNEL_DIR) --directory $(BUILD_DIR) --capture  \
        --config-file $(UT_ROOT_DIR)/lcovrc -o $(BUILD_DIR)/cmock_test.info
    genhtml $(BUILD_DIR)/cmock_test.info --branch-coverage                      \
        --config-file $(UT_ROOT_DIR)/lcovrc --output-directory $(COVERAGE_DIR)

lcov : $(COVINFO)

# Combine lcov from each test bin into one lcov info file for the suite
$(COVINFO) : $(LCOV_LIST)
    lcov $(LCOV_OPTS) -o $@ $(foreach cov,$(LCOV_LIST),--add-tracefile $(cov) )

# Generate lcov for each suite
$(LCOV_LIST) : zero_coverage
    make -C $(subst .info,,$(@F)) lcov

lcovhtml : $(COVINFO)
    mkdir -p $(COVERAGE_DIR)
    genhtml $(COVINFO) $(LCOV_OPTS) --output-directory $(COVERAGE_DIR) --quiet
