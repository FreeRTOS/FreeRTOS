# Change to match installed location
export CC ?= /usr/local/bin/gcc
export LD ?= /usr/local/bin/ld
#
# Add units here when adding a new unit test directory with the same name
UNITS := list

include makefile.in

.PHONY: all doc clean $(UNITS) directories coverage zero_coverage
.PHONY: run run_formatted run_col_formatted run_col Makefile makefile.in
 
all: doc coverage
execs: $(UNITS) | directories


Makefile : ;

makefile.in : ;


$(UNITS) : ${LIB_DIR}/libcmock.so       \
		${LIB_DIR}/libunity.so          \
		${LIB_DIR}/libunitymemory.so    \
		| directories
	$(MAKE) -C $@

doc: | directories
	$(MAKE) -C doc all

directories : $(BUILD_DIR) $(GENERATED_DIR) $(COVERAGE_DIR) $(BIN_DIR) $(DOC_DIR) $(LIB_DIR)

$(BUILD_DIR) :
	-mkdir  $(BUILD_DIR)
$(GENERATED_DIR) :
	-mkdir -p $(GENERATED_DIR)
$(COVERAGE_DIR) :
	-mkdir -p $(COVERAGE_DIR)
$(BIN_DIR) :
	-mkdir -p $(BIN_DIR)
$(DOC_DIR) :
	-mkdir -p $(DOC_DIR)
$(LIB_DIR) :
	-mkdir -p $(LIB_DIR)

clean:
	rm -rf build

help:
	@echo -e 'Usage: $$ make <target>\n '
	@echo -e ' where <target> is one of: $(UNITS) doc all run run_formatted run_col run_col_formatted coverage'
	@echo -e ''
	@echo -e '$(UNITS) : will build the corresponding test including all its configuration'
	@echo -e 'doc               : will generate doxygen docs in $(BUILD_DIR)/doc/index.html'
	@echo -e 'run               : will build and run all $(UNITS) and their various configurations.'
	@echo -e '                    it will also generate a test report in the JUnit format in $(BUILD_DIR)/report.xml'
	@echo -e 'run_col           : same as run but the results are in colors(pass: green, fail: red)'
	@echo -e 'run_formatted     : will show test case results in a formatted way'
	@echo -e 'run_col_formatted : same as formatted but will show the results in colors'
	@echo -e 'coverage          : will run code coverage and generate html docs in $(BUILD_DIR)/coverage/index.html'
	@echo -e 'all               : will build documentations and coverage, which builds and runs all tests'

$(LIB_DIR)/libcmock.so : $(CMOCK_SRC_DIR)/cmock.c                              \
                         $(CMOCK_SRC_DIR)/cmock.h                              \
                         $(LIB_DIR)/libunity.so                                \
                         Makefile | directories
	$(CC) -o $@ -shared -fPIC  $<  $(INCLUDE_DIR)


$(LIB_DIR)/libunity.so : $(UNITY_SRC_DIR)/unity.c                              \
                         $(UNITY_SRC_DIR)/unity.h                              \
                         Makefile | directories
	${CC} -o $@ -shared -fPIC  $<

$(LIB_DIR)/libunitymemory.so: ${UNITY_EXTRAS_DIR}/memory/src/unity_memory.c \
			${UNITY_EXTRAS_DIR}/memory/src/unity_memory.h 					\
			${LIB_DIR}/libunity.so											\
			Makefile | directories
	${CC} -o $@ -shared -fPIC  $<  ${INCLUDE_DIR}

run : $(UNITS) directories
	-rm $(BUILD_DIR)/unit_test_report.txt
	for f in $(BIN_DIR)/*; do                                   \
		$${f} | tee -a $(BUILD_DIR)/unit_test_report.txt;       \
	done
	cd $(BUILD_DIR) &&                              \
		ruby $(UNITY_BIN_DIR)/parse_output.rb -xml  \
			$(BUILD_DIR)/unit_test_report.txt

run_col : $(UNITS) zero_coverage | directories
	for f in $(BIN_DIR)/*; do \
	  ruby -r $(UNITY_BIN_DIR)/colour_reporter.rb  -e "report('`$${f}`')"; done

run_formatted :  $(UNITS) zero_coverage | directories
	for f in $(BIN_DIR)/*; do \
		$${f} > $(BUILD_DIR)/output; \
		ruby  $(UNITY_BIN_DIR)/parse_output.rb $(BUILD_DIR)/output ; \
		done

run_col_formatted :  $(UNITS) zero_coverage | directories
	for f in $(BIN_DIR)/*; do \
		$${f} > $(BUILD_DIR)/output;  \
		ruby -r $(UNITY_BIN_DIR)/colour_reporter.rb  \
		-e "report('$$(ruby $(UNITY_BIN_DIR)/parse_output.rb \
		$(BUILD_DIR)/output)')"; \
	done

zero_coverage :
	lcov --zerocounters --directory $(BUILD_DIR)
coverage : run_col
	lcov --base-directory . --directory . -c --rc lcov_branch_coverage=1 \
	    --rc genhtml_branch_coverage=1  -o $(BUILD_DIR)/cmock_test.info
	genhtml $(BUILD_DIR)/cmock_test.info --branch-coverage               \
	    --output-directory $(COVERAGE_DIR)

