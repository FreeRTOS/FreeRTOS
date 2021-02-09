# Change to match installed location
export CC=/usr/local/bin/gcc
export LD=/usr/local/bin/ld
# Add units here when adding a new unit test directory with the same name
UNITS := queue list

include makefile.in

.PHONY: all run doc clean $(UNITS) coverage | directories

all: doc coverage
execs: $(UNITS) | directories


$(UNITS) : ${LIB_DIR}/libcmock.so  ${LIB_DIR}/libunity.so | directories
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
	@echo -e 'Usage: $$ make <unit>\n '
	@echo -e ' where <unit> is one of: $(UNITS) doc all run run_formatted run_col run_col_formatted coverage'

$(LIB_DIR)/libcmock.so : ${CMOCK_SRC_DIR}/cmock.c     \
			${CMOCK_SRC_DIR}/cmock.h      \
			${LIB_DIR}/libunity.so        \
			Makefile | directories
	${CC} -o $@ -shared -fPIC  $<  ${INCLUDE_DIR}

$(LIB_DIR)/libunity.so : ${UNITY_SRC_DIR}/unity.c     \
			 ${UNITY_SRC_DIR}/unity.h     \
			 Makefile | directories
	${CC} -o $@ -shared -fPIC  $< 

run : $(UNITS) | directories
	for f in $(BIN_DIR)/*; do \
	  $${f}; done 

run_col : $(UNITS) | directories
	for f in $(BIN_DIR)/*; do \
	  ruby -r $(UNITY_BIN_DIR)/colour_reporter.rb  -e "report('`$${f}`')"; done 

run_formatted :  $(UNITS) | directories
	for f in $(BIN_DIR)/*; do \
	  $${f} > $(BUILD_DIR)/output; \
	  ruby  $(UNITY_BIN_DIR)/parse_output.rb $(BUILD_DIR)/output ; \
	  done 

run_col_formatted :  $(UNITS) | directories
	for f in $(BIN_DIR)/*; do \
	  $${f} > $(BUILD_DIR)/output; \
	  ruby -r $(UNITY_BIN_DIR)/colour_reporter.rb  \
		-e "report('$$(ruby $(UNITY_BIN_DIR)/parse_output.rb \
		 $(BUILD_DIR)/output)')"; \
	  done 

coverage : run_col
	lcov --base-directory . --directory . -c --rc lcov_branch_coverage=1 \
	    --rc genhtml_branch_coverage=1  -o $(BUILD_DIR)/cmock_test.info
	genhtml $(BUILD_DIR)/cmock_test.info --branch-coverage               \
	    --output-directory $(COVERAGE_DIR)

