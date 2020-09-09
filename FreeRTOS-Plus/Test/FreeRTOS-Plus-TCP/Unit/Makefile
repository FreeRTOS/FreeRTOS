#CC := /usr/local/bin/gcc
#GCOV := /usr/local/bin/gcov

EXECUTABLE=cmock_test
ROOT_DIR ?= $(shell pwd)

CONFIGURATION_DIR ?= ${ROOT_DIR}/tools/configuration

CMOCK_DIR ?= ${ROOT_DIR}/../CMock
CMOCK_SRC_DIR ?= ${CMOCK_DIR}/src
CMOCK_INCLUDE_DIR ?= ${CMOCK_SRC_DIR}
CMOCK_LIB_DIR ?= ${CMOCK_DIR}/lib

UNITY_DIR ?= ${CMOCK_DIR}/vendor/unity
UNITY_SRC_DIR ?= ${UNITY_DIR}/src
UNITY_INCLUDE_DIR ?= ${UNITY_SRC_DIR}
UNITY_BIN_DIR ?= ${UNITY_DIR}/auto
UNITY_FIXTURE_DIR ?= ${UNITY_DIR}/extras/fixture/src
UNITY_MEMORY_DIR ?= ${UNITY_DIR}/extras/memory/src

BUILD_DIR ?= ${ROOT_DIR}/build
LIB_DIR ?= ${ROOT_DIR}/build/lib
BIN_DIR ?= ${ROOT_DIR}/build/bin
MOCKS_DIR ?= ${ROOT_DIR}/build/mocks
GEN_DIR ?= ${ROOT_DIR}/build/generated

SRC_DIR ?= ${ROOT_DIR}/../../Source/FreeRTOS-Plus-TCP/test

EXAMPLE_DIR ?= ${ROOT_DIR}/tests/example

CONFIG_FILES_DIR ?= $(ROOT_DIR)/Config_files
TEST_DIR ?= test

KERNEL_INCLUDES ?= ${ROOT_DIR}/../../../FreeRTOS/Source/include

# ${FREE_RTOS_INCLUDE_DIR}/FreeRTOS_IP.h       -I ${FREE_RTOS_INCLUDE_DIR}

INCLUDE_DIR ?= -I ${ROOT_DIR} -I ${ROOT_DIR}/tests/example -I $(CONFIG_FILES_DIR) -I ${CMOCK_INCLUDE_DIR} -I ${UNITY_INCLUDE_DIR} -I ${MOCKS_DIR} -I ${UNITY_FIXTURE_DIR} -I ${SRC_DIR} -I ${UNITY_MEMORY_DIR}

MOCK_HEADERS ?= ${ROOT_DIR}/tests/example/some_value.h

CODE_COVERAGE ?= -fprofile-arcs -ftest-coverage -fprofile-generate

.PHONY: all clean directories mocks coverage run

all: ${LIB_DIR}/libcmock.so ${LIB_DIR}/libunity.so directories mocks ${BIN_DIR}/${EXECUTABLE}

directories:
	mkdir -p ${BUILD_DIR}
	mkdir -p ${MOCKS_DIR}
	mkdir -p ${LIB_DIR}
	mkdir -p ${BIN_DIR}
	mkdir -p ${GEN_DIR}

mocks: directories
	cd ${BUILD_DIR} && ruby  ${CMOCK_LIB_DIR}/cmock.rb -o${CONFIGURATION_DIR}/project.yml ${MOCK_HEADERS}
	@echo "\n"

${LIB_DIR}/libcmock.so: ${CMOCK_SRC_DIR}/cmock.c ${CMOCK_SRC_DIR}/cmock.h Makefile ${LIB_DIR}/libunity.so
	${CC} -o $@ -shared -fPIC  $<  ${INCLUDE_DIR}
	@echo "\n"

${LIB_DIR}/libunity.so: ${UNITY_SRC_DIR}/unity.c ${CMOCK_SRC_DIR}/cmock.h Makefile directories
	${CC} -o $@ -shared -fPIC  $< -I ${UNITY_INCLUDE_DIR}
	@echo "\n"

#=============================================================================================
#============== LIST ALL THE HEADERS YOU WANT TO MOCK IN SIMILAR MANNER  =====================
${LIB_DIR}/mock_some_value.o: ${MOCKS_DIR}/mock_some_value.c mocks Makefile
	${CC} -c $< -o $@ ${INCLUDE_DIR} -fPIC

COMMON_OBJECTS ?= ${LIB_DIR}/mock_some_value.o


#=============================================================================================
#======================== LIST ALL THE TEST SOURCE FILES HERE ================================
TEST_FILES ?= ${EXAMPLE_DIR}/hello_world_test.c

#=============================================================================================
#===================== LIST ALL THE SOURCE FILES UNDER TEST HERE =============================
SOURCE_FILES ?= ${EXAMPLE_DIR}/hello_world.c
#---------------------------------------------------------------------------------------------
#=============================================================================================


${LIB_DIR}/libcommon.so: ${COMMON_OBJECTS}
	${CC} -o $@ -shared -fPIC $+ ${INCLUDE_DIR} ${CODE_COVERAGE} -lgcov


${GEN_DIR}/${EXECUTABLE}_test_runner.c: mocks Makefile ${LIB_DIR}/libunity.so ${LIB_DIR}/libcmock.so
	ruby ${UNITY_BIN_DIR}/generate_test_runner.rb   ${CONFIGURATION_DIR}/project.yml ${ROOT_DIR}/tests/example/hello_world_test.c $@
	@echo "\n"


${BIN_DIR}/${EXECUTABLE}: ${GEN_DIR}/${EXECUTABLE}_test_runner.c ${TEST_FILES} ${SOURCE_FILES} ${LIB_DIR}/libcommon.so
	${CC} --coverage -o $@  $+  ${INCLUDE_DIR} -L ${LIB_DIR} -Wl,-rpath,${LIB_DIR} -lunity -lcmock -lcommon
	@echo "\n"

clean:
	@rm -rf build
	@rm -f *.gcda  *.gcno
	@echo "Cleaned...\n"

run:  ${BIN_DIR}/${EXECUTABLE}
	${BIN_DIR}/${EXECUTABLE}

coverage: run
	lcov --base-directory . --directory . -c --rc lcov_branch_coverage=1 --rc genhtml_branch_coverage=1  -o build/cmock_test.info
	genhtml build/cmock_test.info --branch-coverage --output-directory build/coverage_html

