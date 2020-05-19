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

FREE_RTOS_DIR ?= ${SRC_DIR}/..
FREE_RTOS_INCLUDE_DIR ?= ${ROOT_DIR}/../../Source/FreeRTOS-Plus-TCP/include
FREE_RTOS_SOURCE_DIR ?= ${ROOT_DIR}/../../Source/FreeRTOS-Plus-TCP
CONFIG_FILES_DIR ?= $(ROOT_DIR)/Config_files
TEST_DIR ?= test

KERNEL_INCLUDES ?= ../../../FreeRTOS/Source/include

# ${FREE_RTOS_INCLUDE_DIR}/FreeRTOS_IP.h

INCLUDE_DIR ?= -I ${ROOT_DIR} -I ${KERNEL_INCLUDES} -I ${FREE_RTOS_INCLUDE_DIR} -I $(CONFIG_FILES_DIR) -I ${CMOCK_INCLUDE_DIR} -I ${UNITY_INCLUDE_DIR} -I ${FREE_RTOS_DIR} -I ${MOCKS_DIR} -I ${UNITY_FIXTURE_DIR} -I ${SRC_DIR} -I ${UNITY_MEMORY_DIR}
CODE_COVERAGE ?= -fprofile-arcs -ftest-coverage -fprofile-generate

.PHONY: all clean directories mocks coverage run

all: ${LIB_DIR}/libcmock.so  ${LIB_DIR}/libunity.so directories mocks ${BIN_DIR}/${EXECUTABLE} ${LIB_DIR}/libsys_arch.so

directories:
	mkdir -p ${BUILD_DIR}
	mkdir -p ${MOCKS_DIR}
	mkdir -p ${LIB_DIR}
	mkdir -p ${BIN_DIR}
	mkdir -p ${GEN_DIR}

mocks: directories
	cd ${BUILD_DIR} && ruby  ${CMOCK_LIB_DIR}/cmock.rb -o${CONFIGURATION_DIR}/project.yml ${FREE_RTOS_INCLUDE_DIR}/FreeRTOS_DNS.h

${LIB_DIR}/libcmock.so: ${CMOCK_SRC_DIR}/cmock.c ${CMOCK_SRC_DIR}/cmock.h Makefile ${LIB_DIR}/libunity.so
	${CC} -o $@ -shared -fPIC  $<  ${INCLUDE_DIR}

${LIB_DIR}/libunity.so: ${UNITY_SRC_DIR}/unity.c ${CMOCK_SRC_DIR}/cmock.h Makefile directories
	${CC} -o $@ -shared -fPIC  $< -I ${UNITY_INCLUDE_DIR}

${LIB_DIR}/mock_FreeRTOS_DNS.o: ${MOCKS_DIR}/mock_FreeRTOS_DNS.c mocks Makefile
	${CC}  -c  $<  -o  $@ -DipconfigDNS_USE_CALLBACKS=1  ${INCLUDE_DIR}  -fPIC

#${LWIP_DIR}/sys_arch.c ${LIB_DIR}/mock_queue.o
${LIB_DIR}/libsys_arch.so: ${LIB_DIR}/mock_FreeRTOS_DNS.o
	${CC}  -o  $@  -shared  -fPIC  $+  ${INCLUDE_DIR}  ${CODE_COVERAGE}  -lgcov

${GEN_DIR}/${EXECUTABLE}_test_runner.c: mocks Makefile
	ruby ${UNITY_BIN_DIR}/generate_test_runner.rb   ${CONFIGURATION_DIR}/project.yml ${SRC_DIR}/iot_test_freertos_tcp.c ${GEN_DIR}/${EXECUTABLE}_test_runner.c

${BIN_DIR}/${EXECUTABLE}: ${FREE_RTOS_SOURCE_DIR}/FreeRTOS_DNS.c ${GEN_DIR}/${EXECUTABLE}_test_runner.c ${SRC_DIR}/iot_test_freertos_tcp.c ${LIB_DIR}/libsys_arch.so
	${CC} -o $@  $+  ${INCLUDE_DIR} -L ${LIB_DIR} -Wl,-rpath,${LIB_DIR} -lunity -lcmock -lsys_arch

clean:
	-rm -rf build
	-rm -f sys_arch.gcda  sys_arch.gcno
	-rm -f FreeRTOS_IP.h

copy:
	cp ${FREE_RTOS_INCLUDE_DIR}/FreeRTOS_IP.h ./
#cp ${ROOT_DIR}/../../../FreeRTOS/Demo/WIN32-MSVC/FreeRTOSConfig.h ./

run:  ${LIB_DIR}/libcmock.so  ${LIB_DIR}/libunity.so copy ${BIN_DIR}/${EXECUTABLE}
	${BIN_DIR}/${EXECUTABLE}

coverage: run
	lcov --base-directory . --directory . -c --rc lcov_branch_coverage=1 --rc genhtml_branch_coverage=1  -o build/cmock_test.info
	genhtml build/cmock_test.info --branch-coverage --output-directory build/coverage_html

#lcov --remove cmock_test.info "/usr*" --o cmock_test.info
