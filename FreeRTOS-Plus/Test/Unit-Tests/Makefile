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

KERNEL_INCLUDES ?= ${ROOT_DIR}/../../../FreeRTOS/Source/include

# ${FREE_RTOS_INCLUDE_DIR}/FreeRTOS_IP.h       -I ${FREE_RTOS_INCLUDE_DIR}

INCLUDE_DIR ?= -I ${ROOT_DIR} -I ${KERNEL_INCLUDES} -I $(CONFIG_FILES_DIR) -I ${CMOCK_INCLUDE_DIR} -I ${UNITY_INCLUDE_DIR} -I ${FREE_RTOS_DIR} -I ${MOCKS_DIR} -I ${UNITY_FIXTURE_DIR} -I ${SRC_DIR} -I ${UNITY_MEMORY_DIR}

MOCK_HEADERS ?= ${CONFIG_FILES_DIR}/FreeRTOS_IP_Private.h ${CONFIG_FILES_DIR}/FreeRTOS_Sockets.h ${CONFIG_FILES_DIR}/FreeRTOS_IP.h ${KERNEL_INCLUDES}/task.h ${CONFIG_FILES_DIR}/FreeRTOSConfig.h

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
	cd ${BUILD_DIR} && ruby  ${CMOCK_LIB_DIR}/cmock.rb -o${CONFIGURATION_DIR}/project.yml ${MOCK_HEADERS}
	@echo "\n"

${LIB_DIR}/libcmock.so: ${CMOCK_SRC_DIR}/cmock.c ${CMOCK_SRC_DIR}/cmock.h Makefile ${LIB_DIR}/libunity.so
	${CC} -o $@ -shared -fPIC  $<  ${INCLUDE_DIR}
	@echo "\n"

${LIB_DIR}/libunity.so: ${UNITY_SRC_DIR}/unity.c ${CMOCK_SRC_DIR}/cmock.h Makefile directories
	${CC} -o $@ -shared -fPIC  $< -I ${UNITY_INCLUDE_DIR}
	@echo "\n"

#${LWIP_DIR}/sys_arch.c ${LIB_DIR}/mock_queue.o
${LIB_DIR}/libsys_arch.so: ${LIB_DIR}/mock_FreeRTOS_IP_Private.o ${LIB_DIR}/mock_FreeRTOS_Sockets.o ${LIB_DIR}/mock_FreeRTOS_IP.o ${LIB_DIR}/mock_task.o ${LIB_DIR}/mock_FreeRTOSConfig.o
	${CC}  -o  $@  -shared  -fPIC  $+  ${INCLUDE_DIR}  ${CODE_COVERAGE}  -lgcov
	@echo "\n"

#=============================================================================================
#======================== LIST ALL THE HEADERS YOU WANT TO MOCK HERE =========================
${LIB_DIR}/mock_FreeRTOS_IP_Private.o: ${MOCKS_DIR}/mock_FreeRTOS_IP_Private.c mocks Makefile
	${CC}  -c  $<  -o  $@ ${INCLUDE_DIR}  -fPIC
	@echo "\n"

${LIB_DIR}/mock_FreeRTOS_Sockets.o: ${MOCKS_DIR}/mock_FreeRTOS_Sockets.c mocks Makefile
	${CC}  -c  $<  -o  $@ ${INCLUDE_DIR}  -fPIC
	@echo "\n"

${LIB_DIR}/mock_FreeRTOS_IP.o: ${MOCKS_DIR}/mock_FreeRTOS_IP.c mocks Makefile
	${CC}  -c  $<  -o  $@ ${INCLUDE_DIR}  -fPIC
	@echo "\n"

${LIB_DIR}/mock_task.o: ${MOCKS_DIR}/mock_task.c mocks Makefile
	${CC}  -c  $<  -o  $@ ${INCLUDE_DIR}  -fPIC
	@echo "\n"

${LIB_DIR}/mock_FreeRTOSConfig.o: ${MOCKS_DIR}/mock_FreeRTOSConfig.c mocks Makefile
	${CC}  -c  $<  -o  $@ ${INCLUDE_DIR}  -fPIC
	@echo "\n"
#---------------------------------------------------------------------------------------------
#=============================================================================================

#${GEN_DIR}/${EXECUTABLE}_test_runner.c
${GEN_DIR}/${EXECUTABLE}_test_runner.c: mocks Makefile ${LIB_DIR}/libunity.so
	ruby ${UNITY_BIN_DIR}/generate_test_runner.rb   ${CONFIGURATION_DIR}/project.yml ${SRC_DIR}/iot_test_freertos_tcp.c $@
	@echo "\n"

#${SRC_DIR}/iot_test_freertos_tcp.c
${BIN_DIR}/${EXECUTABLE}: ${UNITY_FIXTURE_DIR}/unity_fixture.c ${SRC_DIR}/iot_freertos_tcp_test_access_dns_define.h ${FREE_RTOS_SOURCE_DIR}/FreeRTOS_DNS.c ${GEN_DIR}/${EXECUTABLE}_test_runner.c ${LIB_DIR}/libsys_arch.so ${LIB_DIR}/libcmock.so ${LIB_DIR}/libunity.so
	${CC} --coverage -o $@  $+  ${INCLUDE_DIR} -L ${LIB_DIR} -Wl,-rpath,${LIB_DIR} -lunity -lcmock -lsys_arch
	@echo "\n"

clean:
	@rm -rf build
	@rm -f sys_arch.gcda  sys_arch.gcno
	@echo "Cleaned...\n"

copy:
	@cp ${FREE_RTOS_INCLUDE_DIR}/* ./Config_files/


run:  ${LIB_DIR}/libcmock.so  ${LIB_DIR}/libunity.so copy ${BIN_DIR}/${EXECUTABLE}
	${BIN_DIR}/${EXECUTABLE}

coverage: run
	lcov --base-directory . --directory . -c --rc lcov_branch_coverage=1 --rc genhtml_branch_coverage=1  -o build/cmock_test.info
	genhtml build/cmock_test.info --branch-coverage --output-directory build/coverage_html

#lcov --remove cmock_test.info "/usr*" --o cmock_test.info
