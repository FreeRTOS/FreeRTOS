#!/bin/bash

echo "Running tests..."
SOURCE_DIR=FreeRTOS/Test/CMock
BUILD_DIR=FreeRTOS/Test/CMock/build
cmake -DBUILD_CLONE_SUBMODULES=0 -S ${SOURCE_DIR} -B ${BUILD_DIR} && make -C ${BUILD_DIR} && ${BUILD_DIR}/bin/tests/queue_utest
TEST_RESULT=$?
echo "Done"
exit ${TEST_RESULT}
