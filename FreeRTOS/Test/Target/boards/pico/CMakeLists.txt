# Note that this file can be used as a top level CMakeLists.txt to build all the Demos (it includes
# them all, but they are usable in their own right, which is why no common work is done here)

# The tests are defined here: https://quip-amazon.com/78LdAeL2txGu/Test-Plan

cmake_minimum_required(VERSION 3.13)

set(UNITY_DIR ${CMAKE_CURRENT_LIST_DIR}/../../../CMock/CMock/vendor/unity)

include(pico_sdk_import.cmake)

PROJECT(Tests)

include(CTest)

add_library(unity STATIC
                "${UNITY_DIR}/src/unity.c")
target_include_directories(unity PUBLIC
        "${UNITY_DIR}/src/")

# add_subdirectory(tests/smp/template)
add_subdirectory( tests/smp/multiple_tasks_running )