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

# Find all subdirectories in tests folder then add them by add_subdirectory
file(GLOB_RECURSE SUBDIRS_TESTS_FILES tests/*)
SET(test_dir_list "")

foreach(file_name ${SUBDIRS_TESTS_FILES})
    get_filename_component( dir_path ${file_name} PATH )
    LIST( APPEND test_dir_list ${dir_path})
endforeach()
LIST(REMOVE_DUPLICATES test_dir_list)

foreach(dir_name ${test_dir_list})
    message( STATUS "add subdirectory " ${dir_name} )
    add_subdirectory( ${dir_name} )
endforeach()