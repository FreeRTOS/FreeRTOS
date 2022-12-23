# Note that this file can be used as a top level CMakeLists.txt to build all the Demos (it includes
# them all, but they are usable in their own right, which is why no common work is done here)

# The tests are defined here: https://quip-amazon.com/78LdAeL2txGu/Test-Plan

cmake_minimum_required(VERSION 3.13)


set(UNITY_DIR ${CMAKE_CURRENT_LIST_DIR}/../CMock/CMock/vendor/unity)
option(TARGET_BOARD "Target Board" posix_host)

if(${TARGET_BOARD} STREQUAL "pico")
    include(boards/pico/pico_sdk_import.cmake)
elseif(${TARGET_BOARD} STREQUAL "pico_w")
    include(boards/pico_w/pico_sdk_import.cmake)
elseif(${TARGET_BOARD} STREQUAL "esp32_wroom_adruino")
    include(xtensal6/esp32/esp_idf_import.cmake)
else()
    message(FATAL_ERROR "A valid target board must be specified.")
endif ()

PROJECT(Tests)

include(CTest)

add_library(unity STATIC
                "${UNITY_DIR}/src/unity.c")
target_include_directories(unity PUBLIC
        "${UNITY_DIR}/src/")

add_subdirectory(tests/template)
add_subdirectory(tests/hello_world)
add_subdirectory(tests/fr1)
add_subdirectory(tests/fr2)
add_subdirectory(tests/fr3)
add_subdirectory(tests/fr4)
add_subdirectory(tests/fr5)
add_subdirectory(tests/fr6)
add_subdirectory(tests/fr7)
add_subdirectory(tests/fr8)
add_subdirectory(tests/fr9)
add_subdirectory(tests/fr10)
add_subdirectory(tests/fr11)