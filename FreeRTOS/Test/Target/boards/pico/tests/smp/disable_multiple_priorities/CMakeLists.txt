cmake_minimum_required(VERSION 3.13)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

set(TEST_INCLUDE_PATHS ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/disable_multiple_priorities)
set(TEST_SOURCE_DIR ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/disable_multiple_priorities)

add_library(disable_multiple_priorities INTERFACE)
target_sources(disable_multiple_priorities INTERFACE
        ${BOARD_LIBRARY_DIR}/main.c
        ${CMAKE_CURRENT_LIST_DIR}/disable_multiple_priorities_test_runner.c
        ${TEST_SOURCE_DIR}/disable_multiple_priorities.c)

target_include_directories(disable_multiple_priorities INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}/../../..
        ${TEST_INCLUDE_PATHS}
        )

target_link_libraries(disable_multiple_priorities INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap4
        ${BOARD_LINK_LIBRARIES})

add_executable(test_disable_multiple_priorities)
enable_board_functions(test_disable_multiple_priorities)
target_link_libraries(test_disable_multiple_priorities disable_multiple_priorities)
target_include_directories(test_disable_multiple_priorities PUBLIC
        ${BOARD_INCLUDE_PATHS})
target_compile_definitions(test_disable_multiple_priorities PRIVATE
        ${BOARD_DEFINES}
)
