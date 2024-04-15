cmake_minimum_required(VERSION 3.13)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

set(TEST_INCLUDE_PATHS ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/schedule_affinity)
set(TEST_SOURCE_DIR ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/schedule_affinity)

add_library(schedule_affinity INTERFACE)
target_sources(schedule_affinity INTERFACE
        ${BOARD_LIBRARY_DIR}/main.c
        ${CMAKE_CURRENT_LIST_DIR}/schedule_affinity_test_runner.c
        ${TEST_SOURCE_DIR}/schedule_affinity.c)

target_include_directories(schedule_affinity INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}/../../..
        ${TEST_INCLUDE_PATHS}
        )

target_link_libraries(schedule_affinity INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap4
        ${BOARD_LINK_LIBRARIES})

add_executable(test_schedule_affinity)
enable_board_functions(test_schedule_affinity)
target_link_libraries(test_schedule_affinity schedule_affinity)
target_include_directories(test_schedule_affinity PUBLIC
        ${BOARD_INCLUDE_PATHS})
target_compile_definitions(test_schedule_affinity PRIVATE
        ${BOARD_DEFINES}
)
