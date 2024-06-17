cmake_minimum_required(VERSION 3.13)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

set(TEST_INCLUDE_PATHS ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/schedule_highest_priority)
set(TEST_SOURCE_DIR ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/schedule_highest_priority)

add_library(schedule_highest_priority INTERFACE)
target_sources(schedule_highest_priority INTERFACE
        ${BOARD_LIBRARY_DIR}/main.c
        ${CMAKE_CURRENT_LIST_DIR}/schedule_highest_priority_test_runner.c
        ${TEST_SOURCE_DIR}/schedule_highest_priority.c)

target_include_directories(schedule_highest_priority INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}/../../..
        ${TEST_INCLUDE_PATHS}
        )

target_link_libraries(schedule_highest_priority INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap4
        ${BOARD_LINK_LIBRARIES})

add_executable(test_schedule_highest_priority)
enable_board_functions(test_schedule_highest_priority)
target_link_libraries(test_schedule_highest_priority schedule_highest_priority)
target_include_directories(test_schedule_highest_priority PUBLIC
        ${BOARD_INCLUDE_PATHS})
target_compile_definitions(test_schedule_highest_priority PRIVATE
        ${BOARD_DEFINES}
)
