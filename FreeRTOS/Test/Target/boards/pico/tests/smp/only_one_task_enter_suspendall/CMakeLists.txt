cmake_minimum_required(VERSION 3.13)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

set(TEST_INCLUDE_PATHS ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/only_one_task_enter_suspendall)
set(TEST_SOURCE_DIR ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/only_one_task_enter_suspendall)

add_library(only_one_task_enter_suspendall INTERFACE)
target_sources(only_one_task_enter_suspendall INTERFACE
        ${BOARD_LIBRARY_DIR}/main.c
        ${CMAKE_CURRENT_LIST_DIR}/only_one_task_enter_suspendall_test_runner.c
        ${TEST_SOURCE_DIR}/only_one_task_enter_suspendall.c)

target_include_directories(only_one_task_enter_suspendall INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}/../../..
        ${TEST_INCLUDE_PATHS}
        )

target_link_libraries(only_one_task_enter_suspendall INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap4
        ${BOARD_LINK_LIBRARIES})

add_executable(test_only_one_task_enter_suspendall)
enable_board_functions(test_only_one_task_enter_suspendall)
target_link_libraries(test_only_one_task_enter_suspendall only_one_task_enter_suspendall)
target_include_directories(test_only_one_task_enter_suspendall PUBLIC
        ${BOARD_INCLUDE_PATHS})
target_compile_definitions(test_only_one_task_enter_suspendall PRIVATE
        ${BOARD_DEFINES}
)
