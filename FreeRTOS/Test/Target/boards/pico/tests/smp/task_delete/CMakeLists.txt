cmake_minimum_required(VERSION 3.13)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

set(TEST_INCLUDE_PATHS ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/task_delete)
set(TEST_SOURCE_DIR ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/task_delete)

add_library(task_delete INTERFACE)
target_sources(task_delete INTERFACE
        ${BOARD_LIBRARY_DIR}/main.c
        ${CMAKE_CURRENT_LIST_DIR}/task_delete_test_runner.c
        ${TEST_SOURCE_DIR}/task_delete.c)

target_include_directories(task_delete INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}/../../..
        ${TEST_INCLUDE_PATHS}
        )

target_link_libraries(task_delete INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap4
        ${BOARD_LINK_LIBRARIES})

add_executable(test_task_delete)
enable_board_functions(test_task_delete)
target_link_libraries(test_task_delete task_delete)
target_include_directories(test_task_delete PUBLIC
        ${BOARD_INCLUDE_PATHS})
target_compile_definitions(test_task_delete PRIVATE
        ${BOARD_DEFINES}
)
