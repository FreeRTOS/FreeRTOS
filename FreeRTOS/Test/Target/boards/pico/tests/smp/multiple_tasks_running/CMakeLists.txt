cmake_minimum_required(VERSION 3.13)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

set(TEST_INCLUDE_PATHS ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/multiple_tasks_running)
set(TEST_SOURCE_DIR ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/multiple_tasks_running)

add_library(multiple_tasks_running INTERFACE)
target_sources(multiple_tasks_running INTERFACE
        ${BOARD_LIBRARY_DIR}/main.c
        ${CMAKE_CURRENT_LIST_DIR}/multiple_tasks_running_test_runner.c
        ${TEST_SOURCE_DIR}/multiple_tasks_running.c)

target_include_directories(multiple_tasks_running INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}/../../..
        ${TEST_INCLUDE_PATHS}
        )

target_link_libraries(multiple_tasks_running INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap4
        ${BOARD_LINK_LIBRARIES})

add_executable(test_multiple_tasks_running)
enable_board_functions(test_multiple_tasks_running)
target_link_libraries(test_multiple_tasks_running multiple_tasks_running)
target_include_directories(test_multiple_tasks_running PUBLIC
        ${BOARD_INCLUDE_PATHS})
target_compile_definitions(test_multiple_tasks_running PRIVATE
        ${BOARD_DEFINES}
)
