cmake_minimum_required(VERSION 3.13)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

set(TEST_INCLUDE_PATHS ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/multiple_tasks_running)
set(TEST_SOURCE_DIR ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/multiple_tasks_running)
set(BOARD_INCLUDE_DIR ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/multiple_tasks_running
        ${CMAKE_CURRENT_LIST_DIR}/../../..)

add_library(multiple_tasks_running_common INTERFACE)
target_sources(multiple_tasks_running_common INTERFACE
        ${TEST_SOURCE_DIR}/multiple_tasks_running.c)

board_library_variant(board_multiple_tasks_running ${BOARD_INCLUDE_DIR})

target_include_directories(multiple_tasks_running_common INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}/../../..
        ${BSL_PATHS}
        ${TEST_INCLUDE_PATHS}
        )

target_link_libraries(multiple_tasks_running_common INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap4
        ${BOARD_LINK_LIBRARIES} board_multiple_tasks_running)

add_executable(test_multiple_tasks_running)
board_executable_modifiers(test_multiple_tasks_running)
target_link_libraries(test_multiple_tasks_running multiple_tasks_running_common)
target_include_directories(test_multiple_tasks_running PUBLIC
        ${BOARD_INCLUDE_PATHS})
target_compile_definitions(test_multiple_tasks_running PRIVATE
        ${BOARD_DEFINES}
)
add_test(test_multiple_tasks_running multiple_tasks_running)
