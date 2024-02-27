cmake_minimum_required(VERSION 3.13)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

set(TEST_INCLUDE_PATHS ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/suspend_scheduler)
set(TEST_SOURCE_DIR ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/suspend_scheduler)

add_library(suspend_scheduler INTERFACE)
target_sources(suspend_scheduler INTERFACE
        ${BOARD_LIBRARY_DIR}/main.c
        ${CMAKE_CURRENT_LIST_DIR}/suspend_scheduler_test_runner.c
        ${TEST_SOURCE_DIR}/suspend_scheduler.c)

target_include_directories(suspend_scheduler INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}/../../..
        ${TEST_INCLUDE_PATHS}
        )

target_link_libraries(suspend_scheduler INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap4
        ${BOARD_LINK_LIBRARIES})

add_executable(test_suspend_scheduler)
enable_board_functions(test_suspend_scheduler)
target_link_libraries(test_suspend_scheduler suspend_scheduler)
target_include_directories(test_suspend_scheduler PUBLIC
        ${BOARD_INCLUDE_PATHS})
target_compile_definitions(test_suspend_scheduler PRIVATE
        ${BOARD_DEFINES}
)
