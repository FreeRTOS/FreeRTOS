cmake_minimum_required(VERSION 3.13)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

set(TEST_INCLUDE_PATHS ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/disable_preemption)
set(TEST_SOURCE_DIR ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/disable_preemption)

add_library(disable_preemption INTERFACE)
target_sources(disable_preemption INTERFACE
        ${BOARD_LIBRARY_DIR}/main.c
        ${CMAKE_CURRENT_LIST_DIR}/disable_preemption_test_runner.c
        ${TEST_SOURCE_DIR}/disable_preemption.c)

target_include_directories(disable_preemption INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}/../../..
        ${TEST_INCLUDE_PATHS}
        )

target_link_libraries(disable_preemption INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap4
        ${BOARD_LINK_LIBRARIES})

add_executable(test_disable_preemption)
enable_board_functions(test_disable_preemption)
target_link_libraries(test_disable_preemption disable_preemption)
target_include_directories(test_disable_preemption PUBLIC
        ${BOARD_INCLUDE_PATHS})
target_compile_definitions(test_disable_preemption PRIVATE
        ${BOARD_DEFINES}
)
