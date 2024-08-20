cmake_minimum_required(VERSION 3.13)

set(TEST_INCLUDE_PATHS ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/interrupt_wait_critical)
set(TEST_SOURCE_DIR ${CMAKE_CURRENT_LIST_DIR}/../../../../../tests/smp/interrupt_wait_critical)

add_library(interrupt_wait_critical INTERFACE)
target_sources(interrupt_wait_critical INTERFACE
        ${BOARD_LIBRARY_DIR}/main.c
        ${CMAKE_CURRENT_LIST_DIR}/interrupt_wait_critical_test_runner.c
        ${TEST_SOURCE_DIR}/interrupt_wait_critical.c)

target_include_directories(interrupt_wait_critical INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}/../../..
        ${TEST_INCLUDE_PATHS}
        )

target_link_libraries(interrupt_wait_critical INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap4
        ${BOARD_LINK_LIBRARIES})

add_executable(test_interrupt_wait_critical)
enable_board_functions(test_interrupt_wait_critical)
target_link_libraries(test_interrupt_wait_critical interrupt_wait_critical)
target_include_directories(test_interrupt_wait_critical PUBLIC
        ${BOARD_INCLUDE_PATHS})
target_compile_definitions(test_interrupt_wait_critical PRIVATE
        ${BOARD_DEFINES}
)
