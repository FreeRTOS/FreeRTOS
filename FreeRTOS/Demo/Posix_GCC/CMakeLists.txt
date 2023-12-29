cmake_minimum_required(VERSION 3.15)

project( posix_demo )

add_compile_options( -D_WINDOWS_ )

if( TRACE_ON_ENTER )
    add_compile_options( -DTRACE_ON_ENTER=1 )
else()
    add_compile_options( -DTRACE_ON_ENTER=0 )
endif()

if( COVERAGE_TEST )
    set( COVERAGE_TEST 1 )
    add_compile_options( -DprojCOVERAGE_TEST=1 )
else()
    set( COVERAGE_TEST 0 )
    add_compile_options( -DprojCOVERAGE_TEST=0 )
endif()

if( PROFILE )
    set( CMAKE_BUILD_TYPE "release" )
else()
    set( CMAKE_BUILD_TYPE "debug" )
endif()

if( SANITIZE_ADDRESS )
    add_compile_options( -fsanitize=address -fsanitize=alignment )
endif()

if( SANITIZE_LEAK )
    add_compile_options( -fsanitize=leak )
endif()

set( FREERTOS_KERNEL_PATH "../../Source" )
set( FREERTOS_PLUS_TRACE_PATH "../../../FreeRTOS-Plus/Source/FreeRTOS-Plus-Trace" )

# Add the freertos_config for FreeRTOS-Kernel
add_library( freertos_config INTERFACE )

target_include_directories( freertos_config
    INTERFACE
        ./
        ./Trace_Recorder_Configuration
        ${FREERTOS_PLUS_TRACE_PATH}/Include
)

# Select the heap port
set( FREERTOS_HEAP "3" CACHE STRING "" FORCE)

# Select the native compile PORT
set( FREERTOS_PORT "GCC_POSIX" CACHE STRING "" FORCE)

# Adding the FreeRTOS-Kernel subdirectory
add_subdirectory( ${FREERTOS_KERNEL_PATH} ${CMAKE_CURRENT_BINARY_DIR}/FreeRTOS-Kernel )

target_compile_options( freertos_kernel
    PRIVATE
        # Trace macro cast pointer to int to store memory management event
        $<IF:${COVERAGE_TEST},,-Wno-pointer-to-int-cast>
)

file( GLOB FREERTOS_PLUS_TRACE_SOURCES ${FREERTOS_PLUS_TRACE_PATH}/*.c )

add_executable( posix_demo
                code_coverage_additions.c
                console.c
                main.c
                main_blinky.c
                main_full.c
                run-time-stats-utils.c
                $<$<NOT:${COVERAGE_TEST}>:${FREERTOS_PLUS_TRACE_SOURCES}>
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/AbortDelay.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/BlockQ.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/blocktim.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/countsem.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/death.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/dynamic.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/EventGroupsDemo.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/flop.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/GenQTest.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/integer.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/IntSemTest.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/MessageBufferAMP.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/MessageBufferDemo.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/PollQ.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/QPeek.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/QueueOverwrite.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/QueueSet.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/QueueSetPolling.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/recmutex.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/semtest.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/StaticAllocation.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/StreamBufferDemo.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/StreamBufferInterrupt.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/TaskNotify.c
                ${CMAKE_CURRENT_LIST_DIR}/../Common/Minimal/TimerDemo.c
              )

target_include_directories( posix_demo
    PRIVATE
        ${CMAKE_CURRENT_LIST_DIR}
        ${CMAKE_CURRENT_LIST_DIR}/../Common/include
        ${FREERTOS_PLUS_TRACE_PATH}/Include
        ${FREERTOS_PLUS_TRACE_PATH}/streamports/File/include
        ${FREERTOS_PLUS_TRACE_PATH}/streamports/File/config
)

target_compile_definitions( posix_demo
    PRIVATE
        $<IF:$<STREQUAL:${USER_DEMO},BLINKY_DEMO>,USER_DEMO=0,>
        $<IF:$<STREQUAL:${USER_DEMO},FULL_DEMO>,USER_DEMO=1,>
)

target_link_libraries( posix_demo freertos_kernel freertos_config )
