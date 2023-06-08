cmake_minimum_required(VERSION 3.15)

project( posix_demo )

set( CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -D_WINDOWS_")

if( DEFINED TRACE_ON_ENTER AND TRACE_ON_ENTER )
    set( CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -DTRACE_ON_ENTER=1" )
else()
    set( CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -DTRACE_ON_ENTER=0" )
endif()

if( NOT DEFINED COVERAGE_TEST )
    set( COVERAGE_TEST 0 )
endif()

if( DEFINED PROFILE AND PROFILE )
    set( CMAKE_BUILD_TYPE "release" )
else()
    set( CMAKE_BUILD_TYPE "debug" )
endif()

if( DEFINED SANITIZE_ADDRESS AND SANITIZE_ADDRESS )
    set( CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fsanitize=address -fsanitize=alignment" )
endif()

if( DEFINED SANITIZE_LEAK AND SANITIZE_LEAK )
    set( CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fsanitize=leak" )
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

target_compile_definitions( freertos_config
    INTERFACE
        $<IF:${COVERAGE_TEST},projCOVERAGE_TEST=1,projCOVERAGE_TEST=0>
)

# Select the heap port
set( FREERTOS_HEAP "4" CACHE STRING "" FORCE)

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

target_compile_definitions( posix_demo
    PRIVATE
        mainCREATE_SIMPLE_BLINKY_DEMO_ONLY=0
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
