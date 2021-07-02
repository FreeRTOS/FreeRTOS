cmake_minimum_required(VERSION 3.13)

# Pull in SDK (must be before project)
include(pico_sdk_import.cmake)

# Pull in FreeRTOS
include(FreeRTOS_Kernel_import.cmake)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

pico_sdk_init()

add_executable(main_full
        main.c
        main_full.c
        IntQueueTimer.c
        RegTest.s
        ../../Common/Minimal/blocktim.c
        ../../Common/Minimal/countsem.c
        ../../Common/Minimal/dynamic.c
        ../../Common/Minimal/recmutex.c
        ../../Common/Minimal/QueueOverwrite.c
        ../../Common/Minimal/EventGroupsDemo.c
        ../../Common/Minimal/IntSemTest.c
        ../../Common/Minimal/IntQueue.c
        ../../Common/Minimal/TaskNotify.c
        ../../Common/Minimal/TimerDemo.c
        ../../Common/Minimal/GenQTest.c
        ../../Common/Minimal/death.c
        ../../Common/Minimal/semtest.c
        ../../Common/Minimal/BlockQ.c
        ../../Common/Minimal/flop.c
        )

target_compile_definitions(main_full PRIVATE
        mainCREATE_SIMPLE_BLINKY_DEMO_ONLY=0
        )

target_include_directories(main_full PRIVATE
        ${CMAKE_CURRENT_LIST_DIR}
        ${CMAKE_CURRENT_LIST_DIR}/../../Common/include)

target_compile_definitions(main_full PRIVATE
        PICO_STDIO_STACK_BUFFER_SIZE=64 # use a small printf on stack buffer
)
target_link_libraries(main_full pico_stdlib FreeRTOS-Kernel FreeRTOS-Kernel-Heap4)
pico_add_extra_outputs(main_full)

add_executable(main_blinky
        main.c
        main_blinky.c
        )

target_compile_definitions(main_blinky PRIVATE
        mainCREATE_SIMPLE_BLINKY_DEMO_ONLY=1
        )

target_include_directories(main_blinky PRIVATE
        ${CMAKE_CURRENT_LIST_DIR}
        ${CMAKE_CURRENT_LIST_DIR}/../../Common/include)

target_link_libraries(main_blinky pico_stdlib FreeRTOS-Kernel FreeRTOS-Kernel-Heap1)
pico_add_extra_outputs(main_blinky)