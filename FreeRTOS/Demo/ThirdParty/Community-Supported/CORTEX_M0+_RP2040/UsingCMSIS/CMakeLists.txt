cmake_minimum_required(VERSION 3.13)

# Pull in SDK (must be before project)
include(pico_sdk_import.cmake)
# Pull in FreeRTOS
include(FreeRTOS_Kernel_import.cmake)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

pico_sdk_init()

add_executable(using_cmsis)
target_sources(using_cmsis PUBLIC
        main.c)
target_include_directories(using_cmsis PUBLIC
        ${CMAKE_CURRENT_LIST_DIR}
        )

target_link_libraries(using_cmsis PUBLIC
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap1
        pico_stdlib
        cmsis_core # CMSIS core headers via the SDK
)

pico_add_extra_outputs(using_cmsis)
