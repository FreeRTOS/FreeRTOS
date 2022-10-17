cmake_minimum_required(VERSION 3.13)

project(hello_world C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

add_library(hello_world_common INTERFACE)
target_sources(hello_world_common INTERFACE
        test.c)
target_include_directories(hello_world_common INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}
        ${BSL_PATH}
        )
target_link_libraries(hello_world_common INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap1
        ${BSL_LINK_LIBRARIES})

add_executable(hello_world)
bsl_executable_modifiers(hello_world)
target_link_libraries(hello_world hello_world_common)
target_include_directories(hello_world PUBLIC
        ${BSL_INCLUDE_PATHS})
add_test(hello_world_test hello_world)
