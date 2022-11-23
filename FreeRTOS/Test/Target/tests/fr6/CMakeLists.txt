cmake_minimum_required(VERSION 3.13)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

add_library(fr6_common INTERFACE)
target_sources(fr6_common INTERFACE
        test.c)
target_include_directories(fr6_common INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}
        ${BSL_PATHS}
        )
bsl_library_variant(bsl_fr6 ${CMAKE_CURRENT_LIST_DIR})
target_link_libraries(fr6_common INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap1
        ${BSL_LINK_LIBRARIES} bsl_fr6)

add_executable(test_fr6)
bsl_executable_modifiers(test_fr6)
target_link_libraries(test_fr6 fr6_common)
target_include_directories(test_fr6 PUBLIC
        ${BSL_INCLUDE_PATHS})
target_compile_definitions(test_fr6 PRIVATE
        ${BSL_DEFINES}
)
add_test(test_fr6 fr6)
