cmake_minimum_required(VERSION 3.13)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

add_library(fr3_common INTERFACE)
target_sources(fr3_common INTERFACE
        test.c)
target_include_directories(fr3_common INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}
        ${BSL_PATHS}
        )
bsl_library_variant(bsl_fr3 ${CMAKE_CURRENT_LIST_DIR})
target_link_libraries(fr3_common INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap1
        ${BSL_LINK_LIBRARIES} bsl_fr3)

add_executable(test_fr3)
bsl_executable_modifiers(test_fr3)
target_link_libraries(test_fr3 fr3_common)
target_include_directories(test_fr3 PUBLIC
        ${BSL_INCLUDE_PATHS})
target_compile_definitions(test_fr3 PRIVATE
        ${BSL_DEFINES}
)
add_test(test_fr3 fr3)
