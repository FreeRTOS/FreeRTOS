cmake_minimum_required(VERSION 3.13)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

add_library(fr8_common INTERFACE)
target_sources(fr8_common INTERFACE
        test.c)
target_include_directories(fr8_common INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}
        ${BSL_PATHS}
        )
bsl_library_variant(bsl_fr8 ${CMAKE_CURRENT_LIST_DIR} "-DUSE_BSL_DEFAULT_HOOKS")
target_link_libraries(fr8_common INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap1
        ${BSL_LINK_LIBRARIES} bsl_fr8)

add_executable(test_fr8)
bsl_executable_modifiers(test_fr8)
target_link_libraries(test_fr8 fr8_common)
target_include_directories(test_fr8 PUBLIC
        ${BSL_INCLUDE_PATHS})
target_compile_definitions(test_fr8 PRIVATE
        ${BSL_DEFINES}
)
add_test(test_fr8 fr8)
