cmake_minimum_required(VERSION 3.13)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

add_library(fr4_common INTERFACE)
target_sources(fr4_common INTERFACE
        test.c)
target_include_directories(fr4_common INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}
        ${BSL_PATHS}
        )
bsl_library_variant(bsl_fr4 ${CMAKE_CURRENT_LIST_DIR} "-DUSE_BSL_DEFAULT_HOOKS")
target_link_libraries(fr4_common INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap4
        ${BSL_LINK_LIBRARIES} bsl_fr4)

add_executable(test_fr4)
bsl_executable_modifiers(test_fr4)
target_link_libraries(test_fr4 fr4_common)
target_include_directories(test_fr4 PUBLIC
        ${BSL_INCLUDE_PATHS})
target_compile_definitions(test_fr4 PRIVATE
        ${BSL_DEFINES}
)
add_test(test_fr4 fr4)
