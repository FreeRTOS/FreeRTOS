cmake_minimum_required(VERSION 3.13)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

add_library(template_common INTERFACE)
target_sources(template_common INTERFACE
        test.c)
target_include_directories(template_common INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}
        ${BSL_PATH}
        )
target_link_libraries(template_common INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap1
        ${BSL_LINK_LIBRARIES})

add_executable(template_on_core_zero)
target_link_libraries(template_on_core_zero template_common)
target_include_directories(template_on_core_zero PUBLIC
        ${BSL_INCLUDE_PATHS})
add_test(template_on_core_zero_test one_core_zero)

add_executable(template_on_core_one)
target_link_libraries(template_on_core_one template_common)
target_include_directories(template_on_core_one PUBLIC
        ${BSL_INCLUDE_PATHS})
target_compile_definitions(template_on_core_one PRIVATE
        ${BSL_ON_CORE_ONE_DEFINES}
)
add_test(template_on_core_one_test one_core_one)

add_executable(template_on_core_zero_pico)
# pico_enable_stdio_semihosting(template_on_core_zero_pico ENABLED)
target_link_libraries(template_on_core_zero_pico template_common)
target_include_directories(template_on_core_zero_pico PUBLIC
        ${BSL_INCLUDE_PATHS})
target_compile_definitions(template_on_core_zero_pico PRIVATE
        ${BSL_DEFINES})
add_test(template_on_core_zero_pico_test one_core_zero_pico)

add_executable(template_on_core_one_pico)
# pico_enable_stdio_semihosting(template_on_core_one_pico ENABLED)
target_link_libraries(template_on_core_one_pico template_common)
target_include_directories(template_on_core_one_pico PUBLIC
        ${BSL_INCLUDE_PATHS})
target_compile_definitions(template_on_core_one_pico PRIVATE
        ${BSL_DEFINES}
        ${BSL_ON_CORE_ONE_DEFINES}
)
add_test(template_on_core_one_pico_test one_core_one_pico)

