cmake_minimum_required(VERSION 3.13)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)
set(UNITY_DIR ../../CMock/CMock/vendor/unity)

include(CTest)

add_library(unity STATIC
                "${UNITY_DIR}/src/unity.c")

target_include_directories(unity PUBLIC
        "${UNITY_DIR}/src/")


add_library(template_common INTERFACE)
target_sources(template_common INTERFACE
        test.c)
target_include_directories(template_common INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}
        )
target_link_libraries(template_common INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap1
        pico_stdlib
        pico_multicore)

add_executable(template_on_core_zero)
target_link_libraries(template_on_core_zero template_common unity)
target_include_directories(template_on_core_zero PUBLIC
        "${UNITY_DIR}/src/")
pico_add_extra_outputs(template_on_core_zero)
pico_enable_stdio_usb(template_on_core_zero 1)
add_test(template_on_core_zero_test one_core_zero)

add_executable(template_on_core_one)
target_link_libraries(template_on_core_one template_common unity)
target_include_directories(template_on_core_one PUBLIC
        "${UNITY_DIR}/src/")
target_compile_definitions(template_on_core_one PRIVATE
        mainRUN_FREE_RTOS_template_on_core=1
)
pico_add_extra_outputs(template_on_core_one)
#pico_enable_stdio_usb(template_on_core_one 1)
add_test(template_on_core_one_test one_core_one)

add_executable(template_on_core_zero_pico)
# pico_enable_stdio_semihosting(template_on_core_zero_pico ENABLED)
target_link_libraries(template_on_core_zero_pico template_common unity)
target_include_directories(template_on_core_zero_pico PUBLIC
        "${UNITY_DIR}/src/")
target_compile_definitions(template_on_core_zero_pico PRIVATE
        PICO_STACK_SIZE=0x1000
        TARGET_RASPBERRY_PICO=1
)
pico_add_extra_outputs(template_on_core_zero_pico)
pico_enable_stdio_usb(template_on_core_zero_pico 1)
add_test(template_on_core_zero_pico_test one_core_zero_pico)

add_executable(template_on_core_one_pico)
# pico_enable_stdio_semihosting(template_on_core_one_pico ENABLED)
target_link_libraries(template_on_core_one_pico template_common unity)
target_include_directories(template_on_core_one_pico PUBLIC
        "${UNITY_DIR}/src/")
target_compile_definitions(template_on_core_one_pico PRIVATE
        mainRUN_FREE_RTOS_template_on_core=1
        PICO_STACK_SIZE=0x1000
        TARGET_RASPBERRY_PICO=1
)
pico_add_extra_outputs(template_on_core_one_pico)
pico_enable_stdio_usb(template_on_core_one_pico 1)
add_test(template_on_core_one_pico_test one_core_one_pico)

