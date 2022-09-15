cmake_minimum_required(VERSION 3.13)

# Pull in SDK (must be before project)
include(../pico_sdk_import.cmake)
# Pull in FreeRTOS
include(FreeRTOS_Kernel_import.cmake)

project(example C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

pico_sdk_init()


add_library(template_common INTERFACE)
target_sources(template_common INTERFACE
        main.c)
target_include_directories(template_common INTERFACE
        ${CMAKE_CURRENT_LIST_DIR}
        )
target_link_libraries(template_common INTERFACE
        FreeRTOS-Kernel
        FreeRTOS-Kernel-Heap1
        pico_stdlib
        pico_multicore)

add_executable(on_core_zero)
pico_enable_stdio_semihosting(on_core_zero ENABLED)
target_link_libraries(on_core_zero template_common)
pico_add_extra_outputs(on_core_zero)
pico_enable_stdio_usb(on_core_zero 1)

add_executable(on_core_one)
pico_enable_stdio_semihosting(on_core_one ENABLED)
target_link_libraries(on_core_one template_common)
target_compile_definitions(on_core_one PRIVATE
        mainRUN_FREE_RTOS_ON_CORE=1
)
pico_add_extra_outputs(on_core_one)
#pico_enable_stdio_usb(on_core_one 1)

add_executable(on_core_zero_pico)
pico_enable_stdio_semihosting(on_core_zero_pico ENABLED)
target_link_libraries(on_core_zero_pico template_common)
target_compile_definitions(on_core_zero_pico PRIVATE
        PICO_STACK_SIZE=0x1000
        TARGET_RASPBERRY_PICO=1
)
pico_add_extra_outputs(on_core_zero_pico)
pico_enable_stdio_usb(on_core_zero_pico 1)

add_executable(on_core_one_pico)
pico_enable_stdio_semihosting(on_core_one_pico ENABLED)
target_link_libraries(on_core_one_pico template_common)
target_compile_definitions(on_core_one_pico PRIVATE
        mainRUN_FREE_RTOS_ON_CORE=1
        PICO_STACK_SIZE=0x1000
        TARGET_RASPBERRY_PICO=1
)
pico_add_extra_outputs(on_core_one_pico)
#pico_enable_stdio_usb(on_core_one_pico 1)

