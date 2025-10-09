# Minimum CMake version
cmake_minimum_required(VERSION 3.20)

# Define the project name and language
project(STM32L072_Demo C)

# Specify ARM GCC toolchain
if(NOT CMAKE_TOOLCHAIN_FILE)
    message(FATAL_ERROR "Please specify a toolchain file (arm-gcc-toolchain.cmake) when configuring.")
endif()

# Set the output directory
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

# Include directories
include_directories(
    ${CMAKE_SOURCE_DIR}                                  # Current folder (for main.c, FreeRTOSConfig.h)
    ../FreeRTOS-Kernel/include
    ../FreeRTOS-Kernel/portable/GCC/ARM_CM0
)

# Source files
set(SOURCES
    main.c
    ../FreeRTOS-Kernel/list.c
    ../FreeRTOS-Kernel/queue.c
    ../FreeRTOS-Kernel/tasks.c
    ../FreeRTOS-Kernel/timers.c
    ../FreeRTOS-Kernel/event_groups.c
    ../FreeRTOS-Kernel/stream_buffer.c
    ../FreeRTOS-Kernel/portable/MemMang/heap_4.c
    ../FreeRTOS-Kernel/portable/GCC/ARM_CM0/port.c
)

# Add executable target
add_executable(${PROJECT_NAME}.elf ${SOURCES})

# Compiler flags
target_compile_options(${PROJECT_NAME}.elf PRIVATE
    -mcpu=cortex-m0plus
    -mthumb
    -O0
    -g3
    -Wall
    -Wextra
)

# Linker flags (adjust if needed for STM32L072)
target_link_options(${PROJECT_NAME}.elf PRIVATE
    -TSTM32L072.ld
)
