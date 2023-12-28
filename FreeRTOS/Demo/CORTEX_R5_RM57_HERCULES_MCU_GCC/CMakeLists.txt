cmake_minimum_required(VERSION 3.9)

set(CMAKE_CROSSCOMPILING "TRUE" CACHE STRING "Set Cross Compiling to true" FORCE)

# Strip the default MacOSX flags that cause cross-compilations to fail.
set(CMAKE_OSX_DEPLOYMENT_TARGET "" CACHE STRING "Force unset of the deployment target for iOS" FORCE)
set(CMAKE_OSX_SYSROOT "" CACHE STRING "Force unset of the deployment target for iOS" FORCE)

# Set the compiler before declaring the project for the test build
set(CMAKE_C_COMPILER "arm-none-eabi-gcc")
set(CMAKE_ASM_COMPILER "arm-none-eabi-gcc")

# Set the system processor and name before declaring the project
# Needs to be set here otherwise it will fail the test compilation
set(CMAKE_SYSTEM_NAME "Generic" CACHE STRING "Target system is a generic ARM Processor")
set(CMAKE_SYSTEM_PROCESSOR "armv7-r" CACHE STRING "Target system is an ARM7r Processor")

# Set the ASM and C compilation flags
set(CMAKE_ASM_FLAGS "-mcpu=cortex-r5 -mfpu=vfpv3-d16 -Og -g -ggdb -Wall -MMD -MP")
set(CMAKE_ASM_FLAGS "${CMAKE_ASM_FLAGS} -specs=\"nosys.specs\" -specs=\"nano.specs\"")
set(CMAKE_C_FLAGS "${CMAKE_ASM_FLAGS} -marm -mfloat-abi=hard")

project(RM57_FreeRTOS C ASM)
cmake_minimum_required(VERSION 3.5)

set(EXECUTABLE_OUTPUT_PATH ${PROJECT_BINARY_DIR} CACHE STRING "")

# Increase the debug level of the CMAKE build
set(CMAKE_VERBOSE_MAKEFILE ON)

# Get the absolute path to the Demo Directory
set(DEMO_DIR_REL "${CMAKE_CURRENT_SOURCE_DIR}")
get_filename_component(DEMO_DIR ${DEMO_DIR_REL} ABSOLUTE)

# Get the absolute path to the Board Files
set(BOARD_FILES_DIR_REL "${DEMO_DIR}/BoardFiles")
get_filename_component(BOARD_FILES_DIR ${BOARD_FILES_DIR_REL} ABSOLUTE)

# Get the absolute path to the FreeRTOS-Kernel Directory
set(FREERTOS_KERNEL_DIR_REL "${DEMO_DIR}/../../../FreeRTOS/Source")
get_filename_component(FREERTOS_KERNEL_DIR ${FREERTOS_KERNEL_DIR_REL} ABSOLUTE)

# Get the absolute path to the Port Directory
set(PORT_DIR_REL "${FREERTOS_KERNEL_DIR}/portable/GCC/ARM_CRx_MPU")
get_filename_component(PORT_DIR ${PORT_DIR_REL} ABSOLUTE)

include_directories(
    ${DEMO_DIR}
    ${DEMO_DIR}/include
    ${BOARD_FILES_DIR}/include
    ${FREERTOS_KERNEL_DIR}/include
    ${PORT_DIR}
)

# Source files used for the FreeRTOS Demos
FILE(GLOB FREERTOS_DEMO_SOURCES
    ${DEMO_DIR}/source/mpu_demo.c
    ${DEMO_DIR}/source/blinky_demo.c
    ${DEMO_DIR}/source/reg_test.c
    ${DEMO_DIR}/source/reg_test_GCC.S
)

# Source files used for the Board Support Package
FILE(GLOB TI_BOARD_SOURCES
    ${BOARD_FILES_DIR}/source/*.c
    ${BOARD_FILES_DIR}/source/*.S
)

# FreeRTOS Kernel Files
FILE(GLOB FREERTOS_KERNEL_SOURCES
    ${FREERTOS_KERNEL_DIR}/croutine.c
    ${FREERTOS_KERNEL_DIR}/event_groups.c
    ${FREERTOS_KERNEL_DIR}/list.c
    ${FREERTOS_KERNEL_DIR}/queue.c
    ${FREERTOS_KERNEL_DIR}/stream_buffer.c
    ${FREERTOS_KERNEL_DIR}/tasks.c
    ${FREERTOS_KERNEL_DIR}/timers.c
    ${FREERTOS_KERNEL_DIR}/portable/Common/mpu_wrappers_v2.c
)

FILE(GLOB FREERTOS_PORT_SOURCES
    ${PORT_DIR}/mpu_wrappers_v2_asm.S
    ${PORT_DIR}/portASM.S
    ${PORT_DIR}/port.c
)

# On Mac the C_LINK flags by default adds "-Wl,-search_paths_first -Wl,-headerpad_max_install_names" which
# Causes the executable that gets built to strip the symbols, so force set it to empty here.
set(CMAKE_C_LINK_FLAGS "")
set(CMAKE_EXE_LINKER_FLAGS "-Wl,-Map,\"RTOSDemo.map\" -Wl,-T\"${BOARD_FILES_DIR}/source/sys_link.ld\"")

# Debug
message("Project: ${PROJECT_NAME}")
message("Demo Sources: ${FREERTOS_DEMO_SOURCES}")
message("FreeRTOS Sources: ${FREERTOS_KERNEL_SOURCES}")
message("Port Sources: ${FREERTOS_PORT_SOURCES}")

# Create Blinky Demo executable
add_executable(RM57_FreeRTOS_Blinky_Demo.out
    ${FREERTOS_DEMO_SOURCES}
    ${TI_BOARD_SOURCES}
    ${FREERTOS_KERNEL_SOURCES}
    ${FREERTOS_PORT_SOURCES}
    ./source/main.c
)

# Create MPU Demo executable
add_executable(RM57_FreeRTOS_MPU_Demo.out
    ${FREERTOS_DEMO_SOURCES}
    ${TI_BOARD_SOURCES}
    ${FREERTOS_KERNEL_SOURCES}
    ${FREERTOS_PORT_SOURCES}
    ./source/main.c
)

# These options are set in the FreeRTOSConfig.h file
set_target_properties(RM57_FreeRTOS_Blinky_Demo.out PROPERTIES COMPILE_DEFINITIONS "mainDEMO_TYPE=1")
set_target_properties(RM57_FreeRTOS_MPU_Demo.out PROPERTIES COMPILE_DEFINITIONS "mainDEMO_TYPE=2")
