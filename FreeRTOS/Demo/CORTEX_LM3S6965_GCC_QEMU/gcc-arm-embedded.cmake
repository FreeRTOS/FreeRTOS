set(CMAKE_SYSTEM_NAME      Generic)
set(CMAKE_SYSTEM_PROCESSOR arm)

set(CMAKE_TOOLCHAIN_PREFIX arm-none-eabi-)

set(CMAKE_C_COMPILER   ${CMAKE_TOOLCHAIN_PREFIX}gcc)
set(CMAKE_ASM_COMPILER ${CMAKE_C_COMPILER})
set(CMAKE_CXX_COMPILER ${CMAKE_TOOLCHAIN_PREFIX}g++)
set(CMAKE_LINKER       ${CMAKE_TOOLCHAIN_PREFIX}gcc)
set(CMAKE_OBJCOPY      ${CMAKE_TOOLCHAIN_PREFIX}objcopy)
set(CMAKE_SIZE         ${CMAKE_TOOLCHAIN_PREFIX}size)

set(CMAKE_EXECUTABLE_SUFFIX_ASM ".elf")
set(CMAKE_EXECUTABLE_SUFFIX_C   ".elf")
set(CMAKE_EXECUTABLE_SUFFIX_CXX ".elf")

# Adjust the default behavior of the FIND_XXX() commands:
# - Search programs in the host environment
set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
# - Search headers and libraries in the target environment
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)

# Don't try to execute linked programs
set(CMAKE_TRY_COMPILE_TARGET_TYPE STATIC_LIBRARY)

set(CMAKE_C_FLAGS_INIT "-mcpu=cortex-m3 -mthumb")
set(CMAKE_C_FLAGS_INIT "${CMAKE_C_FLAGS_INIT} --specs=nano.specs")

# Always build debug information (stripped out for executable)
# Add `-g3` to put macro values into debug information
if(CMAKE_BUILD_TYPE MATCHES Debug)
    set(CMAKE_C_FLAGS_INIT "${CMAKE_C_FLAGS_INIT} -O0 -g3")
endif()
if(CMAKE_BUILD_TYPE MATCHES Release)
    set(CMAKE_C_FLAGS_INIT "${CMAKE_C_FLAGS_INIT} -O3 -g3")
endif()
if(CMAKE_BUILD_TYPE MATCHES MinSizeRel)
    set(CMAKE_C_FLAGS_INIT "${CMAKE_C_FLAGS_INIT} -Os -g3")
endif()

set(CMAKE_ASM_FLAGS_INIT "${CMAKE_C_FLAGS_INIT} -x assembler-with-cpp")
set(CMAKE_CXX_FLAGS_INIT "${CMAKE_C_FLAGS_INIT} -fno-rtti -fno-exceptions")

set(CMAKE_ASM_LINK_FLAGS "-T ${CMAKE_CURRENT_LIST_DIR}/standalone.ld -nostartfiles")
set(CMAKE_ASM_LINK_FLAGS "${CMAKE_ASM_LINK_FLAGS} -Wl,-Map=${CMAKE_PROJECT_NAME}.map")
set(CMAKE_ASM_LINK_FLAGS "${CMAKE_ASM_LINK_FLAGS} -Wl,--print-memory-usage")

set(CMAKE_C_LINK_FLAGS "${CMAKE_ASM_LINK_FLAGS} -Wl,--start-group -lc -lm -Wl,--end-group")
set(CMAKE_C_LINK_FLAGS "${CMAKE_C_LINK_FLAGS} -ffunction-sections -fdata-sections -Wl,--gc-sections")

set(CMAKE_CXX_LINK_FLAGS "${CMAKE_C_LINK_FLAGS} -Wl,--start-group -lstdc++ -lsupc++ -Wl,--end-group")
