# Tell CMake this is a cross-compilation project
set(CMAKE_SYSTEM_NAME Generic)
set(CMAKE_SYSTEM_PROCESSOR arm)

# Specify compilers
set(CMAKE_C_COMPILER "C:/Users/prana/Downloads/arm-gnu-toolchain-14.3.rel1-mingw-w64-i686-arm-none-eabi/bin/arm-none-eabi-gcc.exe")
set(CMAKE_CXX_COMPILER "C:/Users/prana/Downloads/arm-gnu-toolchain-14.3.rel1-mingw-w64-i686-arm-none-eabi/bin/arm-none-eabi-g++.exe")
set(CMAKE_ASM_COMPILER "C:/Users/prana/Downloads/arm-gnu-toolchain-14.3.rel1-mingw-w64-i686-arm-none-eabi/bin/arm-none-eabi-gcc.exe")

# Include directories if needed
# set(CMAKE_FIND_ROOT_PATH "C:/Users/prana/STM32CubeL0/Drivers")

# Prevent CMake from trying to run test executables (important for cross-compiling)
set(CMAKE_TRY_COMPILE_TARGET_TYPE STATIC_LIBRARY)
