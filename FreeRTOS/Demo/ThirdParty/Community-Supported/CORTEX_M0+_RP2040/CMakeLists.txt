# Note that this file can be used as a top level CMakeLists.txt to build all the Demos (it includes
# them all, but they are usable in their own right, which is why no common work is done here)

cmake_minimum_required(VERSION 3.13)

# Pull in SDK (must be before project)
include(pico_sdk_import.cmake)

PROJECT(examples)

add_subdirectory(OnEitherCore)
add_subdirectory(Standard)
add_subdirectory(UsingCMSIS)