cmake_minimum_required ( VERSION 3.13.0 )
project ( "FreeRTOS Unit Tests"
          VERSION 1.0.0
          LANGUAGES C )

# Allow the project to be organized into folders.
set_property( GLOBAL PROPERTY USE_FOLDERS ON )

# Use C90.
set( CMAKE_C_STANDARD 90 )
set( CMAKE_C_STANDARD_REQUIRED ON )

# Do not allow in-source build.
if( ${PROJECT_SOURCE_DIR} STREQUAL ${PROJECT_BINARY_DIR} )
    message( FATAL_ERROR "In-source build is not allowed. Please build in a separate directory, such as ${PROJECT_SOURCE_DIR}/build." )
endif()

# Set global path variables.
get_filename_component(__MODULE_ROOT_DIR "${CMAKE_CURRENT_LIST_DIR}/../../.." ABSOLUTE)
set(MODULE_ROOT_DIR ${__MODULE_ROOT_DIR} CACHE INTERNAL "FreeRTOS root.")

# Configure options to always show in CMake GUI.
option( BUILD_CLONE_SUBMODULES
        "Set this to ON to automatically clone any required Git submodules. When OFF, submodules must be manually cloned."
        ON )

# Set output directories.
set( CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin )
set( CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )
set( CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )

# Define a CMock resource path.
set( CMOCK_DIR ${MODULE_ROOT_DIR}/FreeRTOS/Test/CMock/CMock CACHE INTERNAL "CMock library source directory." )

# Include CMock build configuration.
include( cmock_build.cmake )

# Check if the CMock source directory exists, and if not present, clone the submodule
# if BUILD_CLONE_SUBMODULES configuration is enabled.
if( NOT EXISTS ${CMOCK_DIR}/src )
    # Attempt to clone CMock.
    if( ${BUILD_CLONE_SUBMODULES} )
        clone_cmock()
    else()
        message( FATAL_ERROR "The required submodule CMock does not exist. Either clone it manually, or set BUILD_CLONE_SUBMODULES to 1 to automatically clone it during build." )
    endif()
endif()

# Add unit test and coverage configuration.

# Use CTest utility for managing test runs. This has to be added BEFORE
# defining test targets with add_test()
enable_testing()

# Add build targets for CMock and Unit, required for unit testing.
add_cmock_targets()

# Add function to enable CMock based tests and coverage.
include( ${MODULE_ROOT_DIR}/tools/cmock/create_test.cmake )

# Include build configuration for unit tests.
include( queue/queue.cmake )

# List of unit tests
set( unit_test_list 
     queue_utest
)

# Add a target for running coverage on tests.
add_custom_target( coverage
    COMMAND ${CMAKE_COMMAND} -P ${MODULE_ROOT_DIR}/tools/cmock/coverage.cmake
    DEPENDS cmock unity ${unit_test_list}
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
)
