cmake_minimum_required( VERSION 3.0 )
project( Integration_Tests )

set( FREERTOS_DIR ../../../FreeRTOS )
set( UNITY_DIR ${FREERTOS_DIR}/Test/CMock/CMock/vendor/unity )


# Port setup
add_subdirectory( portable )

# Unity Setup
add_subdirectory( ${UNITY_DIR} ${CMAKE_CURRENT_BINARY_DIR}/unity )

# Modules
add_subdirectory( timers )