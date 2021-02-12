cmake_minimum_required( VERSION 3.1)
project( Integration_Timers )

set( FREERTOS_DIR ../../../../FreeRTOS )
set( FREERTOS_PLUS_DIR ../../../../FreeRTOS-Plus )
set( PORT_DIR ${FREERTOS_DIR}/Source/portable/ThirdParty/GCC/Posix )
set( TRACE_DIR ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace )
set( LIBPORT_DIR ../portable )
get_filename_component( UNITY_DIR ${FREERTOS_DIR}/Test/CMock/CMock/vendor/unity  ABSOLUTE )

# Test setup
add_executable( Timers 
                    harness.c
                    itest.c
)
target_include_directories( Timers 
                            PUBLIC
                                ${FREERTOS_DIR}/Source/include
                                ${FREERTOS_DIR}/Source
                                ${PORT_DIR}
                                ${TRACE_DIR}/Include
)

# Unity Setup
target_include_directories( Timers
                            PUBLIC
                                ${UNITY_DIR}/src
                                ${UNITY_DIR}/extras/fixture/src
                                ${UNITY_DIR}/extras/memory/src
)

target_link_libraries( Timers 
                       PUBLIC
                           unity
)

target_sources( Timers 
                PUBLIC
                ${UNITY_DIR}/extras/fixture/src/unity_fixture.c

)

# Port setup
target_include_directories( Timers
                            PUBLIC
                                ${LIBPORT_DIR}/config
)
target_link_libraries( Timers 
                       PUBLIC 
                           port
)