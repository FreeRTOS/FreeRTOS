cmake_minimum_required( VERSION 3.1 )
project( libport VERSION 1.0.0 DESCRIPTION "Architecture port library" )

set( FREERTOS_DIR ../../../../FreeRTOS )
set( FREERTOS_PLUS_DIR ../../../../FreeRTOS-Plus )
set( PORT_DIR ${FREERTOS_DIR}/Source/portable/ThirdParty/GCC/Posix )
set( TRACE_DIR ${FREERTOS_PLUS_DIR}/Source/FreeRTOS-Plus-Trace )

add_library( port 
             STATIC 
                ${PORT_DIR}/port.c
                ${PORT_DIR}/utils/wait_for_event.c

                Posix_GCC/code_coverage_additions.c
                Posix_GCC/console.c
                Posix_GCC/run-time-stats-utils.c

                ${FREERTOS_DIR}/Source/portable/MemMang/heap_3.c

                ${TRACE_DIR}/trcKernelPort.c
                ${TRACE_DIR}/trcSnapshotRecorder.c
                ${TRACE_DIR}/trcStreamingRecorder.c
                ${TRACE_DIR}/streamports/File/trcStreamingPort.c

                ${FREERTOS_DIR}/Source/list.c
                ${FREERTOS_DIR}/Source/timers.c
                ${FREERTOS_DIR}/Source/tasks.c
                ${FREERTOS_DIR}/Source/queue.c
                ${FREERTOS_DIR}/Source/stream_buffer.c
                ${FREERTOS_DIR}/Source/croutine.c
                ${FREERTOS_DIR}/Source/event_groups.c
)     

target_include_directories( port
                            PUBLIC
                                ${FREERTOS_DIR}/Source/include
                                ${PORT_DIR}
                                ${PORT_DIR}/utils
                                ${TRACE_DIR}/Include
                                config

)

target_link_libraries( port
                       PRIVATE
                           pthread
)
