/*
 * Trace Recorder for Tracealyzer v4.8.1
 * Copyright 2023 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * The configuration for trace streaming ("stream ports").
 */

#ifndef TRC_STREAM_PORT_CONFIG_H
    #define TRC_STREAM_PORT_CONFIG_H

    #if ( TRC_USE_TRACEALYZER_RECORDER == 1 )

        #if ( TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING )

            #include <trcTypes.h>

            #ifdef __cplusplus
            extern "C" {
            #endif

/* Type flags */
            #define TRC_STREAM_PORT_RINGBUFFER_MODE_STOP_WHEN_FULL         ( 0U )
            #define TRC_STREAM_PORT_RINGBUFFER_MODE_OVERWRITE_WHEN_FULL    ( 1U )

/**
 * @def TRC_CFG_STREAM_PORT_BUFFER_SIZE
 *
 * @brief Defines the size of the ring buffer use for storing trace events.
 */
            #define TRC_CFG_STREAM_PORT_BUFFER_SIZE                        10240

/**
 * @def TRC_CFG_STREAM_PORT_BUFFER_MODE
 *
 * @brief Configures the behavior of the ring buffer when full.
 *
 * With TRC_CFG_STREAM_PORT_MODE set to TRC_STREAM_PORT_RINGBUFFER_MODE_OVERWRITE_WHEN_FULL, the
 * events are stored in a ring buffer, i.e., where the oldest events are
 * overwritten when the buffer becomes full. This allows you to get the last
 * events leading up to an interesting state, e.g., an error, without having
 * to store the whole run since startup.
 *
 * When TRC_CFG_STREAM_PORT_MODE is TRC_STREAM_PORT_RINGBUFFER_MODE_STOP_WHEN_FULL, the
 * recording is stopped when the buffer becomes full. This is useful for
 * recording events following a specific state, e.g., the startup sequence.
 */
            #define TRC_CFG_STREAM_PORT_RINGBUFFER_MODE                    TRC_STREAM_PORT_RINGBUFFER_MODE_OVERWRITE_WHEN_FULL

            #ifdef __cplusplus
}
            #endif

        #endif /*(TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)*/

    #endif /*(TRC_USE_TRACEALYZER_RECORDER == 1)*/

#endif /* TRC_STREAM_PORT_CONFIG_H */
