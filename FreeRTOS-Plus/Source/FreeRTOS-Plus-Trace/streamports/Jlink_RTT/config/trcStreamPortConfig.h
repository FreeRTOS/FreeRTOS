/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * The configuration for trace streaming ("stream ports").
 */

#ifndef TRC_STREAM_PORT_CONFIG_H
#define TRC_STREAM_PORT_CONFIG_H

#ifdef __cplusplus
extern "C" {
#endif

/* This define will determine whether to use the internal buffer or not.
If file writing creates additional trace events (i.e. it uses semaphores or mutexes),
then the internal buffer must be enabled to avoid infinite recursion. */
#define TRC_CFG_STREAM_PORT_USE_INTERNAL_BUFFER 0

/**
* @def TRC_CFG_INTERNAL_BUFFER_SIZE
*
* @brief Configures the size of the internal buffer if used.
* is enabled.
*/
#define TRC_CFG_STREAM_PORT_INTERNAL_BUFFER_SIZE 5000

/**
* @def TRC_CFG_STREAM_PORT_RTT_UP_BUFFER_SIZE
* 
* @brief Defines the size of the "up" RTT buffer (target -> host) to use for writing
* the trace data, for RTT buffer 1 or higher.
*
* This setting is ignored for RTT buffer 0, which can't be reconfigured
* in runtime and therefore hard-coded to use the defines in SEGGER_RTT_Conf.h.
*
* Default buffer size for Tracealyzer is 5000 bytes. 
*
* If you have a stand-alone J-Link probe, the can be decreased to around 1 KB.
* But integrated J-Link OB interfaces are slower and needs about 5-10 KB, 
* depending on the amount of data produced.
*/
#define TRC_CFG_STREAM_PORT_RTT_UP_BUFFER_SIZE 5000

/**
* @def TRC_CFG_STREAM_PORT_RTT_DOWN_BUFFER_SIZE
*
* @brief Defines the size of the "down" RTT buffer (host -> target) to use for reading
* commands from Tracealyzer, for RTT buffer 1 or higher.
*
* Default buffer size for Tracealyzer is 32 bytes.
*
* This setting is ignored for RTT buffer 0, which can't be reconfigured
* in runtime and therefore hard-coded to use the defines in SEGGER_RTT_Conf.h.
*/
#define TRC_CFG_STREAM_PORT_RTT_DOWN_BUFFER_SIZE 32

/**
* @def TRC_CFG_STREAM_PORT_RTT_UP_BUFFER_INDEX
*
* @brief Defines the RTT buffer to use for writing the trace data. Make sure that
* the PC application has the same setting (File->Settings).
*
* Default: 1
*
* We don't recommend using RTT buffer 0, since mainly intended for terminals.
* If you prefer to use buffer 0, it must be configured in SEGGER_RTT_Conf.h.
*/
#define TRC_CFG_STREAM_PORT_RTT_UP_BUFFER_INDEX 1

/**
* @def TRC_CFG_STREAM_PORT_RTT_DOWN_BUFFER_INDEX
*
* @brief Defines the RTT buffer to use for reading the trace data. Make sure that
* the PC application has the same setting (File->Settings).
*
* Default: 1
*
* We don't recommend using RTT buffer 0, since mainly intended for terminals.
* If you prefer to use buffer 0, it must be configured in SEGGER_RTT_Conf.h.
*/
#define TRC_CFG_STREAM_PORT_RTT_DOWN_BUFFER_INDEX 1

/**
* @def TRC_CFG_STREAM_PORT_RTT_MODE
*
* @brief This stream port for J-Link streaming relies on SEGGER RTT, that contains an
* internal RAM buffer read by the J-Link probes during execution.
*
* Possible values:
* - SEGGER_RTT_MODE_BLOCK_IF_FIFO_FULL
* - SEGGER_RTT_MODE_NO_BLOCK_SKIP (default)
*
* Using SEGGER_RTT_MODE_BLOCK_IF_FIFO_FULL ensure that you get a
* complete and valid trace. This may however cause blocking if your streaming
* interface isn't fast enough, which may disturb the real-time behavior.
*
* We therefore recommend SEGGER_RTT_MODE_NO_BLOCK_SKIP. In this mode,
* Tracealyzer will report lost events if the transfer is not
* fast enough. In that case, try increasing the size of the "up buffer".
*/
#define TRC_CFG_STREAM_PORT_RTT_MODE SEGGER_RTT_MODE_BLOCK_IF_FIFO_FULL

/**
 * @def TRC_CFG_STREAM_PORT_RTT_NO_LOCK_WRITE
 * 
 * @brief Sets if RTT should write without locking or not when writing
 * RTT data. This should normally be disabled with an exception being
 * Zephyr, where the SEGGER RTT locks aren't necessary and causes
 * problems if enabled.
 * 
 * Default: 0
 */
#define TRC_CFG_STREAM_PORT_RTT_NO_LOCK_WRITE 0

#ifdef __cplusplus
}
#endif

#endif /* TRC_STREAM_PORT_CONFIG_H */
