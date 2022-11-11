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

/*******************************************************************************
 * TRC_CFG_STREAM_PORT_ITM_PORT
 *
 * Valid values: 0 - 31
 *
 * What ITM port to use for the ITM software events. Make sure the IDE is
 * configured for the same channel.
 *
 * Default: 1 (0 is typically terminal output and 31 is used by Keil)
 *
 ******************************************************************************/
#define TRC_CFG_STREAM_PORT_ITM_PORT 1

#ifdef __cplusplus
}
#endif

#endif /* TRC_STREAM_PORT_CONFIG_H */
