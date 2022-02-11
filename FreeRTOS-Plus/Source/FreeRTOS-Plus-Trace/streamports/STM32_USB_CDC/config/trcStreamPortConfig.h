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

/* The time to wait if the USB interface is busy. */
#define TRC_CFG_STREAM_PORT_DELAY_ON_BUSY 3

/*******************************************************************************
* Configuration Macro: TRC_CFG_STREAM_PORT_USB_BUFFER_SIZE
*
* Specifies the size of the usb buffer.
******************************************************************************/
#define TRC_CFG_STREAM_PORT_USB_BUFFER_SIZE 64

/*******************************************************************************
* Configuration Macro: TRC_CFG_STREAM_PORT_INTERNAL_BUFFER_SIZE
*
* Specifies the size of the internal buffer.
******************************************************************************/
#define TRC_CFG_STREAM_PORT_INTERNAL_BUFFER_SIZE 10000

#ifdef __cplusplus
}
#endif

#endif /* TRC_STREAM_PORT_CONFIG_H */
