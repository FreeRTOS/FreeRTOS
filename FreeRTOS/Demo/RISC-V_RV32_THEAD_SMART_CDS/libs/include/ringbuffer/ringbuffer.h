/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited
 */

/******************************************************************************
* @file     ringbuffer.h
* @brief    header file for ringbuffer Driver
* @version  V1.0
* @date     August 15.  2019
******************************************************************************/
#ifndef _RING_BUFFER_H_
#define _RING_BUFFER_H_

#ifdef __cplusplus
extern "C" {
#endif

#include "stdint.h"
#include <stdbool.h>

typedef struct ringbuffer {
    uint8_t *buffer;
    uint32_t size;
    uint32_t write;
    uint32_t read;
    uint32_t data_len;
} ringbuffer_t;

void ringbuffer_reset(ringbuffer_t *fifo);
uint32_t ringbuffer_len(ringbuffer_t *fifo);
uint32_t ringbuffer_avail(ringbuffer_t *fifo);
bool ringbuffer_is_empty(ringbuffer_t *fifo);
bool ringbuffer_is_full(ringbuffer_t *fifo);

/*write to ringbuffer*/
uint32_t ringbuffer_in(ringbuffer_t *fifo, const void *in, uint32_t len);

/*read to ringbuffer*/
uint32_t ringbuffer_out(ringbuffer_t *fifo, void *out, uint32_t len);

#ifdef __cplusplus
}
#endif

#endif /* _RING_BUFFER_H_ */
