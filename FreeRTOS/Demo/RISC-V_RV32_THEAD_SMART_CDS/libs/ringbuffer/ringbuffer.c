/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include "ringbuffer/ringbuffer.h"

#define min(a, b)  (((a) < (b)) ? (a) : (b))

/**
  * \brief  Removes the entire FIFO contents.
  * \param  [in] fifo: The fifo to be emptied.
  * \return None.
  */
void ringbuffer_reset(ringbuffer_t *fifo)
{
    fifo->write = fifo->read = 0;
    fifo->data_len = 0;
}

/**
  * \brief  Returns the size of the FIFO in bytes.
  * \param  [in] fifo: The fifo to be used.
  * \return The size of the FIFO.
  */
static inline uint32_t ringbuffer_size(ringbuffer_t *fifo)
{
    return fifo->size;
}

/**
  * \brief  Returns the number of used bytes in the FIFO.
  * \param  [in] fifo: The fifo to be used.
  * \return The number of used bytes.
  */
uint32_t ringbuffer_len(ringbuffer_t *fifo)
{
    return fifo->data_len;
}

/**
  * \brief  Returns the number of bytes available in the FIFO.
  * \param  [in] fifo: The fifo to be used.
  * \return The number of bytes available.
  */
uint32_t ringbuffer_avail(ringbuffer_t *fifo)
{
    return ringbuffer_size(fifo) - ringbuffer_len(fifo);
}

/**
  * \brief  Is the FIFO empty?
  * \param  [in] fifo: The fifo to be used.
  * \retval true:      Yes.
  * \retval false:     No.
  */
bool ringbuffer_is_empty(ringbuffer_t *fifo)
{
    return ringbuffer_len(fifo) == 0;
}

/**
  * \brief  Is the FIFO full?
  * \param  [in] fifo: The fifo to be used.
  * \retval true:      Yes.
  * \retval false:     No.
  */
bool ringbuffer_is_full(ringbuffer_t *fifo)
{
    return ringbuffer_avail(fifo) == 0;
}

/**
  * \brief  Puts some data into the FIFO.
  * \param  [in] fifo: The fifo to be used.
  * \param  [in] in:   The data to be added.
  * \param  [in] len:  The length of the data to be added.
  * \return The number of bytes copied.
  * \note   This function copies at most @len bytes from the @in into
  *         the FIFO depending on the free space, and returns the number
  *         of bytes copied.
  */
uint32_t ringbuffer_in(ringbuffer_t *fifo, const void *datptr, uint32_t len)
{
    uint32_t writelen = 0, tmplen = 0;

    if(ringbuffer_is_full(fifo))
        return 0;

    tmplen = fifo->size - fifo->data_len;
    writelen = tmplen > len ? len : tmplen;

    if(fifo->write < fifo->read) {
        memcpy((void*)&fifo->buffer[fifo->write], (void*)datptr, writelen);
    } else {
        tmplen = fifo->size - fifo->write;
        if(writelen <= tmplen) {
            memcpy((void*)&fifo->buffer[fifo->write], (void*)datptr, writelen);
        } else {
            memcpy((void*)&fifo->buffer[fifo->write], (void*)datptr, tmplen);
            memcpy((void*)fifo->buffer, (uint8_t*)datptr + tmplen, writelen - tmplen);
        }
    }

    fifo->write = (fifo->write + writelen) % fifo->size;
    fifo->data_len += writelen;

    return writelen;
}

/**
  * \brief  Gets some data from the FIFO.
  * \param  [in] fifo: The fifo to be used.
  * \param  [in] out:  Where the data must be copied.
  * \param  [in] len:  The size of the destination buffer.
  * \return The number of copied bytes.
  * \note   This function copies at most @len bytes from the FIFO into
  *         the @out and returns the number of copied bytes.
  */
uint32_t ringbuffer_out(ringbuffer_t *fifo, void *outbuf, uint32_t len)
{
    uint32_t readlen = 0, tmplen = 0;
    if(ringbuffer_is_empty(fifo))
        return 0;

    readlen = len > fifo->data_len ? fifo->data_len : len;
    tmplen = fifo->size - fifo->read;

    if(NULL != outbuf) {
        if(readlen <= tmplen) {
            memcpy((void*)outbuf, (void*)&fifo->buffer[fifo->read], readlen);
        } else {
            memcpy((void*)outbuf,(void*)&fifo->buffer[fifo->read], tmplen);
            memcpy((uint8_t*)outbuf + tmplen,(void*)fifo->buffer,readlen - tmplen);
        }
    }

    fifo->read = (fifo->read + readlen) % fifo->size;
    fifo->data_len -= readlen;

    return readlen;
}

