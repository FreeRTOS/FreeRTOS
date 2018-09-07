/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

#ifndef _RING_H_
#define _RING_H_

#include "intmath.h"

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

/** Return count in buffer */
#define RING_CNT(head,tail,size) fixed_mod((head) - (tail), (size))

/** Return space available, 0..size-1. always leave one free char as a
 * completely full buffer has head == tail, which is the same as empty */
#define RING_SPACE(head,tail,size) RING_CNT((tail),((head) + 1),(size))

/** Return count up to the end of the buffer. Carefully avoid accessing head
 * and tail more than once, so they can change underneath us without returning
 * inconsistent results */
#define RING_CNT_TO_END(head,tail,size) \
     ({int end = (size) - (tail); \
     int n = fixed_mod((head) + end, (size));   \
     n < end ? n : end;})

/** Return space available up to the end of the buffer */
#define RING_SPACE_TO_END(head,tail,size) \
   ({int end = (size) - 1 - (head); \
     int n = fixed_mod(end + (tail), (size)); \
     n <= end ? n : end+1;})

/** Increment head or tail */
#define RING_INC(headortail,size) \
        (headortail)++; \
        if((headortail) >= (size)) { \
            (headortail) = 0; \
        }

/** Decrement head or tail */
#define RING_DEC(headortail,size) \
        if((headortail) == 0) { \
            (headortail) = (size) - 1; \
        } else { \
            (headortail)--; \
        }

/** Circular buffer is empty ? */
#define RING_EMPTY(head, tail) ((head) == (tail))

/** Clear circular buffer */
#define RING_CLEAR(head, tail) ((head) = (tail) = 0)

#endif /* _RING_H_ */
