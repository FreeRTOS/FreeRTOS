/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

#ifndef MESSAGE_BUFFER_AMP_H
#define MESSAGE_BUFFER_AMP_H

/* Enough four 4 8 byte strings, plus the additional 4 bytes per message
overhead of message buffers. */
#define mbaTASK_MESSAGE_BUFFER_SIZE ( 60 )

#define mbaCONTROL_MESSAGE_BUFFER_SIZE ( 24 )

/* The number of instances of prvM4CoreTasks that are created. */
#define mbaNUMBER_OF_CORE_2_TASKS	2

/* A block time of 0 simply means, don't block. */
#define mbaDONT_BLOCK				0

/* Place the message buffers at a fixed location so it is the same for both
cores. */
#pragma location = 0x38000000
MessageBufferHandle_t xControlMessageBuffer;

#pragma location = 0x38000004
MessageBufferHandle_t xDataMessageBuffers[ mbaNUMBER_OF_CORE_2_TASKS ];

#pragma location = 0x3800000c
static volatile uint32_t ulStartSyncCounters[ mbaNUMBER_OF_CORE_2_TASKS ];


/* The variable used to hold the stream buffer structure.*/
#pragma location = 0x38000050
StaticStreamBuffer_t xControlMessageBufferStruct;
#pragma location = 0x380000A0
StaticStreamBuffer_t xDataMessageBufferStructs[mbaNUMBER_OF_CORE_2_TASKS];
/* Used to dimension the array used to hold the streams.*/
/* Defines the memory that will actually hold the streams within the stream buffer.*/
#pragma location = 0x38000100
static uint8_t ucControlBufferStorage[ mbaCONTROL_MESSAGE_BUFFER_SIZE ];
#pragma location = 0x38000200
static uint8_t ucDataBufferStorage[mbaNUMBER_OF_CORE_2_TASKS][ mbaTASK_MESSAGE_BUFFER_SIZE ];


#endif /* MESSAGE_BUFFER_AMP_H */
