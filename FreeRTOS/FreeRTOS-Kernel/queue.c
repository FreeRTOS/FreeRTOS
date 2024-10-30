/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/* Standard includes. */
#include <stdlib.h>
#include <string.h>

/* Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE ensures that PRIVILEGED_FUNCTION
 * is defined correctly and privileged functions are placed in correct sections. */
#define MPU_WRAPPERS_INCLUDED_FROM_API_FILE

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"

#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE

/* Lint e9021, e961 and e750 are suppressed as a MISRA exception justified
 * because the MPU ports require MPU_WRAPPERS_INCLUDED_FROM_API_FILE to be defined
 * for the header files above, but not in this file, in order to generate the
 * correct privileged Vs unprivileged linkage and placement. */

/* Constants used with the xRxLock and xTxLock structure members. */
#define queueUNLOCKED            ( ( int8_t ) -1 )
#define queueLOCKED_UNMODIFIED   ( ( int8_t ) 0 )

/* For internal use only.  These definitions *must* match those in queue.h. */
#define queueSEND_TO_BACK        ( ( BaseType_t ) 0 )
#define queueSEND_TO_FRONT       ( ( BaseType_t ) 1 )
#define queueOVERWRITE           ( ( BaseType_t ) 2 )

/* Effectively make a union out of the xQUEUE structure. */
#define uxQueueType              pcHead
#define queueQUEUE_TYPE_BASE     ( ( uint8_t ) 0U )
#define queueQUEUE_TYPE_SET      ( ( uint8_t ) 0U )
#define queueQUEUE_TYPE_MUTEX    ( ( uint8_t ) 1U )
#define queueQUEUE_TYPE_COUNTING_SEMAPHORE ( ( uint8_t ) 2U )
#define queueQUEUE_TYPE_BINARY_SEMAPHORE   ( ( uint8_t ) 3U )
#define queueQUEUE_TYPE_RECURSIVE_MUTEX    ( ( uint8_t ) 4U )

/* Semaphores do not actually store or copy data, so have an item size of
 * zero. */
#define queueSEMAPHORE_QUEUE_ITEM_LENGTH ( ( UBaseType_t ) 0 )
#define queueMUTEX_GIVE_BLOCK_TIME       ( ( TickType_t ) 0U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX              ( ( UBaseType_t ) 0x80000000U )
#define queueQUEUE_IS_QUEUE              ( ( UBaseType_t ) 0x40000000U )
#define queueQUEUE_IS_SEMAPHORE          ( ( UBaseType_t ) 0x20000000U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE ( ( UBaseType_t ) 0x10000000U )
#define queueQUEUE_IS_BINARY_SEMAPHORE   ( ( UBaseType_t ) 0x08000000U )
#define queueQUEUE_IS_RECURSIVE_MUTEX    ( ( UBaseType_t ) 0x04000000U )
#define queueQUEUE_IS_QUEUE_SET          ( ( UBaseType_t ) 0x02000000U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER   ( ( UBaseType_t ) 0x01000000U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK             ( ( UBaseType_t ) 0xFF000000U )
#define queueQUEUE_TYPE_SHIFT            ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_MASK         ( ( UBaseType_t ) 0x80000000U )
#define queueQUEUE_IS_QUEUE_MASK         ( ( UBaseType_t ) 0x40000000U )
#define queueQUEUE_IS_SEMAPHORE_MASK     ( ( UBaseType_t ) 0x20000000U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_MASK ( ( UBaseType_t ) 0x10000000U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_MASK   ( ( UBaseType_t ) 0x08000000U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_MASK    ( ( UBaseType_t ) 0x04000000U )
#define queueQUEUE_IS_QUEUE_SET_MASK     ( ( UBaseType_t ) 0x02000000U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_MASK   ( ( UBaseType_t ) 0x01000000U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_IS_MUTEX_SHIFT        ( ( UBaseType_t ) 31U )
#define queueQUEUE_IS_QUEUE_SHIFT        ( ( UBaseType_t ) 30U )
#define queueQUEUE_IS_SEMAPHORE_SHIFT    ( ( UBaseType_t ) 29U )
#define queueQUEUE_IS_COUNTING_SEMAPHORE_SHIFT ( ( UBaseType_t ) 28U )
#define queueQUEUE_IS_BINARY_SEMAPHORE_SHIFT   ( ( UBaseType_t ) 27U )
#define queueQUEUE_IS_RECURSIVE_MUTEX_SHIFT    ( ( UBaseType_t ) 26U )
#define queueQUEUE_IS_QUEUE_SET_SHIFT    ( ( UBaseType_t ) 25U )
#define queueQUEUE_IS_QUEUE_SET_MEMBER_SHIFT   ( ( UBaseType_t ) 24U )

/* The following bit fields convey information in the xQueueHandle_t type. */
#define queueQUEUE_TYPE_MASK_SHIFT       ( ( UBaseType_t ) 24U
