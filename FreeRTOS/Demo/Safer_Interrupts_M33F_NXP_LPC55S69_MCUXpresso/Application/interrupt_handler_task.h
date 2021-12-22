/*
 * FreeRTOS V202112.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#ifndef INTERRUPT_HANDLER_TASK_H_
#define INTERRUPT_HANDLER_H_

/* Standard includes. */
#include <stdint.h>

/* The interrupt handler task serves user IRQ requests sent to the interrupt
 * queue. A user IRQ request comprises of the following 2 things:
 *
 * 1. Data.
 * 2. IRQ handler function.
 */

/**
 * @brief Type of the handler function for every user IRQ request.
 */
typedef void ( * UserIrqHandlerFunction_t )( uint32_t ulData );

/**
 * @brief Represents user IRQ requests sent to the interrupt queue.
 */
typedef struct UserIrqRequest
{
    uint32_t ulData;
    UserIrqHandlerFunction_t xHandlerFunction;
} UserIrqRequest_t;

/**
 * @brief Function that implements the interrupt handler task.
 *
 * A FreeRTOS queue, known as interrupt queue, which holds UserIrqRequest_t items,
 * is passed as the parameter to this task. The interrupt handler task reads the
 * user IRQ requests from the interrupt queue and invokes the corresponding
 * handlers.
 */
void vInterruptHandlerTask( void * pvParams );

#endif /* INTERRUPT_HANDLER_H_ */
