/*
 * FreeRTOS V202212.00
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

.balign 128, 0
.option norvc
.global freertos_vector_table
freertos_vector_table:
IRQ_0:
        j freertos_risc_v_exception_handler
IRQ_1:
        j freertos_risc_v_interrupt_handler
IRQ_2:
        j freertos_risc_v_interrupt_handler
IRQ_3:
        j freertos_risc_v_interrupt_handler
IRQ_4:
        j freertos_risc_v_interrupt_handler
IRQ_5:
        j freertos_risc_v_interrupt_handler
IRQ_6:
        j freertos_risc_v_interrupt_handler
IRQ_7:
        j freertos_risc_v_mtimer_interrupt_handler
IRQ_8:
        j freertos_risc_v_interrupt_handler
IRQ_9:
        j freertos_risc_v_interrupt_handler
IRQ_10:
        j freertos_risc_v_interrupt_handler
IRQ_11:
        j freertos_risc_v_interrupt_handler
IRQ_12:
        j freertos_risc_v_interrupt_handler
IRQ_13:
        j freertos_risc_v_interrupt_handler
IRQ_14:
        j freertos_risc_v_interrupt_handler
IRQ_15:
        j freertos_risc_v_interrupt_handler
