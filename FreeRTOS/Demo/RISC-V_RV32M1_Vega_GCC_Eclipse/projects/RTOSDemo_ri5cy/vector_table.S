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

#include "portContext.h"

.extern freertos_risc_v_exception_handler
.extern freertos_risc_v_interrupt_handler
.extern vTaskSwitchContext

.text
.section .vectors, "ax"
.option norvc
freertos_vector_table:
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler
    jal x0, freertos_risc_v_interrupt_handler

    /* Reset vector. */
    jal x0, Reset_Handler

    /* Illegal instrution exception. */
    jal x0, freertos_risc_v_exception_handler

    /* Ecall handler. */
    jal x0, Ecall_Handler

    /* LSU error (Invalid Memory Access) exception. */
    jal x0, freertos_risc_v_exception_handler
/*-----------------------------------------------------------*/

.section .startup

/* Reset Handler */
Reset_Handler:

    /* Disable global interrupt. */
    csrci mstatus, 8

    /* Initialize stack pointer. */
    la sp, __StackTop

    /* Initialize global pointer */
    la gp, __global_pointer

#ifndef __NO_SYSTEM_INIT
    jal SystemInit
#endif

    call __libc_init_array

    /* Enable global interrupt. */
    csrsi mstatus, 8

    jal main
    ebreak

    .size Reset_Handler, . - Reset_Handler

    .global _init
    .global _fini
_init:
_fini:
    ret
/*-----------------------------------------------------------*/

/* RISC-V RI5CY core has a separate ecall entry point in the vector table.
 * Therefore we can write a more efficient ecall handler which do not need to
 * check the mcause value. */
Ecall_Handler:
    portcontextSAVE_EXCEPTION_CONTEXT
    call vTaskSwitchContext
    portcontextRESTORE_CONTEXT
/*-----------------------------------------------------------*/
