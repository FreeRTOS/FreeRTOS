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

.extern freertos_risc_v_trap_handler

.text
.section .vectors, "ax"
.option norvc
.global freertos_vector_table
freertos_vector_table:
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler

    // reset vector
    jal x0, Reset_Handler

    // Illegal instrution exception
    jal x0, freertos_risc_v_exception_handler

    // ecall handler
    jal x0, freertos_risc_v_trap_handler

    // LSU error
    jal x0, freertos_risc_v_exception_handler

    .section .startup

/* Reset Handler */
Reset_Handler:

    # Disable global interrupt. */
    csrci mstatus, 8

    # initialize stack pointer
    la sp, __StackTop

    # initialize global pointer
    la gp, __global_pointer

#ifndef __NO_SYSTEM_INIT
    jal SystemInit
#endif

    call __libc_init_array

    # Enable global interrupt. */
    csrsi mstatus, 8

    jal main
    ebreak

    .size Reset_Handler, . - Reset_Handler
