/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

#include <csi_config.h>

#define VIC_TSPDR 0XE000EC08

/********************************************************************
 * Functions: cpu_yeild
 *
 ********************************************************************/
.global cpu_yeild
.type   cpu_yeild, %function
cpu_yeild:
    lrw    r0, VIC_TSPDR
    bgeni  r1, 0
    stw    r1, (r0)
    rts

/********************************************************************
 * Functions: vPortStartTask
 *
 ********************************************************************/
.global vPortStartTask
.type   vPortStartTask, %function
vPortStartTask:
    psrclr   ie
    lrw      r4, pxCurrentTCB
    ld.w     r4, (r4)                // the current task stack pointer is the first member
    ld.w     sp, (r4)

    ldw      r0, (sp, 64)
    mtcr     r0, epc
    ldw      r0, (sp, 60)
    mtcr     r0, epsr
    ldw      r15, (sp, 56)
    ldm      r0-r13, (sp)
    addi     sp, 68
    rte

/********************************************************************
 * Functions: tspend_handler
 *
 ********************************************************************/
.global tspend_handler
.type   tspend_handler, %function
tspend_handler:
    subi   sp, 68
    stm    r0-r13, (sp)
    stw    r15, (sp, 56)
    mfcr   r0, epsr
    stw    r0, (sp, 60)
    mfcr   r0, epc
    stw    r0, (sp, 64)

    lrw    r2, pxCurrentTCB
    ld.w   r3, (r2)
    st.w   sp, (r3)

    jbsr   vTaskSwitchContext

    lrw    r4, pxCurrentTCB
    ld.w   r4, (r4)
    ld.w   sp, (r4)

    ldw    r0, (sp, 64)
    mtcr   r0, epc
    ldw    r0, (sp, 60)
    mtcr   r0, epsr
    ldw    r15, (sp, 56)
    ldm    r0-r13, (sp)
    addi   sp, 68
    rte
