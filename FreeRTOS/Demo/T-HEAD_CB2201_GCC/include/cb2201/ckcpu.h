/*
 * Copyright (C) 2017 C-SKY Microsystems Co., Ltd. All rights reserved.
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
#ifndef _CKCPU_H_
#define _CKCPU_H_
.macro  csky_cpu_initpsr
    /*Init psr value, enable exception, disable interrupt and fast interrupt.
     * psr = 0x80000100
     */
    mfcr    a3, psr
    bseti   a3, 8
    bseti   a3, 5
    bseti   a3, 31
    bseti   a3, 30
    mtcr    a3, psr
.endm

.macro  csky_cpu_initnspsr
    mfcr    a3, cr<0,3>
    bseti   a3, 5
    bseti   a3, 6
    bseti   a3, 8
    bseti   a3, 31
    mtcr    a3, cr<0,3>
.endm

.macro  csky_cpu_initvec vsrtable
    /*
     * Setup initial vector base table for interrupts and exceptions
     */
    lrw     a2, \vsrtable
    mtcr    a2, vbr
.endm

.macro  csky_cpu_initnsvec nsvsrtable
    /*
     * Setup initial security vector base table for interrupts and exceptions
     */
    lrw     a2, \nsvsrtable
    //mtcr    a2, cr<1,3>
    mtcr    a2, cr<1,0>
.endm

.macro  csky_cpu_initstack stack
    /* Initialize the normal stack pointer from the linker definition. */
    lrw     a3, \stack
    mov     sp, a3
.endm

.macro  csky_cpu_init_nor_stack _nor_stack
    /* Initialize the normal stack pointer from the linker definition. */
    lrw     a3, \_nor_stack
    mtcr    a3,  cr<14,3>
.endm
.macro  csky_cpu_init_ns_stack ns_stack
    /* Initialize the normal stack pointer from the linker definition. */
    lrw     a3, \ns_stack
    mov     sp, a3
    //mtcr    a3, cr<6,3>
.endm
.macro  csky_cpu_init_nor_ns_stack _nor_ns_stack
    /* Initialize the normal stack pointer from the linker definition. */
    lrw     a3, \_nor_ns_stack
    mtcr    a3, cr<14,1>
.endm

.macro  csky_cpu_initfstack fstack
    /* Initialize the fast interrupt stack pointer . */
    psrset  af
    lrw     a3, \fstack
    mov     sp, a3
    psrclr  af
.endm

#endif
