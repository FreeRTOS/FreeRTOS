/*
 * FreeRTOS Kernel V10.1.1
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and t

 o permit persons to whom the Software is furnished to do so,
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

#if __riscv_xlen == 64
    #error Not implemented yet - change lw to ld, and sw to sd.
    #define WORD_SIZE 8
#elif __riscv_xlen == 32
    #define WORD_SIZE 4
#else
    #error Assembler has not defined __riscv_xlen
#endif

#define CONTEXT_SIZE ( 30 * WORD_SIZE )

.global xPortStartFirstTask
.global vPortTrapHandler
.extern pxCurrentTCB
.extern handle_trap

/*-----------------------------------------------------------*/

.align 8
xPortStartFirstTask:

	lw  sp, pxCurrentTCB            /* Load pxCurrentTCB. */
	lw  sp, 0( sp )                 /* Read sp from first TCB member. */

	lw  x1, 0( sp ) /* Note for starting the scheduler the exception return address is used as the function return address. */
	lw  x5, 2 * WORD_SIZE( sp )     /* t0 */
	lw  x6, 3 * WORD_SIZE( sp )     /* t1 */
	lw  x7, 4 * WORD_SIZE( sp )     /* t2 */
	lw  x8, 5 * WORD_SIZE( sp )     /* s0/fp */
	lw  x9, 6 * WORD_SIZE( sp )     /* s1 */
	lw  x10, 7 * WORD_SIZE( sp )    /* a0 */
	lw  x11, 8 * WORD_SIZE( sp )    /* a1 */
	lw  x12, 9 * WORD_SIZE( sp )    /* a2 */
	lw  x13, 10 * WORD_SIZE( sp )   /* a3 */
	lw  x14, 11 * WORD_SIZE( sp )   /* a4 */
	lw  x15, 12 * WORD_SIZE( sp )   /* a5 */
	lw  x16, 13 * WORD_SIZE( sp )   /* a6 */
	lw  x17, 14 * WORD_SIZE( sp )   /* a7 */
	lw  x18, 15 * WORD_SIZE( sp )   /* s2 */
	lw  x19, 16 * WORD_SIZE( sp )   /* s3 */
	lw  x20, 17 * WORD_SIZE( sp )   /* s4 */
	lw  x21, 18 * WORD_SIZE( sp )   /* s5 */
	lw  x22, 19 * WORD_SIZE( sp )   /* s6 */
	lw  x23, 20 * WORD_SIZE( sp )   /* s7 */
	lw  x24, 21 * WORD_SIZE( sp )   /* s8 */
	lw  x25, 22 * WORD_SIZE( sp )   /* s9 */
	lw  x26, 23 * WORD_SIZE( sp )   /* s10 */
	lw  x27, 24 * WORD_SIZE( sp )   /* s11 */
	lw  x28, 25 * WORD_SIZE( sp )   /* t3 */
	lw  x29, 26 * WORD_SIZE( sp )   /* t4 */
	lw  x30, 27 * WORD_SIZE( sp )   /* t5 */
	lw  x31, 28 * WORD_SIZE( sp )   /* t6 */
	addi    sp, sp, CONTEXT_SIZE
	csrs    mstatus, 8              /* Enable machine interrupts. */
	ret

/*-----------------------------------------------------------*/

.align 8
vPortTrapHandler:
	addi sp, sp, -CONTEXT_SIZE
	sw x1, 1 * WORD_SIZE( sp )
	sw x5, 2 * WORD_SIZE( sp )
	sw x6, 3 * WORD_SIZE( sp )
	sw x7, 4 * WORD_SIZE( sp )
	sw x8, 5 * WORD_SIZE( sp )
	sw x9, 6 * WORD_SIZE( sp )
	sw x10, 7 * WORD_SIZE( sp )
	sw x11, 8 * WORD_SIZE( sp )
	sw x12, 9 * WORD_SIZE( sp )
	sw x13, 10 * WORD_SIZE( sp )
	sw x14, 11 * WORD_SIZE( sp )
	sw x15, 12 * WORD_SIZE( sp )
	sw x16, 13 * WORD_SIZE( sp )
	sw x17, 14 * WORD_SIZE( sp )
	sw x18, 15 * WORD_SIZE( sp )
	sw x19, 16 * WORD_SIZE( sp )
	sw x20, 17 * WORD_SIZE( sp )
	sw x21, 18 * WORD_SIZE( sp )
	sw x22, 19 * WORD_SIZE( sp )
	sw x23, 20 * WORD_SIZE( sp )
	sw x24, 21 * WORD_SIZE( sp )
	sw x25, 22 * WORD_SIZE( sp )
	sw x26, 23 * WORD_SIZE( sp )
	sw x27, 24 * WORD_SIZE( sp )
	sw x28, 25 * WORD_SIZE( sp )
	sw x29, 26 * WORD_SIZE( sp )
	sw x30, 27 * WORD_SIZE( sp )
	sw x31, 28 * WORD_SIZE( sp )

	csrr t0, mstatus                /* Required for MPIE bit. */
	sw t0, 29 * WORD_SIZE( sp )

	lw  t0, pxCurrentTCB            /* Load pxCurrentTCB. */
	sw  sp, 0( t0 )                 /* Write sp to first TCB member. */

	csrr a0, mcause
	csrr a1, mepc
	mv a2, sp
/*_RB_ Does stack need aligning here? */
	jal handle_trap
	csrw mepc, a0
	/* Save exception return address. */
	sw a0, 0( sp )


	lw  sp, pxCurrentTCB            /* Load pxCurrentTCB. */
	lw  sp, 0( sp )                 /* Read sp from first TCB member. */

	/* Load mret with the address of the next task. */
	lw t0, 0( sp )
	csrw mepc, t0

	/* Load mstatus with the interrupt enable bits used by the task. */
	lw  t0, 29 * WORD_SIZE( sp )
	csrw mstatus, t0                /* Required for MPIE bit. */

	lw  x1, 1 * WORD_SIZE( sp )
	lw  x5, 2 * WORD_SIZE( sp )     /* t0 */
	lw  x6, 3 * WORD_SIZE( sp )     /* t1 */
	lw  x7, 4 * WORD_SIZE( sp )     /* t2 */
	lw  x8, 5 * WORD_SIZE( sp )     /* s0/fp */
	lw  x9, 6 * WORD_SIZE( sp )     /* s1 */
	lw  x10, 7 * WORD_SIZE( sp )    /* a0 */
	lw  x11, 8 * WORD_SIZE( sp )    /* a1 */
	lw  x12, 9 * WORD_SIZE( sp )    /* a2 */
	lw  x13, 10 * WORD_SIZE( sp )   /* a3 */
	lw  x14, 11 * WORD_SIZE( sp )   /* a4 */
	lw  x15, 12 * WORD_SIZE( sp )   /* a5 */
	lw  x16, 13 * WORD_SIZE( sp )   /* a6 */
	lw  x17, 14 * WORD_SIZE( sp )   /* a7 */
	lw  x18, 15 * WORD_SIZE( sp )   /* s2 */
	lw  x19, 16 * WORD_SIZE( sp )   /* s3 */
	lw  x20, 17 * WORD_SIZE( sp )   /* s4 */
	lw  x21, 18 * WORD_SIZE( sp )   /* s5 */
	lw  x22, 19 * WORD_SIZE( sp )   /* s6 */
	lw  x23, 20 * WORD_SIZE( sp )   /* s7 */
	lw  x24, 21 * WORD_SIZE( sp )   /* s8 */
	lw  x25, 22 * WORD_SIZE( sp )   /* s9 */
	lw  x26, 23 * WORD_SIZE( sp )   /* s10 */
	lw  x27, 24 * WORD_SIZE( sp )   /* s11 */
	lw  x28, 25 * WORD_SIZE( sp )   /* t3 */
	lw  x29, 26 * WORD_SIZE( sp )   /* t4 */
	lw  x30, 27 * WORD_SIZE( sp )   /* t5 */
	lw  x31, 28 * WORD_SIZE( sp )   /* t6 */
	addi    sp, sp, CONTEXT_SIZE

	mret


