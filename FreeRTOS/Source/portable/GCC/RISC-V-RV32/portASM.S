/*
 * FreeRTOS Kernel V10.1.1
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/*
 * The FreeRTOS kernel's RISC-V port is split between the the code that is
 * common across all currently supported RISC-V chips (implementations of the
 * RISC-V ISA), and code which tailors the port to a specific RISC-V chip:
 *
 * + The code that is common to all RISC-V chips is implemented in
 *   FreeRTOS\Source\portable\GCC\RISC-V-RV32\portASM.S.  There is only one
 *   portASM.S file because the same file is used no matter which RISC-V chip is
 *   in use.
 *
 * + The code that tailors the kernel's RISC-V port to a specific RISC-V
 *   chip is implemented in freertos_risc_v_port_specific_extensions.h.  There
 *   is one freertos_risc_v_port_specific_extensions.h that can be used with any
 *   RISC-V chip that both includes a standard CLINT and does not add to the
 *   base set of RISC-V registers.  There are additional
 *   freertos_risc_v_port_specific_extensions.h files for RISC-V implementations
 *   that do not include a standard CLINT or do add to the base set of RISC-V
 *   regiters.
 *
 * CARE MUST BE TAKEN TO INCLDUE THE CORRECT
 * freertos_risc_v_port_specific_extensions.h HEADER FILE FOR THE CHIP
 * IN USE.  To include the correct freertos_risc_v_port_specific_extensions.h
 * header file ensure the path to the correct header file is in the assembler's
 * include path.
 *
 * This freertos_risc_v_port_specific_extensions.h is for use on RISC-V chips
 * that include a standard CLINT and do not add to the base set of RISC-V
 * registers.
 *
 */
#include "freertos_risc_v_port_specific_extensions.h"

/* Check the freertos_risc_v_port_specific_extensions.h and/or command line
definitions. */
#ifndef portasmHAS_CLINT
	#error freertos_risc_v_port_specific_extensions.h must define portasmHAS_CLINT to either 1 (CLINT present) or 0 (clint not present).
#endif

#ifndef portasmHANDLE_INTERRUPT
	#error portasmHANDLE_INTERRUPT must be defined to the function to be called to handle external/peripheral interrupts.  portASM_HANDLE_INTERRUPT can be defined on the assmbler command line or in the appropriate freertos_risc_v_port_specific_extensions.h header file.
#endif

#ifndef portasmSAVE_ADDITIONAL_REGISTERS
	/* portasmSAVE_ADDITIONAL_REGISTERS is not defined so assume no additional
	registers need to be saved. */
	#define portasmSAVE_ADDITIONAL_REGISTERS
#endif

#ifndef portasmRESTORE_ADDITIONAL_REGISTERS
	/* portasmRESTORE_ADDITIONAL_REGISTERS is not defined so assume no
	additional registers need to be restored. */
	#define portasmRESTORE_ADDITIONAL_REGISTERS
#endif

#if __riscv_xlen == 64
	#error Not implemented yet - change lw to ld, and sw to sd.
	#define portWORD_SIZE 8
#elif __riscv_xlen == 32
	#define portWORD_SIZE 4
#else
	#error Assembler did not define __riscv_xlen
#endif

/* Only the standard core registers are stored by default.  Any additional
registers must be saved by the portasmSAVE_ADDITIONAL_REGISTERS and
portasmRESTORE_ADDITIONAL_REGISTERS macros - which can be defined in a chip
specific version of freertos_risc_v_port_specific_extensions.h.  See the notes
at the top of this file. */
#define portCONTEXT_SIZE ( 30 * portWORD_SIZE )

.global xPortStartFirstTask
.global vFreeRTOSPortTrapHandler
.extern pxCurrentTCB
.extern ulPortTrapHandler
.extern vTaskSwitchContext
.extern Timer_IRQHandler
.extern pullMachineTimerCompareRegister
.extern pullNextTime
.extern ulTimerIncrementsForOneTick
.extern xISRStackTop
.extern vPortHandleInterrupt

/*-----------------------------------------------------------*/

.align 16
vFreeRTOSPortTrapHandler:
	addi sp, sp, -portCONTEXT_SIZE
	sw x1, 1 * portWORD_SIZE( sp )
	sw x5, 2 * portWORD_SIZE( sp )
	sw x6, 3 * portWORD_SIZE( sp )
	sw x7, 4 * portWORD_SIZE( sp )
	sw x8, 5 * portWORD_SIZE( sp )
	sw x9, 6 * portWORD_SIZE( sp )
	sw x10, 7 * portWORD_SIZE( sp )
	sw x11, 8 * portWORD_SIZE( sp )
	sw x12, 9 * portWORD_SIZE( sp )
	sw x13, 10 * portWORD_SIZE( sp )
	sw x14, 11 * portWORD_SIZE( sp )
	sw x15, 12 * portWORD_SIZE( sp )
	sw x16, 13 * portWORD_SIZE( sp )
	sw x17, 14 * portWORD_SIZE( sp )
	sw x18, 15 * portWORD_SIZE( sp )
	sw x19, 16 * portWORD_SIZE( sp )
	sw x20, 17 * portWORD_SIZE( sp )
	sw x21, 18 * portWORD_SIZE( sp )
	sw x22, 19 * portWORD_SIZE( sp )
	sw x23, 20 * portWORD_SIZE( sp )
	sw x24, 21 * portWORD_SIZE( sp )
	sw x25, 22 * portWORD_SIZE( sp )
	sw x26, 23 * portWORD_SIZE( sp )
	sw x27, 24 * portWORD_SIZE( sp )
	sw x28, 25 * portWORD_SIZE( sp )
	sw x29, 26 * portWORD_SIZE( sp )
	sw x30, 27 * portWORD_SIZE( sp )
	sw x31, 28 * portWORD_SIZE( sp )

	portasmSAVE_ADDITIONAL_REGISTERS	/* Defined in freertos_risc_v_port_specific_extensions.h to save any registers unique to the RISC-V implementation. */

	csrr t0, mstatus					/* Required for MPIE bit. */
	sw t0, 29 * portWORD_SIZE( sp )

	lw  t0, pxCurrentTCB				/* Load pxCurrentTCB. */
	sw  sp, 0( t0 )				 		/* Write sp to first TCB member. */

	csrr a0, mcause
	csrr a1, mepc

test_if_asynchronous:
	srli a2, a0, 0x1f					/* MSB of mcause is 1 if handing an asynchronous interrupt - shift to LSB to clear other bits. */
	beq a2, x0, handle_synchronous		/* Branch past interrupt handing if not asynchronous. */
	sw a1, 0( sp )						/* Asynch so save unmodified exception return address. */

handle_asynchronous:

#if( portasmHAS_CLINT != 0 )

	test_if_mtimer:							/* If there is a CLINT then the mtimer is used to generate the tick interrupt. */
		lui t0, 0x80000
		addi t1, t0, 7						/* 0x80000007 == machine timer interrupt. */
		bne a0, t1, test_if_external_interrupt

		lw t0, pullMachineTimerCompareRegister	/* Load address of compare register into t0. */
		lw t1, pullNextTime					/* Load the address of ullNextTime into t1. */
		lw t2, 0(t1)						/* Load the low word of ullNextTime into t2. */
		lw t3, 4(t1)						/* Load the high word of ullNextTime into t3. */
		sw t2, 0(t0)						/* Store low word of ullNextTime into compare register. */
		sw t3, 4(t0)						/* Store high word of ullNextTime into compare register. */
		lw t0, ulTimerIncrementsForOneTick	/* Load the value of ullTimerIncrementForOneTick into t0 (could this be optimized by storing in an array next to pullNextTime?). */
		add t4, t0, t2						/* Add the low word of ullNextTime to the timer increments for one tick (assumes timer increment for one tick fits in 32-bits. */
		sltu t5, t4, t2						/* See if the sum of low words overflowed (what about the zero case?). */
		add t6, t3, t5						/* Add overflow to high word of ullNextTime. */
		sw t4, 0(t1)						/* Store new low word of ullNextTime. */
		sw t6, 4(t1)						/* Store new high word of ullNextTime. */
		lw sp, xISRStackTop					/* Switch to ISR stack before function call. */
		jal xTaskIncrementTick
		beqz a0, processed_source			/* Don't switch context if incrementing tick didn't unblock a task. */
		jal vTaskSwitchContext
		j processed_source

	test_if_external_interrupt:			/* If there is a CLINT and the mtimer interrupt is not pending then check to see if an external interrupt is pending. */
		addi t1, t1, 4					/* 0x80000007 + 4 = 0x8000000b == Machine external interrupt. */
		bne a0, t1, as_yet_unhandled	/* Something as yet unhandled. */

#endif /* portasmHAS_CLINT */

	lw sp, xISRStackTop					/* Switch to ISR stack before function call. */
	jal portasmHANDLE_INTERRUPT			/* Jump to the interrupt handler if there is no CLINT or if there is a CLINT and it has been determined that an external interrupt is pending. */
	j processed_source

handle_synchronous:
	addi a1, a1, 4						/* Synchronous so updated exception return address to the instruction after the instruction that generated the exeption. */
	sw a1, 0( sp )						/* Save updated exception return address. */

test_if_environment_call:
	li t0, 11 							/* 11 == environment call. */
	bne a0, t0, is_exception			/* Not an M environment call, so some other exception. */
	lw sp, xISRStackTop					/* Switch to ISR stack before function call. */
	jal vTaskSwitchContext
	j processed_source

is_exception:
	ebreak
	j is_exception

as_yet_unhandled:
	ebreak
	j as_yet_unhandled

processed_source:
	lw  sp, pxCurrentTCB				/* Load pxCurrentTCB. */
	lw  sp, 0( sp )				 		/* Read sp from first TCB member. */

	/* Load mret with the address of the next task. */
	lw t0, 0( sp )
	csrw mepc, t0

	/* Load mstatus with the interrupt enable bits used by the task. */
	lw  t0, 29 * portWORD_SIZE( sp )
	csrw mstatus, t0					/* Required for MPIE bit. */

	portasmRESTORE_ADDITIONAL_REGISTERS	/* Defined in freertos_risc_v_port_specific_extensions.h to restore any registers unique to the RISC-V implementation. */

	lw  x1, 1 * portWORD_SIZE( sp )
	lw  x5, 2 * portWORD_SIZE( sp )		/* t0 */
	lw  x6, 3 * portWORD_SIZE( sp )		/* t1 */
	lw  x7, 4 * portWORD_SIZE( sp )		/* t2 */
	lw  x8, 5 * portWORD_SIZE( sp )		/* s0/fp */
	lw  x9, 6 * portWORD_SIZE( sp )		/* s1 */
	lw  x10, 7 * portWORD_SIZE( sp )	/* a0 */
	lw  x11, 8 * portWORD_SIZE( sp )	/* a1 */
	lw  x12, 9 * portWORD_SIZE( sp )	/* a2 */
	lw  x13, 10 * portWORD_SIZE( sp )	/* a3 */
	lw  x14, 11 * portWORD_SIZE( sp )	/* a4 */
	lw  x15, 12 * portWORD_SIZE( sp )	/* a5 */
	lw  x16, 13 * portWORD_SIZE( sp )	/* a6 */
	lw  x17, 14 * portWORD_SIZE( sp )	/* a7 */
	lw  x18, 15 * portWORD_SIZE( sp )	/* s2 */
	lw  x19, 16 * portWORD_SIZE( sp )	/* s3 */
	lw  x20, 17 * portWORD_SIZE( sp )	/* s4 */
	lw  x21, 18 * portWORD_SIZE( sp )	/* s5 */
	lw  x22, 19 * portWORD_SIZE( sp )	/* s6 */
	lw  x23, 20 * portWORD_SIZE( sp )	/* s7 */
	lw  x24, 21 * portWORD_SIZE( sp )	/* s8 */
	lw  x25, 22 * portWORD_SIZE( sp )	/* s9 */
	lw  x26, 23 * portWORD_SIZE( sp )	/* s10 */
	lw  x27, 24 * portWORD_SIZE( sp )	/* s11 */
	lw  x28, 25 * portWORD_SIZE( sp )	/* t3 */
	lw  x29, 26 * portWORD_SIZE( sp )	/* t4 */
	lw  x30, 27 * portWORD_SIZE( sp )	/* t5 */
	lw  x31, 28 * portWORD_SIZE( sp )	/* t6 */
	addi	sp, sp, portCONTEXT_SIZE

	mret
/*-----------------------------------------------------------*/

.align 16
xPortStartFirstTask:

#if( portasmHAS_CLINT != 0 )
	/* If there is a clint then interrupts can branch directly to the FreeRTOS
	trap handler.  Otherwise the interrupt controller will need to be configured
	outside of this file. */
	la t0, vFreeRTOSPortTrapHandler
	csrw mtvec, t0
#endif /* portasmHAS_CLILNT */

	lw  sp, pxCurrentTCB			/* Load pxCurrentTCB. */
	lw  sp, 0( sp )				 	/* Read sp from first TCB member. */

	lw  x1, 0( sp ) /* Note for starting the scheduler the exception return address is used as the function return address. */
	lw  x5, 2 * portWORD_SIZE( sp )		/* t0 */
	lw  x6, 3 * portWORD_SIZE( sp )		/* t1 */
	lw  x7, 4 * portWORD_SIZE( sp )		/* t2 */
	lw  x8, 5 * portWORD_SIZE( sp )		/* s0/fp */
	lw  x9, 6 * portWORD_SIZE( sp )		/* s1 */
	lw  x10, 7 * portWORD_SIZE( sp )	/* a0 */
	lw  x11, 8 * portWORD_SIZE( sp )	/* a1 */
	lw  x12, 9 * portWORD_SIZE( sp )	/* a2 */
	lw  x13, 10 * portWORD_SIZE( sp )	/* a3 */
	lw  x14, 11 * portWORD_SIZE( sp )	/* a4 */
	lw  x15, 12 * portWORD_SIZE( sp )	/* a5 */
	lw  x16, 13 * portWORD_SIZE( sp )	/* a6 */
	lw  x17, 14 * portWORD_SIZE( sp )	/* a7 */
	lw  x18, 15 * portWORD_SIZE( sp )	/* s2 */
	lw  x19, 16 * portWORD_SIZE( sp )	/* s3 */
	lw  x20, 17 * portWORD_SIZE( sp )	/* s4 */
	lw  x21, 18 * portWORD_SIZE( sp )	/* s5 */
	lw  x22, 19 * portWORD_SIZE( sp )	/* s6 */
	lw  x23, 20 * portWORD_SIZE( sp )	/* s7 */
	lw  x24, 21 * portWORD_SIZE( sp )	/* s8 */
	lw  x25, 22 * portWORD_SIZE( sp )	/* s9 */
	lw  x26, 23 * portWORD_SIZE( sp )	/* s10 */
	lw  x27, 24 * portWORD_SIZE( sp )	/* s11 */
	lw  x28, 25 * portWORD_SIZE( sp )	/* t3 */
	lw  x29, 26 * portWORD_SIZE( sp )	/* t4 */
	lw  x30, 27 * portWORD_SIZE( sp )	/* t5 */
	lw  x31, 28 * portWORD_SIZE( sp )	/* t6 */
	addi	sp, sp, portCONTEXT_SIZE
	csrs	mstatus, 8					/* Enable machine interrupts. */
	ret

/*-----------------------------------------------------------*/

