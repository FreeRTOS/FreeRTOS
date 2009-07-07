/*
	FreeRTOS.org V5.4.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
*/

#include "FreeRTOSConfig.h"

#define portCONTEXT_SIZE 132
#define portEPC_STACK_LOCATION	124
#define portSTATUS_STACK_LOCATION 128

/******************************************************************/ 	
.macro	portSAVE_CONTEXT

	/* Make room for the context. First save the current status so we can 
	manipulate it, and the cause and EPC registers so we capture their 
	original values in case of interrupt nesting. */
	mfc0		k0, _CP0_CAUSE
	addiu		sp,	sp, -portCONTEXT_SIZE
	mfc0		k1, _CP0_STATUS

	/* Also save s6 and s5 so we can use them during this interrupt.  Any
	nesting interrupts should maintain the values of these registers
	across the ISR. */
	sw			s6, 44(sp)
	sw			s5, 40(sp)
	sw			k1, portSTATUS_STACK_LOCATION(sp)

	/* Enable interrupts above the current priority. */
	srl			k0, k0, 0xa
	ins 		k1, k0, 10, 6
	ins			k1, zero, 1, 4

	/* s5 is used as the frame pointer. */
	add			s5, zero, sp

	/* Check the nesting count value. */
	la			k0, uxInterruptNesting
	lw			s6, (k0)

	/* If the nesting count is 0 then swap to the the system stack, otherwise
	the system stack is already being used. */
	bne			s6, zero, .+20
	nop

	/* Swap to the system stack. */
	la			sp, xISRStackTop
	lw			sp, (sp)

	/* Increment and save the nesting count. */
	addiu		s6, s6, 1
	sw			s6, 0(k0)

	/* s6 holds the EPC value, this is saved after interrupts are re-enabled. */
	mfc0 		s6, _CP0_EPC

	/* Re-enable interrupts. */
	mtc0		k1, _CP0_STATUS

	/* Save the context into the space just created.  s6 is saved again
	here as it now contains the EPC value.  No other s registers need be
	saved. */
	sw			ra,	120(s5)
	sw			s8, 116(s5)
	sw			t9, 112(s5)
	sw			t8,	108(s5)
	sw			t7,	104(s5)
	sw			t6, 100(s5)
	sw			t5, 96(s5)
	sw			t4, 92(s5)
	sw			t3, 88(s5)
	sw			t2, 84(s5)
	sw			t1, 80(s5)
	sw			t0, 76(s5)
	sw			a3, 72(s5)
	sw			a2, 68(s5)
	sw			a1, 64(s5)
	sw			a0, 60(s5)
	sw			v1, 56(s5)
	sw			v0, 52(s5)
	sw			s6, portEPC_STACK_LOCATION(s5)
	sw			$1, 16(s5)

	/* s6 is used as a scratch register. */
	mfhi		s6
	sw			s6, 12(s5)
	mflo		s6
	sw			s6, 8(s5)

	/* Update the task stack pointer value if nesting is zero. */
	la			s6, uxInterruptNesting
	lw			s6, (s6)
	addiu		s6, s6, -1
	bne			s6, zero, .+20
	nop

	/* Save the stack pointer. */
	la			s6, uxSavedTaskStackPointer
	sw			s5, (s6)

	.endm
	
/******************************************************************/	
.macro	portRESTORE_CONTEXT

	/* Restore the stack pointer from the TCB.  This is only done if the
	nesting count is 1. */
	la			s6, uxInterruptNesting
	lw			s6, (s6)
	addiu		s6, s6, -1
	bne			s6, zero, .+20
	nop
	la			s6, uxSavedTaskStackPointer
	lw			s5, (s6)
	
	/* Restore the context. */
	lw			s6, 8(s5)
	mtlo		s6
	lw			s6, 12(s5)
	mthi		s6
	lw			$1, 16(s5)
	/* s6 is loaded as it was used as a scratch register and therefore saved
	as part of the interrupt context. */
	lw			s6, 44(s5)
	lw			v0, 52(s5)
	lw			v1, 56(s5)
	lw			a0, 60(s5)
	lw			a1, 64(s5)
	lw			a2, 68(s5)
	lw			a3, 72(s5)
	lw			t0, 76(s5)
	lw			t1, 80(s5)
	lw			t2, 84(s5)
	lw			t3, 88(s5)
	lw			t4, 92(s5)
	lw			t5, 96(s5)
	lw			t6, 100(s5)
	lw			t7, 104(s5)
	lw			t8, 108(s5)
	lw			t9, 112(s5)
	lw			s8, 116(s5)
	lw			ra, 120(s5)

	/* Protect access to the k registers, and others. */
	di

	/* Decrement the nesting count. */
	la			k0, uxInterruptNesting
	lw			k1, (k0)
	addiu		k1, k1, -1
	sw			k1, 0(k0)

	lw			k0, portSTATUS_STACK_LOCATION(s5)
	lw			k1, portEPC_STACK_LOCATION(s5)

	/* Leave the stack how we found it.  First load sp from s5, then restore
	s5 from the stack. */
	add			sp, zero, s5
	lw			s5, 40(sp)
	addiu		sp,	sp,	portCONTEXT_SIZE

	mtc0		k0, _CP0_STATUS
	ehb
	mtc0 		k1, _CP0_EPC
	eret 
	nop

	.endm

