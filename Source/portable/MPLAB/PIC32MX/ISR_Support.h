/*
	FreeRTOS.org V4.8.0 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	***************************************************************************
	*																		  *
	* SAVE TIME AND MONEY!  Why not get us to quote to get FreeRTOS.org		  *
	* running on your hardware - or even write all or part of your application*
	* for you?  See http://www.OpenRTOS.com for details.					  *
	*																		  *
	***************************************************************************
	***************************************************************************

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

#define portCONTEXT_SIZE 136
#define portEXL_AND_IE_BITS	0x03

#define portEPC_STACK_LOCATION	124
#define portSTATUS_STACK_LOCATION 128
#define portCAUSE_STACK_LOCATION 132

/******************************************************************/ 	
.macro	portSAVE_CONTEXT

	/* Make room for the context. */	
	addiu		sp,	sp, -portCONTEXT_SIZE

	/* Get interrupts above the kernel priority enabled again ASAP.  First
	save the current status so we can manipulate it, and the cause and EPC
	registers so we capture their original values in case of interrupt nesting. */

	mfc0		k0, _CP0_CAUSE
	sw			k0, portCAUSE_STACK_LOCATION(sp)
	mfc0		k1, _CP0_STATUS
	sw			k1, portSTATUS_STACK_LOCATION(sp)

	/* Also save s6 so we can use it during this interrupt.  Any
	nesting interrupts should maintain the values of this register
	accross the ISR. */
	sw			s6, 44(sp)

	/* s6 holds the EPC value, we may want this during the context switch. */
	mfc0 		s6, _CP0_EPC

	/* Enable interrupts above the kernel priority. */
	addiu		k0, zero, configKERNEL_INTERRUPT_PRIORITY
	ins 		k1, k0, 10, 6
	ins			k1, zero, 1, 4
	mtc0		k1, _CP0_STATUS

	/* Save the context into the space just created.  s6 is saved again
	here as it now contains the EPC value. */
	sw			ra,	120(sp)
	sw			s8, 116(sp)
	sw			t9, 112(sp)
	sw			t8,	108(sp)
	sw			t7,	104(sp)
	sw			t6, 100(sp)
	sw			t5, 96(sp)
	sw			t4, 92(sp)
	sw			t3, 88(sp)
	sw			t2, 84(sp)
	sw			t1, 80(sp)
	sw			t0, 76(sp)
	sw			a3, 72(sp)
	sw			a2, 68(sp)
	sw			a1, 64(sp)
	sw			a0, 60(sp)
	sw			v1, 56(sp)
	sw			v0, 52(sp)
	sw			s7, 48(sp)
	sw			s6, portEPC_STACK_LOCATION(sp)
	sw			s5, 40(sp)
	sw			s4,	36(sp)
	sw			s3, 32(sp)
	sw			s2, 28(sp)
	sw			s1, 24(sp)
	sw			s0, 20(sp)
	sw			$1, 16(sp)

	/* s7 is used as a scratch register. */
	mfhi		s7
	sw			s7, 12(sp)
	mflo		s7
	sw			s7, 8(sp)

	/* Each task maintains its own nesting count. */
	la			s7, uxCriticalNesting
	lw			s7, (s7)
	sw			s7, 4(sp)
	
	/* Update the TCB stack pointer value */
	la			s7, pxCurrentTCB
	lw			s7, (s7)
	sw			sp, (s7)

	/* Switch to the ISR stack, saving the current stack in s5.  This might
	be used to determine the cause of a general exception. */
	add			s5, zero, sp
	la			s7, xISRStackTop
	lw			sp, (s7)

	.endm
	
/******************************************************************/	
.macro	portRESTORE_CONTEXT

	/* Restore the stack pointer from the TCB */
	la			s0, pxCurrentTCB
	lw			s1, (s0)
	lw			sp, (s1)
	
	/* Restore the context, the first item of which is the critical nesting
	depth. */
	la			s0, uxCriticalNesting
	lw			s1, 4(sp)
	sw			s1, (s0)

	/* Restore the rest of the context. */
	lw			s0, 8(sp)
	mtlo		s0
	lw			s0, 12(sp)
	mthi		s0
	lw			$1, 16(sp)
	lw			s0, 20(sp)
	lw			s1, 24(sp)
	lw			s2, 28(sp)
	lw			s3, 32(sp)
	lw			s4, 36(sp)
	lw			s5, 40(sp)
	lw			s6, 44(sp)
	lw			s7, 48(sp)
	lw			v0, 52(sp)
	lw			v1, 56(sp)
	lw			a0, 60(sp)
	lw			a1, 64(sp)
	lw			a2, 68(sp)
	lw			a3, 72(sp)
	lw			t0, 76(sp)
	lw			t1, 80(sp)
	lw			t2, 84(sp)
	lw			t3, 88(sp)
	lw			t4, 92(sp)
	lw			t5, 96(sp)
	lw			t6, 100(sp)
	lw			t7, 104(sp)
	lw			t8, 108(sp)
	lw			t9, 112(sp)
	lw			s8, 116(sp)
	lw			ra, 120(sp)

	/* Protect access to the k registers. */
	di
	lw			k1, portSTATUS_STACK_LOCATION(sp)
	lw			k0, portEPC_STACK_LOCATION(sp)

	/* Leave the stack how we found it. */
	addiu		sp,	sp,	portCONTEXT_SIZE

	mtc0		k1, _CP0_STATUS
	ehb
	mtc0 		k0, _CP0_EPC
	eret 
	nop

	.endm

