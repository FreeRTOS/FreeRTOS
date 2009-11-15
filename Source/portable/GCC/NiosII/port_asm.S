/*
    FreeRTOS V6.0.1 - Copyright (C) 2009 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/

.extern		vTaskSwitchContext
	
.set noat

# Exported to start the first task.
.globl restore_sp_from_pxCurrentTCB		
	
# Entry point for exceptions.
.section .exceptions.entry, "xa"		

# Save the entire context of a task.
save_context:
	addi	ea, ea, -4			# Point to the next instruction.
	addi	sp,	sp, -116		# Create space on the stack.
	stw		ra, 0(sp)
								# Leave a gap for muldiv 0
	stw		at, 8(sp)		 
	stw		r2, 12(sp)
	stw		r3, 16(sp)
	stw		r4, 20(sp)
	stw		r5, 24(sp) 
	stw		r6, 28(sp) 
	stw		r7, 32(sp) 
	stw		r8, 36(sp) 
	stw		r9, 40(sp) 
	stw		r10, 44(sp)
	stw		r11, 48(sp)
	stw		r12, 52(sp)
	stw		r13, 56(sp)
	stw		r14, 60(sp)
	stw		r15, 64(sp)
	rdctl	r5, estatus 		# Save the eStatus
	stw		r5, 68(sp)
	stw		ea, 72(sp)			# Save the PC
	stw		r16, 76(sp)			# Save the remaining registers
	stw		r17, 80(sp)
	stw		r18, 84(sp)
	stw		r19, 88(sp)
	stw		r20, 92(sp)
	stw		r21, 96(sp)
	stw		r22, 100(sp)
	stw		r23, 104(sp)
	stw		gp, 108(sp)
	stw		fp, 112(sp)

save_sp_to_pxCurrentTCB:
	movia	et, pxCurrentTCB	# Load the address of the pxCurrentTCB pointer
	ldw		et, (et)			# Load the value of the pxCurrentTCB pointer
	stw		sp, (et)			# Store the stack pointer into the top of the TCB
	
	.section .exceptions.irqtest, "xa"	
hw_irq_test:
	/*
     * Test to see if the exception was a software exception or caused 
     * by an external interrupt, and vector accordingly.
     */
    rdctl	r4, ipending		# Load the Pending Interrupts indication
	rdctl	r5, estatus 		# Load the eStatus (enabled interrupts).
    andi	r2, r5, 1			# Are interrupts enabled globally.
    beq		r2, zero, soft_exceptions		# Interrupts are not enabled.
    beq		r4, zero, soft_exceptions		# There are no interrupts triggered.

	.section .exceptions.irqhandler, "xa"
hw_irq_handler:
	call	alt_irq_handler					# Call the alt_irq_handler to deliver to the registered interrupt handler.

    .section .exceptions.irqreturn, "xa"
restore_sp_from_pxCurrentTCB:
	movia	et, pxCurrentTCB		# Load the address of the pxCurrentTCB pointer
	ldw		et, (et)				# Load the value of the pxCurrentTCB pointer
	ldw		sp, (et)				# Load the stack pointer with the top value of the TCB

restore_context:
	ldw		ra, 0(sp)		# Restore the registers.
							# Leave a gap for muldiv 0.
	ldw		at, 8(sp)
	ldw		r2, 12(sp)
	ldw		r3, 16(sp)
	ldw		r4, 20(sp)
	ldw		r5, 24(sp) 
	ldw		r6, 28(sp) 
	ldw		r7, 32(sp) 
	ldw		r8, 36(sp) 
	ldw		r9, 40(sp) 
	ldw		r10, 44(sp)
	ldw		r11, 48(sp)
	ldw		r12, 52(sp)
	ldw		r13, 56(sp)
	ldw		r14, 60(sp)
	ldw		r15, 64(sp)
	ldw		et, 68(sp)		# Load the eStatus
	wrctl	estatus, et 	# Write the eStatus
	ldw		ea, 72(sp)		# Load the Program Counter
	ldw		r16, 76(sp)
	ldw		r17, 80(sp)
	ldw		r18, 84(sp)
	ldw		r19, 88(sp)
	ldw		r20, 92(sp)
	ldw		r21, 96(sp)
	ldw		r22, 100(sp)
	ldw		r23, 104(sp)
	ldw		gp, 108(sp)
	ldw		fp, 112(sp)
	addi	sp,	sp, 116		# Release stack space

    eret					# Return to address ea, loading eStatus into Status.
   
	.section .exceptions.soft, "xa"
soft_exceptions:
	ldw		et, 0(ea)				# Load the instruction where the interrupt occured.
	movhi	at, %hi(0x003B683A)		# Load the registers with the trap instruction code
	ori		at, at, %lo(0x003B683A)
   	cmpne	et, et, at				# Compare the trap instruction code to the last excuted instruction
  	beq		et, r0, call_scheduler	# its a trap so switchcontext
  	break							# This is an un-implemented instruction or muldiv problem.
  	br		restore_context			# its something else

call_scheduler:
	addi	ea, ea, 4						# A trap was called, increment the program counter so it is not called again.
	stw		ea, 72(sp)						# Save the new program counter to the context.
	call	vTaskSwitchContext				# Pick the next context.
	br		restore_sp_from_pxCurrentTCB	# Switch in the task context and restore. 
