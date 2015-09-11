/*
    FreeRTOS V8.2.2 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved


    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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

#define portNESTING_INTERRUPT_ENTRY()											 	\
	__asm volatile (															 	\
						".extern ulPortYieldRequired						\t\n"	\
						".extern ulPortInterruptNesting						\t\n"	\
						".extern FreeRTOS_SVC_Handler						\t\n"	\
						/* Return to the interrupted instruction. */			 	\
						"SUB	LR, LR, #4									\t\n"	\
																			 		\
						/* Push the return address and SPSR. */				 		\
						"PUSH	{LR}										\t\n"	\
						"MRS	LR, SPSR									\t\n"	\
						"PUSH	{LR}										\t\n"	\
																					\
						/* Change to supervisor mode to allow reentry. */	 		\
						"CPS	#0x13										\t\n"	\
																			 		\
						/* Push used registers. */							 		\
						"PUSH	{r0-r4, r12}								\t\n"	\
																			 		\
						/* Increment nesting count.  r3 holds the address */ 		\
						/* of ulPortInterruptNesting future use. */			 		\
						"LDR	r2, =ulPortInterruptNestingConst			\t\n"	\
						"LDR	r3, [r2]									\t\n"	\
																					\
						"LDR	r1, [r3]									\t\n"	\
						"ADD	r4, r1, #1									\t\n"	\
						"STR	r4, [r3]									\t\n"	\
																			 		\
						/* Ensure bit 2 of the stack pointer is clear. */ 	 		\
						/* r2 holds the bit 2 value for future use. */		 		\
						"MOV	r2, sp										\t\n"	\
						"AND	r2, r2, #4									\t\n"	\
						"SUB	sp, sp, r2									\t\n"	\
																					\
						/* Call the interrupt handler. */					 		\
						"PUSH	{r0-r3, LR}										"	\
					);

#warning Why is ulPortYieldRequired accessed differently to the other variables?
#warning R0 seems to being pushed even though it is not used.
#warning Writing to the EOI register uses R4 on consecutive lines.


#define portNESTING_INTERRUPT_EXIT()												\
	__asm volatile (																\
						"POP	{r0-r3, LR}									\t\n"	\
						"ADD	sp, sp, r2									\t\n"	\
						"													\t\n"	\
						"CPSID	i											\t\n"	\
						"DSB												\t\n"	\
						"ISB												\t\n"	\
						"													\t\n"	\
						/* Write to the EOI register. */						 	\
						"LDR 	r4, ulICCEOIRConst							\t\n"	\
						"LDR	r4, [r4]									\t\n"	\
						"STR	r0, [r4]									\t\n"	\
																			 	 	\
						/* Restore the old nesting count. */					 	\
						"STR	r1, [r3]									\t\n"	\
																			 	 	\
						/* A context switch is never performed if the */		 	\
						/* nesting count is not 0. */							 	\
						"CMP	r1, #0										\t\n"	\
						"BNE	1f											\t\n"	\
																			 	 	\
						/* Did the interrupt request a context switch? */		 	\
						/* r1 holds the address of ulPortYieldRequired */		 	\
						/* and r0 the value of ulPortYieldRequired for */		 	\
						/* future use. */										 	\
						"LDR	r1, =ulPortYieldRequired					\t\n"	\
						"LDR	r0, [r1]									\t\n"	\
						"CMP	r0, #0										\t\n"	\
						"BNE	2f											\t\n"	\
																			 	 	\
					"1:														\t\n"	\
						/* No context switch.  Restore used registers, */		 	\
					    /* LR_irq and SPSR before returning. 0x12 is IRQ */			\
						/* mode. */					 								\
						"POP	{r0-r4, r12}								\t\n"	\
						"CPS	#0x12										\t\n"	\
						"POP	{LR}										\t\n"	\
						"MSR	SPSR_cxsf, LR								\t\n"	\
						"POP	{LR}										\t\n"	\
						"MOVS	PC, LR										\t\n"	\
																			 	 	\
					"2:														\t\n"	\
						/* A context switch is to be performed.  */				 	\
						/* Clear the context switch pending	flag. */			 	\
						"MOV	r0, #0										\t\n"	\
						"STR	r0, [r1]									\t\n"	\
																			 	 	\
						/* Restore used registers, LR-irq and  */				 	\
						/* SPSR before saving the context to the */				 	\
						/* task stack. 0x12 is IRQ mode. */							\
						"POP	{r0-r4, r12}								\t\n"	\
						"CPS	#0x12										\t\n"	\
						"POP	{LR}										\t\n"	\
						"MSR	SPSR_cxsf, LR								\t\n"	\
						"POP	{LR}										\t\n"	\
						"b 	FreeRTOS_SVC_Handler											\t\n"	\
						"ISB												\t\n"	\
						"ulICCEOIRConst:	.word ulICCEOIR					\t\n"	\
						" ulPortInterruptNestingConst: .word ulPortInterruptNesting " \
					);

