/*
    FreeRTOS V8.2.0rc1 - Copyright (C) 2014 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?".  Have you defined configASSERT()?  *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    ***************************************************************************
     *                                                                       *
     *   Investing in training allows your team to be as productive as       *
     *   possible as early as possible, lowering your overall development    *
     *   cost, and enabling you to bring a more robust product to market     *
     *   earlier than would otherwise be possible.  Richard Barry is both    *
     *   the architect and key author of FreeRTOS, and so also the world's   *
     *   leading authority on what is the world's most popular real time     *
     *   kernel for deeply embedded MCU designs.  Obtaining your training    *
     *   from Richard ensures your team will gain directly from his in-depth *
     *   product knowledge and years of usage experience.  Contact Real Time *
     *   Engineers Ltd to enquire about the FreeRTOS Masterclass, presented  *
     *   by Richard Barry:  http://www.FreeRTOS.org/contact
     *                                                                       *
    ***************************************************************************

    ***************************************************************************
     *                                                                       *
     *    You are receiving this top quality software for free.  Please play *
     *    fair and reciprocate by reporting any suspected issues and         *
     *    participating in the community forum:                              *
     *    http://www.FreeRTOS.org/support                                    *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

#include "PriorityDefinitions.h"

	PUBLIC _prvStartFirstTask
	PUBLIC ___interrupt_27

	EXTERN _pxCurrentTCB
	EXTERN _vTaskSwitchContext

	RSEG CODE:CODE(4)

_prvStartFirstTask:

		/* When starting the scheduler there is nothing that needs moving to the
		interrupt stack because the function is not called from an interrupt.
		Just ensure the current stack is the user stack. */
		SETPSW		U

		/* Obtain the location of the stack associated with which ever task
		pxCurrentTCB is currently pointing to. */
		MOV.L		#_pxCurrentTCB, R15
		MOV.L		[R15], R15
		MOV.L		[R15], R0

		/* Restore the registers from the stack of the task pointed to by
		pxCurrentTCB. */
		POP			R15

		/* Accumulator low 32 bits. */
		MVTACLO		R15
		POP			R15

		/* Accumulator high 32 bits. */
		MVTACHI		R15

		/* R1 to R15 - R0 is not included as it is the SP. */
		POPM		R1-R15

		/* This pops the remaining registers. */
		RTE
		NOP
		NOP

/*-----------------------------------------------------------*/

/* The software interrupt - overwrite the default 'weak' definition. */
___interrupt_27:

		/* Re-enable interrupts. */
		SETPSW		I

		/* Move the data that was automatically pushed onto the interrupt stack when
		the interrupt occurred from the interrupt stack to the user stack.

		R15 is saved before it is clobbered. */
		PUSH.L		R15

		/* Read the user stack pointer. */
		MVFC		USP, R15

		/* Move the address down to the data being moved. */
		SUB			#12, R15
		MVTC		R15, USP

		/* Copy the data across, R15, then PC, then PSW. */
		MOV.L		[ R0 ], [ R15 ]
		MOV.L 		4[ R0 ], 4[ R15 ]
		MOV.L		8[ R0 ], 8[ R15 ]

		/* Move the interrupt stack pointer to its new correct position. */
		ADD		#12, R0

		/* All the rest of the registers are saved directly to the user stack. */
		SETPSW		U

		/* Save the rest of the general registers (R15 has been saved already). */
		PUSHM		R1-R14

		/* Save the accumulator. */
		MVFACHI 	R15
		PUSH.L		R15

		/* Middle word. */
		MVFACMI	R15

		/* Shifted left as it is restored to the low order word. */
		SHLL		#16, R15
		PUSH.L		R15

		/* Save the stack pointer to the TCB. */
		MOV.L		#_pxCurrentTCB, R15
		MOV.L		[ R15 ], R15
		MOV.L		R0, [ R15 ]

		/* Ensure the interrupt mask is set to the syscall priority while the kernel
		structures are being accessed. */
		MVTIPL		#configMAX_SYSCALL_INTERRUPT_PRIORITY

		/* Select the next task to run. */
		BSR.A		_vTaskSwitchContext

		/* Reset the interrupt mask as no more data structure access is required. */
		MVTIPL		#configKERNEL_INTERRUPT_PRIORITY

		/* Load the stack pointer of the task that is now selected as the Running
		state task from its TCB. */
		MOV.L		#_pxCurrentTCB,R15
		MOV.L		[ R15 ], R15
		MOV.L		[ R15 ], R0

		/* Restore the context of the new task.  The PSW (Program Status Word) and
		PC will be popped by the RTE instruction. */
		POP			R15
		MVTACLO 	R15
		POP			R15
		MVTACHI 	R15
		POPM		R1-R15
		RTE
		NOP
		NOP

/*-----------------------------------------------------------*/

		END

