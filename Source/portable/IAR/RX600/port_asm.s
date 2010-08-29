/*
    FreeRTOS V6.0.5 - Copyright (C) 2010 Real Time Engineers Ltd.

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
		POP			R15

		/* Floating point status word. */
		MVTC		R15, FPSW

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

		/* Save the FPSW and accumulator. */
		MVFC		FPSW, R15
		PUSH.L		R15
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
		MVTIPL		#4

		/* Select the next task to run. */
		BSR.A		_vTaskSwitchContext

		/* Reset the interrupt mask as no more data structure access is required. */
		MVTIPL		#1

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
		POP			R15
		MVTC		R15, FPSW
		POPM		R1-R15
		RTE
		NOP
		NOP

/*-----------------------------------------------------------*/

		END

