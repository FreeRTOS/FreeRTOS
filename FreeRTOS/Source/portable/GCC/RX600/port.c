/*
    FreeRTOS V8.1.0 - Copyright (C) 2014 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

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
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the SH2A port.
 *----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Library includes. */
#include "string.h"

/* Hardware specifics. */
#include "iodefine.h"

/*-----------------------------------------------------------*/

/* Tasks should start with interrupts enabled and in Supervisor mode, therefore
PSW is set with U and I set, and PM and IPL clear. */
#define portINITIAL_PSW     ( ( StackType_t ) 0x00030000 )
#define portINITIAL_FPSW    ( ( StackType_t ) 0x00000100 )

/* These macros allow a critical section to be added around the call to
xTaskIncrementTick(), which is only ever called from interrupts at the kernel
priority - ie a known priority.  Therefore these local macros are a slight
optimisation compared to calling the global SET/CLEAR_INTERRUPT_MASK macros,
which would require the old IPL to be read first and stored in a local variable. */
#define portDISABLE_INTERRUPTS_FROM_KERNEL_ISR() 	__asm volatile ( "MVTIPL	%0" ::"i"(configMAX_SYSCALL_INTERRUPT_PRIORITY) )
#define portENABLE_INTERRUPTS_FROM_KERNEL_ISR() 	__asm volatile ( "MVTIPL	%0" ::"i"(configKERNEL_INTERRUPT_PRIORITY) )

/*-----------------------------------------------------------*/

/*
 * Function to start the first task executing - written in asm code as direct
 * access to registers is required.
 */
static void prvStartFirstTask( void ) __attribute__((naked));

/*
 * Software interrupt handler.  Performs the actual context switch (saving and
 * restoring of registers).  Written in asm code as direct register access is
 * required.
 */
void vSoftwareInterruptISR( void ) __attribute__((naked));

/*
 * The tick interrupt handler.
 */
void vTickISR( void ) __attribute__((interrupt));

/*-----------------------------------------------------------*/

extern void *pxCurrentTCB;

/*-----------------------------------------------------------*/

/*
 * See header file for description.
 */
StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{
	/* R0 is not included as it is the stack pointer. */

	*pxTopOfStack = 0x00;
	pxTopOfStack--;
 	*pxTopOfStack = portINITIAL_PSW;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) pxCode;

	/* When debugging it can be useful if every register is set to a known
	value.  Otherwise code space can be saved by just setting the registers
	that need to be set. */
	#ifdef USE_FULL_REGISTER_INITIALISATION
	{
		pxTopOfStack--;
		*pxTopOfStack = 0xffffffff;	/* r15. */
		pxTopOfStack--;
		*pxTopOfStack = 0xeeeeeeee;
		pxTopOfStack--;
		*pxTopOfStack = 0xdddddddd;
		pxTopOfStack--;
		*pxTopOfStack = 0xcccccccc;
		pxTopOfStack--;
		*pxTopOfStack = 0xbbbbbbbb;
		pxTopOfStack--;
		*pxTopOfStack = 0xaaaaaaaa;
		pxTopOfStack--;
		*pxTopOfStack = 0x99999999;
		pxTopOfStack--;
		*pxTopOfStack = 0x88888888;
		pxTopOfStack--;
		*pxTopOfStack = 0x77777777;
		pxTopOfStack--;
		*pxTopOfStack = 0x66666666;
		pxTopOfStack--;
		*pxTopOfStack = 0x55555555;
		pxTopOfStack--;
		*pxTopOfStack = 0x44444444;
		pxTopOfStack--;
		*pxTopOfStack = 0x33333333;
		pxTopOfStack--;
		*pxTopOfStack = 0x22222222;
		pxTopOfStack--;
	}
	#else
	{
		pxTopOfStack -= 15;
	}
	#endif

	*pxTopOfStack = ( StackType_t ) pvParameters; /* R1 */
	pxTopOfStack--;
	*pxTopOfStack = portINITIAL_FPSW;
	pxTopOfStack--;
	*pxTopOfStack = 0x12345678; /* Accumulator. */
	pxTopOfStack--;
	*pxTopOfStack = 0x87654321; /* Accumulator. */

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

BaseType_t xPortStartScheduler( void )
{
extern void vApplicationSetupTimerInterrupt( void );

	/* Use pxCurrentTCB just so it does not get optimised away. */
	if( pxCurrentTCB != NULL )
	{
		/* Call an application function to set up the timer that will generate the
		tick interrupt.  This way the application can decide which peripheral to
		use.  A demo application is provided to show a suitable example. */
		vApplicationSetupTimerInterrupt();

		/* Enable the software interrupt. */
		_IEN( _ICU_SWINT ) = 1;

		/* Ensure the software interrupt is clear. */
		_IR( _ICU_SWINT ) = 0;

		/* Ensure the software interrupt is set to the kernel priority. */
		_IPR( _ICU_SWINT ) = configKERNEL_INTERRUPT_PRIORITY;

		/* Start the first task. */
		prvStartFirstTask();
	}

	/* Should not get here. */
	return pdFAIL;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Not implemented in ports where there is nothing to return to.
	Artificially force an assert. */
	configASSERT( pxCurrentTCB == NULL );
}
/*-----------------------------------------------------------*/

static void prvStartFirstTask( void )
{
	__asm volatile
	(
		/* When starting the scheduler there is nothing that needs moving to the
		interrupt stack because the function is not called from an interrupt.
		Just ensure the current stack is the user stack. */
		"SETPSW		U						\n" \

		/* Obtain the location of the stack associated with which ever task
		pxCurrentTCB is currently pointing to. */
		"MOV.L		#_pxCurrentTCB, R15		\n" \
		"MOV.L		[R15], R15				\n" \
		"MOV.L		[R15], R0				\n" \

		/* Restore the registers from the stack of the task pointed to by
		pxCurrentTCB. */
	    "POP		R15						\n" \

		/* Accumulator low 32 bits. */
	    "MVTACLO	R15 					\n" \
	    "POP		R15						\n" \

		/* Accumulator high 32 bits. */
	    "MVTACHI	R15 					\n" \
	    "POP		R15						\n" \

		/* Floating point status word. */
	    "MVTC		R15, FPSW 				\n" \

		/* R1 to R15 - R0 is not included as it is the SP. */
	    "POPM		R1-R15 					\n" \

		/* This pops the remaining registers. */
	    "RTE								\n" \
	    "NOP								\n" \
	    "NOP								\n"
	);
}
/*-----------------------------------------------------------*/

void vSoftwareInterruptISR( void )
{
	__asm volatile
	(
		/* Re-enable interrupts. */
		"SETPSW		I							\n" \

		/* Move the data that was automatically pushed onto the interrupt stack when
		the interrupt occurred from the interrupt stack to the user stack.

		R15 is saved before it is clobbered. */
		"PUSH.L		R15							\n" \

		/* Read the user stack pointer. */
		"MVFC		USP, R15					\n" \

		/* Move the address down to the data being moved. */
		"SUB		#12, R15					\n" \
		"MVTC		R15, USP					\n" \

		/* Copy the data across, R15, then PC, then PSW. */
		"MOV.L		[ R0 ], [ R15 ]				\n" \
		"MOV.L 		4[ R0 ], 4[ R15 ]			\n" \
		"MOV.L		8[ R0 ], 8[ R15 ]			\n" \

		/* Move the interrupt stack pointer to its new correct position. */
		"ADD		#12, R0						\n" \

		/* All the rest of the registers are saved directly to the user stack. */
		"SETPSW		U							\n" \

		/* Save the rest of the general registers (R15 has been saved already). */
		"PUSHM		R1-R14						\n" \

		/* Save the FPSW and accumulator. */
		"MVFC		FPSW, R15					\n" \
		"PUSH.L		R15							\n" \
		"MVFACHI 	R15							\n" \
		"PUSH.L		R15							\n" \

		/* Middle word. */
		"MVFACMI	R15							\n" \

		/* Shifted left as it is restored to the low order word. */
		"SHLL		#16, R15					\n" \
		"PUSH.L		R15							\n" \

		/* Save the stack pointer to the TCB. */
		"MOV.L		#_pxCurrentTCB, R15			\n" \
		"MOV.L		[ R15 ], R15				\n" \
		"MOV.L		R0, [ R15 ]					\n" \

		/* Ensure the interrupt mask is set to the syscall priority while the kernel
		structures are being accessed. */
		"MVTIPL		%0 							\n" \

		/* Select the next task to run. */
		"BSR.A		_vTaskSwitchContext			\n" \

		/* Reset the interrupt mask as no more data structure access is required. */
		"MVTIPL		%1							\n" \

		/* Load the stack pointer of the task that is now selected as the Running
		state task from its TCB. */
		"MOV.L		#_pxCurrentTCB,R15			\n" \
		"MOV.L		[ R15 ], R15				\n" \
		"MOV.L		[ R15 ], R0					\n" \

		/* Restore the context of the new task.  The PSW (Program Status Word) and
		PC will be popped by the RTE instruction. */
		"POP		R15							\n" \
		"MVTACLO 	R15							\n" \
		"POP		R15							\n" \
		"MVTACHI 	R15							\n" \
		"POP		R15							\n" \
		"MVTC		R15, FPSW					\n" \
		"POPM		R1-R15						\n" \
		"RTE									\n" \
		"NOP									\n" \
		"NOP									  "
		:: "i"(configMAX_SYSCALL_INTERRUPT_PRIORITY), "i"(configKERNEL_INTERRUPT_PRIORITY)
	);
}
/*-----------------------------------------------------------*/

void vTickISR( void )
{
	/* Re-enabled interrupts. */
	__asm volatile( "SETPSW	I" );

	/* Increment the tick, and perform any processing the new tick value
	necessitates.  Ensure IPL is at the max syscall value first. */
	portDISABLE_INTERRUPTS_FROM_KERNEL_ISR();
	{
		if( xTaskIncrementTick() != pdFALSE )
		{
			taskYIELD();
		}
	}
	portENABLE_INTERRUPTS_FROM_KERNEL_ISR();
}
/*-----------------------------------------------------------*/

uint32_t ulPortGetIPL( void )
{
	__asm volatile
	(
		"MVFC	PSW, R1			\n"	\
		"SHLR	#24, R1			\n"	\
		"RTS					  "
	);

	/* This will never get executed, but keeps the compiler from complaining. */
	return 0;
}
/*-----------------------------------------------------------*/

void vPortSetIPL( uint32_t ulNewIPL )
{
	__asm volatile
	(
		"PUSH	R5				\n" \
		"MVFC	PSW, R5			\n"	\
		"SHLL	#24, R1			\n" \
		"AND	#-0F000001H, R5 \n" \
		"OR		R1, R5			\n" \
		"MVTC	R5, PSW			\n" \
		"POP	R5				\n" \
		"RTS					  "
	 );
}
