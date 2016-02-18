/*
    FreeRTOS V9.0.0rc1 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

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

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the ARM CM4F port.
 *----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Constants required to manipulate the NVIC. */
#define portNVIC_SYSTICK_CTRL		( ( volatile uint32_t * ) 0xe000e010 )
#define portNVIC_SYSTICK_LOAD		( ( volatile uint32_t * ) 0xe000e014 )
#define portNVIC_SYSPRI2			( ( volatile uint32_t * ) 0xe000ed20 )
#define portNVIC_SYSTICK_CLK		0x00000004
#define portNVIC_SYSTICK_INT		0x00000002
#define portNVIC_SYSTICK_ENABLE		0x00000001
#define portNVIC_PENDSV_PRI			( ( ( uint32_t ) configKERNEL_INTERRUPT_PRIORITY ) << 16 )
#define portNVIC_SYSTICK_PRI		( ( ( uint32_t ) configKERNEL_INTERRUPT_PRIORITY ) << 24 )

/* Masks off all bits but the VECTACTIVE bits in the ICSR register. */
#define portVECTACTIVE_MASK			( 0xFFUL )

/* Constants required to manipulate the VFP. */
#define portFPCCR					( ( volatile uint32_t * ) 0xe000ef34 ) /* Floating point context control register. */
#define portASPEN_AND_LSPEN_BITS	( 0x3UL << 30UL )

/* Constants required to set up the initial stack. */
#define portINITIAL_XPSR			( 0x01000000 )
#define portINITIAL_EXEC_RETURN		( 0xfffffffd )

/* Let the user override the pre-loading of the initial LR with the address of
prvTaskExitError() in case it messes up unwinding of the stack in the
debugger. */
#ifdef configTASK_RETURN_ADDRESS
	#define portTASK_RETURN_ADDRESS	configTASK_RETURN_ADDRESS
#else
	#define portTASK_RETURN_ADDRESS	prvTaskExitError
#endif

/* The priority used by the kernel is assigned to a variable to make access
from inline assembler easier. */
const uint32_t ulKernelPriority = configKERNEL_INTERRUPT_PRIORITY;

/* Each task maintains its own interrupt status in the critical nesting
variable. */
static uint32_t ulCriticalNesting = 0xaaaaaaaaUL;

/*
 * Setup the timer to generate the tick interrupts.
 */
static void prvSetupTimerInterrupt( void );

/*
 * Exception handlers.
 */
void SysTick_Handler( void );

/*
 * Functions defined in port_asm.asm.
 */
extern void vPortEnableVFP( void );
extern void vPortStartFirstTask( void );

/*
 * Used to catch tasks that attempt to return from their implementing function.
 */
static void prvTaskExitError( void );

/* This exists purely to allow the const to be used from within the
port_asm.asm assembly file. */
const uint32_t ulMaxSyscallInterruptPriorityConst = configMAX_SYSCALL_INTERRUPT_PRIORITY;

/*-----------------------------------------------------------*/

/*
 * See header file for description.
 */
StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{
	/* Simulate the stack frame as it would be created by a context switch
	interrupt. */

	/* Offset added to account for the way the MCU uses the stack on entry/exit
	of interrupts, and to ensure alignment. */
	pxTopOfStack--;

	*pxTopOfStack = portINITIAL_XPSR;	/* xPSR */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) pxCode;	/* PC */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) portTASK_RETURN_ADDRESS;	/* LR */

	/* Save code space by skipping register initialisation. */
	pxTopOfStack -= 5;	/* R12, R3, R2 and R1. */
	*pxTopOfStack = ( StackType_t ) pvParameters;	/* R0 */

	/* A save method is being used that requires each task to maintain its
	own exec return value. */
	pxTopOfStack--;
	*pxTopOfStack = portINITIAL_EXEC_RETURN;

	pxTopOfStack -= 8;	/* R11, R10, R9, R8, R7, R6, R5 and R4. */

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

static void prvTaskExitError( void )
{
	/* A function that implements a task must not exit or attempt to return to
	its caller as there is nothing to return to.  If a task wants to exit it
	should instead call vTaskDelete( NULL ).

	Artificially force an assert() to be triggered if configASSERT() is
	defined, then stop here so application writers can catch the error. */
	configASSERT( ulCriticalNesting == ~0UL );
	portDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

/*
 * See header file for description.
 */
BaseType_t xPortStartScheduler( void )
{
	/* configMAX_SYSCALL_INTERRUPT_PRIORITY must not be set to 0.
	See http://www.FreeRTOS.org/RTOS-Cortex-M3-M4.html */
	configASSERT( ( configMAX_SYSCALL_INTERRUPT_PRIORITY ) );

	/* Make PendSV and SysTick the lowest priority interrupts. */
	*(portNVIC_SYSPRI2) |= portNVIC_PENDSV_PRI;
	*(portNVIC_SYSPRI2) |= portNVIC_SYSTICK_PRI;

	/* Start the timer that generates the tick ISR.  Interrupts are disabled
	here already. */
	prvSetupTimerInterrupt();

	/* Initialise the critical nesting count ready for the first task. */
	ulCriticalNesting = 0;

	/* Ensure the VFP is enabled - it should be anyway. */
	vPortEnableVFP();

	/* Lazy save always. */
	*( portFPCCR ) |= portASPEN_AND_LSPEN_BITS;

	/* Start the first task. */
	vPortStartFirstTask();

	/* Should not get here! */
	return 0;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Not implemented in ports where there is nothing to return to.
	Artificially force an assert. */
	configASSERT( ulCriticalNesting == 1000UL );
}
/*-----------------------------------------------------------*/

void vPortYield( void )
{
	/* Set a PendSV to request a context switch. */
	*(portNVIC_INT_CTRL) = portNVIC_PENDSVSET;

	/* Barriers are normally not required but do ensure the code is completely
	within the specified behaviour for the architecture. */
	__DSB();
	__ISB();
}
/*-----------------------------------------------------------*/

void vPortEnterCritical( void )
{
	portDISABLE_INTERRUPTS();
	ulCriticalNesting++;
	__DSB();
	__ISB();

	/* This is not the interrupt safe version of the enter critical function so
	assert() if it is being called from an interrupt context.  Only API
	functions that end in "FromISR" can be used in an interrupt.  Only assert if
	the critical nesting count is 1 to protect against recursive calls if the
	assert function also uses a critical section. */
	if( ulCriticalNesting == 1 )
	{
		configASSERT( ( ( *(portNVIC_INT_CTRL) ) & portVECTACTIVE_MASK ) == 0 );
	}
}
/*-----------------------------------------------------------*/

void vPortExitCritical( void )
{
	configASSERT( ulCriticalNesting );
	ulCriticalNesting--;
	if( ulCriticalNesting == 0 )
	{
		portENABLE_INTERRUPTS();
	}
}
/*-----------------------------------------------------------*/

void SysTick_Handler( void )
{
uint32_t ulDummy;

	ulDummy = portSET_INTERRUPT_MASK_FROM_ISR();
	{
		if( xTaskIncrementTick() != pdFALSE )
		{
			/* Pend a context switch. */
			*(portNVIC_INT_CTRL) = portNVIC_PENDSVSET;
		}
	}
	portCLEAR_INTERRUPT_MASK_FROM_ISR( ulDummy );
}
/*-----------------------------------------------------------*/

/*
 * Setup the systick timer to generate the tick interrupts at the required
 * frequency.
 */
void prvSetupTimerInterrupt( void )
{
	/* Configure SysTick to interrupt at the requested rate. */
	*(portNVIC_SYSTICK_LOAD) = ( configCPU_CLOCK_HZ / configTICK_RATE_HZ ) - 1UL;
	*(portNVIC_SYSTICK_CTRL) = portNVIC_SYSTICK_CLK | portNVIC_SYSTICK_INT | portNVIC_SYSTICK_ENABLE;
}
/*-----------------------------------------------------------*/

