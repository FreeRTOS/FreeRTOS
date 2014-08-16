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

/******************************************************************************
 * This project provides two demo applications.  A simple blinky style project,
 * and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting (defined in this file) is used to
 * select between the two.  The simply blinky demo is implemented and described
 * in main_blinky.c.  The more comprehensive test and demo application is
 * implemented and described in main_full.c.
 *
 * This file implements the code that is not demo specific, including the
 * hardware setup and FreeRTOS hook functions.  It also contains a dummy
 * interrupt service routine called Dummy_IRQHandler() that is provided as an
 * example of how to use interrupt safe FreeRTOS API functions (those that end
 * in "FromISR").
 *
 *****************************************************************************/

/* Standard includes. */
#include "string.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Hardware specific includes. */
#include "lpc11xx.h"

/* Set mainCREATE_SIMPLE_BLINKY_DEMO_ONLY to one to run the simple blinky demo,
or 0 to run the more comprehensive test and demo application. */
#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY	0

/* The bit on port 0 to which the LED is wired. */
#define mainLED_BIT		( 1UL << 7UL )

/* The configCHECK_FOR_STACK_OVERFLOW setting in FreeRTOSConifg can be used to
check task stacks for overflows.  It does not however check the stack used by
interrupts.  This demo has a simple addition that will also check the stack used
by interrupts if mainCHECK_INTERRUPT_STACK is set to 1.  Note that this check is
only performed from the tick hook function (which runs in an interrupt context).
It is a good debugging aid - but won't catch interrupt stack problems until the
tick interrupt next executes. */
#define mainCHECK_INTERRUPT_STACK			1
#if mainCHECK_INTERRUPT_STACK == 1
	const unsigned char ucExpectedInterruptStackValues[] = { 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC };
#endif

/*-----------------------------------------------------------*/

/*
 * Perform any application specific hardware configuration.  The clocks,
 * memory, etc. are configured before main() is called.
 */
static void prvSetupHardware( void );

/*
 * The hardware only has a single LED.  Simply toggle it.
 */
void vMainToggleLED( void );

/* main_blinky() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 1.
main_full() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0. */
void main_blinky( void );
void main_full( void );

/*-----------------------------------------------------------*/

/* The GPIO port to which the LED is attached. */
static LPC_GPIO_TypeDef * const xGPIO0 = LPC_GPIO0;

/*-----------------------------------------------------------*/
int main( void )
{
	/* Prepare the hardware to run this demo. */
	prvSetupHardware();

	/* The mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting is described at the top
	of this file. */
	#if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1
	{
		main_blinky();
	}
	#else
	{
		main_full();
	}
	#endif

	return 0;
}
/*-----------------------------------------------------------*/

void vMainToggleLED( void )
{
static unsigned long ulLEDState = 0UL;

	if( ulLEDState == 0UL )
	{
		xGPIO0->MASKED_ACCESS[ mainLED_BIT ] = 0UL;
	}
	else
	{
		xGPIO0->MASKED_ACCESS[ mainLED_BIT ] = mainLED_BIT;
	}

	ulLEDState = !ulLEDState;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
extern unsigned long _vStackTop[], _pvHeapStart[];
unsigned long ulInterruptStackSize;

	/* Enable AHB clock for GPIO. */
	LPC_SYSCON->SYSAHBCLKCTRL |= ( 1 << 6 );

	/* Configure GPIO for LED output. */
	xGPIO0->DIR |= mainLED_BIT;

	/* The size of the stack used by main and interrupts is not defined in
	the linker, but just uses whatever RAM is left.  Calculate the amount of
	RAM available for the main/interrupt/system stack, and check it against
	a reasonable number.  If this assert is hit then it is likely you don't
	have enough stack to start the kernel, or to allow interrupts to nest.
	Note - this is separate to the stacks that are used by tasks.  The stacks
	that are used by tasks are automatically checked if
	configCHECK_FOR_STACK_OVERFLOW is not 0 in FreeRTOSConfig.h - but the stack
	used by interrupts is not.  Reducing the conifgTOTAL_HEAP_SIZE setting will
	increase the stack available to main() and interrupts. */
	ulInterruptStackSize = ( ( unsigned long ) _vStackTop ) - ( ( unsigned long ) _pvHeapStart );
	configASSERT( ulInterruptStackSize > 350UL );

	/* Fill the stack used by main() and interrupts to a known value, so its
	use can be manually checked. */
	memcpy( ( void * ) _pvHeapStart, ucExpectedInterruptStackValues, sizeof( ucExpectedInterruptStackValues ) );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* vApplicationMallocFailedHook() will only be called if
	configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	function that will get called if a call to pvPortMalloc() fails.
	pvPortMalloc() is called internally by the kernel whenever a task, queue,
	timer or semaphore is created.  It is also called by various parts of the
	demo application.  If heap_1.c or heap_2.c are used, then the size of the
	heap available to pvPortMalloc() is defined by configTOTAL_HEAP_SIZE in
	FreeRTOSConfig.h, and the xPortGetFreeHeapSize() API function can be used
	to query the size of free heap space that remains (although it does not
	provide information on how the remaining heap might be fragmented). */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set
	to 1 in FreeRTOSConfig.h.  It will be called on each iteration of the idle
	task.  It is essential that code added to this hook function never attempts
	to block in any way (for example, call xQueueReceive() with a block time
	specified, or call vTaskDelay()).  If the application makes use of the
	vTaskDelete() API function (as this demo application does) then it is also
	important that vApplicationIdleHook() is permitted to return to its calling
	function, because it is the responsibility of the idle task to clean up
	memory allocated by the kernel to any task that has since been deleted. */
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
#if mainCHECK_INTERRUPT_STACK == 1
extern unsigned long _pvHeapStart[];

	/* This function will be called by each tick interrupt if
	configUSE_TICK_HOOK is set to 1 in FreeRTOSConfig.h.  User code can be
	added here, but the tick hook is called from an interrupt context, so
	code must not attempt to block, and only the interrupt safe FreeRTOS API
	functions can be used (those that end in FromISR()). */

	/* Manually check the last few bytes of the interrupt stack to check they
	have not been overwritten.  Note - the task stacks are automatically
	checked for overflow if configCHECK_FOR_STACK_OVERFLOW is set to 1 or 2
	in FreeRTOSConifg.h, but the interrupt stack is not. */
	configASSERT( memcmp( ( void * ) _pvHeapStart, ucExpectedInterruptStackValues, sizeof( ucExpectedInterruptStackValues ) ) == 0U );
#endif /* mainCHECK_INTERRUPT_STACK */
}
/*-----------------------------------------------------------*/

#ifdef JUST_AN_EXAMPLE_ISR

void Dummy_IRQHandler(void)
{
long lHigherPriorityTaskWoken = pdFALSE;

	/* Clear the interrupt if necessary. */
	Dummy_ClearITPendingBit();

	/* This interrupt does nothing more than demonstrate how to synchronise a
	task with an interrupt.  A semaphore is used for this purpose.  Note
	lHigherPriorityTaskWoken is initialised to zero.  Only FreeRTOS API functions
	that end in "FromISR" can be called from an ISR. */
	xSemaphoreGiveFromISR( xTestSemaphore, &lHigherPriorityTaskWoken );

	/* If there was a task that was blocked on the semaphore, and giving the
	semaphore caused the task to unblock, and the unblocked task has a priority
	higher than the current Running state task (the task that this interrupt
	interrupted), then lHigherPriorityTaskWoken will have been set to pdTRUE
	internally within xSemaphoreGiveFromISR().  Passing pdTRUE into the
	portEND_SWITCHING_ISR() macro will result in a context switch being pended to
	ensure this interrupt returns directly to the unblocked, higher priority,
	task.  Passing pdFALSE into portEND_SWITCHING_ISR() has no effect. */
	portEND_SWITCHING_ISR( lHigherPriorityTaskWoken );
}

#endif /* JUST_AN_EXAMPLE_ISR */




