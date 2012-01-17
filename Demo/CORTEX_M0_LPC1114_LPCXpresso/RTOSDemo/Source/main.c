/*
    FreeRTOS V7.1.0 - Copyright (C) 2011 Real Time Engineers Ltd.


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

/* Standard includes. */
#include "string.h"

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"

/* Common demo includes. */
#include "dynamic.h"
#include "blocktim.h"
#include "countsem.h"
#include "GenQTest.h"
#include "recmutex.h"
#include "IntQueue.h"

/* Hardware specific includes. */
#include "lpc11xx.h"

/* The bit on port 0 to which the LED is wired. */
#define mainLED_BIT		( 1UL << 7UL )

/* The period after which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_RATE_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_RATE_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_RATE_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_RATE_MS )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0UL )

#define mainCHECK_INTERRUPT_STACK			1

#if mainCHECK_INTERRUPT_STACK == 1
	const unsigned char ucExpectedInterruptStackValues[] = { 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC, 0xCC };
#endif

/*-----------------------------------------------------------*/

/*
 * Register check tasks, as described at the top of this file.  The nature of
 * these files necessitates that they are written in an assembly file.
 */
extern void vRegTest1Task( void *pvParameters );
extern void vRegTest2Task( void *pvParameters );

/*
 * Perform any application specific hardware configuration.  The clocks,
 * memory, etc. are configured before main() is called.
 */
static void prvSetupHardware( void );

/*
 * The hardware only has a single LED.  Simply toggle it.
 */
static void prvToggleLED( void );

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( xTimerHandle xTimer );

/*-----------------------------------------------------------*/

/* The GPIO port to which the LED is attached. */
static LPC_GPIO_TypeDef * const xGPIO0 = LPC_GPIO0;

/* The following two variables are used to communicate the status of the
register check tasks to the check software timer.  If the variables keep
incrementing, then the register check tasks has not discovered any errors.  If
a variable stops incrementing, then an error has been found. */
volatile unsigned long ulRegTest1LoopCounter = 0UL, ulRegTest2LoopCounter = 0UL;

/*-----------------------------------------------------------*/

int main( void )
{
xTimerHandle xCheckTimer = NULL;

	prvSetupHardware();

	/* Create the standard demo tasks. */
//	vStartDynamicPriorityTasks();
//	vCreateBlockTimeTasks();
//	vStartCountingSemaphoreTasks();
//	vStartGenericQueueTasks( tskIDLE_PRIORITY );
//	vStartRecursiveMutexTasks();
	vStartInterruptQueueTasks();

	/* Create the register test tasks as described at the top of this file. */
	xTaskCreate( 	vRegTest1Task,			/* Function that implements the task. */
					( signed char * ) "Reg1", /* Text name of the task. */
					configMINIMAL_STACK_SIZE, /* Stack allocated to the task. */
					NULL, 					/* The task parameter is not used. */
					tskIDLE_PRIORITY, 		/* The priority to assign to the task. */
					NULL );					/* Don't receive a handle back, it is not needed. */

	xTaskCreate( 	vRegTest2Task,			/* Function that implements the task. */
					( signed char * ) "Reg2", /* Text name of the task. */
					configMINIMAL_STACK_SIZE, /* Stack allocated to the task. */
					NULL, 					/* The task parameter is not used. */
					tskIDLE_PRIORITY, 		/* The priority to assign to the task. */
					NULL );					/* Don't receive a handle back, it is not needed. */

	/* Create the software timer that performs the 'check' functionality,
	as described at the top of this file. */
	xCheckTimer = xTimerCreate( ( const signed char * ) "CheckTimer",/* A text name, purely to help debugging. */
								( mainCHECK_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
								pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) 0,						/* The ID is not used, so can be set to anything. */
								prvCheckTimerCallback				/* The callback function that inspects the status of all the other tasks. */
							  );

	if( xCheckTimer != NULL )
	{
		xTimerStart( xCheckTimer, mainDONT_BLOCK );
	}

	/* Start the kernel.  From here on, only tasks and interrupts will run. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following
	line will never be reached.  If the following line does execute, then there
	was	insufficient FreeRTOS heap memory available for the idle and/or timer
	tasks to be created.  See the memory management section on the FreeRTOS web
	site, or the FreeRTOS tutorial books for more details. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTimerCallback( xTimerHandle xTimer )
{
static long lChangedTimerPeriodAlready = pdFALSE;
static unsigned long ulLastRegTest1Value = 0, ulLastRegTest2Value = 0;
unsigned long ulErrorFound = pdFALSE;

	/* Check all the demo and test tasks to ensure that they are all still
	running, and that none have detected an error. */
	if( xAreIntQueueTasksStillRunning() != pdPASS )
	{
		ulErrorFound |= ( 0x01UL << 0UL );
	}

	/* Check that the register test 1 task is still running. */
	if( ulLastRegTest1Value == ulRegTest1LoopCounter )
	{
		ulErrorFound |= ( 0x01UL << 10UL );
	}
	ulLastRegTest1Value = ulRegTest1LoopCounter;

	/* Check that the register test 2 task is still running. */
	if( ulLastRegTest2Value == ulRegTest2LoopCounter )
	{
		ulErrorFound |= ( 0x01UL << 11UL );
	}
	ulLastRegTest2Value = ulRegTest2LoopCounter;

	/* Toggle the check LED to give an indication of the system status.  If
	the LED toggles every mainCHECK_TIMER_PERIOD_MS milliseconds then
	everything is ok.  A faster toggle indicates an error. */
	prvToggleLED();

	/* Have any errors been latched in ulErrorFound?  If so, shorten the
	period of the check timer to mainERROR_CHECK_TIMER_PERIOD_MS milliseconds.
	This will result in an increase in the rate at which mainCHECK_LED
	toggles. */
	if( ulErrorFound != pdFALSE )
	{
		if( lChangedTimerPeriodAlready == pdFALSE )
		{
			lChangedTimerPeriodAlready = pdTRUE;

			/* This call to xTimerChangePeriod() uses a zero block time.
			Functions called from inside of a timer callback function must
			*never* attempt	to block. */
			xTimerChangePeriod( xTimer, ( mainERROR_CHECK_TIMER_PERIOD_MS ), mainDONT_BLOCK );
		}
	}
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

static void prvToggleLED( void )
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

void vApplicationStackOverflowHook( xTaskHandle pxTask, signed char *pcTaskName )
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





