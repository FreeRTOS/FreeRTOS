/*
    FreeRTOS V8.2.3 - Copyright (C) 2015 Real Time Engineers Ltd.
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

/******************************************************************************
 * This project provides two demo applications.  A simple blinky style project
 * that demonstrates low power tickless functionality, and a more comprehensive
 * test and demo application.  The configCREATE_LOW_POWER_DEMO setting, which is
 * defined in FreeRTOSConfig.h, is used to select between the two, and to select
 * the clock used when demonstrating tickless functionality.
 *
 * The simply blinky low power demo is implemented and described in
 * main_low_power.c.  The more comprehensive test and demo application is
 * implemented and described in main_full.c.
 *
 * This file implements the code that is not demo specific, including the
 * hardware setup and standard FreeRTOS hook functions.
 *
 * ENSURE TO READ THE DOCUMENTATION PAGE FOR THIS PORT AND DEMO APPLICATION ON
 * THE http://www.FreeRTOS.org WEB SITE FOR FULL INFORMATION ON USING THIS DEMO
 * APPLICATION, AND ITS ASSOCIATE FreeRTOS ARCHITECTURE PORT!
 *
 */

#warning Check the tick suppression routine in the case where the system unblocks before an entire tick period has expired.

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* SiLabs includes. */
#include "em_chip.h"
#include "bsp.h"
#include "bsp_trace.h"
#include "sleep.h"

/* Set mainCREATE_LOW_POWER_DEMO to one to run the simple blinky demo, or 0 to
run the more comprehensive test and demo application. */
#define mainCREATE_LOW_POWER_DEMO	0

/*-----------------------------------------------------------*/

/*
 * Configure the hardware as necessary to run this demo.
 */
static void prvSetupHardware( void );

/*
 * main_low_power() is used when configCREATE_LOW_POWER_DEMO is set to 1.
 * main_full() is used when configCREATE_LOW_POWER_DEMO is set to 0.
 */
#if( configCREATE_LOW_POWER_DEMO == 1 )
	extern void main_low_power( void );
#else
	extern void main_full( void );
#endif /* #if configCREATE_LOW_POWER_DEMO == 1 */

/* Prototypes for the standard FreeRTOS callback/hook functions implemented
within this file. */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );

/*-----------------------------------------------------------*/

int main( void )
{
	/* Configure the hardware ready to run the demo. */
	prvSetupHardware();

	/* The mainCREATE_LOW_POWER_DEMO setting is described at the top
	of this file. */
	#if( configCREATE_LOW_POWER_DEMO != 0 )
	{
		main_low_power();
	}
	#else
	{
		main_full();
	}
	#endif

	/* Should not get here. */
	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Library initialisation routines. */
	CHIP_Init();
	BSP_TraceProfilerSetup();
	SLEEP_Init( NULL, NULL );
	BSP_LedsInit();

	SLEEP_SleepBlockBegin( configENERGY_MODE );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues, software
	timers, and semaphores.  The size of the FreeRTOS heap is set by the
	configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h. */

	/* Force an assert. */
	configASSERT( ( volatile void * ) NULL );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */

	/* Force an assert. */
	configASSERT( ( volatile void * ) NULL );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
volatile size_t xFreeHeapSpace;

	/* This is just a trivial example of an idle hook.  It is called on each
	cycle of the idle task.  It must *NOT* attempt to block.  In this case the
	idle task just queries the amount of FreeRTOS heap that remains.  See the
	memory management section on the http://www.FreeRTOS.org web site for memory
	management options.  If there is a lot of heap memory free then the
	configTOTAL_HEAP_SIZE value in FreeRTOSConfig.h can be reduced to free up
	RAM. */
	xFreeHeapSpace = xPortGetFreeHeapSize();

	/* Remove compiler warning about xFreeHeapSpace being set but never used. */
	( void ) xFreeHeapSpace;
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	/* The full demo includes tests that run from the tick hook. */
	#if( configCREATE_LOW_POWER_DEMO == 0 )
	{
	extern void vFullDemoTickHook( void );

		/* Some of the tests and demo tasks executed by the full demo include
		interaction from an interrupt - for which the tick interrupt is used
		via the tick hook function. */
		vFullDemoTickHook();
	}
	#endif
}
/*-----------------------------------------------------------*/

void vApplicationGetIdleTaskMemory( StaticTask_t **ppxIdleTaskTCBBuffer, StackType_t **ppxIdleTaskStackBuffer, uint16_t *pusIdleTaskStackSize )
{
	/* configUSE_STATIC_ALLOCATION is set to 1, so the application has the
	opportunity to supply the buffers that will be used by the Idle task as its
	stack and to hold its TCB.  If these are set to NULL then the buffers will
	be allocated dynamically, just as if xTaskCreate() had been called. */
	*ppxIdleTaskTCBBuffer = NULL;
	*ppxIdleTaskStackBuffer = NULL;
	*pusIdleTaskStackSize = configMINIMAL_STACK_SIZE; /* In words.  NOT in bytes! */
}
/*-----------------------------------------------------------*/

void vApplicationGetTimerTaskMemory( StaticTask_t **ppxTimerTaskTCBBuffer, StackType_t **ppxTimerTaskStackBuffer, uint16_t *pusTimerTaskStackSize )
{
	/* configUSE_STATIC_ALLOCATION is set to 1, so the application has the
	opportunity to supply the buffers that will be used by the Timer/RTOS daemon
	task as its	stack and to hold its TCB.  If these are set to NULL then the
	buffers will be allocated dynamically, just as if xTaskCreate() had been
	called. */
	*ppxTimerTaskTCBBuffer = NULL;
	*ppxTimerTaskStackBuffer = NULL;
	*pusTimerTaskStackSize = configTIMER_TASK_STACK_DEPTH; /* In words.  NOT in bytes! */
}
/*-----------------------------------------------------------*/

