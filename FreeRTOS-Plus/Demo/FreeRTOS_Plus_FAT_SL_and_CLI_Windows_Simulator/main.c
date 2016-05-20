/*
    FreeRTOS V9.0.0 - Copyright (C) 2016 Real Time Engineers Ltd.
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
 *
 * This demo is described on the following web page:
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT_SL/Demos/File_System_Win32_Simulator_demo.shtml
 *
 ******************************************************************************/

/* Standard includes. */
#include <stdio.h>
#include <stdint.h>

/* FreeRTOS includes. */
#include <FreeRTOS.h>
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* File system includes. */
#include "config_fat_sl.h"

/* Priorities at which the tasks are created. */
#define mainUDP_CLI_TASK_PRIORITY			( tskIDLE_PRIORITY )

/*-----------------------------------------------------------*/

/*
 * Register the generic commands that can be used with FreeRTOS+CLI.
 */
extern void vRegisterSampleCLICommands( void );

/*
 * Register the file system commands that can be used with FreeRTOS+CLI.
 */
extern void vRegisterFileSystemCLICommands( void );

/*
 * The task that implements the UDP command interpreter using FreeRTOS+CLI.
 */
extern void vUDPCommandInterpreterTask( void *pvParameters );

/*
 * Creates and verifies different files on the volume, demonstrating the use of
 * various different API functions.
 */
extern void vCreateAndVerifySampleFiles( void );

/*-----------------------------------------------------------*/

/******************************************************************************
 *
 * This demo is described on the following web page:
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT_SL/Demos/File_System_Win32_Simulator_demo.shtml
 *
 ******************************************************************************/

int main( void )
{
const uint32_t ulLongTime_ms = 250UL;

	/* If the file system is only going to be accessed from one task then
	F_FS_THREAD_AWARE can be set to 0 and the set of example files are created
	before the RTOS scheduler is started.  If the file system is going to be
	access from more than one task then F_FS_THREAD_AWARE must be set to 1 and
	the	set of sample files are created from the idle task hook function
	vApplicationIdleHook() - which is defined in this file. */
	#if F_FS_THREAD_AWARE == 0
	{
		/* Initialise the drive and file system, then create a few example
		files.  The output from this function just goes to the stdout window,
		allowing the output to be viewed when the UDP command console is not
		connected. */
		vCreateAndVerifySampleFiles();
	}
	#endif

	/* Register generic commands with the FreeRTOS+CLI command interpreter. */
	vRegisterSampleCLICommands();

	/* Register file system related commands with the FreeRTOS+CLI command
	interpreter. */
	vRegisterFileSystemCLICommands();

	/* Create the task that handles the CLI on a UDP port.  The port number
	is set using the configUDP_CLI_PORT_NUMBER setting in FreeRTOSConfig.h. */
	xTaskCreate( vUDPCommandInterpreterTask, 	/* The function that implements the command interpreter IO handling. */
				"CLI", 							/* The name of the task - just to assist debugging. */
				configMINIMAL_STACK_SIZE, NULL, /* The size of the stack allocated to the task. */
				mainUDP_CLI_TASK_PRIORITY, 		/* The priority at which the task will run. */
				NULL );							/* A handle to the task is not required, so NULL is passed. */

	/* Start the RTOS scheduler. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following
	line will never be reached.  If the following line does execute, then
	there was insufficient FreeRTOS heap memory available for the idle and/or
	timer tasks	to be created.  See the memory management section on the
	FreeRTOS web site for more details (this is standard text that is not not
	really applicable to the Win32 simulator port). */
	for( ;; )
	{
		Sleep( ulLongTime_ms );
	}
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
const unsigned long ulMSToSleep = 5;

	/* If the file system is only going to be accessed from one task then
	F_FS_THREAD_AWARE can be set to 0 and the set of example files is created
	before the RTOS scheduler is started.  If the file system is going to be
	access from more than one task then F_FS_THREAD_AWARE must be set to 1 and
	the	set of sample files are created from the idle task hook function. */
	#if F_FS_THREAD_AWARE == 1
	{
		static BaseType_t xCreatedSampleFiles = pdFALSE;

		/* Initialise the drive and file system, then create a few example
		files.  The output from this function just goes to the stdout window,
		allowing the output to be viewed when the UDP command console is not
		connected. */
		if( xCreatedSampleFiles == pdFALSE )
		{
			vCreateAndVerifySampleFiles();
			xCreatedSampleFiles = pdTRUE;
		}
	}
	#endif

	/* This function is called on each cycle of the idle task if
	configUSE_IDLE_HOOK is set to 1 in FreeRTOSConfig.h.  Sleep to reduce CPU
	load. */
	Sleep( ulMSToSleep );
}
/*-----------------------------------------------------------*/

void vAssertCalled( const char *pcFile, unsigned long ulLine )
{
	printf( "ASSERT FAILED: File %s, line %u\r\n", pcFile, ulLine );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* vApplicationMallocFailedHook() will only be called if
	configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	function that will get called if a call to pvPortMalloc() fails.
	pvPortMalloc() is called internally by the kernel whenever a task, queue,
	timer or semaphore is created.  It is also called by various parts of the
	demo application.  If heap_1.c, heap_2.c or heap_4.c are used, then the
	size of the heap available to pvPortMalloc() is defined by
	configTOTAL_HEAP_SIZE in FreeRTOSConfig.h, and the xPortGetFreeHeapSize()
	API function can be used to query the size of free heap space that remains
	(although it does not provide information on how the remaining heap might
	be fragmented). */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}



