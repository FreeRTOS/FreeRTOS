/*
 * FreeRTOS V202112.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/* Standard includes. */
#include <stdio.h>
#include <stdint.h>

/* FreeRTOS includes. */
#include <FreeRTOS.h>
#include "task.h"

/* This application is using the FreeRTOS Windows simulator, which uses the
FreeRTOS scheduler to schedule FreeRTOS task within the Windows environment.
The Windows environment must not be allowed to block any Windows threads that
are running FreeRTOS tasks, unless the FreeRTOS task is running at the FreeRTOS
idle priority.  For simplicity, this demo uses the Windows TCP/IP stack, the
API for which can cause Windows threads to block.  Therefore, any FreeRTOS task
that makes calls to the Windows TCP/IP stack must be assigned the idle priority.
Note this is only a restriction of the simulated Windows environment - real
FreeRTOS ports do not have this restriction. */
#define mainSECURE_SERVER_TASK_PRIORITY		( tskIDLE_PRIORITY )


/*-----------------------------------------------------------*/

/*
 * The task that implements the server side.
 */
extern void vSecureTCPServerTask( void *pvParameters );

/*-----------------------------------------------------------*/

/*
 *! It is necessary to update the build hash before running this project for the
 *! time.  Ensure to read README_wolfSSL_FIPS_ready.md in the directory that contains
 *! this Visual Studio project for instructions.
 */
int main( void )
{
const uint32_t ulLongTime_ms = 250UL;

	/* Create the TCP server task.  This will itself create the client task
	once it has completed the wolfSSL initialisation. */
	xTaskCreate( vSecureTCPServerTask, "Server", configMINIMAL_STACK_SIZE, NULL, mainSECURE_SERVER_TASK_PRIORITY, NULL );

	/* Start the task running. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following
	line will never be reached.  If the following line does execute, then
	there was insufficient FreeRTOS heap memory available for the idle and/or
	timer tasks	to be created.  See the memory management section on the
	FreeRTOS web site for more details (this is standard text that is not
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

	/* This function is called on each cycle of the idle task if
	configUSE_IDLE_HOOK is set to 1 in FreeRTOSConfig.h.  Sleep to reduce CPU
	load. */
	Sleep( ulMSToSleep );
}
/*-----------------------------------------------------------*/

void vAssertCalled( void )
{
const unsigned long ulLongSleep = 1000UL;

	taskDISABLE_INTERRUPTS();
	for( ;; )
	{
		/* Cause debugger break point if being debugged.

		If you see reach here and the console shows "In core integrity check error"
		then you have not updated the expected build hash since building this
		project.  See README_wolfSSL_FIPS_ready.md in the directory that contains
		this Visual Studio project for instructions. */
		__debugbreak();

		Sleep( ulLongSleep );
	}
}
/*-----------------------------------------------------------*/

