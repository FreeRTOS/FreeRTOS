/*
    FreeRTOS V8.0.0:rc1 - Copyright (C) 2014 Real Time Engineers Ltd. 
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

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

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

/*
	NOTE : Tasks run in System mode and the scheduler runs in Supervisor mode.
	The processor MUST be in supervisor mode when vTaskStartScheduler is
	called.  The demo applications included in the FreeRTOS.org download switch
	to supervisor mode prior to main being called.  If you are not using one of
	these demo application projects then ensure Supervisor mode is used.
*/

/*
 * This demo includes a (basic) USB mouse driver and a WEB server.  It is
 * targeted for the AT91SAM7X EK prototyping board which includes a small
 * joystick to provide the mouse inputs.  The WEB interface provides some basic
 * interactivity through the use of a check box to turn on and off an LED.
 *
 * main() creates the WEB server, USB, and a set of the standard demo tasks
 * before starting the scheduler.  See the online FreeRTOS.org documentation 
 * for more information on the standard demo tasks.  
 *
 * LEDs D1 to D3 are controlled by the standard 'flash' tasks - each will 
 * toggle at a different fixed frequency.
 *
 * A tick hook function is used to monitor the standard demo tasks - with LED
 * D4 being used to indicate the system status.  D4 toggling every 5 seconds
 * indicates that all the standard demo tasks are executing without error.  The
 * toggle rate increasing to 500ms is indicative of an error having been found
 * in at least one demo task.
 *
 * See the online documentation page that accompanies this demo for full setup
 * and usage information.
 */

/* Standard includes. */
#include <stdlib.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo application includes. */
#include "partest.h"
#include "USBSample.h"
#include "uIP_Task.h"
#include "BlockQ.h"
#include "blocktim.h"
#include "flash.h"
#include "QPeek.h"
#include "dynamic.h"

/* Priorities for the demo application tasks. */
#define mainUIP_PRIORITY					( tskIDLE_PRIORITY + 2 )
#define mainUSB_PRIORITY					( tskIDLE_PRIORITY + 2 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainFLASH_PRIORITY                  ( tskIDLE_PRIORITY + 2 )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY ) 

/* The task allocated to the uIP task is large to account for its use of the
sprintf() library function.  Use of a cut down printf() library would allow
the stack usage to be greatly reduced. */
#define mainUIP_TASK_STACK_SIZE		( configMINIMAL_STACK_SIZE * 6 )

/* The LED toggle by the tick hook should an error have been found in a task. */
#define mainERROR_LED						( 3 )

/*-----------------------------------------------------------*/

/*
 * Configure the processor for use with the Atmel demo board.  Setup is minimal
 * as the low level init function (called from the startup asm file) takes care
 * of most things.
 */
static void prvSetupHardware( void );

/*-----------------------------------------------------------*/

/*
 * Starts all the other tasks, then starts the scheduler.
 */
int main( void )
{
	/* Setup any hardware that has not already been configured by the low
	level init routines. */
	prvSetupHardware();

	/* Start the task that handles the TCP/IP and WEB server functionality. */
    xTaskCreate( vuIP_Task, "uIP", mainUIP_TASK_STACK_SIZE, NULL, mainUIP_PRIORITY, NULL );
	
	/* Also start the USB demo which is just for the SAM7. */
    vStartUSBTask( mainUSB_PRIORITY );
	
	/* Start the standard demo tasks. */
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
    vCreateBlockTimeTasks();
    vStartLEDFlashTasks( mainFLASH_PRIORITY );
    vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
    vStartQueuePeekTasks();   
    vStartDynamicPriorityTasks();

	/* Start the scheduler.

	NOTE : Tasks run in system mode and the scheduler runs in Supervisor mode.
	The processor MUST be in supervisor mode when vTaskStartScheduler is
	called.  The demo applications included in the FreeRTOS.org download switch
	to supervisor mode prior to main being called.  If you are not using one of
	these demo application projects then ensure Supervisor mode is used here. */

	vTaskStartScheduler();

	/* We should never get here as control is now taken by the scheduler. */
  	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	portDISABLE_INTERRUPTS();
	
	/* When using the JTAG debugger the hardware is not always initialised to
	the correct default state.  This line just ensures that this does not
	cause all interrupts to be masked at the start. */
	AT91C_BASE_AIC->AIC_EOICR = 0;
	
	/* Most setup is performed by the low level init function called from the
	startup asm file. */

	/* Enable the peripheral clock. */
    AT91C_BASE_PMC->PMC_PCER = 1 << AT91C_ID_PIOA;
    AT91C_BASE_PMC->PMC_PCER = 1 << AT91C_ID_PIOB;
	AT91C_BASE_PMC->PMC_PCER = 1 << AT91C_ID_EMAC;

	/* Initialise the LED outputs for use by the demo application tasks. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
static unsigned long ulCallCount = 0, ulErrorFound = pdFALSE;

/* The rate at which LED D4 will toggle if an error has been found in one or 
more of the standard demo tasks. */
const unsigned long ulErrorFlashRate = 500 / portTICK_RATE_MS;

/* The rate at which LED D4 will toggle if no errors have been found in any
of the standard demo tasks. */
const unsigned long ulNoErrorCheckRate = 5000 / portTICK_RATE_MS;

	ulCallCount++;

	if( ulErrorFound != pdFALSE )
	{
		/* We have already found an error, so flash the LED with the appropriate
		frequency. */
		if( ulCallCount > ulErrorFlashRate )
		{
			ulCallCount = 0;
			vParTestToggleLED( mainERROR_LED );
		}
	}
	else
	{
		if( ulCallCount > ulNoErrorCheckRate )
		{
			ulCallCount = 0;
			
			/* We have not yet found an error.  Check all the demo tasks to ensure
			this is still the case. */
			
			if( xAreBlockingQueuesStillRunning() != pdTRUE )
			{
				ulErrorFound |= 0x01;
			}
			
			if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
			{
				ulErrorFound |= 0x02;
			}
	
			if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
			{
				ulErrorFound |= 0x04;
			}
			
			if( xAreGenericQueueTasksStillRunning() != pdTRUE )
			{
				ulErrorFound |= 0x08;
			}
			
			if( xAreQueuePeekTasksStillRunning() != pdTRUE )
			{
				ulErrorFound |= 0x10;
			}
			
			vParTestToggleLED( mainERROR_LED );
		}
	}
}




