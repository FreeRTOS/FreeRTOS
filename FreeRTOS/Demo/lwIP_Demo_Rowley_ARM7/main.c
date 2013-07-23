/*
    FreeRTOS V7.5.1 - Copyright (C) 2013 Real Time Engineers Ltd.

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
	NOTE : Tasks run in system mode and the scheduler runs in Supervisor mode.
	The processor MUST be in supervisor mode when vTaskStartScheduler is 
	called.  The demo applications included in the FreeRTOS.org download switch
	to supervisor mode prior to main being called.  If you are not using one of
	these demo application projects then ensure Supervisor mode is used.
*/


/*
 * Creates all the application tasks, then starts the scheduler.
 *
 * A task defined by the function vBasicWEBServer is created.  This executes 
 * the lwIP stack and basic WEB server sample.  A task defined by the function
 * vUSBCDCTask.  This executes the USB to serial CDC example.  All the other 
 * tasks are from the set of standard demo tasks.  The WEB documentation 
 * provides more details of the standard demo application tasks.
 *
 * Main.c also creates a task called "Check".  This only executes every three
 * seconds but has the highest priority so is guaranteed to get processor time.
 * Its main function is to check the status of all the other demo application
 * tasks.  LED mainCHECK_LED is toggled every three seconds by the check task
 * should no error conditions be detected in any of the standard demo tasks.
 * The toggle rate increasing to 500ms indicates that at least one error has
 * been detected.
 *
 * Main.c includes an idle hook function that simply periodically sends data
 * to the USB task for transmission.
 */

/*
	Changes from V3.2.2

	+ Modified the stack sizes used by some tasks to permit use of the 
	  command line GCC tools.
*/

/* Library includes. */
#include <string.h>
#include <stdio.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo application includes. */
#include "partest.h"
#include "PollQ.h"
#include "semtest.h"
#include "flash.h"
#include "integer.h"
#include "BlockQ.h"
#include "BasicWEB.h"
#include "USB-CDC.h"

/* lwIP includes. */
#include "lwip/api.h" 

/* Hardware specific headers. */
#include "Board.h"
#include "AT91SAM7X256.h"

/* Priorities/stacks for the various tasks within the demo application. */
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + 3 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainFLASH_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainWEBSERVER_PRIORITY      ( tskIDLE_PRIORITY + 2 )
#define mainUSB_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainUSB_TASK_STACK			( 200 )

/* The rate at which the on board LED will toggle when there is/is not an
error. */
#define mainNO_ERROR_FLASH_PERIOD	( ( portTickType ) 3000 / portTICK_RATE_MS  )
#define mainERROR_FLASH_PERIOD		( ( portTickType ) 500 / portTICK_RATE_MS  )

/* The rate at which the idle hook sends data to the USB port. */
#define mainUSB_TX_FREQUENCY		( 100 / portTICK_RATE_MS )

/* The string that is transmitted down the USB port. */
#define mainFIRST_TX_CHAR			'a'
#define mainLAST_TX_CHAR			'z'

/* The LED used by the check task to indicate the system status. */
#define mainCHECK_LED 				( 3 )
/*-----------------------------------------------------------*/

/*
 * Checks that all the demo application tasks are still executing without error
 * - as described at the top of the file.
 */
static long prvCheckOtherTasksAreStillRunning( void );

/*
 * The task that executes at the highest priority and calls
 * prvCheckOtherTasksAreStillRunning().  See the description at the top
 * of the file.
 */
static void vErrorChecks( void *pvParameters );

/*
 * Configure the processor for use with the Atmel demo board.  This is very
 * minimal as most of the setup is performed in the startup code.
 */
static void prvSetupHardware( void );

/*
 * The idle hook is just used to stream data to the USB port.
 */
void vApplicationIdleHook( void );
/*-----------------------------------------------------------*/

/*
 * Setup hardware then start all the demo application tasks.
 */
int main( void )
{
	/* Setup the ports. */
	prvSetupHardware();

	/* Setup the IO required for the LED's. */
	vParTestInitialise();

	/* Setup lwIP. */
    vlwIPInit();

	/* Create the lwIP task.  This uses the lwIP RTOS abstraction layer.*/
    sys_thread_new( vBasicWEBServer, ( void * ) NULL, mainWEBSERVER_PRIORITY );

	/* Create the demo USB CDC task. */
	xTaskCreate( vUSBCDCTask, ( signed char * ) "USB", mainUSB_TASK_STACK, NULL, mainUSB_PRIORITY, NULL );

	/* Create the standard demo application tasks. */
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartLEDFlashTasks( mainFLASH_PRIORITY );
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );

	/* Start the check task - which is defined in this file. */	
    xTaskCreate( vErrorChecks, ( signed char * ) "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Finally, start the scheduler. 

	NOTE : Tasks run in system mode and the scheduler runs in Supervisor mode.
	The processor MUST be in supervisor mode when vTaskStartScheduler is 
	called.  The demo applications included in the FreeRTOS.org download switch
	to supervisor mode prior to main being called.  If you are not using one of
	these demo application projects then ensure Supervisor mode is used here. */
	vTaskStartScheduler();

	/* Should never get here! */
	return 0;
}
/*-----------------------------------------------------------*/


static void prvSetupHardware( void )
{
	/* When using the JTAG debugger the hardware is not always initialised to
	the correct default state.  This line just ensures that this does not
	cause all interrupts to be masked at the start. */
	AT91C_BASE_AIC->AIC_EOICR = 0;
	
	/* Most setup is performed by the low level init function called from the
	startup asm file.

	Configure the PIO Lines corresponding to LED1 to LED4 to be outputs as
	well as the UART Tx line. */
	AT91C_BASE_PIOB->PIO_PER = LED_MASK; // Set in PIO mode
	AT91C_BASE_PIOB->PIO_OER = LED_MASK; // Configure in Output


	/* Enable the peripheral clock. */
    AT91C_BASE_PMC->PMC_PCER = 1 << AT91C_ID_PIOA;
    AT91C_BASE_PMC->PMC_PCER = 1 << AT91C_ID_PIOB;
	AT91C_BASE_PMC->PMC_PCER = 1 << AT91C_ID_EMAC;
}
/*-----------------------------------------------------------*/

static void vErrorChecks( void *pvParameters )
{
portTickType xDelayPeriod = mainNO_ERROR_FLASH_PERIOD;
portTickType xLastWakeTime;

	/* The parameters are not used. */
	( void ) pvParameters;

	/* Initialise xLastWakeTime to ensure the first call to vTaskDelayUntil()
	functions correctly. */
	xLastWakeTime = xTaskGetTickCount();

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error.  If an error is detected then the delay period
	is decreased from mainNO_ERROR_FLASH_PERIOD to mainERROR_FLASH_PERIOD so
	the Check LED flash rate will increase. */
	for( ;; )
	{
		/* Delay until it is time to execute again.  The delay period is
		shorter following an error. */
		vTaskDelayUntil( &xLastWakeTime, xDelayPeriod );
	
		/* Check all the standard demo application tasks are executing without
		error.  */
		if( prvCheckOtherTasksAreStillRunning() != pdPASS )
		{
			/* An error has been detected in one of the tasks - flash faster. */
			xDelayPeriod = mainERROR_FLASH_PERIOD;
		}

		vParTestToggleLED( mainCHECK_LED );
	}
}
/*-----------------------------------------------------------*/

static long prvCheckOtherTasksAreStillRunning( void )
{
long lReturn = ( long ) pdPASS;

	/* Check all the demo tasks (other than the flash tasks) to ensure
	that they are all still running, and that none of them have detected
	an error. */

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		lReturn = ( long ) pdFAIL;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		lReturn = ( long ) pdFAIL;
	}

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		lReturn = ( long ) pdFAIL;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		lReturn = ( long ) pdFAIL;
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
static portTickType xLastTx = 0;
char cTxByte;

	/* The idle hook simply sends a string of characters to the USB port.
	The characters will be buffered and sent once the port is connected. */
	if( ( xTaskGetTickCount() - xLastTx ) > mainUSB_TX_FREQUENCY )
	{
		xLastTx = xTaskGetTickCount();
		for( cTxByte = mainFIRST_TX_CHAR; cTxByte <= mainLAST_TX_CHAR; cTxByte++ )
		{
			vUSBSendByte( cTxByte );
		}		
	}
}


