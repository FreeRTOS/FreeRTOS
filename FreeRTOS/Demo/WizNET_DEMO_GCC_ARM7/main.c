/*
    FreeRTOS V8.2.2 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

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

/*
	NOTE : Tasks run in system mode and the scheduler runs in Supervisor mode.
	The processor MUST be in supervisor mode when vTaskStartScheduler is
	called.  The demo applications included in the FreeRTOS.org download switch
	to supervisor mode prior to main being called.  If you are not using one of
	these demo application projects then ensure Supervisor mode is used.
*/


/*
 * Program entry point.
 *
 * main() is responsible for setting up the microcontroller peripherals, then
 * starting the demo application tasks.  Once the tasks have been created the
 * scheduler is started and main() should never complete.
 *
 * The demo creates the three standard 'flash' tasks to provide some visual
 * feedback that the system and scheduler are still operating correctly.
 *
 * The HTTP server task operates at the highest priority so will always preempt
 * the flash or idle task on TCP/IP events.
 */

/* Standard includes. */
#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "semphr.h"
#include "task.h"

/* Application includes. */
#include "i2c.h"
#include "HTTP_Serv.h"
#include "flash.h"
#include "partest.h"
#include "dynamic.h"
#include "semtest.h"
#include "PollQ.h"
#include "BlockQ.h"
#include "integer.h"

/*-----------------------------------------------------------*/

/* Constants to setup the PLL. */
#define mainPLL_MUL_4		( ( unsigned char ) 0x0003 )
#define mainPLL_DIV_1		( ( unsigned char ) 0x0000 )
#define mainPLL_ENABLE		( ( unsigned char ) 0x0001 )
#define mainPLL_CONNECT		( ( unsigned char ) 0x0003 )
#define mainPLL_FEED_BYTE1	( ( unsigned char ) 0xaa )
#define mainPLL_FEED_BYTE2	( ( unsigned char ) 0x55 )
#define mainPLL_LOCK		( ( unsigned long ) 0x0400 )

/* Constants to setup the MAM. */
#define mainMAM_TIM_3		( ( unsigned char ) 0x03 )
#define mainMAM_MODE_FULL	( ( unsigned char ) 0x02 )

/* Constants to setup the peripheral bus. */
#define mainBUS_CLK_FULL	( ( unsigned char ) 0x01 )

/* Constants to setup I/O and processor. */
#define mainBUS_CLK_FULL	( ( unsigned char ) 0x01 )
#define mainLED_TO_OUTPUT	( ( unsigned long ) 0xff0000 )
#define mainJTAG_PORT		( ( unsigned long ) 0x3E0000UL )

/* Priorities for the demo application tasks. */
#define mainLED_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainHTTP_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainERROR_CHECK_PRIORITY	( tskIDLE_PRIORITY + 1 )

/* Flash rates of the on board LED to indicate the health of the system. */
#define mainNO_ERROR_DELAY			( 3000 )
#define mainERROR_DELAY				( 500 )
#define mainON_BOARD_LED_BIT		( ( unsigned long ) 0x80 )

/*-----------------------------------------------------------*/

/*
 * The Olimex demo board has a single built in LED.  This function simply
 * toggles its state.
 */
void prvToggleOnBoardLED( void );

/*
 * Configure the processor for use with the Olimex demo board.
 */
static void prvSetupHardware( void );

/*
 * Simply check for errors and toggle the onboard LED.
 */
static void prvErrorChecks( void *pvParameters );

/*
 * Return true if the demo tasks are executing without error - otherwise
 * return false.
 */
static void prvMainCheckOtherTasksAreStillRunning( void );
/*-----------------------------------------------------------*/

/* Flag set by prvMainCheckOtherTasksAreStillExecuting(). */
long lErrorInTask = pdFALSE;

/*
 * Application entry point:
 * Starts all the other tasks, then starts the scheduler.
 */
int main( void )
{
	/* Setup the hardware for use with the Olimex demo board. */
	prvSetupHardware();

	/* Start the standard flash tasks so the WEB server is not the only thing
	running. */
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );
	vStartSemaphoreTasks( tskIDLE_PRIORITY );
	vStartDynamicPriorityTasks();
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vStartIntegerMathTasks( tskIDLE_PRIORITY );

	/* Start the WEB server task and the error check task. */
	xTaskCreate( vHTTPServerTask, "HTTP", configMINIMAL_STACK_SIZE, NULL, mainHTTP_TASK_PRIORITY, NULL );
	xTaskCreate( prvErrorChecks, "Check", configMINIMAL_STACK_SIZE, NULL, mainERROR_CHECK_PRIORITY, NULL );

	/* Now all the tasks have been started - start the scheduler.

	NOTE : Tasks run in system mode and the scheduler runs in Supervisor mode.
	The processor MUST be in supervisor mode when vTaskStartScheduler is
	called.  The demo applications included in the FreeRTOS.org download switch
	to supervisor mode prior to main being called.  If you are not using one of
	these demo application projects then ensure Supervisor mode is used. */
	vTaskStartScheduler();

	/* Should never reach here! */
	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	#ifdef RUN_FROM_RAM
		/* Remap the interrupt vectors to RAM if we are are running from RAM. */
		SCB_MEMMAP = 2;
	#endif

	/* Set all GPIO to output other than the P0.14 (BSL), and the JTAG pins.
	The JTAG pins are left as input as I'm not sure what will happen if the
	Wiggler is connected after powerup - not that it would be a good idea to
	do that anyway. */
	GPIO_IODIR = ~( mainJTAG_PORT );

	/* Setup the PLL to multiply the XTAL input by 4. */
	SCB_PLLCFG = ( mainPLL_MUL_4 | mainPLL_DIV_1 );

	/* Activate the PLL by turning it on then feeding the correct sequence of
	bytes. */
	SCB_PLLCON = mainPLL_ENABLE;
	SCB_PLLFEED = mainPLL_FEED_BYTE1;
	SCB_PLLFEED = mainPLL_FEED_BYTE2;

	/* Wait for the PLL to lock... */
	while( !( SCB_PLLSTAT & mainPLL_LOCK ) );

	/* ...before connecting it using the feed sequence again. */
	SCB_PLLCON = mainPLL_CONNECT;
	SCB_PLLFEED = mainPLL_FEED_BYTE1;
	SCB_PLLFEED = mainPLL_FEED_BYTE2;

	/* Setup and turn on the MAM.  Three cycle access is used due to the fast
	PLL used.  It is possible faster overall performance could be obtained by
	tuning the MAM and PLL settings. */
	MAM_TIM = mainMAM_TIM_3;
	MAM_CR = mainMAM_MODE_FULL;

	/* Setup the peripheral bus to be the same as the PLL output. */
	SCB_VPBDIV = mainBUS_CLK_FULL;

	/* Initialise the i2c peripheral. */
	i2cInit();

	/* Initialise the LED's used by the flash tasks. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

static void prvMainCheckOtherTasksAreStillRunning( void )
{
	/* Check all the demo tasks (other than the flash tasks) to ensure
	that they are all still running, and that none of them have detected
	an error. */

	/* This function is called from more than one task. */
	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		lErrorInTask = pdTRUE;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		lErrorInTask = pdTRUE;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		lErrorInTask = pdTRUE;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		lErrorInTask = pdTRUE;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		lErrorInTask = pdTRUE;
	}
}
/*-----------------------------------------------------------*/

void prvToggleOnBoardLED( void )
{
unsigned long ulState;

	ulState = GPIO0_IOPIN;
	if( ulState & mainON_BOARD_LED_BIT )
	{
		GPIO_IOCLR = mainON_BOARD_LED_BIT;
	}
	else
	{
		GPIO_IOSET = mainON_BOARD_LED_BIT;
	}
}
/*-----------------------------------------------------------*/

static void prvErrorChecks( void *pvParameters )
{
TickType_t xDelay = mainNO_ERROR_DELAY;

	/* The parameters are not used. */
	( void ) pvParameters;

	for( ;; )
	{
		/* How long we delay depends on whether an error has been detected
		or not.  Therefore the flash rate of the on board LED indicates
		whether or not an error has occurred. */
		vTaskDelay( xDelay );

		/* Update the lErrorInTask flag. */
		prvMainCheckOtherTasksAreStillRunning();

		if( lErrorInTask )
		{
			/* An error has been found so reduce the delay period and in so
			doing speed up the flash rate of the on board LED. */
			xDelay = mainERROR_DELAY;
		}

		prvToggleOnBoardLED();
	}
}

