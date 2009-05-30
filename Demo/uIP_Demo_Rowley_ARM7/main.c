/*
	FreeRTOS.org V5.3.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
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
 * A task is created called "uIP".  This executes the uIP stack and small
 * WEB server sample.  All the other tasks are from the set of standard
 * demo tasks.  The WEB documentation provides more details of the standard
 * demo application tasks.
 *
 * Main.c also creates a task called "Check".  This only executes every three 
 * seconds but has the highest priority so is guaranteed to get processor time.  
 * Its main function is to check that all the other tasks are still operational.
 * Each standard demo task maintains a unique count that is incremented each 
 * time the task successfully completes its function.  Should any error occur 
 * within such a task the count is permanently halted.  The check task inspects
 * the count of each task to ensure it has changed since the last time the 
 * check task executed.  If all the count variables have changed all the tasks 
 * are still executing error free, and the check task toggles the yellow LED.  
 * Should any task contain an error at any time the LED toggle rate will change 
 * from 3 seconds to 500ms.
 *
 */


/* Standard includes. */
#include <stdlib.h>
#include <string.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo application includes. */
#include "PollQ.h"
#include "dynamic.h"
#include "semtest.h"

/*-----------------------------------------------------------*/

/* Constants to setup the PLL. */
#define mainPLL_MUL_4		( ( unsigned portCHAR ) 0x0003 )
#define mainPLL_DIV_1		( ( unsigned portCHAR ) 0x0000 )
#define mainPLL_ENABLE		( ( unsigned portCHAR ) 0x0001 )
#define mainPLL_CONNECT		( ( unsigned portCHAR ) 0x0003 )
#define mainPLL_FEED_BYTE1	( ( unsigned portCHAR ) 0xaa )
#define mainPLL_FEED_BYTE2	( ( unsigned portCHAR ) 0x55 )
#define mainPLL_LOCK		( ( unsigned portLONG ) 0x0400 )

/* Constants to setup the MAM. */
#define mainMAM_TIM_3		( ( unsigned portCHAR ) 0x03 )
#define mainMAM_MODE_FULL	( ( unsigned portCHAR ) 0x02 )

/* Constants to setup the peripheral bus. */
#define mainBUS_CLK_FULL	( ( unsigned portCHAR ) 0x01 )

/* Priorities/stacks for the demo application tasks. */
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + 4 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainUIP_PRIORITY			( tskIDLE_PRIORITY + 3 )
#define mainUIP_TASK_STACK_SIZE		( 150 )

/* The rate at which the on board LED will toggle when there is/is not an 
error. */
#define mainNO_ERROR_FLASH_PERIOD	( ( portTickType ) 3000 / portTICK_RATE_MS  )
#define mainERROR_FLASH_PERIOD		( ( portTickType ) 500 / portTICK_RATE_MS  )
#define mainON_BOARD_LED_BIT		( ( unsigned portLONG ) 0x80 )
#define mainYELLOW_LED				( 1 << 11 )

/*-----------------------------------------------------------*/

/*
 * This is the uIP task which is defined within the uip.c file.  This has not
 * been placed into a header file in order to minimise the changes to the uip
 * code.
 */
extern void ( vuIP_TASK ) ( void *pvParameters );

/*
 * The Yellow LED is under the control of the Check task.  All the other LED's
 * are under the control of the uIP task. 
 */
void prvToggleOnBoardLED( void );

/*
 * Checks that all the demo application tasks are still executing without error
 * - as described at the top of the file.
 */
static portLONG prvCheckOtherTasksAreStillRunning( void );

/*
 * The task that executes at the highest priority and calls 
 * prvCheckOtherTasksAreStillRunning().  See the description at the top
 * of the file.
 */
static void vErrorChecks( void *pvParameters );

/*
 * Configure the processor for use with the Olimex demo board.  This includes
 * setup for the I/O, system clock, and access timings.
 */
static void prvSetupHardware( void );

/*-----------------------------------------------------------*/

/*
 * Starts all the other tasks, then starts the scheduler. 
 */
int main( void )
{
	/* Configure the processor. */
	prvSetupHardware();

	/* Start the task that handles the TCP/IP functionality. */
    xTaskCreate( vuIP_TASK, "uIP", mainUIP_TASK_STACK_SIZE, NULL, mainUIP_PRIORITY, NULL );
	
	/* Start the demo/test application tasks.  These are created in addition 
	to the TCP/IP task for demonstration and test purposes. */
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartDynamicPriorityTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );

	/* Start the check task - which is defined in this file. */	
    xTaskCreate( vErrorChecks, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Now all the tasks have been started - start the scheduler.

	NOTE : Tasks run in system mode and the scheduler runs in Supervisor mode.
	The processor MUST be in supervisor mode when vTaskStartScheduler is 
	called.  The demo applications included in the FreeRTOS.org download switch
	to supervisor mode prior to main being called.  If you are not using one of
	these demo application projects then ensure Supervisor mode is used here. */
	vTaskStartScheduler();

	/* Should never reach here! */
	return 0;
}
/*-----------------------------------------------------------*/

static void vErrorChecks( void *pvParameters )
{
portTickType xDelayPeriod = mainNO_ERROR_FLASH_PERIOD;

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error.  If an error is detected then the delay period
	is decreased from mainNO_ERROR_FLASH_PERIOD to mainERROR_FLASH_PERIOD so
	the on board LED flash rate will increase. */
	for( ;; )
	{
		/* Delay until it is time to execute again. */
		vTaskDelay( xDelayPeriod );
	
		/* Check all the standard demo application tasks are executing without 
		error.  */
		if( prvCheckOtherTasksAreStillRunning() != pdPASS )
		{
			/* An error has been detected in one of the tasks - flash faster. */
			xDelayPeriod = mainERROR_FLASH_PERIOD;
		}

		prvToggleOnBoardLED();
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	#ifdef RUN_FROM_RAM
		/* Remap the interrupt vectors to RAM if we are are running from RAM. */
		SCB_MEMMAP = 2;
	#endif

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
}
/*-----------------------------------------------------------*/

void prvToggleOnBoardLED( void )
{
unsigned portLONG ulState;

	ulState = GPIO0_IOPIN;
	if( ulState & mainYELLOW_LED )
	{
		GPIO_IOCLR = mainYELLOW_LED;
	}
	else
	{
		GPIO_IOSET = mainYELLOW_LED;
	}	
}
/*-----------------------------------------------------------*/

static portLONG prvCheckOtherTasksAreStillRunning( void )
{
portLONG lReturn = ( portLONG ) pdPASS;

	/* Check all the demo tasks (other than the flash tasks) to ensure
	that they are all still running, and that none of them have detected
	an error. */

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		lReturn = ( portLONG ) pdFAIL;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		lReturn = ( portLONG ) pdFAIL;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		lReturn = ( portLONG ) pdFAIL;
	}

	return lReturn;
}



