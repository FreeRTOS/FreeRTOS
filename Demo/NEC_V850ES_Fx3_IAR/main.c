/*
	FreeRTOS.org V5.1.1 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and 
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety 
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting, 
	licensing and training services.
*/

#include <stdlib.h>
#include <string.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo file headers. */
#include <intrinsics.h>
#include "PollQ.h"
#include "semtest.h"
#include "print.h"
#include "semtest.h"
#include "led.h"
#include "integer.h"

/*
 * Priority definitions for most of the tasks in the demo application.  Some
 * tasks just use the idle priority.
 */
#define mainCHECK_TASK_PRIORITY	( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY	( tskIDLE_PRIORITY + 1 )
#define mainSEMTEST_PRIORITY    ( tskIDLE_PRIORITY + 1 )
#define mainLED_TOGGLE_PRIORITY ( tskIDLE_PRIORITY + 1 )

/* The period between executions of the check task. */
#define mainCHECK_PERIOD	( ( portTickType ) 3000 / portTICK_RATE_MS  )

/* The task function for the "Check" task. */
static void vErrorChecks( void *pvParameters );

/*
 * Checks the unique counts of other tasks to ensure they are still operational.
 * Flashes an LED if everything is okay.
 */
static long prvCheckOtherTasksAreStillRunning( void );

/* low level initialization prototype */
unsigned portCHAR __low_level_init(void);

extern void vRegTest1( void *pvParameters );
extern void vRegTest2( void *pvParameters );

/*-----------------------------------------------------------*/

volatile portLONG lRegTestStatus = pdPASS;

void vRegTestFailed( void )
{
	lRegTestStatus = pdFAIL;
	for( ;; );
}

void main( void )
{
	/* Create some standard demo tasks. */
//	vStartIntegerMathTasks( tskIDLE_PRIORITY );
//	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
//	vStartSemaphoreTasks(mainSEMTEST_PRIORITY);

	/* Create a simple task that toggles a pin. */
//	vStartLEDToggleTasks( mainLED_TOGGLE_PRIORITY );

	/* Create the tasks defined within this file. */
//	xTaskCreate( vErrorChecks, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

//	vPrintInitialise();

xTaskCreate( vRegTest1, "Check", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
xTaskCreate( vRegTest2, "Check", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );

	/* Start the scheduler. */
	vTaskStartScheduler();

	/* If this line is reached then vTaskStartScheduler() returned because there
	was insufficient heap memory remaining for the idle task to be created. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void vErrorChecks( void *pvParameters )
{
volatile long lError = pdFALSE;

	/* Just to remove the compiler warning. */
	( void ) pvParameters;

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error. */
	for( ;; )
	{
		/* Delay until it is time to check the other tasks again. */
		vTaskDelay( mainCHECK_PERIOD );

		if( prvCheckOtherTasksAreStillRunning() != pdPASS )
		{
			lError = pdTRUE;
			
			/* Do something to indicate the error. */
			( void ) lError;
		}
	}
}
/*-----------------------------------------------------------*/

static long prvCheckOtherTasksAreStillRunning( void )
{
long lStatus = pdPASS;

	if( xAreIntegerMathsTaskStillRunning() != pdPASS )
	{
		lStatus = pdFAIL;
	}

	if( xArePollingQueuesStillRunning() != pdPASS )
	{
		lStatus = pdFAIL;
	}

	if( xAreSemaphoreTasksStillRunning() != pdPASS )
	{
		lStatus = pdFAIL;
	}

	if( xAreLEDToggleTaskStillRunning() != pdPASS )
	{
		lStatus = pdFAIL;
	}

	return lStatus;
}
/*-----------------------------------------------------------*/

unsigned portCHAR __low_level_init(void)
{
unsigned portCHAR resetflag = RESF;
unsigned portCHAR psval = 0;

	/* Setup provided by NEC. */

	/* Disable global interrupts to ensure no interrupts occur during system
	setup. */
	portDISABLE_INTERRUPTS();

	PRCMD = 0x00;
	OCDM = 0x00;
	VSWC = 0x12;
	VSWC = 18;

	/* Set main system clock */
	OSTS = 0x06;
	psval = 0x80;
	PRCMD = psval;
	PCC = psval;
	while (!OSTC)
	{
		;
	}

	PLLS = 0x03;
	PLLON = 1;
	while (LOCKR)
	{
		;
	}

	psval = 0x01;
	PRCMD = psval;
	MCM = psval;
	SELPLL = 1;

	/* Set fCPU */
	psval = PCC | 0x00;
	PRCMD = psval;
	PCC = psval;
	RCM = 0x83;

	/* Set fXP1 */
	SELCNT4 = 0x00;

	/* Set fBRG */
	PRSM0 = 0x00;

	/* Stand-by setting */
	psval = 0x00;
	PRCMD = psval;
	PSC = psval;

	/* WDT2 setting */
	WDTM2 = 0x1F;

	/* PCL setting */
	PCLM = 0x00;

	/* disable dma0 - dma3 */
	E00 = 0;	
	E11 = 0;
	E22 = 0;
	E33 = 0;	

	return pdTRUE;
}


