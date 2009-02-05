/*
	FreeRTOS.org V5.1.1 - Copyright (C) 2003-2009 Richard Barry.

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

/* Standard includes. */
#include <stdlib.h>
#include <string.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo file headers. */
#include "int78K0R.h"
#include "PollQ.h"
#include "semtest.h"
#include "GenQTest.h"
#include "dynamic.h"
#include "blocktim.h"

/*
 * Priority definitions for most of the tasks in the demo application.  Some
 * tasks just use the idle priority.
 */
#define mainCHECK_TASK_PRIORITY	( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY	( tskIDLE_PRIORITY + 1 )
#define mainSEMTEST_PRIORITY    ( tskIDLE_PRIORITY + 1 )
#define mainBUTTON_PRIORITY		( configMAX_PRIORITIES - 1 )
#define mainGEN_QUEUE_PRIORITY	( tskIDLE_PRIORITY )

/* The period between executions of the check task. */
#define mainNO_ERROR_TOGGLE_PERIOD	( ( portTickType ) 3000 / portTICK_RATE_MS  )
#define mainERROR_TOGGLE_PERIOD		( ( portTickType ) 500 / portTICK_RATE_MS  )

#define LED00   P7_bit.no6
#define LED01   P7_bit.no7

/*
 * 78K0R/Kx3 Option Byte Definition
 * watchdog disabled, LVI enabled, OCD interface enabled
 */
__root __far const unsigned portCHAR OptionByte[OPT_BYTES_SIZE] @ 0x00C0 =
{
	WATCHDOG_DISABLED, LVI_ENABLED, RESERVED_FF, OCD_ENABLED
};

/* Security Byte Definition */
__root __far const unsigned portCHAR SecuIDCode[SECU_ID_SIZE]   @ 0x00C4 =
{
	0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
};

/* The task function for the "Check" task. */
static void vErrorChecks( void *pvParameters );


/* 78K0R/Kx3 low level init Initialization of the System Clock */
int __low_level_init(void);

extern void vRegTest1( void *pvParameters );
extern void vRegTest2( void *pvParameters );
extern void vButtonTask( void *pvParameters );

static short sRegTestStatus = pdPASS;

portSHORT main( void )
{
	/* Create the standard demo tasks. */
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartSemaphoreTasks(mainSEMTEST_PRIORITY);
	vStartGenericQueueTasks( mainGEN_QUEUE_PRIORITY );
	vStartDynamicPriorityTasks();
	vCreateBlockTimeTasks();

	xTaskCreate( vButtonTask, "Button", configMINIMAL_STACK_SIZE, NULL, mainBUTTON_PRIORITY, NULL );
	
	/* Create the tasks defined within this file. */
	xTaskCreate( vErrorChecks, "Check", configMINIMAL_STACK_SIZE, (void*)0x12345678, mainCHECK_TASK_PRIORITY, NULL );

	xTaskCreate( vRegTest1, "Reg1", configMINIMAL_STACK_SIZE, NULL, 0, NULL );
	xTaskCreate( vRegTest2, "Reg2", configMINIMAL_STACK_SIZE, NULL, 0, NULL );	


	vTaskStartScheduler();

	for( ;; );
}
/*-----------------------------------------------------------*/

static void vErrorChecks( void *pvParameters )
{
portTickType xToggleRate = mainNO_ERROR_TOGGLE_PERIOD, xLastWakeTime;

	/* The pointer will only actually be either 3 or 2 bytes, depending on the
	memory model. */
	if( pvParameters != ( void * ) 0x12345678 )
	{
		xToggleRate = mainERROR_TOGGLE_PERIOD;
	}

	xLastWakeTime = xTaskGetTickCount();

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error. */
	for( ;; )
	{
		vTaskDelayUntil( &xLastWakeTime, xToggleRate );

		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			xToggleRate = mainERROR_TOGGLE_PERIOD;
		}

		if( xArePollingQueuesStillRunning() != pdTRUE)
		{
			xToggleRate = mainERROR_TOGGLE_PERIOD;
		}

		if( xAreSemaphoreTasksStillRunning() != pdTRUE)
		{
			xToggleRate = mainERROR_TOGGLE_PERIOD;
		}
		
		if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
		{
			xToggleRate = mainERROR_TOGGLE_PERIOD;
		}

		if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			xToggleRate = mainERROR_TOGGLE_PERIOD;
		}

		if( sRegTestStatus != pdPASS )
		{
			xToggleRate = mainERROR_TOGGLE_PERIOD;
		}

		/* Toggle the LED. */
		LED00 = !LED00;
	}
}
/*-----------------------------------------------------------*/

int __low_level_init(void)
{
unsigned portCHAR resetflag = RESF;

	portDISABLE_INTERRUPTS();

	/*
	 * Clock Configuration:
	 * In this port, to use the internal high speed clock source of the microcontroller
	 * define the configCLOCK_SOURCE as 1 in FreeRTOSConfig.h.  To use an external
	 * clock define configCLOCK_SOURCE as 0.
	 */
	#if configCLOCK_SOURCE == 1
	{
		/*
		 * Set XT1 and XT2 in Input Port Mode
		 * Set X1  and X2  in Input Port Mode
		 * High speed oszillation frequency 2MHz <= fMX <= 10MHz
		 */
		CMC = 0x00;

		/* X1 external oszillation stopped */
		MSTOP = 1;

		/* enable internal high speed oszillation */
		HIOSTOP = 0;
		MCM0 = 0;

		/* stop internal subsystem clock */
		XTSTOP = 1;

		/* Set clock speed */
		CSS = 0;
		CKC &= (unsigned portCHAR)~0x07;
		CKC |= 0x00;
	}
	#else
	{
		/*
		 * XT1 and XT2 pin in input port mode
		 * X1  and X2  pin in crystal resonator mode
		 * High speed oszillation frequency 10MHz < fMX <= 20MHz
		 */
		CMC   = 0x41;
		
		/* Set oscillation stabilization time */
		OSTS  = 0x07;
		
		/* Set speed mode: fMX > 10MHz for Flash memory high speed operation */
		OSMC  = 0x01;
		
		/*
		 * Start up X1 oscillator operation
		 * Internal high-speed oscillator operating
		 */
		MSTOP = 0;
		
		/* Check oscillation stabilization time status */
		while(OSTC < 0x07)
		{
			/* wait until X1 clock stabilization time */
			portNOP();
		}
		
		/* Switch CPU clock to X1 oscillator */
		MCM0 = 1;
		while(MCS != 1)
		{
			/* wait until CPU and peripherals operate with fX1 clock */
			portNOP();
		}

		/* Stop the internal high-speed oscillator operation */
		HIOSTOP = 1;
		
		/* Stop the XT1 oscillator operation */
		XTSTOP  = 1;
		
		/*
		 * operating frequency f = fx
		 * Change clock generator setting, if necessary
		 */
		CKC &= 0xF8;

		/* From here onwards the X1 oscillator is supplied to the CPU */
	}
	#endif
	
	/* LED Port Initialization - set Port Register */
	P7  = 0x80;
	
	/* Set Port Mode Register */
	PM7 = 0x3F;
	
	/* Switch Pin Initialization - enable pull-up resistor */
	PU12_bit.no0  = 1;
	
	/* INTP0 disable */
	PMK0 = 1;			
	
	/* INTP0 IF clear */
	PIF0 = 0;			
	EGN0_bit.no0  = 1;
	
	/* INTP0 priority low */
	PPR10 = 0;
	PPR00 = 1;
	
	/* enable ext. INTP0 interrupt */
	PMK0  = 0;	

	return pdTRUE;
}
/*-----------------------------------------------------------*/

void vRegTestError( void )
{
	sRegTestStatus = pdFAIL;
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( void )
{
	for( ;; );
}

