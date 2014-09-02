/*
    FreeRTOS V8.1.2 - Copyright (C) 2014 Real Time Engineers Ltd. 
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

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

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
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the standard demo application tasks.
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Check" task -  This only executes every three seconds but has a high priority
 * to ensure it gets processor time.  Its main function is to check that all the
 * standard demo tasks are still operational.  If everything is running as
 * expected then the check task will toggle an LED every 3 seconds.  An error
 * being discovered in any task will cause the toggle rate to increase to 500ms.
 *
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register still contains its expected value.  Each task uses
 * different values.  The tasks run with very low priority so get preempted very
 * frequently.  A register containing an unexpected value is indicative of an
 * error in the context switching mechanism.
 *
 *
 * Also in addition to the standard demo tasks is a button push task.  This is
 * a very basic task that is included as an example of how to write an interrupt
 * service routine that interacts with a task.  The button on the target board
 * is used to generate an interrupt that 'gives' a semaphore in order to unblock
 * a task.  In doing so the task is synchronised with the interrupt.  Each time
 * the task unblocks it simply toggles an LED before entering the Blocked state
 * again to wait for the next button push.
 */

/* Standard includes. */
#include <stdlib.h>
#include <string.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard demo file headers. */
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
#define mainNO_ERROR_TOGGLE_PERIOD	( ( TickType_t ) 3000 / portTICK_PERIOD_MS  )
#define mainERROR_TOGGLE_PERIOD		( ( TickType_t ) 500 / portTICK_PERIOD_MS  )

/* The LED toggled by the check task. */
#define mainLED_0   P7_bit.no6

/* A value that is passed in as the parameter to the 'check' task.  This is done
purely to check that the parameter passing mechanism is functioning correctly. */
#define mainCHECK_PARAMETER_VALUE	( 0x5678 )

/*-----------------------------------------------------------*/

/*
 * The function that defines the 'check' task as described at the top of this
 * file.
 */
static void vErrorChecks( void *pvParameters );


/*
 * This function is called from the C startup routine to setup the processor -
 * in particular the clock source.
 */
int __low_level_init(void);

/*
 * Functions that define the RegTest tasks as described at the top of this file.
 */
extern void vRegTest1( void *pvParameters );
extern void vRegTest2( void *pvParameters );

/*
 * Function that defines the button push task as described at the top of this
 * file.
 */
extern void vButtonTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* If an error is discovered by one of the RegTest tasks then this flag is set
to pdFAIL.  The 'check' task then inspects this flag to detect errors within
the RegTest tasks. */
static short sRegTestStatus = pdPASS;

/* 78K0R Option Byte Definition. Watchdog disabled, LVI enabled, OCD interface
enabled. */
__root __far const unsigned char OptionByte[] @ 0x00C0 =
{
	WATCHDOG_DISABLED, LVI_ENABLED, RESERVED_FF, OCD_ENABLED
};

/* Security byte definition */
__root __far const unsigned char SecuIDCode[]  @ 0x00C4 =
{
	0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
};


/*-----------------------------------------------------------*/

short main( void )
{
	/* Creates all the tasks, then starts the scheduler. */

	/* First create the 'standard demo' tasks.  These are used to demonstrate
	API functions being used and also to test the kernel port.  More information
	is provided on the FreeRTOS.org WEB site. */
	vStartDynamicPriorityTasks();

	/* Create the RegTest tasks as described at the top of this file. */
	xTaskCreate( vRegTest1, "Reg1", configMINIMAL_STACK_SIZE, NULL, 0, NULL );
	xTaskCreate( vRegTest2, "Reg2", configMINIMAL_STACK_SIZE, NULL, 0, NULL );	
	
	/* Create the button push task as described at the top of this file. */
	xTaskCreate( vButtonTask, "Button", configMINIMAL_STACK_SIZE, NULL, mainBUTTON_PRIORITY, NULL );		
	
	/* Create the 'check' task as described at the top of this file. */
	xTaskCreate( vErrorChecks, "Check", configMINIMAL_STACK_SIZE, ( void* )mainCHECK_PARAMETER_VALUE, mainCHECK_TASK_PRIORITY, NULL );

	#ifdef __IAR_78K0R_Kx3__
	{
		/* The Kx3 has enough RAM to create more of the standard demo tasks. */
		vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
		vStartSemaphoreTasks(mainSEMTEST_PRIORITY);
		vStartGenericQueueTasks( mainGEN_QUEUE_PRIORITY );
		vCreateBlockTimeTasks();
	}
	#endif
	
	/* Finally start the scheduler running. */
	vTaskStartScheduler();

	/* If this line is reached then vTaskStartScheduler() returned because there
	was insufficient heap memory remaining for the idle task to be created. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void vErrorChecks( void *pvParameters )
{
TickType_t xToggleRate = mainNO_ERROR_TOGGLE_PERIOD, xLastWakeTime;

	/* Ensure the parameter was passed in as expected.  This is just a test of
	the kernel port, the parameter is not actually used for anything.  The
	pointer will only actually be either 3 or 2 bytes, depending on the memory
	model. */
	if( pvParameters != ( void * ) mainCHECK_PARAMETER_VALUE )
	{
		xToggleRate = mainERROR_TOGGLE_PERIOD;
	}

	/* Initialise xLastWakeTime before it is used.  After this point it is not
	written to directly. */
	xLastWakeTime = xTaskGetTickCount();

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error. */
	for( ;; )
	{
		/* Wait until it is time to check all the other tasks again. */
		vTaskDelayUntil( &xLastWakeTime, xToggleRate );

		if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
		{
			xToggleRate = mainERROR_TOGGLE_PERIOD;
		}

		if( sRegTestStatus != pdPASS )
		{
			xToggleRate = mainERROR_TOGGLE_PERIOD;
		}

		#ifdef __IAR_78K0R_Kx3__
		{
			/* Only the Kx3 runs all the tasks. */
			if( xArePollingQueuesStillRunning() != pdTRUE)
			{
				xToggleRate = mainERROR_TOGGLE_PERIOD;
			}
		
			if( xAreSemaphoreTasksStillRunning() != pdTRUE)
			{
				xToggleRate = mainERROR_TOGGLE_PERIOD;
			}
			
			if( xAreGenericQueueTasksStillRunning() != pdTRUE )
			{
				xToggleRate = mainERROR_TOGGLE_PERIOD;
			}	
		
			if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
			{
				xToggleRate = mainERROR_TOGGLE_PERIOD;
			}			
		}
		#endif
		
		/* Toggle the LED.  The toggle rate will depend on whether or not an
		error has been found in any tasks. */
		mainLED_0 = !mainLED_0;
	}
}
/*-----------------------------------------------------------*/

int __low_level_init(void)
{
unsigned char ucResetFlag = RESF;

	portDISABLE_INTERRUPTS();

	/* Clock Configuration:
	In this port, to use the internal high speed clock source of the microcontroller
	define the configCLOCK_SOURCE as 1 in FreeRTOSConfig.h.  To use an external
	clock define configCLOCK_SOURCE as 0. */
	#if configCLOCK_SOURCE == 1
	{
		/* Set XT1 and XT2 in Input Port Mode
		   Set X1  and X2  in Input Port Mode
		   High speed oscillator frequency 2MHz <= fMX <= 10MHz */
		CMC = 0x00;

		/* X1 external oszillation stopped. */
		MSTOP = 1;

		/* Enable internal high speed oszillation. */
		HIOSTOP = 0;
		MCM0 = 0;

		/* Stop internal subsystem clock. */
		XTSTOP = 1;

		/* Set clock speed. */
		CSS = 0;
		CKC &= (unsigned char)~0x07;
		CKC |= 0x00;
	}
	#else
	{
		/* XT1 and XT2 pin in input port mode
		   X1  and X2  pin in crystal resonator mode
		   High speed oszillation frequency 10MHz < fMX <= 20MHz */
		CMC   = 0x41;
		
		/* Set oscillation stabilization time. */
		OSTS  = 0x07;
		
		/* Set speed mode: fMX > 10MHz for Flash memory high speed operation. */
		OSMC  = 0x01;
		
		/* Start up X1 oscillator operation
		   Internal high-speed oscillator operating. */
		MSTOP = 0;
		
		/* Check oscillation stabilization time status. */
		while(OSTC < 0x07)
		{
			/* Wait until X1 clock stabilization time. */
			portNOP();
		}
		
		/* Switch CPU clock to X1 oscillator. */
		MCM0 = 1;
		while(MCS != 1)
		{
			/* Wait until CPU and peripherals operate with fX1 clock. */
			portNOP();
		}

		/* Stop the internal high-speed oscillator operation. */
		HIOSTOP = 1;
		
		/* Stop the XT1 oscillator operation. */
		XTSTOP  = 1;
		
		/* Operating frequency f = fx
		   Change clock generator setting, if necessary. */
		CKC &= 0xF8;

		/* From here onwards the X1 oscillator is supplied to the CPU. */
	}
	#endif
	
	/* LED port initialization - set port register. */
	P7  = 0x80;
	
	/* Set port mode register. */
	PM7 = 0x3F;
	
	/* Switch pin initialization - enable pull-up resistor. */
	PU12_bit.no0  = 1;

	/* INTP0 is used by the button on the target board. */
	
	/* INTP0 disable. */
	PMK0 = 1;			
	
	/* INTP0 IF clear. */
	PIF0 = 0;			
	EGN0_bit.no0  = 1;
	
	/* INTP0 priority low. */
	PPR10 = 0;
	PPR00 = 1;
	
	/* Enable ext. INTP0 interrupt */
	PMK0  = 0;	

	return pdTRUE;
}
/*-----------------------------------------------------------*/

void vRegTestError( void )
{
	/* Called by the RegTest tasks if an error is found.  lRegTestStatus is
	inspected by the check task. */
	sRegTestStatus = pdFAIL;

	/* Do not return from here as the reg test tasks clobber all registers so
	function calls may not function correctly. */
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( void )
{
	/* This will get called if an overflow is detected in the stack of a task.
	Inspect pxCurrentTCB to see which was the offending task. */
	for( ;; );
}

