/*
    FreeRTOS V6.1.0 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS books - available as PDF or paperback  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/
#include <stdio.h>

#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

#include "msp430.h"
#include "hal_MSP-EXP430F5438.h"

/* The rate at which mainCHECK_LED will toggle when all the tasks are running
without error.  Controlled by the check task as described at the top of this
file. */
#define mainNO_ERROR_CYCLE_TIME		( 5000 / portTICK_RATE_MS )

/* The rate at which mainCHECK_LED will toggle when an error has been reported
by at least one task.  Controlled by the check task as described at the top of
this file. */
#define mainERROR_CYCLE_TIME		( 200 / portTICK_RATE_MS )

/* Codes sent within messages to the LCD task so the LCD task can interpret
exactly what the message it just received was.  These are sent in the
cMessageID member of the message structure (defined below). */
#define mainMESSAGE_BUTTON_UP			( 1 )
#define mainMESSAGE_BUTTON_SEL			( 2 )
#define mainMESSAGE_STATUS				( 3 )

/* When the cMessageID member of the message sent to the LCD task is
mainMESSAGE_STATUS then these definitions are sent in the cMessageValue member
of the same message and indicate what the status actually is. */
#define mainERROR_DYNAMIC_TASKS			( pdPASS + 1 )
#define mainERROR_COM_TEST				( pdPASS + 2 )
#define mainERROR_GEN_QUEUE_TEST		( pdPASS + 3 )

/* The length of the queue (the number of items the queue can hold) that is used
to send messages from tasks and interrupts the the LCD task. */
#define mainQUEUE_LENGTH				( 5 )

#define mainLCD_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )

/*-----------------------------------------------------------*/

extern void vRegTest1Task( void *pvParameters );
extern void vRegTest2Task( void *pvParameters );
static void prvCheckTask( void *pvParameters );
static void prvSetupHardware( void );
static void prvTerminalIOTask( void *pvParameters );
static void prvButtonPollTask( void *pvParameters );
static void prvGenerateStatusMessage( char *pcBuffer, long lStatusValue );

/*-----------------------------------------------------------*/

volatile unsigned short usRegTest1Counter = 0, usRegTest2Counter = 0;

/* The handle of the queue used to send messages from tasks and interrupts to
the LCD task. */
static xQueueHandle xLCDQueue = NULL;

/* The definition of each message sent from tasks and interrupts to the LCD
task. */
typedef struct
{
	char cMessageID;	/* << States what the message is. */
	char cMessageValue; /* << States the message value (can be an integer, string pointer, etc. depending on the value of cMessageID. */
} xQueueMessage;
/*-----------------------------------------------------------*/

void main( void )
{
	prvSetupHardware();
	
	/* Create the queue used by tasks and interrupts to send strings to the LCD
	task. */
	xLCDQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( xQueueMessage ) );
	
	if( xLCDQueue != NULL )
	{
		/* Add the created queue to the queue registry so it can be viewed in
		the IAR FreeRTOS state viewer plug-in. */
		vQueueAddToRegistry( xLCDQueue, "LCDQueue" );

		/* Create the terminal IO and button poll tasks, as described at the top
		of this	file. */
		xTaskCreate( prvTerminalIOTask, ( signed char * ) "LCD", configMINIMAL_STACK_SIZE, NULL, mainLCD_TASK_PRIORITY, NULL );
		xTaskCreate( prvButtonPollTask, ( signed char * ) "ButPoll", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );

		xTaskCreate( vRegTest1Task, "RegTest1", configMINIMAL_STACK_SIZE, NULL, 0, NULL );
		xTaskCreate( vRegTest2Task, "RegTest2", configMINIMAL_STACK_SIZE, NULL, 0, NULL );
		xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, NULL );
		vTaskStartScheduler();
	}
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvTerminalIOTask( void *pvParameters )
{
xQueueMessage xReceivedMessage;

/* Buffer into which strings are formatted and placed ready for display on the
LCD.  Note this is a static variable to prevent it being allocated on the task
stack, which is too small to hold such a variable.  The stack size is configured
when the task is created. */
static char cBuffer[ 512 ];

	/* This function is the only function that uses printf().  If printf() is
	used from any other function then some sort of mutual exclusion on stdout
	will be necessary.
	
	This is also the only function that is permitted to access the LCD.
	
	First print out the number of bytes that remain in the FreeRTOS heap.  This
	can be viewed in the terminal IO window within the IAR Embedded Workbench. */
	printf( "%d bytes of heap space remain unallocated\n", ( int ) xPortGetFreeHeapSize() );

	for( ;; )
	{
		/* Wait for a message to be received.  Using portMAX_DELAY as the block
		time will result in an indefinite wait provided INCLUDE_vTaskSuspend is
		set to 1 in FreeRTOSConfig.h, therefore there is no need to check the
		function return value and the function will only return when a value
		has been received. */
		xQueueReceive( xLCDQueue, &xReceivedMessage, portMAX_DELAY );

		/* What is this message?  What does it contain? */
		switch( xReceivedMessage.cMessageID )
		{
			case mainMESSAGE_BUTTON_UP		:	/* The button poll task has just
												informed this task that the up
												button on the joystick input has
												been pressed or released. */
												sprintf( cBuffer, "Button up = %d", xReceivedMessage.cMessageValue );
												break;

			case mainMESSAGE_BUTTON_SEL		:	/* The select button interrupt
												just informed this task that the
												select button was pressed.
												Generate a table of task run time
												statistics and output this to
												the terminal IO window in the IAR
												embedded workbench. */
												printf( "\nTask\t     Abs Time\t     %%Time\n*****************************************" );
//												vTaskGetRunTimeStats( ( signed char * ) cBuffer );
//												printf( cBuffer );
												break;
												
			case mainMESSAGE_STATUS			:	/* The tick interrupt hook
												function has just informed this
												task of the system status.
												Generate a string in accordance
												with the status value. */
												prvGenerateStatusMessage( cBuffer, xReceivedMessage.cMessageValue );
												break;
												
			default							:	sprintf( cBuffer, "Unknown message" );
												break;
		}
		
		/* Output the message that was placed into the cBuffer array within the
		switch statement above. */
		printf( "%s", cBuffer );
	}
}
/*-----------------------------------------------------------*/

static void prvGenerateStatusMessage( char *pcBuffer, long lStatusValue )
{
	/* Just a utility function to convert a status value into a meaningful
	string for output onto the LCD. */
	switch( lStatusValue )
	{
		case pdPASS						:	sprintf( pcBuffer, "Task status = PASS" );
											break;
		case mainERROR_DYNAMIC_TASKS	:	sprintf( pcBuffer, "Error: Dynamic tasks" );
											break;
		case mainERROR_COM_TEST			:	sprintf( pcBuffer, "Err: loop connected?" ); /* Error in COM test - is the Loopback connector connected? */														
											break;
		case mainERROR_GEN_QUEUE_TEST 	:	sprintf( pcBuffer, "Error: Gen Q test" );
											break;
		default							:	sprintf( pcBuffer, "Unknown status" );
											break;
	}
}
/*-----------------------------------------------------------*/

static void prvButtonPollTask( void *pvParameters )
{
unsigned char ucLastState = pdFALSE, ucState;
xQueueMessage xMessage;

	/* This tasks performs the button polling functionality as described at the
	top of this file. */
	for( ;; )
	{
		/* Check the button state. */
		ucState = ( halButtonsPressed() & BUTTON_UP );
		if( ucState != ucLastState )
		{
			/* The state has changed, send a message to the LCD task. */
			xMessage.cMessageID = mainMESSAGE_BUTTON_UP;
			xMessage.cMessageValue = ucState;
			ucLastState = ucState;
			xQueueSend( xLCDQueue, &xMessage, portMAX_DELAY );
		}
		
		/* Block for 10 milliseconds so this task does not utilise all the CPU
		time and debouncing of the button is not necessary. */
		vTaskDelay( 10 / portTICK_RATE_MS );
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	halBoardInit();
	halButtonsInit( BUTTON_ALL );
	halButtonsInterruptEnable( BUTTON_SELECT );
	LFXT_Start (XT1DRIVE_0);
	Init_FLL_Settle( 25000, 488 );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
volatile unsigned short usLastRegTest1Counter = 0, usLastRegTest2Counter = 0;
portTickType xNextWakeTime, xCycleFrequency = mainNO_ERROR_CYCLE_TIME;
const char *pcStatusMessage = "OK";

	/* Initialise xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Place this task in the blocked state until it is time to run again. */
		vTaskDelayUntil( &xNextWakeTime, xCycleFrequency );

		/* Check the reg test tasks are still cycling.  They will stop incrementing
		their loop counters if they encounter an error. */
		if( usRegTest1Counter == usLastRegTest1Counter )
		{
			pcStatusMessage = "Error: RegTest1";
		}

		if( usRegTest2Counter == usLastRegTest2Counter )
		{
			pcStatusMessage = "Error: RegTest2";
		}

		usLastRegTest1Counter = usRegTest1Counter;
		usLastRegTest2Counter = usRegTest2Counter;
		
		printf( "%s, tick count = %u\n", pcStatusMessage, ( unsigned int ) xTaskGetTickCount() );
		fflush( stdout );
	}
}
/*-----------------------------------------------------------*/

void vApplicationSetupTimerInterrupt( void )
{
const unsigned short usACLK_Frequency_Hz = 32768;

	/* Ensure the timer is stopped. */
	TA0CTL = 0;

	/* Run the timer of the ACLK. */
	TA0CTL = TASSEL_1;

	/* Clear everything to start with. */
	TA0CTL |= TACLR;

	/* Set the compare match value according to the tick rate we want. */
	TA0CCR0 = usACLK_Frequency_Hz / configTICK_RATE_HZ;

	/* Enable the interrupts. */
	TA0CCTL0 = CCIE;

	/* Start up clean. */
	TA0CTL |= TACLR;

	/* Up mode. */
	TA0CTL |= MC_1;
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName )
{
	( void ) pxTask;
	( void ) pcTaskName;
	
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	__bis_SR_register( LPM3_bits + GIE );
}



