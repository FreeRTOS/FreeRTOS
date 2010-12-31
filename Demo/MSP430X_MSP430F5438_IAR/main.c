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

/* Standard includes. */
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Hardware includes. */
#include "msp430.h"
#include "hal_MSP-EXP430F5438.h"

/* Standard demo includes. */
#include "ParTest.h"
#include "dynamic.h"
#include "comtest2.h"
#include "GenQTest.h"

/* Codes sent within messages to the LCD task so the LCD task can interpret
exactly what the message it just received was.  These are sent in the
cMessageID member of the message structure (defined below). */
#define mainMESSAGE_BUTTON_UP			( 1 )
#define mainMESSAGE_BUTTON_SEL			( 2 )
#define mainMESSAGE_STATUS				( 3 )

/* When the cMessageID member of the message sent to the LCD task is
mainMESSAGE_STATUS then these definitions are sent in the ulMessageValue member
of the same message and indicate what the status actually is. */
#define mainERROR_DYNAMIC_TASKS			( pdPASS + 1 )
#define mainERROR_COM_TEST				( pdPASS + 2 )
#define mainERROR_GEN_QUEUE_TEST		( pdPASS + 3 )
#define mainERROR_REG_TEST				( pdPASS + 4 )

/* The length of the queue (the number of items the queue can hold) that is used
to send messages from tasks and interrupts the the LCD task. */
#define mainQUEUE_LENGTH				( 5 )

#define mainLCD_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainCOM_TEST_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainGENERIC_QUEUE_TEST_PRIORITY	( tskIDLE_PRIORITY )

/* The LED used by the comtest tasks. See the comtest.c file for more
information.  In this case it is deliberately out of range as there are only
two LEDs, and they are both already in use. */
#define mainCOM_TEST_LED				( 3 )

/* The baud rate used by the comtest tasks described at the top of this file. */
#define mainCOM_TEST_BAUD_RATE			( 9600 )
/*-----------------------------------------------------------*/

extern void vRegTest1Task( void *pvParameters );
extern void vRegTest2Task( void *pvParameters );
static void prvSetupHardware( void );
static void prvTerminalIOTask( void *pvParameters );
static void prvButtonPollTask( void *pvParameters );
static void prvGenerateStatusMessage( char *pcBuffer, long lStatusValue );

/*-----------------------------------------------------------*/

volatile unsigned short usRegTest1Counter = 0, usRegTest2Counter = 0;
volatile unsigned long ulStatsOverflowCount = 0;

/* The handle of the queue used to send messages from tasks and interrupts to
the LCD task. */
static xQueueHandle xLCDQueue = NULL;

/* The definition of each message sent from tasks and interrupts to the LCD
task. */
typedef struct
{
	char cMessageID;	/* << States what the message is. */
	unsigned long ulMessageValue; /* << States the message value (can be an integer, string pointer, etc. depending on the value of cMessageID. */
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

		/* Create the standard demo tasks. */
		vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
		vStartDynamicPriorityTasks();
		vStartGenericQueueTasks( mainGENERIC_QUEUE_TEST_PRIORITY );
		
		/* Create the terminal IO and button poll tasks, as described at the top
		of this	file. */
		xTaskCreate( prvTerminalIOTask, ( signed char * ) "IO", configMINIMAL_STACK_SIZE * 2, NULL, mainLCD_TASK_PRIORITY, NULL );
		xTaskCreate( prvButtonPollTask, ( signed char * ) "BPoll", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );

		/* Create the register test tasks as described at the top of this file. */
		xTaskCreate( vRegTest1Task, "Reg1", configMINIMAL_STACK_SIZE, NULL, 0, NULL );
		xTaskCreate( vRegTest2Task, "Reg2", configMINIMAL_STACK_SIZE, NULL, 0, NULL );
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
unsigned char ucLine = 1;


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

		/* Clear the LCD if no room remains for any more text output. */
		if( ucLine > 8 )
		{
			halLcdClearScreen();
			ucLine = 0;
		}
		
		/* What is this message?  What does it contain? */
		switch( xReceivedMessage.cMessageID )
		{
			case mainMESSAGE_BUTTON_UP		:	/* The button poll task has just
												informed this task that the up
												button on the joystick input has
												been pressed or released. */
												sprintf( cBuffer, "Button up = %d", ( int ) xReceivedMessage.ulMessageValue );
												break;

			case mainMESSAGE_BUTTON_SEL		:	/* The select button interrupt
												just informed this task that the
												select button was pressed.
												Generate a table of task run time
												statistics and output this to
												the terminal IO window in the IAR
												embedded workbench. */
												printf( "\nTask\t     Abs Time\t     %%Time\n*****************************************" );
												fflush( stdout );
												vTaskGetRunTimeStats( ( signed char * ) cBuffer );
												printf( cBuffer );
												fflush( stdout );
												
												/* Also print out a message to
												the LCD - in this case the
												pointer to the string to print
												is sent directly in the
												lMessageValue member of the
												message.  This just demonstrates
												a different communication
												technique. */
												sprintf( cBuffer, "%s", ( char * ) xReceivedMessage.ulMessageValue );
												break;
												
			case mainMESSAGE_STATUS			:	/* The tick interrupt hook
												function has just informed this
												task of the system status.
												Generate a string in accordance
												with the status value. */
												prvGenerateStatusMessage( cBuffer, xReceivedMessage.ulMessageValue );
												break;
												
			default							:	sprintf( cBuffer, "Unknown message" );
												break;
		}
		
		halLcdPrintLine( cBuffer, ucLine,  OVERWRITE_TEXT );
		ucLine++;
	}
}
/*-----------------------------------------------------------*/

static void prvGenerateStatusMessage( char *pcBuffer, long lStatusValue )
{
	/* Just a utility function to convert a status value into a meaningful
	string for output onto the LCD. */
	switch( lStatusValue )
	{
		case pdPASS						:	sprintf( pcBuffer, "Status = PASS" );
											break;
		case mainERROR_DYNAMIC_TASKS	:	sprintf( pcBuffer, "Err: Dynamic tsks" );
											break;
		case mainERROR_COM_TEST			:	sprintf( pcBuffer, "Err: COM test" ); /* Error in COM test - is the Loopback connector connected? */														
											break;
		case mainERROR_GEN_QUEUE_TEST 	:	sprintf( pcBuffer, "Error: Gen Q test" );
											break;
		case mainERROR_REG_TEST			:	sprintf( pcBuffer, "Error: Reg test" );
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
		
		if( ucState != 0 )
		{
			ucState = pdTRUE;
		}
		
		if( ucState != ucLastState )
		{
			/* The state has changed, send a message to the LCD task. */
			xMessage.cMessageID = mainMESSAGE_BUTTON_UP;
			xMessage.ulMessageValue = ( unsigned long ) ucState;
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
unsigned long ulCPU_Clock_KHz = ( configCPU_CLOCK_HZ / 1000UL );

	halBoardInit();

	LFXT_Start( XT1DRIVE_0 );
	Init_FLL_Settle( ( unsigned short ) ulCPU_Clock_KHz, 488 );

	halButtonsInit( BUTTON_ALL );
	halButtonsInterruptEnable( BUTTON_SELECT );
	halLcdInit();
	halLcdBackLightInit();
	halLcdSetBackLight( 0 );
	halLcdSetContrast( 100 );
	halLcdClearScreen();
	
	halLcdPrintLine( " www.FreeRTOS.org", 0,  OVERWRITE_TEXT );
}
/*-----------------------------------------------------------*/

void vApplicationSetupTimerInterrupt( void )
{
const unsigned short usACLK_Frequency_Hz = 32768;

	/* Ensure the timer is stopped. */
	TA0CTL = 0;

	/* Run the timer from the ACLK. */
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
	/* Want to leave the SMCLK running so the COMTest tasks don't fail. */
	__bis_SR_register( LPM1_bits + GIE );
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
static unsigned short usLastRegTest1Counter = 0, usLastRegTest2Counter = 0;
static unsigned long ulCounter = 0;
static const unsigned long ulCheckFrequency = 5000UL / portTICK_RATE_MS;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

/* Define the status message that is sent to the LCD task.  By default the
status is PASS. */
static xQueueMessage xStatusMessage = { mainMESSAGE_STATUS, pdPASS };

	/* This is called from within the tick interrupt and performs the 'check'
	functionality as described in the comments at the top of this file.

	Is it time to perform the 'check' functionality again? */
	ulCounter++;
	if( ulCounter >= ulCheckFrequency )
	{
		/* See if the standard demo tasks are executing as expected, changing
		the message that is sent to the LCD task from PASS to an error code if
		any tasks set reports an error. */
		if( xAreComTestTasksStillRunning() != pdPASS )
		{
			xStatusMessage.ulMessageValue = mainERROR_COM_TEST;
		}

		if( xAreDynamicPriorityTasksStillRunning() != pdPASS )
		{
			xStatusMessage.ulMessageValue = mainERROR_DYNAMIC_TASKS;
		}
		
		if( xAreGenericQueueTasksStillRunning() != pdPASS )
		{
			xStatusMessage.ulMessageValue = mainERROR_GEN_QUEUE_TEST;
		}			

		/* Check the reg test tasks are still cycling.  They will stop incrementing
		their loop counters if they encounter an error. */
		if( usRegTest1Counter == usLastRegTest1Counter )
		{
			xStatusMessage.ulMessageValue = mainERROR_REG_TEST;
		}

		if( usRegTest2Counter == usLastRegTest2Counter )
		{
			xStatusMessage.ulMessageValue = mainERROR_REG_TEST;
		}

		usLastRegTest1Counter = usRegTest1Counter;
		usLastRegTest2Counter = usRegTest2Counter;
		
		/* As this is the tick hook the lHigherPriorityTaskWoken parameter is not
		needed (a context switch is going to be performed anyway), but it must
		still be provided. */
		xQueueSendFromISR( xLCDQueue, &xStatusMessage, &xHigherPriorityTaskWoken );
		ulCounter = 0;
	}

	if( ( ulCounter & 0xff ) == 0 )
	{
		if( ( LED_PORT_OUT & LED_1 ) == 0 )
		{
			LED_PORT_OUT |= LED_1;
			LED_PORT_OUT &= ~LED_2;
		}
		else
		{
			LED_PORT_OUT &= ~LED_1;
			LED_PORT_OUT |= LED_2;
		}
	}
}
/*-----------------------------------------------------------*/

#pragma vector=PORT2_VECTOR
__interrupt static void prvSelectButtonInterrupt(void)
{
/* Define the message sent to the LCD task from this interrupt. */
static const xQueueMessage xMessage = { mainMESSAGE_BUTTON_SEL, ( unsigned long ) "Select Interrupt" };
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* This is the interrupt handler for the joystick select button input.
	The button has been pushed, write a message to the LCD via the LCD task. */
	xQueueSendFromISR( xLCDQueue, &xMessage, &xHigherPriorityTaskWoken );

	P2IFG = 0;
	
	/* If writing to xLCDQueue caused a task to unblock, and the unblocked task
	has a priority equal to or above the task that this interrupt interrupted,
	then lHigherPriorityTaskWoken will have been set to pdTRUE internally within
	xQueuesendFromISR(), and portEND_SWITCHING_ISR() will ensure that this
	interrupt returns directly to the higher priority unblocked task. */
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

void vConfigureTimerForRunTimeStats( void )
{
	/* Ensure the timer is stopped. */
	TA1CTL = 0;

	/* Run the timer from the ACLK/4. */
	TA1CTL = TASSEL_1 | ID__4;

	/* Clear everything to start with. */
	TA1CTL |= TACLR;

	/* Enable the interrupts. */
	TA1CCTL0 = CCIE;

	/* Start up clean. */
	TA1CTL |= TACLR;

	/* Continuous mode. */
	TA1CTL |= MC__CONTINOUS;
}
/*-----------------------------------------------------------*/

#pragma vector=TIMER1_A0_VECTOR
static __interrupt void prvRunTimeStatsOverflowISR( void )
{
	ulStatsOverflowCount++;
}
/*-----------------------------------------------------------*/

inline unsigned long ulGetRunTimeStatsTime( void )
{
unsigned long ulReturn;

	TA1CTL &= ~MC__CONTINOUS;
	ulReturn = ( ( ulStatsOverflowCount << 16UL ) | ( unsigned long ) TA1R );
	TA1CTL |= MC__CONTINOUS;
	
	return ulReturn;
}




