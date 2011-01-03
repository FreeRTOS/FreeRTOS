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

/*
 * The documentation page for this demo available on http://www.FreeRTOS.org
 * documents the hardware configuration required to run this demo.  It also
 * provides more information on the expected demo application behaviour.
 *
 * main() creates all the demo application tasks, then starts the scheduler.
 * A lot of the created tasks are from the pool of "standard demo" tasks.  The
 * web documentation provides more details of the standard demo tasks, which
 * provide no particular functionality but do provide good examples of how to
 * use the FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks, interrupts and
 * tests are defined and/or created within this file:
 *
 * "LCD" task - The LCD task is a 'gatekeeper' task.  It is the only task that
 * is permitted to access the LCD and therefore ensures access to the LCD is
 * always serialised and there are no mutual exclusion issues.  When a task or
 * an interrupt wants to write to the LCD, it does not access the LCD directly
 * but instead sends the message to the LCD task.  The LCD task then performs
 * the actual LCD output.  This mechanism also allows interrupts to, in effect,
 * write to the LCD by sending messages to the LCD task.
 *
 * The LCD task is also a demonstration of a 'controller' task design pattern.
 * Some tasks do not actually send a string to the LCD task directly, but
 * instead send a command that is interpreted by the LCD task.  In a normal
 * application these commands can be control values or set points, in this
 * simple example the commands just result in messages being displayed on the
 * LCD.
 *
 * "Button Poll" task - This task polls the state of the 'up' key on the
 * joystick input device.  It uses the vTaskDelay() API function to control
 * the poll rate to ensure debouncing is not necessary and that the task does
 * not use all the available CPU processing time.
 *
 * Button Interrupt and run time stats display - The select button on the
 * joystick input device is configured to generate an external interrupt.  The
 * handler for this interrupt sends a message to LCD task, which interprets the
 * message to mean, firstly write a message to the LCD, and secondly, generate
 * a table of run time statistics.  The run time statistics are displayed as a
 * table that contains information on how much processing time each task has
 * been allocated since the application started to execute.  This information
 * is provided both as an absolute time, and as a percentage of the total run
 * time.  The information is displayed in the terminal IO window of the IAR
 * embedded workbench.  The online documentation for this demo shows a screen
 * shot demonstrating where the run time stats can be viewed.
 *
 * Idle Hook - The idle hook is a function that is called on each iteration of
 * the idle task.  In this case it is used to place the processor into a low
 * power mode.  Note however that this application is implemented using standard
 * components, and is therefore not optimised for low power operation.  Lower
 * power consumption would be achieved by converting polling tasks into event
 * driven tasks, and slowing the tick interrupt frequency.
 *
 * "Check" function called from the tick hook - The tick hook is called during
 * each tick interrupt.  It is called from an interrupt context so must execute
 * quickly, not attempt to block, and not call any FreeRTOS API functions that
 * do not end in "FromISR".  In this case the tick hook executes a 'check'
 * function.  This only executes every five seconds.  Its main function is to
 * check that all the standard demo tasks are still operational.  Each time it
 * executes it sends a status code to the LCD task.  The LCD task interprets the
 * code and displays an appropriate message - which will be PASS if no tasks
 * have reported any errors, or a message stating which task has reported an
 * error.
 *
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register still contains its expected value.  Each task uses
 * different values.  The tasks run with very low priority so get preempted
 * very frequently.  A check variable is incremented on each iteration of the
 * test loop.  A register containing an unexpected value is indicative of an
 * error in the context switching mechanism and will result in a branch to a
 * null loop - which in turn will prevent the check variable from incrementing
 * any further and allow the check task (described a above) to determine that an
 * error has occurred.  The nature of the reg test tasks necessitates that they
 * are written in assembly code.
 *
 * *NOTE 1* vApplicationSetupTimerInterrupt() is called by the kernel to let
 * the application set up a timer to generate the tick interrupt.  In this
 * example a timer A0 is used for this purpose.
 *
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

/* Priorities used by the test and demo tasks. */
#define mainLCD_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainCOM_TEST_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainGENERIC_QUEUE_TEST_PRIORITY	( tskIDLE_PRIORITY )

/* The LED used by the comtest tasks. See the comtest.c file for more
information.  */
#define mainCOM_TEST_LED				( 1 )

/* The baud rate used by the comtest tasks described at the top of this file. */
#define mainCOM_TEST_BAUD_RATE			( 38400 )

/* The maximum number of lines of text that can be displayed on the LCD. */
#define mainMAX_LCD_LINES				( 8 )

/* Just used to ensure parameters are passed into tasks correctly. */
#define mainTASK_PARAMETER_CHECK_VALUE	( ( void * ) 0xDEAD )
/*-----------------------------------------------------------*/

/*
 * The reg test tasks as described at the top of this file.
 */
extern void vRegTest1Task( void *pvParameters );
extern void vRegTest2Task( void *pvParameters );

/*
 * Configures clocks, LCD, port pints, etc. necessary to execute this demo.
 */
static void prvSetupHardware( void );

/*
 * Definition of the LCD/controller task described in the comments at the top
 * of this file.
 */
static void prvLCDTask( void *pvParameters );

/*
 * Definition of the button poll task described in the comments at the top of
 * this file.
 */
static void prvButtonPollTask( void *pvParameters );

/*
 * Converts a status message value into an appropriate string for display on
 * the LCD.  The string is written to pcBuffer.
 */
static void prvGenerateStatusMessage( char *pcBuffer, long lStatusValue );

/*-----------------------------------------------------------*/

/* Variables that are incremented on each iteration of the reg test tasks -
provided the tasks have not reported any errors.  The check task inspects these
variables to ensure they are still incrementing as expected.  If a variable
stops incrementing then it is likely that its associate task has stalled. */
volatile unsigned short usRegTest1Counter = 0, usRegTest2Counter = 0;

/* The handle of the queue used to send messages from tasks and interrupts to
the LCD task. */
static xQueueHandle xLCDQueue = NULL;

/* The definition of each message sent from tasks and interrupts to the LCD
task. */
typedef struct
{
	char cMessageID;				/* << States what the message is. */
	unsigned long ulMessageValue; 	/* << States the message value (can be an integer, string pointer, etc. depending on the value of cMessageID). */
} xQueueMessage;

/*-----------------------------------------------------------*/

/* The linker script tests the FreeRTOS ports use of 20bit addresses by
locating all code in high memory.  The following pragma ensures that main
remains in low memory. */
#pragma CODE_SECTION(main,".main")
void main( void )
{
	/* Configure the peripherals used by this demo application.  This includes
	configuring the joystick input select button to generate interrupts. */
	prvSetupHardware();

	/* Create the queue used by tasks and interrupts to send strings to the LCD
	task. */
	xLCDQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( xQueueMessage ) );

	/* If the queue could not be created then don't create any tasks that might
	attempt to use the queue. */
	if( xLCDQueue != NULL )
	{
		/* Add the created queue to the queue registry so it can be viewed in
		the IAR FreeRTOS state viewer plug-in. */
		vQueueAddToRegistry( xLCDQueue, ( signed char * ) "LCDQueue" );

		/* Create the standard demo tasks. */
		vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
		vStartDynamicPriorityTasks();
		vStartGenericQueueTasks( mainGENERIC_QUEUE_TEST_PRIORITY );
		
		/* Create the LCD, button poll and register test tasks, as described at
		the top	of this	file. */
		xTaskCreate( prvLCDTask, ( signed char * ) "LCD", configMINIMAL_STACK_SIZE * 2, mainTASK_PARAMETER_CHECK_VALUE, mainLCD_TASK_PRIORITY, NULL );
		xTaskCreate( prvButtonPollTask, ( signed char * ) "BPoll", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
		xTaskCreate( vRegTest1Task, ( signed char * ) "Reg1", configMINIMAL_STACK_SIZE, NULL, 0, NULL );
		xTaskCreate( vRegTest2Task, ( signed char * ) "Reg2", configMINIMAL_STACK_SIZE, NULL, 0, NULL );

		/* Start the scheduler. */
		vTaskStartScheduler();
	}

	/* If all is well then this line will never be reached.  If it is reached
	then it is likely that there was insufficient (FreeRTOS) heap memory space
	to create the idle task.  This may have been trapped by the malloc() failed
	hook function, if one is configured. */	
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvLCDTask( void *pvParameters )
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
	fflush( stdout );
	
	/* Just as a test of the port, and for no functional reason, check the task
	parameter contains its expected value. */
	if( pvParameters != mainTASK_PARAMETER_CHECK_VALUE )
	{
		halLcdPrintLine( "Invalid parameter", ucLine,  OVERWRITE_TEXT );
		ucLine++;		
	}

	for( ;; )
	{
		/* Wait for a message to be received.  Using portMAX_DELAY as the block
		time will result in an indefinite wait provided INCLUDE_vTaskSuspend is
		set to 1 in FreeRTOSConfig.h, therefore there is no need to check the
		function return value and the function will only return when a value
		has been received. */
		xQueueReceive( xLCDQueue, &xReceivedMessage, portMAX_DELAY );

		/* Clear the LCD if no room remains for any more text output. */
		if( ucLine > mainMAX_LCD_LINES )
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
												
												/* Also generate and output a
												table of task states. */
												printf( "\nTask\t\tState Priority\tStack\t#\n*****************************************" );
												fflush( stdout );
												vTaskList( ( signed char * ) cBuffer );
												printf( cBuffer );
												fflush( stdout );
												
												/* Finally print out a message 
												to the LCD - in this case the
												pointer to the string to print
												is sent directly in the
												ulMessageValue member of the
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
		
		/* Output the message that was placed into the cBuffer array within the
		switch statement above, then move onto the next line ready for the next
		message to arrive on the queue. */
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
		case mainERROR_COM_TEST			:	sprintf( pcBuffer, "Err: COM test" );
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
			/* The button was pressed. */
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
/* Convert a Hz value to a KHz value, as required by the Init_FLL_Settle()
function. */
unsigned long ulCPU_Clock_KHz = ( configCPU_CLOCK_HZ / 1000UL );

	taskDISABLE_INTERRUPTS();
	
	/* Disable the watchdog. */
	WDTCTL = WDTPW + WDTHOLD;
  
	halBoardInit();

	LFXT_Start( XT1DRIVE_0 );
	Init_FLL_Settle( ( unsigned short ) ulCPU_Clock_KHz, 488 );

	halButtonsInit( BUTTON_ALL );
	halButtonsInterruptEnable( BUTTON_SELECT );

	/* Initialise the LCD, but note that the backlight is not used as the
	library function uses timer A0 to modulate the backlight, and this file
	defines	vApplicationSetupTimerInterrupt() to also use timer A0 to generate
	the tick interrupt.  If the backlight is required, then change either the
	halLCD library or vApplicationSetupTimerInterrupt() to use a different
	timer.  Timer A1 is used for the run time stats time base6. */
	halLcdInit();
	halLcdSetContrast( 100 );
	halLcdClearScreen();
	
	halLcdPrintLine( " www.FreeRTOS.org", 0,  OVERWRITE_TEXT );
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

		/* Check the reg test tasks are still cycling.  They will stop
		incrementing their loop counters if they encounter an error. */
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

	/* Just periodically toggle an LED to show that the tick interrupt is
	running.  Note that this access LED_PORT_OUT in a non-atomic way, so tasks
	that access the same port must do so from a critical section. */
	if( ( ulCounter & 0xff ) == 0 )
	{
		if( ( LED_PORT_OUT & LED_1 ) == 0 )
		{
			LED_PORT_OUT |= LED_1;
		}
		else
		{
			LED_PORT_OUT &= ~LED_1;
		}
	}
}
/*-----------------------------------------------------------*/

#pragma vector=PORT2_VECTOR
interrupt void prvSelectButtonInterrupt( void )
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

/* The MSP430X port uses this callback function to configure its tick interrupt.
This allows the application to choose the tick interrupt source.
configTICK_VECTOR must also be set in FreeRTOSConfig.h to the correct
interrupt vector for the chosen tick interrupt source.  This implementation of
vApplicationSetupTimerInterrupt() generates the tick from timer A0, so in this
case configTICK_VECTOR is set to TIMER0_A0_VECTOR. */
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

void vApplicationIdleHook( void )
{
	/* Called on each iteration of the idle task.  In this case the idle task
	just enters a low(ish) power mode. */
	__bis_SR_register( LPM1_bits + GIE );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues or
	semaphores. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName )
{
	( void ) pxTask;
	( void ) pcTaskName;
	
	/* Run time stack overflow checking is performed if
	configconfigCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

