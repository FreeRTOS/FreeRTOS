/*
 * FreeRTOS V202112.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
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
 * In addition to the standard demo tasks, the following tasks, interrupts tests
 * and timers are defined and/or created within this file:
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
 * Button Interrupt - The select button on the joystick input device is 
 * configured to generate an external interrupt.  The handler for this interrupt 
 * sends a message to LCD task, which then prints out a string to say the 
 * joystick select button was pressed.
 *
 * Idle Hook - The idle hook is a function that is called on each iteration of
 * the idle task.  In this case it is used to place the processor into a low
 * power mode.  Note however that this application is implemented using standard
 * components, and is therefore not optimised for low power operation.  Lower
 * power consumption would be achieved by converting polling tasks into event
 * driven tasks, and slowing the tick interrupt frequency, etc.
 *
 * "Check" callback function - Called each time the 'check' timer expires.  The
 * check timer executes every five seconds.  Its main function is to check that 
 * all the standard demo tasks are still operational.  Each time it executes it 
 * sends a status code to the LCD task.  The LCD task interprets the code and 
 * displays an appropriate message - which will be PASS if no tasks have 
 * reported any errors, or a message stating which task has reported an error.
 *
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register still contains its expected value.  Each task uses
 * different values.  The tasks run with very low priority so get preempted
 * very frequently.  A check variable is incremented on each iteration of the
 * test loop.  A register containing an unexpected value is indicative of an
 * error in the context switching mechanism and will result in a branch to a
 * null loop - which in turn will prevent the check variable from incrementing
 * any further and allow the check timer callback (described a above) to 
 * determine that an error has occurred.  The nature of the reg test tasks 
 * necessitates that they are written in assembly code.
 *
 * Tick hook function - called inside the RTOS tick function, this simple 
 * example does nothing but toggle an LED.
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
#include "timers.h"
#include "queue.h"

/* Hardware includes. */
#include "msp430.h"
#include "hal_MSP-EXP430F5438.h"

/* Standard demo includes. */
#include "ParTest.h"
#include "dynamic.h"
#include "comtest2.h"
#include "GenQTest.h"
#include "TimerDemo.h"
#include "countsem.h"

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
#define mainERROR_TIMER_TEST			( pdPASS + 5 )
#define mainERROR_COUNT_SEM_TEST		( pdPASS + 6 )

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

/* The baud rate used by the comtest tasks. */
#define mainCOM_TEST_BAUD_RATE			( 38400 )

/* The maximum number of lines of text that can be displayed on the LCD. */
#define mainMAX_LCD_LINES				( 8 )

/* Just used to ensure parameters are passed into tasks correctly. */
#define mainTASK_PARAMETER_CHECK_VALUE	( ( void * ) 0xDEAD )

/* The base period used by the timer test tasks. */
#define mainTIMER_TEST_PERIOD			( 50 )

/* The frequency at which the check timer (described in the comments at the top
of this file) will call its callback function. */
#define mainCHECK_TIMER_PERIOD			( 5000UL / ( unsigned long ) portTICK_PERIOD_MS )

/* Misc. */
#define mainDONT_BLOCK					( 0 )
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
static void prvGenerateStatusMessage( char *pcBuffer, unsigned long ulStatusValue );

/*
 * Defines the 'check' functionality as described at the top of this file.  This
 * function is the callback function for the 'check' timer. */
static void vCheckTimerCallback( TimerHandle_t xTimer );

/*-----------------------------------------------------------*/

/* Variables that are incremented on each iteration of the reg test tasks -
provided the tasks have not reported any errors.  The check task inspects these
variables to ensure they are still incrementing as expected.  If a variable
stops incrementing then it is likely that its associate task has stalled. */
volatile unsigned short usRegTest1Counter = 0, usRegTest2Counter = 0;

/* The handle of the queue used to send messages from tasks and interrupts to
the LCD task. */
static QueueHandle_t xLCDQueue = NULL;

/* The 'check' timer, as described at the top of this file. */
static TimerHandle_t xCheckTimer = NULL;

/* The definition of each message sent from tasks and interrupts to the LCD
task. */
typedef struct
{
	char cMessageID;				/* << States what the message is. */
	unsigned long ulMessageValue; 	/* << States the message value (can be an integer, string pointer, etc. depending on the value of cMessageID). */
} xQueueMessage;

/*-----------------------------------------------------------*/

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
		/* Create the standard demo tasks. */
		vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
		vStartDynamicPriorityTasks();
		vStartGenericQueueTasks( mainGENERIC_QUEUE_TEST_PRIORITY );
		vStartCountingSemaphoreTasks();
		
		/* Note that creating the timer test/demo tasks will fill the timer
		command queue.  This is intentional, and forms part of the test the tasks
		perform.  It does mean however that, after this function is called, no
		more timer commands can be sent until after the scheduler has been
		started (at which point the timer daemon will drained the timer command
		queue, freeing up space for more commands to be received). */
		vStartTimerDemoTask( mainTIMER_TEST_PERIOD );
		
		/* Create the LCD, button poll and register test tasks, as described at
		the top	of this	file. */
		xTaskCreate( prvLCDTask, "LCD", configMINIMAL_STACK_SIZE * 2, mainTASK_PARAMETER_CHECK_VALUE, mainLCD_TASK_PRIORITY, NULL );
		xTaskCreate( prvButtonPollTask, "BPoll", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
		xTaskCreate( vRegTest1Task, "Reg1", configMINIMAL_STACK_SIZE, NULL, 0, NULL );
		xTaskCreate( vRegTest2Task, "Reg2", configMINIMAL_STACK_SIZE, NULL, 0, NULL );

		/* Create the 'check' timer - the timer that periodically calls the
		check function as described at the top of this file.  Note that, for
		the reasons stated in the comments above the call to 
		vStartTimerDemoTask(), that the check timer is not actually started 
		until after the scheduler has been started. */
		xCheckTimer = xTimerCreate( "Check timer", mainCHECK_TIMER_PERIOD, pdTRUE, ( void * ) 0, vCheckTimerCallback ); 

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
static char cBuffer[ 50 ];
unsigned char ucLine = 1;

	/* Now the scheduler has been started (it must have been for this task to
	be running), start the check timer too.  The call to xTimerStart() will
	block until the command has been accepted. */
	if( xCheckTimer != NULL )
	{
		xTimerStart( xCheckTimer, portMAX_DELAY );
	}

	/* This is the only function that is permitted to access the LCD.
	
	First print out the number of bytes that remain in the FreeRTOS heap.  This
	is done after a short delay to ensure all the demo tasks have created all
	the objects they are going to use.  */
	vTaskDelay( mainTIMER_TEST_PERIOD * 10 );
	sprintf( cBuffer, "%d heap free", ( int ) xPortGetFreeHeapSize() );
	halLcdPrintLine( cBuffer, ucLine, OVERWRITE_TEXT );
	ucLine++;
	
	/* Just as a test of the port, and for no functional reason, check the task
	parameter contains its expected value. */
	if( pvParameters != mainTASK_PARAMETER_CHECK_VALUE )
	{
		halLcdPrintLine( "Invalid parameter", ucLine, OVERWRITE_TEXT );
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
												select button has been pressed.
												In this case the pointer to the 
												string to print is sent directly 
												in the ulMessageValue member of 
												the	message.  This just 
												demonstrates a different 
												communication technique. */
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

static void prvGenerateStatusMessage( char *pcBuffer, unsigned long ulStatusValue )
{
	/* Just a utility function to convert a status value into a meaningful
	string for output onto the LCD. */
	switch( ulStatusValue )
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
		case mainERROR_TIMER_TEST		:	sprintf( pcBuffer, "Error: Tmr test" );
											break;
		case mainERROR_COUNT_SEM_TEST	:	sprintf( pcBuffer, "Error: Count sem" );
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
		vTaskDelay( 10 / portTICK_PERIOD_MS );
	}
}
/*-----------------------------------------------------------*/

static void vCheckTimerCallback( TimerHandle_t xTimer )
{
static unsigned short usLastRegTest1Counter = 0, usLastRegTest2Counter = 0;

/* Define the status message that is sent to the LCD task.  By default the
status is PASS. */
static xQueueMessage xStatusMessage = { mainMESSAGE_STATUS, pdPASS };

	/* This is the callback function used by the 'check' timer, as described
	at the top of this file. */

	/* The parameter is not used. */
	( void ) xTimer;
	
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
	
	if( xAreCountingSemaphoreTasksStillRunning() != pdPASS )
	{
		xStatusMessage.ulMessageValue = mainERROR_COUNT_SEM_TEST;
	}
	
	if( xAreTimerDemoTasksStillRunning( ( TickType_t ) mainCHECK_TIMER_PERIOD ) != pdPASS )
	{
		xStatusMessage.ulMessageValue = mainERROR_TIMER_TEST;
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
	
	/* This is called from a timer callback so must not block! */
	xQueueSendToBack( xLCDQueue, &xStatusMessage, mainDONT_BLOCK );
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	taskDISABLE_INTERRUPTS();
	
	/* Disable the watchdog. */
	WDTCTL = WDTPW + WDTHOLD;
  
	halBoardInit();

	LFXT_Start( XT1DRIVE_0 );
	hal430SetSystemClock( configCPU_CLOCK_HZ, configLFXT_CLOCK_HZ );

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
static unsigned long ulCounter = 0;

	/* Is it time to toggle the LED again? */
	ulCounter++;

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

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
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


