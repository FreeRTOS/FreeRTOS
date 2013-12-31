/*
    FreeRTOS V8.0.0:rc1 - Copyright (C) 2014 Real Time Engineers Ltd.
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
*/

/* Standard includes. */
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo application includes. */
#include "partest.h"
#include "flash.h"
#include "dynamic.h"
#include "comtest2.h"
#include "GenQTest.h"

/* Eval board includes. */
#include "stm32_eval.h"
#include "stm32l152_eval_lcd.h"

/* The priorities assigned to the tasks. */
#define mainFLASH_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainLCD_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainCOM_TEST_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainGENERIC_QUEUE_TEST_PRIORITY	( tskIDLE_PRIORITY )

/* The length of the queue (the number of items the queue can hold) that is used
to send messages from tasks and interrupts the the LCD task. */
#define mainQUEUE_LENGTH				( 5 )

/* Codes sent within messages to the LCD task so the LCD task can interpret
exactly what the message it just received was.  These are sent in the
cMessageID member of the message structure (defined below). */
#define mainMESSAGE_BUTTON_UP			( 1 )
#define mainMESSAGE_BUTTON_SEL			( 2 )
#define mainMESSAGE_STATUS				( 3 )

/* When the cMessageID member of the message sent to the LCD task is
mainMESSAGE_STATUS then these definitions are sent in the lMessageValue member
of the same message and indicate what the status actually is. */
#define mainERROR_DYNAMIC_TASKS			( pdPASS + 1 )
#define mainERROR_COM_TEST				( pdPASS + 2 )
#define mainERROR_GEN_QUEUE_TEST		( pdPASS + 3 )

/* Baud rate used by the comtest tasks. */
#define mainCOM_TEST_BAUD_RATE			( 115200 )

/* The LED used by the comtest tasks. See the comtest.c file for more
information. */
#define mainCOM_TEST_LED				( 3 )

/* The LCD task uses printf() so requires more stack than most of the other
tasks. */
#define mainLCD_TASK_STACK_SIZE			( configMINIMAL_STACK_SIZE * 2 )

/*-----------------------------------------------------------*/

/*
 * System configuration is performed prior to main() being called, this function
 * configures the peripherals used by the demo application.
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

/* The time base for the run time stats is generated by the 16 bit timer 6.
Each time the timer overflows ulTIM6_OverflowCount is incremented.  Therefore,
when converting the total run time to a 32 bit number, the most significant two
bytes are given by ulTIM6_OverflowCount and the least significant two bytes are
given by the current TIM6 counter value.  Care must be taken with data
consistency when combining the two in case a timer overflow occurs as the
value is being read. */
unsigned long ulTIM6_OverflowCount = 0UL;

/* The handle of the queue used to send messages from tasks and interrupts to
the LCD task. */
static xQueueHandle xLCDQueue = NULL;

/* The definition of each message sent from tasks and interrupts to the LCD
task. */
typedef struct
{
	char cMessageID;	/* << States what the message is. */
	long lMessageValue; /* << States the message value (can be an integer, string pointer, etc. depending on the value of cMessageID). */
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
		/* Add the created queue to the queue registry so it can be viewed in
		the IAR FreeRTOS state viewer plug-in. */
		vQueueAddToRegistry( xLCDQueue, "LCDQueue" );

		/* Create the LCD and button poll tasks, as described at the top of this
		file. */
		xTaskCreate( prvLCDTask, "LCD", mainLCD_TASK_STACK_SIZE, NULL, mainLCD_TASK_PRIORITY, NULL );
		xTaskCreate( prvButtonPollTask, "ButPoll", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );

		/* Create a subset of the standard demo tasks. */
		vStartDynamicPriorityTasks();
		vStartLEDFlashTasks( mainFLASH_TASK_PRIORITY );
		vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
		vStartGenericQueueTasks( mainGENERIC_QUEUE_TEST_PRIORITY );

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
long lLine = Line1;
const long lFontHeight = (((sFONT *)LCD_GetFont())->Height);

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
	printf( "%d bytes of heap space remain unallocated\n", xPortGetFreeHeapSize() );

	for( ;; )
	{
		/* Wait for a message to be received.  Using portMAX_DELAY as the block
		time will result in an indefinite wait provided INCLUDE_vTaskSuspend is
		set to 1 in FreeRTOSConfig.h, therefore there is no need to check the
		function return value and the function will only return when a value
		has been received. */
		xQueueReceive( xLCDQueue, &xReceivedMessage, portMAX_DELAY );

		/* Clear the LCD if no room remains for any more text output. */
		if( lLine > Line9 )
		{
			LCD_Clear( Blue );
			lLine = 0;
		}

		/* What is this message?  What does it contain? */
		switch( xReceivedMessage.cMessageID )
		{
			case mainMESSAGE_BUTTON_UP		:	/* The button poll task has just
												informed this task that the up
												button on the joystick input has
												been pressed or released. */
												sprintf( cBuffer, "Button up = %d", xReceivedMessage.lMessageValue );
												break;

			case mainMESSAGE_BUTTON_SEL		:	/* The select button interrupt
												just informed this task that the
												select button was pressed.
												Generate a table of task run time
												statistics and output this to
												the terminal IO window in the IAR
												embedded workbench. */
												printf( "\nTask\t     Abs Time\t     %%Time\n*****************************************" );
												vTaskGetRunTimeStats( cBuffer );
												printf( cBuffer );

												/* Also print out a message to
												the LCD - in this case the
												pointer to the string to print
												is sent directly in the
												lMessageValue member of the
												message.  This just demonstrates
												a different communication
												technique. */
												sprintf( cBuffer, "%s", ( char * ) xReceivedMessage.lMessageValue );
												break;

			case mainMESSAGE_STATUS			:	/* The tick interrupt hook
												function has just informed this
												task of the system status.
												Generate a string in accordance
												with the status value. */
												prvGenerateStatusMessage( cBuffer, xReceivedMessage.lMessageValue );
												break;

			default							:	sprintf( cBuffer, "Unknown message" );
												break;
		}

		/* Output the message that was placed into the cBuffer array within the
		switch statement above. */
		LCD_DisplayStringLine( lLine, ( uint8_t * ) cBuffer );

		/* Move onto the next LCD line, ready for the next iteration of this
		loop. */
		lLine += lFontHeight;
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

void EXTI9_5_IRQHandler( void )
{
/* Define the message sent to the LCD task from this interrupt. */
const xQueueMessage xMessage = { mainMESSAGE_BUTTON_SEL, ( unsigned long ) "Select Interrupt!" };
long lHigherPriorityTaskWoken = pdFALSE;

	/* This is the interrupt handler for the joystick select button input.
	The button has been pushed, write a message to the LCD via the LCD task. */
	xQueueSendFromISR( xLCDQueue, &xMessage, &lHigherPriorityTaskWoken );

	EXTI_ClearITPendingBit( SEL_BUTTON_EXTI_LINE );

	/* If writing to xLCDQueue caused a task to unblock, and the unblocked task
	has a priority equal to or above the task that this interrupt interrupted,
	then lHigherPriorityTaskWoken will have been set to pdTRUE internally within
	xQueuesendFromISR(), and portEND_SWITCHING_ISR() will ensure that this
	interrupt returns directly to the higher priority unblocked task. */
	portEND_SWITCHING_ISR( lHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
static unsigned long ulCounter = 0;
static const unsigned long ulCheckFrequency = 5000UL / portTICK_RATE_MS;
long lHigherPriorityTaskWoken = pdFALSE;

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
		if( xAreDynamicPriorityTasksStillRunning() != pdPASS )
		{
			xStatusMessage.lMessageValue = mainERROR_DYNAMIC_TASKS;
		}

		if( xAreComTestTasksStillRunning() != pdPASS )
		{
			xStatusMessage.lMessageValue = mainERROR_COM_TEST;
		}

		if( xAreGenericQueueTasksStillRunning() != pdPASS )
		{
			xStatusMessage.lMessageValue = mainERROR_GEN_QUEUE_TEST;
		}

		/* As this is the tick hook the lHigherPriorityTaskWoken parameter is not
		needed (a context switch is going to be performed anyway), but it must
		still be provided. */
		xQueueSendFromISR( xLCDQueue, &xStatusMessage, &lHigherPriorityTaskWoken );
		ulCounter = 0;
	}
}
/*-----------------------------------------------------------*/

static void prvButtonPollTask( void *pvParameters )
{
long lLastState = pdTRUE;
long lState;
xQueueMessage xMessage;

	/* This tasks performs the button polling functionality as described at the
	top of this file. */
	for( ;; )
	{
		/* Check the button state. */
		lState = STM_EVAL_PBGetState( BUTTON_UP );
		if( lState != lLastState )
		{
			/* The state has changed, send a message to the LCD task. */
			xMessage.cMessageID = mainMESSAGE_BUTTON_UP;
			xMessage.lMessageValue = lState;
			lLastState = lState;
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
	/* Ensure that all 4 interrupt priority bits are used as the pre-emption
	priority. */
	NVIC_PriorityGroupConfig( NVIC_PriorityGroup_4 );

	/* Initialise the LEDs. */
	vParTestInitialise();

	/* Initialise the joystick inputs. */
	STM_EVAL_PBInit( BUTTON_UP, BUTTON_MODE_GPIO );
	STM_EVAL_PBInit( BUTTON_DOWN, BUTTON_MODE_GPIO );
	STM_EVAL_PBInit( BUTTON_LEFT, BUTTON_MODE_GPIO );
	STM_EVAL_PBInit( BUTTON_RIGHT, BUTTON_MODE_GPIO );

	/* The select button in the middle of the joystick is configured to generate
	an interrupt.  The Eval board library will configure the interrupt
	priority to be the lowest priority available so the priority need not be
	set here explicitly.  It is important that the priority is equal to or
	below that set by the configMAX_SYSCALL_INTERRUPT_PRIORITY value set in
	FreeRTOSConfig.h. */
	STM_EVAL_PBInit( BUTTON_SEL, BUTTON_MODE_EXTI );

	/* Initialize the LCD */
	STM32L152_LCD_Init();
	LCD_Clear( Blue );
	LCD_SetBackColor( Blue );
	LCD_SetTextColor( White );
	LCD_DisplayStringLine( Line0, "  www.FreeRTOS.org" );
}
/*-----------------------------------------------------------*/

void vConfigureTimerForRunTimeStats( void )
{
TIM_TimeBaseInitTypeDef  TIM_TimeBaseStructure;
NVIC_InitTypeDef NVIC_InitStructure;

	/* The time base for the run time stats is generated by the 16 bit timer 6.
	Each time the timer overflows ulTIM6_OverflowCount is incremented.
	Therefore, when converting the total run time to a 32 bit number, the most
	significant two bytes are given by ulTIM6_OverflowCount and the least
	significant two bytes are given by the current TIM6 counter value.  Care
	must be taken with data	consistency when combining the two in case a timer
	overflow occurs as the value is being read.

	The portCONFIGURE_TIMER_FOR_RUN_TIME_STATS() macro (in FreeRTOSConfig.h) is
	defined to call this function, so the kernel will call this function
	automatically at the appropriate time. */

	/* TIM6 clock enable */
	RCC_APB1PeriphClockCmd( RCC_APB1Periph_TIM6, ENABLE );

	/* The 32MHz clock divided by 5000 should tick (very) approximately every
	150uS and overflow a 16bit timer (very) approximately every 10 seconds. */
	TIM_TimeBaseStructure.TIM_Period = 65535;
	TIM_TimeBaseStructure.TIM_Prescaler = 5000;
	TIM_TimeBaseStructure.TIM_ClockDivision = TIM_CKD_DIV1;
	TIM_TimeBaseStructure.TIM_CounterMode = TIM_CounterMode_Up;

	TIM_TimeBaseInit( TIM6, &TIM_TimeBaseStructure );

	/* Only interrupt on overflow events. */
	TIM6->CR1 |= TIM_CR1_URS;

	/* Enable the interrupt. */
	TIM_ITConfig( TIM6, TIM_IT_Update, ENABLE );

	/* Enable the TIM6 global Interrupt */
	NVIC_InitStructure.NVIC_IRQChannel = TIM6_IRQn;
	NVIC_InitStructure.NVIC_IRQChannelPreemptionPriority = configLIBRARY_LOWEST_INTERRUPT_PRIORITY;
	NVIC_InitStructure.NVIC_IRQChannelSubPriority = 0x00; /* Not used as 4 bits are used for the pre-emption priority. */
	NVIC_InitStructure.NVIC_IRQChannelCmd = ENABLE;
	NVIC_Init(&NVIC_InitStructure);

	TIM_ClearITPendingBit( TIM6, TIM_IT_Update );
	TIM_Cmd( TIM6, ENABLE );
}
/*-----------------------------------------------------------*/

void TIM6_IRQHandler( void )
{
	/* Interrupt handler for TIM 6

	The time base for the run time stats is generated by the 16 bit timer 6.
	Each time the timer overflows ulTIM6_OverflowCount is incremented.
	Therefore, when converting the total run time to a 32 bit number, the most
	significant two bytes are given by ulTIM6_OverflowCount and the least
	significant two bytes are given by the current TIM6 counter value.  Care
	must be taken with data	consistency when combining the two in case a timer
	overflow occurs as the value is being read. */
	if( TIM_GetITStatus( TIM6, TIM_IT_Update) != RESET)
	{
		ulTIM6_OverflowCount++;
		TIM_ClearITPendingBit( TIM6, TIM_IT_Update );
	}
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configconfigCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues or
	semaphores. */
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* Called on each iteration of the idle task.  In this case the idle task
	just enters a low(ish) power mode. */
	PWR_EnterSleepMode( PWR_Regulator_ON, PWR_SLEEPEntry_WFI );
}



