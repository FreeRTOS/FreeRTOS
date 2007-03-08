/*
	FreeRTOS.org V4.2.0 - Copyright (C) 2003-2007 Richard Barry.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS, without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	See http://www.FreeRTOS.org for documentation, latest information, license
	and contact details.  Please ensure to read the configuration and relevant
	port sections of the online documentation.
	***************************************************************************
*/

/*
	NOTE : Tasks run in system mode and the scheduler runs in Supervisor mode.
	The processor MUST be in supervisor mode when vTaskStartScheduler is
	called.  The demo applications included in the FreeRTOS.org download switch
	to supervisor mode prior to main being called.  If you are not using one of
	these demo application projects then ensure Supervisor mode is used.
*/

/*
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the demo application tasks.
 *
 * A few tasks are created that are not part of the standard demo.  These are
 * the 'LCD' task, the 'LCD Message' task, a WEB server task and the 'Check' 
 * task.
 *
 * The LCD task is the only task that accesses the LCD directly, so mutual
 * exclusion is ensured.  Any task wishing to display text sends the LCD task
 * a message containing a pointer to the string that should be displayed.
 * The LCD task itself just blocks on a queue waiting for such a message to 
 * arrive - processing each in turn.
 *
 * The LCD Message task does nothing other than periodically send messages to
 * the LCD task.  The messages originating from the LCD Message task are 
 * displayed on the top row of the LCD.
 *
 * The Check task only executes every three seconds but has the highest 
 * priority so is guaranteed to get processor time.  Its main function is to 
 * check that all the other tasks are still operational. Most tasks maintain 
 * a unique count that is incremented each time the task successfully completes 
 * a cycle of its function.  Should any error occur within such a task the 
 * count is permanently halted.  The check task sets a bit in an error status
 * flag should it find any counter variable at a value that indicates an
 * error has occurred.  The error flag value is converted to a string and sent 
 * to the LCD task for display on the bottom row on the LCD.
 */

/* Standard includes. */
#include <stdio.h>

/* Library includes. */
#include "91x_lib.h"

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo application includes. */
#include "lcd.h"
#include "flash.h"
#include "integer.h"
#include "PollQ.h"
#include "BlockQ.h"
#include "semtest.h"
#include "dynamic.h"
#include "partest.h"
#include "flop.h"
#include "comtest2.h"
#include "serial.h"

/* Priorities for the demo application tasks. */
#define mainLED_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + 4 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCOM_TEST_PRIORITY		( tskIDLE_PRIORITY + 3 )
#define mainLCD_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainMSG_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )

/* Delays used by the various tasks defined in this file. */
#define mainCHECK_PERIOD			( ( portTickType ) 3000 / portTICK_RATE_MS  )
#define mainSTRING_WRITE_DELAY		( 500 / portTICK_RATE_MS )
#define mainLCD_DELAY				( 20 / portTICK_RATE_MS )

/* Constants for the ComTest tasks. */
#define mainCOM_TEST_BAUD_RATE		( ( unsigned portLONG ) 115200 )
#define mainCOM_TEST_LED			( 3 )

/* The maximum number of messages that can be pending to be written to the LCD. */
#define mainLCD_QUEUE_LEN			( 6 )

/* Dimension the buffer used to write the error flag string. */
#define mainMAX_FLAG_STRING_LEN		( 32 )

/* The structure that is passed on the LCD message queue. */
typedef struct
{
	portCHAR **ppcMessageToDisplay; /*<< Points to a char* pointing to the message to display. */
	portBASE_TYPE xRow;				/*<< The row on which the message should be displayed. */
} xLCDMessage;
/*-----------------------------------------------------------*/

/*
 * The task that executes at the highest priority and calls
 * prvCheckOtherTasksAreStillRunning().  See the description at the top
 * of the file.
 */
static void vErrorChecks( void *pvParameters );

/*
 * Configure the processor clock and ports.
 */
static void prvSetupHardware( void );

/*
 * Checks that all the demo application tasks are still executing without error
 * - as described at the top of the file.  Called by vErrorChecks().
 */
static void prvCheckOtherTasksAreStillRunning( void );

/*
 * The WEB server task prototype.  The task is created in this file but defined
 * elsewhere. 
 */
extern void vuIP_Task(void *pvParameters);

/*
 * The task that displays text on the LCD.
 */
static void prvLCDTask( void * pvParameters );

/*
 * The task that sends messages to be displayed on the top row of the LCD.
 */
static void prvLCDMessageTask( void * pvParameters );

/*-----------------------------------------------------------*/

/* The queue used to pass messages to the LCD task. */
static xQueueHandle xLCDQueue;

/* Error status flag. */
static unsigned portLONG ulErrorFlags = 0;

/*-----------------------------------------------------------*/

/*
 * Starts all the other tasks, then starts the scheduler.
 */
void main( void )
{
	#ifdef DEBUG
		debug();
	#endif
	
	/* Setup any hardware that has not already been configured by the low
	level init routines. */
	prvSetupHardware();

	/* Create the queue used to send data to the LCD task. */
	xLCDQueue = xQueueCreate( mainLCD_QUEUE_LEN, sizeof( xLCDMessage ) );

	/* Start all the standard demo application tasks. */
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vStartDynamicPriorityTasks();
	vStartMathTasks( tskIDLE_PRIORITY );
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );

	/* Start the tasks which are defined in this file. */
	xTaskCreate( vErrorChecks, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );
	xTaskCreate( prvLCDTask, "LCD", configMINIMAL_STACK_SIZE, ( void * ) &xLCDQueue, mainLCD_TASK_PRIORITY, NULL );
	xTaskCreate( prvLCDMessageTask, "MSG", configMINIMAL_STACK_SIZE, ( void * ) &xLCDQueue, mainMSG_TASK_PRIORITY, NULL );

	/* Finally, create the WEB server task. */
	xTaskCreate( vuIP_Task, "uIP", configMINIMAL_STACK_SIZE * 3, NULL, mainCHECK_TASK_PRIORITY - 1, NULL );
	

	/* Start the scheduler.

	NOTE : Tasks run in system mode and the scheduler runs in Supervisor mode.
	The processor MUST be in supervisor mode when vTaskStartScheduler is
	called.  The demo applications included in the FreeRTOS.org download switch
	to supervisor mode prior to main being called.  If you are not using one of
	these demo application projects then ensure Supervisor mode is used here. */

	vTaskStartScheduler();

	/* We should never get here as control is now taken by the scheduler. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Configuration taken from the ST code.

	Set Flash banks size & address */
	FMI_BankRemapConfig( 4, 2, 0, 0x80000 ); 

	/* FMI Waite States */
	FMI_Config( FMI_READ_WAIT_STATE_2, FMI_WRITE_WAIT_STATE_0, FMI_PWD_ENABLE, FMI_LVD_ENABLE, FMI_FREQ_HIGH ); 

	/* Configure the FPLL = 96MHz, and APB to 48MHz. */
	SCU_PCLKDivisorConfig( SCU_PCLK_Div2 );
	SCU_PLLFactorsConfig( 192, 25, 2 ); 
	SCU_PLLCmd( ENABLE );
	SCU_MCLKSourceConfig( SCU_MCLK_PLL );

	WDG_Cmd( DISABLE );
	VIC_DeInit();

	/* GPIO8 clock source enable, used by the LCD. */
	SCU_APBPeriphClockConfig(__GPIO8, ENABLE);
	GPIO_DeInit(GPIO8);

	/* GPIO 9 clock source enable, used by the LCD. */
	SCU_APBPeriphClockConfig(__GPIO9, ENABLE);
	GPIO_DeInit(GPIO9);

	/* Enable VIC clock */
	SCU_AHBPeriphClockConfig(__VIC, ENABLE);
	SCU_AHBPeriphReset(__VIC, DISABLE);

	/* Peripheral initialisation. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

static void vErrorChecks( void *pvParameters )
{
static portCHAR cCheckVal[ mainMAX_FLAG_STRING_LEN ];
portCHAR *pcFlagString;
xLCDMessage xMessageToSend;
portTickType xLastWakeTime;
portCHAR *pcStringsToDisplay[] = {										
									"Check status flag"
								 };

	/* The parameters are not used in this task. */
	( void ) pvParameters;
	pcFlagString = &cCheckVal[ 0 ];	


	/* Initialise xLastWakeTime to ensure the first call to vTaskDelayUntil()
	functions correctly. */
	xLastWakeTime = xTaskGetTickCount();

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error. */

	for( ;; )
	{
		/* Delay until it is time to execute again. */
		vTaskDelayUntil( &xLastWakeTime, mainCHECK_PERIOD );
	
		/* Check all the other tasks to see if the error flag needs updating. */
		prvCheckOtherTasksAreStillRunning();
		
		/* Create a string indicating the error flag status. */
		sprintf( cCheckVal, "equals 0x%x       ", ulErrorFlags );
		xMessageToSend.xRow = Line2;

		/* Send the first part of the message to the LCD task. */
		xMessageToSend.ppcMessageToDisplay = &pcStringsToDisplay[ 0 ];
		xQueueSend( xLCDQueue, ( void * ) &xMessageToSend, 0 );
		vTaskDelay( mainSTRING_WRITE_DELAY );

		/* Send the second part of the message to the LCD task. */
		xMessageToSend.ppcMessageToDisplay = &pcFlagString;
		xQueueSend( xLCDQueue, ( void * ) &xMessageToSend, 0 );
	}
}
/*-----------------------------------------------------------*/

static void prvCheckOtherTasksAreStillRunning( void )
{
	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		ulErrorFlags |= 0x01;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		ulErrorFlags |=  0x02;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		ulErrorFlags |= 0x04;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		ulErrorFlags |= 0x08;
	}

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		ulErrorFlags |= 0x10;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		ulErrorFlags |= 0x20;
	}

	if( xAreMathsTaskStillRunning() != pdTRUE )
	{
		ulErrorFlags |= 0x40;
	}
}
/*-----------------------------------------------------------*/

static void prvLCDMessageTask( void * pvParameters )
{
xQueueHandle *pxLCDQueue;	
xLCDMessage xMessageToSend;
portBASE_TYPE xIndex = 0;

/* The strings that are written to the LCD. */
portCHAR *pcStringsToDisplay[] = {										
									"IAR             ",
									"STR912          ",
									"Demo            ",
									"www.FreeRTOS.org",
									""
								};


	/* To test the parameter passing mechanism, the queue on which messages are
	posted is passed in as a parameter even though it is available as a file
	scope variable anyway. */
	pxLCDQueue = ( xQueueHandle * ) pvParameters;

	for( ;; )
	{
		/* Wait until it is time to move onto the next string. */
		vTaskDelay( mainSTRING_WRITE_DELAY );		
		
		/* Configure the message object to send to the LCD task. */
		xMessageToSend.ppcMessageToDisplay = &pcStringsToDisplay[ xIndex ];
		xMessageToSend.xRow = Line1;
		
		/* Post the message to be displayed. */
		xQueueSend( *pxLCDQueue, ( void * ) &xMessageToSend, 0 );
		
		/* Move onto the next message, wrapping when necessary. */
		xIndex++;		
		if( *( pcStringsToDisplay[ xIndex ] ) == 0x00 )
		{
			xIndex = 0;

			/* Delay longer before going back to the start of the messages. */
			vTaskDelay( mainSTRING_WRITE_DELAY * 2 );
		}
	}
}
/*-----------------------------------------------------------*/

void prvLCDTask( void * pvParameters )
{
xQueueHandle *pxLCDQueue;
xLCDMessage xReceivedMessage;
portCHAR *pcString;

	/* To test the parameter passing mechanism, the queue on which messages are
	received is passed in as a parameter even though it is available as a file
	scope variable anyway. */
	pxLCDQueue = ( xQueueHandle * ) pvParameters;

	LCD_Init();

	for( ;; )    
	{
		/* Wait for a message to arrive. */
		if( xQueueReceive( *pxLCDQueue, &xReceivedMessage, portMAX_DELAY ) )
		{
			/* Where is the string we are going to display? */
			pcString = *xReceivedMessage.ppcMessageToDisplay;
  			LCD_DisplayString(xReceivedMessage.xRow, pcString, BlackText);

			/* The delay here is just to ensure the LCD task does not starve
			out lower priority tasks as writhing to the LCD can take a long
			time. */
			vTaskDelay( mainLCD_DELAY );
		}
	}
}
/*-----------------------------------------------------------*/

