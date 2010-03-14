/*
    FreeRTOS V6.0.4 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
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
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the demo application tasks.
 *
 * In addition to the standard demo tasks there are two tasks defined within
 * this file:
 *
 * 1 - The check task
 * The 'check' task is responsible for ensuring that all the standard demo
 * tasks are executing as expected.  It only executes every three seconds, but
 * has the highest priority within the system so is guaranteed to get execution
 * time.  Any errors discovered by the check task are latched until the
 * processor is reset.  At the end of each cycle the check task sends either
 * a pass or fail message to the 'print' task for display on the LCD.
 *
 * 2 - The print task
 * The print task is the LCD 'gatekeeper'.  That is, it is the only task that
 * should access the LCD directly so is always guaranteed exclusive (and
 * therefore consistent) access.  The print task simply blocks on a queue
 * to wait for messages from other tasks wishing to display text on the LCD.
 * When a message arrives it displays its contents on the LCD then blocks to
 * wait again.
 */

/* ST includes. */
#include "lcd.h"

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo application includes. */
#include "partest.h"
#include "flash.h"
#include "integer.h"
#include "blocktim.h"
#include "BlockQ.h"
#include "comtest2.h"
#include "dynamic.h"

/* Demo application task priorities. */
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + 4 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainLED_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainCOM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainLCD_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )

/* How often should we check the other tasks? */
#define mainCHECK_TASK_CYCLE_TIME	( 3000 )

/* The maximum offset into the pass and fail strings sent to the LCD.  An
offset is used a simple method of using a different column each time a message
is written to the LCD. */
#define mainMAX_WRITE_COLUMN		( 14 )

/* Baud rate used by the comtest tasks. */
#define mainCOM_TEST_BAUD_RATE		( 19200 )

/* The LED used by the comtest tasks. See the comtest.c file for more
information. */
#define mainCOM_TEST_LED			( 3 )

/* The number of messages that can be queued for display on the LCD at any one
time. */
#define mainLCD_QUEUE_LENGTH 		( 2 )

/* The time to wait when sending to mainLCD_QUEUE_LENGTH. */
#define mainNO_DELAY				( 0 )

/*-----------------------------------------------------------*/

/* The type that is posted to the LCD queue. */
typedef struct LCD_MESSAGE
{
	unsigned char *pucString; /* Points to the string to be displayed. */
	unsigned char ucLine;	  /* The line of the LCD that should be used. */
} LCDMessage;

/*-----------------------------------------------------------*/

/*
 * The task that executes at the highest priority and checks the operation of
 * all the other tasks in the system.  See the description at the top of the
 * file.
 */
static void vCheckTask( void *pvParameters );

/*
 * ST provided routine to configure the processor.
 */
static void prvSetupHardware(void);

/*
 * The only task that should access the LCD.  Other tasks wanting to write
 * to the LCD should send a message of type LCDMessage containing the
 * information to display to the print task.  The print task simply blocks
 * waiting for the arrival of such messages, displays the message, then blocks
 * again.
 */
static void vPrintTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* The queue used to communicate with the LCD print task. */
static xQueueHandle xLCDQueue;

/*-----------------------------------------------------------*/

/* Create all the demo application tasks, then start the scheduler. */
int main( void )
{
	/* Perform any hardware setup necessary. */
  	prvSetupHardware();
	vParTestInitialise();

	/* Create the queue used to communicate with the LCD print task. */
	xLCDQueue = xQueueCreate( mainLCD_QUEUE_LENGTH, sizeof( LCDMessage ) );	
	
  	/* Create the standard demo application tasks.  See the WEB documentation
	for more information on these tasks. */
	vCreateBlockTimeTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
	vStartDynamicPriorityTasks();
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	
	/* Create the tasks defined within this file. */
	xTaskCreate( vPrintTask, ( signed char * ) "LCD", configMINIMAL_STACK_SIZE, NULL, mainLCD_TASK_PRIORITY, NULL );
	xTaskCreate( vCheckTask, ( signed char * ) "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );
	
	vTaskStartScheduler();
	
	/* Execution will only reach here if there was insufficient heap to
	start the scheduler. */
	return 0;
}
/*-----------------------------------------------------------*/

static void vCheckTask( void *pvParameters )
{
static unsigned long ulErrorDetected = pdFALSE;	
portTickType xLastExecutionTime;
unsigned char *ucErrorMessage = ( unsigned char * )"              FAIL";
unsigned char *ucSuccessMessage = ( unsigned char * )"              PASS";
unsigned portBASE_TYPE uxColumn = mainMAX_WRITE_COLUMN;
LCDMessage xMessage;

	/* Initialise xLastExecutionTime so the first call to vTaskDelayUntil()
	works correctly. */
	xLastExecutionTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Wait until it is time for the next cycle. */
		vTaskDelayUntil( &xLastExecutionTime, mainCHECK_TASK_CYCLE_TIME );

		/* Has an error been found in any of the standard demo tasks? */
		
		if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
		{
			ulErrorDetected = pdTRUE;
		}

		if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			ulErrorDetected = pdTRUE;
		}

		if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			ulErrorDetected = pdTRUE;
		}
		
		if( xAreComTestTasksStillRunning() != pdTRUE )
		{
			ulErrorDetected = pdTRUE;
		}		
		
		if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
		{
			ulErrorDetected = pdTRUE;
		}		
	
		/* Calculate the LCD line on which we would like the message to
		be displayed.  The column variable is used for convenience as
		it is incremented each cycle anyway. */
		xMessage.ucLine = ( unsigned char ) ( uxColumn & 0x01 );

		/* The message displayed depends on whether an error was found or
		not.  Any discovered error is latched.  Here the column variable
		is used as an index into the text string as a simple way of moving
		the text from column to column. */		
		if( ulErrorDetected == pdFALSE )
		{
			xMessage.pucString = ucSuccessMessage + uxColumn;
		}
		else
		{
			xMessage.pucString = ucErrorMessage + uxColumn;			
		}		

		/* Send the message to the print task for display. */
		xQueueSend( xLCDQueue, ( void * ) &xMessage, mainNO_DELAY );
		
		/* Make sure the message is printed in a different column the next
		time around. */
		uxColumn--;
		if( uxColumn == 0 )
		{
			uxColumn = mainMAX_WRITE_COLUMN;
		}
	}
}

/*-----------------------------------------------------------*/

static void vPrintTask( void *pvParameters )
{
LCDMessage xMessage;

	for( ;; )
	{
		/* Wait until a message arrives. */
		while( xQueueReceive( xLCDQueue, ( void * ) &xMessage, portMAX_DELAY ) != pdPASS );
		
		/* The message contains the text to display, and the line on which the
		text should be displayed. */
		LCD_Clear();
		LCD_DisplayString( xMessage.ucLine, xMessage.pucString, BlackText );
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware(void)
{
ErrorStatus OSC4MStartUpStatus01;	

	/* ST provided routine. */

	/* MRCC system reset */
	MRCC_DeInit();
	
	/* Wait for OSC4M start-up */
	OSC4MStartUpStatus01 = MRCC_WaitForOSC4MStartUp();
	
	if(OSC4MStartUpStatus01 == SUCCESS)
	{
		/* Set HCLK to 60MHz */
		MRCC_HCLKConfig(MRCC_CKSYS_Div1);
		
		/* Set CKTIM to 60MHz */
		MRCC_CKTIMConfig(MRCC_HCLK_Div1);
		
		/* Set PCLK to 30MHz */
		MRCC_PCLKConfig(MRCC_CKTIM_Div2);
		
		/* Enable Flash Burst mode */
		CFG_FLASHBurstConfig(CFG_FLASHBurst_Enable);
		
		/* Set CK_SYS to 60 MHz */
		MRCC_CKSYSConfig(MRCC_CKSYS_OSC4MPLL, MRCC_PLL_Mul_15);
	}
	
	/* GPIO pins optimized for 3V3 operation */
	MRCC_IOVoltageRangeConfig(MRCC_IOVoltageRange_3V3);
	
	/* GPIO clock source enable */
	MRCC_PeripheralClockConfig(MRCC_Peripheral_GPIO, ENABLE);
	
	/* EXTIT clock source enable */
	MRCC_PeripheralClockConfig(MRCC_Peripheral_EXTIT, ENABLE);
	/* TB clock source enable */
	MRCC_PeripheralClockConfig(MRCC_Peripheral_TB, ENABLE);
	
	/* Initialize the demonstration menu */
	LCD_Init();
	
	LCD_DisplayString(Line1, ( unsigned char * ) "www.FreeRTOS.org", BlackText);
	LCD_DisplayString(Line2, ( unsigned char * ) "  STR750 Demo  ", BlackText);
	
	EIC_IRQCmd(ENABLE);
}
/*-----------------------------------------------------------*/

