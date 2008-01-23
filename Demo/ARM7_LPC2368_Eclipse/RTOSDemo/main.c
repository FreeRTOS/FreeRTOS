/*
	FreeRTOS.org V4.7.0 - Copyright (C) 2003-2007 Richard Barry.

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
	See http://www.FreeRTOS.org for documentation, latest information, license 
	and contact details.  Please ensure to read the configuration and relevant 
	port sections of the online documentation.

	Also see http://www.SafeRTOS.com a version that has been certified for use
	in safety critical systems, plus commercial licensing, development and
	support options.
	***************************************************************************
*/

/*
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the standard demo application tasks.
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "LCD" task - the LCD task is a 'gatekeeper' task.  It is the only task that
 * is permitted to access the display directly.  Other tasks wishing to write a
 * message to the LCD send the message on a queue to the LCD task instead of
 * accessing the LCD themselves.  The LCD task just blocks on the queue waiting
 * for messages - waking and displaying the messages as they arrive.
 *
 * "Check" hook -  This only executes every five seconds from the tick hook.
 * Its main function is to check that all the standard demo tasks are still 
 * operational.  Should any unexpected behaviour within a demo task be discovered 
 * the tick hook will write an error to the LCD (via the LCD task).  If all the 
 * demo tasks are executing with their expected behaviour then the check task 
 * writes PASS to the LCD (again via the LCD task), as described above.
 *
 * "uIP" task -  This is the task that handles the uIP stack.  All TCP/IP
 * processing is performed in this task.
 */

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "Task.h"
#include "queue.h"
#include "semphr.h"

/* Demo app includes. */
#include "BlockQ.h"
#include "death.h"
#include "blocktim.h"
#include "LCD/portlcd.h"
#include "flash.h"
#include "partest.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "dynamic.h"

/* Demo application definitions. */
#define mainQUEUE_SIZE						( 3 )
#define mainCHECK_DELAY						( ( portTickType ) 5000 / portTICK_RATE_MS )
#define mainBASIC_WEB_STACK_SIZE            ( configMINIMAL_STACK_SIZE * 6 )

/* Task priorities. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainFLASH_PRIORITY                  ( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY           ( tskIDLE_PRIORITY + 3 )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY ) 

/* Constants to setup the PLL. */
#define mainPLL_MUL			( ( unsigned portLONG ) ( 12 - 1 ) )
#define mainPLL_DIV			( ( unsigned portLONG ) 0x0000 )
#define mainCPU_CLK_DIV		( ( unsigned portLONG ) 0x0003 )
#define mainPLL_ENABLE		( ( unsigned portLONG ) 0x0001 )
#define mainPLL_CONNECT		( ( ( unsigned portLONG ) 0x0002 ) | mainPLL_ENABLE )
#define mainPLL_FEED_BYTE1	( ( unsigned portLONG ) 0xaa )
#define mainPLL_FEED_BYTE2	( ( unsigned portLONG ) 0x55 )
#define mainPLL_LOCK		( ( unsigned portLONG ) 0x4000000 )
#define mainPLL_CONNECTED	( ( unsigned portLONG ) 0x2000000 )
#define mainOSC_ENABLE		( ( unsigned portLONG ) 0x20 )
#define mainOSC_STAT		( ( unsigned portLONG ) 0x40 )
#define mainOSC_SELECT		( ( unsigned portLONG ) 0x01 )

/* Constants to setup the MAM. */
#define mainMAM_TIM_3		( ( unsigned portCHAR ) 0x03 )
#define mainMAM_MODE_FULL	( ( unsigned portCHAR ) 0x02 )

/* 
 * The task that handles the uIP stack.  All TCP/IP processing is performed in
 * this task.
 */
extern void vuIP_Task( void *pvParameters );

/*
 * The LCD is written two by more than one task so is controlled by a 
 * 'gatekeeper' task.  This is the only task that is actually permitted to 
 * access the LCD directly.  Other tasks wanting to display a message send
 * the message to the gatekeeper.
 */
static void vLCDTask( void *pvParameters );

/* Configure the hardware as required by the demo. */
static void prvSetupHardware( void );

/* The queue used to send messages to the LCD task. */
xQueueHandle xLCDQueue;

/*-----------------------------------------------------------*/

int main( void )
{
	prvSetupHardware();
	
	/* Create the queue used by the LCD task.  Messages for display on the LCD
	are received via this queue. */
	xLCDQueue = xQueueCreate( mainQUEUE_SIZE, sizeof( xLCDMessage ) );

	/* Create the uIP task.  This uses the lwIP RTOS abstraction layer.*/
    xTaskCreate( vuIP_Task, ( signed portCHAR * ) "uIP", mainBASIC_WEB_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY - 1, NULL );

	/* Start the standard demo tasks. */
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
    vCreateBlockTimeTasks();
    vStartLEDFlashTasks( mainFLASH_PRIORITY );
    vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
    vStartQueuePeekTasks();   
    vStartDynamicPriorityTasks();

	/* Start the tasks defined within this file/specific to this demo. */
	xTaskCreate( vLCDTask, ( signed portCHAR * ) "LCD", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY - 1, NULL );

	/* Start the scheduler. */
	vTaskStartScheduler();

    /* Will only get here if there was insufficient memory to create the idle
    task. */
	return 0; 
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
unsigned portBASE_TYPE uxColumn = 0;
static xLCDMessage xMessage = { 0, "PASS" };
static unsigned portLONG ulTicksSinceLastDisplay = 0;

	/* Called from every tick interrupt.  Have enough ticks passed to make it
	time to perform our health status check again? */
	ulTicksSinceLastDisplay++;
	if( ulTicksSinceLastDisplay >= mainCHECK_DELAY )
	{
		ulTicksSinceLastDisplay = 0;
		
		/* Has an error been found in any task? */

        if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR - BLOCKQ";
		}

		if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR - BLOCKTIM";
		}

		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR - GENQ";
		}
		
		if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR - PEEKQ";
		}       
		
		if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR - DYNAMIC";
		}
        
        xMessage.xColumn++;

		/* Send the message to the LCD gatekeeper for display. */
		xQueueSendToBackFromISR( xLCDQueue, &xMessage, pdFALSE );
	}
}
/*-----------------------------------------------------------*/

void vLCDTask( void *pvParameters )
{
xLCDMessage xMessage;

	/* Initialise the LCD and display a startup message. */
	LCD_init();
	LCD_cur_off();
    LCD_cls();    
    LCD_gotoxy( 1, 1 );
    LCD_puts( "www.FreeRTOS.org" );

	for( ;; )
	{
		/* Wait for a message to arrive that requires displaying. */
		while( xQueueReceive( xLCDQueue, &xMessage, portMAX_DELAY ) != pdPASS );
		
		/* Display the message.  Print each message to a different position. */
		LCD_cls();
		LCD_gotoxy( ( xMessage.xColumn & 0x07 ) + 1, ( xMessage.xColumn & 0x01 ) + 1 );
		LCD_puts( xMessage.pcMessage );
	}

}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	#ifdef RUN_FROM_RAM
		/* Remap the interrupt vectors to RAM if we are are running from RAM. */
		SCB_MEMMAP = 2;
	#endif
	
	/* Disable the PLL. */
	PLLCON = 0;
	PLLFEED = mainPLL_FEED_BYTE1;
	PLLFEED = mainPLL_FEED_BYTE2;
	
	/* Configure clock source. */
	SCS |= mainOSC_ENABLE;
	while( !( SCS & mainOSC_STAT ) );
	CLKSRCSEL = mainOSC_SELECT; 
	
	/* Setup the PLL to multiply the XTAL input by 4. */
	PLLCFG = ( mainPLL_MUL | mainPLL_DIV );
	PLLFEED = mainPLL_FEED_BYTE1;
	PLLFEED = mainPLL_FEED_BYTE2;

	/* Turn on and wait for the PLL to lock... */
	PLLCON = mainPLL_ENABLE;
	PLLFEED = mainPLL_FEED_BYTE1;
	PLLFEED = mainPLL_FEED_BYTE2;
	CCLKCFG = mainCPU_CLK_DIV;	
	while( !( PLLSTAT & mainPLL_LOCK ) );
	
	/* Connecting the clock. */
	PLLCON = mainPLL_CONNECT;
	PLLFEED = mainPLL_FEED_BYTE1;
	PLLFEED = mainPLL_FEED_BYTE2;
	while( !( PLLSTAT & mainPLL_CONNECTED ) ); 
	
	/* 
	This code is commented out as the MAM does not work on the original revision
	LPC2368 chips.  If using Rev B chips then you can increase the speed though
	the use of the MAM.
	
	Setup and turn on the MAM.  Three cycle access is used due to the fast
	PLL used.  It is possible faster overall performance could be obtained by
	tuning the MAM and PLL settings.
	MAMCR = 0;
	MAMTIM = mainMAM_TIM_3;
	MAMCR = mainMAM_MODE_FULL;
	*/
	
	/* Setup the led's on the MCB2300 board */
	vParTestInitialise();
}







