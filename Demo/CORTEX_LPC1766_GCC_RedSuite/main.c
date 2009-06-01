/*
	FreeRTOS.org V5.3.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
*/


/*
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the standard demo application tasks
 * (which just exist to test the kernel port and provide an example of how to use
 * each FreeRTOS API function).
 * 
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "LCD" task - the LCD task is a 'gatekeeper' task.  It is the only task that
 * is permitted to access the display directly.  Other tasks wishing to write a
 * message to the LCD send the message on a queue to the LCD task instead of
 * accessing the LCD themselves.  The LCD task just blocks on the queue waiting
 * for messages - waking and displaying the messages as they arrive.  The use
 * of a gatekeeper in this manner permits both tasks and interrupts to write to 
 * the LCD without worrying about mutual exclusion.  This is demonstrated by the 
 * check hook (see below) which sends messages to the display even though it 
 * executes from an interrupt context.
 *
 * "Check" hook -  This only executes fully every five seconds from the tick 
 * hook.  Its main function is to check that all the standard demo tasks are 
 * still operational.  Should any unexpected behaviour be discovered within a 
 * demo task then the tick hook will write an error to the LCD (via the LCD task).  
 * If all the demo tasks are executing with their expected behaviour then the 
 * check task writes PASS to the LCD (again via the LCD task), as described above.
 *
 * LED tasks - These just demonstrate how multiple instances of a single task
 * definition can be created.  Each LED task simply toggles an LED.  The task
 * parameter is used to pass the number of the LED to be toggled into the task.
 * 
 * "uIP" task -  This is the task that handles the uIP stack.  All TCP/IP
 * processing is performed in this task.
 */

/* Standard includes. */
#include <stdio.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Hardware library includes. */
#include "LPC17xx_defs.h"

/* Demo app includes. */
#include "BlockQ.h"
#include "integer.h"
#include "blocktim.h"
#include "flash.h"
#include "partest.h"
#include "semtest.h"
#include "PollQ.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"
#include "lcd/portlcd.h"
#include "LED.h"

/*-----------------------------------------------------------*/

/* The number of LED tasks that will be created. */
#define mainNUM_LED_TASKS					( 6 )

/* The time between cycles of the 'check' functionality (defined within the
tick hook. */
#define mainCHECK_DELAY						( ( portTickType ) 5000 / portTICK_RATE_MS )

/* Task priorities. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainUIP_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainLCD_TASK_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainINTEGER_TASK_PRIORITY           ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )

/* The WEB server has a larger stack as it utilises stack hungry string
handling library calls. */
#define mainBASIC_WEB_STACK_SIZE            ( configMINIMAL_STACK_SIZE * 4 )

/* The length of the queue used to send messages to the LCD task. */
#define mainQUEUE_SIZE						( 3 )

/*-----------------------------------------------------------*/

/*
 * Configure the hardware for the demo.
 */
static void prvSetupHardware( void );

/*
 * Very simple task that toggles an LED.
 */
static void vLEDTask( void *pvParameters );

/* 
 * The task that handles the uIP stack.  All TCP/IP processing is performed in
 * this task.
 */
extern void vuIP_Task( void *pvParameters );

/*
 * The LCD gatekeeper task as described in the comments at the top of this file. 
 * */
static void vLCDTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* The queue used to send messages to the LCD task. */
xQueueHandle xLCDQueue;



/*-----------------------------------------------------------*/

int main( void )
{
long l;

	/* Configure the hardware for use by this demo. */
	prvSetupHardware();

	/* Start the standard demo tasks.  These are just here to exercise the
	kernel port and provide examples of how the FreeRTOS API can be used. */
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
    vCreateBlockTimeTasks();
    vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
    vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
    vStartIntegerMathTasks( mainINTEGER_TASK_PRIORITY );
    vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
    vStartQueuePeekTasks();
    vStartRecursiveMutexTasks();

	/* Start the tasks that toggle LEDs - the LED to toggle is passed in as the
	task parameter. */
	for( l = 0; l < mainNUM_LED_TASKS; l++ )
	{
		xTaskCreate( vLEDTask, (signed char *) "LED", configMINIMAL_STACK_SIZE, ( void * ) l, tskIDLE_PRIORITY, NULL );
	}
    
	/* Create the uIP task.  The WEB server runs in this task. */
    xTaskCreate( vuIP_Task, ( signed char * ) "uIP", mainBASIC_WEB_STACK_SIZE, ( void * ) NULL, mainUIP_TASK_PRIORITY, NULL );
	
	/* Create the queue used by the LCD task.  Messages for display on the LCD
	are received via this queue. */
	xLCDQueue = xQueueCreate( mainQUEUE_SIZE, sizeof( xLCDMessage ) );

	/* Start the LCD gatekeeper task - as described in the comments at the top
	of this file. */
	xTaskCreate( vLCDTask, ( signed portCHAR * ) "LCD", configMINIMAL_STACK_SIZE * 2, NULL, mainLCD_TASK_PRIORITY, NULL );
    
    /* Start the scheduler. */
	vTaskStartScheduler();

    /* Will only get here if there was insufficient memory to create the idle
    task.  The idle task is created within vTaskStartScheduler(). */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void vLEDTask( void *pvParameters ) 
{
/* The LED to toggle is passed in as the task parameter. */
long lLED = ( long ) pvParameters;
unsigned long ulLEDToToggle = 1 << lLED;

/* Calculate a delay period based on the LED number. */
unsigned long ulDelayPeriod = 100 * ( lLED + 1 );

	for( ;; )
	{
		/* Delay for the calculated time. */
		vTaskDelay( ulDelayPeriod );
		
		/* Toggle the LED before going back to delay again. */
		vToggleLED( ulLEDToToggle );
	}
}
/*-----------------------------------------------------------*/

void vLCDTask( void *pvParameters )
{
xLCDMessage xMessage;
unsigned long ulRow = 0;
char cIPAddr[ 17 ]; /* To fit max IP address length of xxx.xxx.xxx.xxx\0 */

	( void ) pvParameters;

	/* The LCD gatekeeper task as described in the comments at the top of this
	file. */
	
	/* Initialise the LCD and display a startup message that includes the
	configured IP address. */
	LCD_init();
	LCD_cur_off();
    LCD_cls();    
    LCD_gotoxy( 1, 1 );
    LCD_puts( "www.FreeRTOS.org" );
    LCD_gotoxy( 1, 2 );
    sprintf( cIPAddr, "%d.%d.%d.%d", configIP_ADDR0, configIP_ADDR1, configIP_ADDR2, configIP_ADDR3 );
    LCD_puts( cIPAddr );

	for( ;; )
	{
		/* Wait for a message to arrive to be displayed. */
		while( xQueueReceive( xLCDQueue, &xMessage, portMAX_DELAY ) != pdPASS );
		
		/* Clear the old message. */
		LCD_cls();
		
		/* Switch LCD rows, jut to make it obvious that messages are arriving. */
		ulRow++;		
		LCD_gotoxy( 1, ( ulRow & 0x01 ) + 1 );
		
		/* Display the received text. */
		LCD_puts( xMessage.pcMessage );
	}
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
static xLCDMessage xMessage = { "PASS" };
static unsigned portLONG ulTicksSinceLastDisplay = 0;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* Called from every tick interrupt as described in the comments at the top
	of this file.  
	 
	Have enough ticks passed to make it	time to perform our health status 
	check again? */
	ulTicksSinceLastDisplay++;
	if( ulTicksSinceLastDisplay >= mainCHECK_DELAY )
	{
		/* Reset the counter so these checks run again in mainCHECK_DELAY
		ticks time. */
		ulTicksSinceLastDisplay = 0;

		/* Has an error been found in any task? */
		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR: GEN Q";
		}
		else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR: PEEK Q";
		}
		else if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR: BLOCK Q";
		}
		else if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR: BLOCK TIME";
		}
	    else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	    {
	        xMessage.pcMessage = "ERROR: SEMAPHR";
	    }
	    else if( xArePollingQueuesStillRunning() != pdTRUE )
	    {
	        xMessage.pcMessage = "ERROR: POLL Q";
	    }
	    else if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	    {
	        xMessage.pcMessage = "ERROR: INT MATH";
	    }
	    else if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	    {
	    	xMessage.pcMessage = "ERROR: REC MUTEX";
	    }

		/* Send the message to the OLED gatekeeper for display.  The
		xHigherPriorityTaskWoken parameter is not actually used here
		as this function is running in the tick interrupt anyway - but
		it must still be supplied. */
		xHigherPriorityTaskWoken = pdFALSE;
		xQueueSendFromISR( xLCDQueue, &xMessage, &xHigherPriorityTaskWoken );
	}
}
/*-----------------------------------------------------------*/

void prvSetupHardware( void )
{
	/* Disable peripherals power. */
	PCONP = 0;							
	
	/* Enable GPIO power. */
	PCONP = PCONP_PCGPIO;				
	
	/* Disable TPIU. */
	PINSEL10 = 0;						
	
	/* Disconnect the main PLL. */
	PLL0CON &= ~PLLCON_PLLC;			
	PLL0FEED = PLLFEED_FEED1;
	PLL0FEED = PLLFEED_FEED2;
	while ((PLL0STAT & PLLSTAT_PLLC) != 0); 
	
	/* Turn off the main PLL. */
	PLL0CON &= ~PLLCON_PLLE;			
	PLL0FEED = PLLFEED_FEED1;
	PLL0FEED = PLLFEED_FEED2;
	while ((PLL0STAT & PLLSTAT_PLLE) != 0);    
	
	/* No CPU clock divider. */
	CCLKCFG = 0;
	
	/* OSCEN. */
	SCS = 0x20;							
	while ((SCS & 0x40) == 0);
	
	/* Use main oscillator. */
	CLKSRCSEL = 1;						
	PLL0CFG = (PLLCFG_MUL16 | PLLCFG_DIV1);
	
	PLL0FEED = PLLFEED_FEED1;
	PLL0FEED = PLLFEED_FEED2;  
	
	/*  Activate the PLL by turning it on then feeding the correct 
	sequence of bytes. */
	PLL0CON  = PLLCON_PLLE;
	PLL0FEED = PLLFEED_FEED1;
	PLL0FEED = PLLFEED_FEED2;
	
	/* 6x CPU clock divider (64 MHz) */
	CCLKCFG = 5;						
	
	/*  Wait for the PLL to lock. */
	while ((PLL0STAT & PLLSTAT_PLOCK) == 0);
	
	/*  Connect the PLL. */
	PLL0CON  = PLLCON_PLLC | PLLCON_PLLE;
	PLL0FEED = PLLFEED_FEED1;
	PLL0FEED = PLLFEED_FEED2;
	
	/*  Setup the peripheral bus to be the same as the PLL output (64 MHz). */
	PCLKSEL0 = 0x05555555;

	/* Configure LED GPIOs as outputs. */
	FIO2DIR  = 0xff;
	FIO2CLR  = 0xff;
	FIO2MASK = 0;
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed portCHAR *pcTaskName )
{
	/* This function will get called if a task overflows its stack. */
	
	( void ) pxTask;
	( void ) pcTaskName;
	
	for( ;; );
}
/*-----------------------------------------------------------*/

void vConfigureTimerForRunTimeStats( void )
{
const unsigned long TCR_COUNT_RESET = 2, CTCR_CTM_TIMER = 0x00, TCR_COUNT_ENABLE = 0x01;

	/* This function configures a timer that is used as the time base when
	collecting run time statistical information - basically the percentage
	of CPU time that each task is utilising.  It is called automatically when
	the scheduler is started (assuming configGENERATE_RUN_TIME_STATS is set
	to 1. */
	
	/* Power up and feed the timer. */
	PCONP |= 0x02UL;
	PCLKSEL0 = (PCLKSEL0 & (~(0x3<<2))) | (0x01 << 2);
	
	/* Reset Timer 0 */
	T0TCR = TCR_COUNT_RESET;
	
	/* Just count up. */
	T0CTCR = CTCR_CTM_TIMER;

	/* Prescale to a frequency that is good enough to get a decent resolution,
	but not too fast so as to overflow all the time. */
	T0PR =  ( configCPU_CLOCK_HZ / 10000UL ) - 1UL;

	/* Start the counter. */
	T0TCR = TCR_COUNT_ENABLE;
}
/*-----------------------------------------------------------*/

