/*
	FreeRTOS.org V5.2.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it 
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or 
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for 
	more details.

	You should have received a copy of the GNU General Public License along 
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59 
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.

	A special exception to the GPL is included to allow you to distribute a 
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details.


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




/* Standard includes. */
#include <stdio.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Hardware library includes. */
#include "LPC17xx_defs.h"


#define NUM_LEDS	8

/* Demo app includes. */
#include "BlockQ.h"
#include "death.h"
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

/*-----------------------------------------------------------*/

/* The time between cycles of the 'check' functionality (defined within the
tick hook. */
#define mainCHECK_DELAY						( ( portTickType ) 5000 / portTICK_RATE_MS )

/* Task priorities. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY           ( tskIDLE_PRIORITY + 3 )
#define mainINTEGER_TASK_PRIORITY           ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )

/* The period of the system clock in nano seconds.  This is used to calculate
the jitter time in nano seconds. */
#define mainNS_PER_CLOCK					( ( unsigned portLONG ) ( ( 1.0 / ( double ) configCPU_CLOCK_HZ ) * 1000000000.0 ) )

#define mainBASIC_WEB_STACK_SIZE            ( configMINIMAL_STACK_SIZE * 4 )
#define mainQUEUE_SIZE						( 3 )
/*-----------------------------------------------------------*/

/*
 * Configure the hardware for the demo.
 */
static void prvSetupHardware( void );

/*
 * Simply toggles the indicated LED.
 */
static void vToggleLED( unsigned portBASE_TYPE uxLED );

/*
 * Very simple task that toggles an LED.
 */
static void vLEDTask( void *pvParameters );

/* 
 * The task that handles the uIP stack.  All TCP/IP processing is performed in
 * this task.
 */
extern void vuIP_Task( void *pvParameters );

static void vLCDTask( void *pvParameters );

/* The queue used to send messages to the LCD task. */
xQueueHandle xLCDQueue;

/*-----------------------------------------------------------*/

int main( void )
{
long l;

	prvSetupHardware();

	/* Start the standard demo tasks. */
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
    vCreateBlockTimeTasks();
    vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
    vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
    vStartIntegerMathTasks( mainINTEGER_TASK_PRIORITY );
    vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
    vStartQueuePeekTasks();
    vStartRecursiveMutexTasks();

	/* Start 8 tasks, each of which toggles a different LED at a different rate. */
	for( l = 0; l < NUM_LEDS; l++ )
	{
		xTaskCreate( vLEDTask, (signed char *) "LED", configMINIMAL_STACK_SIZE, ( void * ) l, tskIDLE_PRIORITY+1, NULL );
	}
    
	/* Create the uIP task.  This uses the lwIP RTOS abstraction layer.*/
    xTaskCreate( vuIP_Task, ( signed char * ) "uIP", mainBASIC_WEB_STACK_SIZE, ( void * ) NULL, mainCHECK_TASK_PRIORITY - 1, NULL );
	
	/* Create the queue used by the LCD task.  Messages for display on the LCD
	are received via this queue. */
	xLCDQueue = xQueueCreate( mainQUEUE_SIZE, sizeof( xLCDMessage ) );

	/* Start the tasks defined within this file/specific to this demo. */
	xTaskCreate( vLCDTask, ( signed portCHAR * ) "LCD", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY - 1, NULL );
    
	/* The suicide tasks must be created last as they need to know how many
	tasks were running prior to their creation in order to ascertain whether
	or not the correct/expected number of tasks are running at any given time. */
    vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

    /* Start the scheduler. */
	vTaskStartScheduler();

    /* Will only get here if there was insufficient memory to create the idle
    task. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void vLEDTask( void *pvParameters ) 
{
/* The LED to toggle is passed in as the task paramter. */
long lLED = ( long ) pvParameters;
unsigned long ulLEDToToggle = 1 << lLED;

/* Calculate a delay period based on the LED number. */
unsigned long ulDelayPeriod = 100 * ( lLED + 1 );

	for( ;; )
	{
		vTaskDelay( ulDelayPeriod );
		vToggleLED( ulLEDToToggle );
	}
}
/*-----------------------------------------------------------*/

static void vToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( FIO2PIN & uxLED )
	{
		FIO2CLR = uxLED;
	}
	else
	{
		FIO2SET = uxLED;
	}
}
/*-----------------------------------------------------------*/

void prvSetupHardware( void )
{
	PCONP = 0;							/* Disable peripherals power. */
	PCONP = PCONP_PCGPIO;				/* Enable GPIO power. */
	PINSEL10 = 0;						/* Disable TPIU. */
	
	PLL0CON &= ~PLLCON_PLLC;			/* Disconnect the main PLL. */
	PLL0FEED = PLLFEED_FEED1;
	PLL0FEED = PLLFEED_FEED2;
	while ((PLL0STAT & PLLSTAT_PLLC) != 0); 
	
	PLL0CON &= ~PLLCON_PLLE;			/* Turn off the main PLL. */
	PLL0FEED = PLLFEED_FEED1;
	PLL0FEED = PLLFEED_FEED2;
	while ((PLL0STAT & PLLSTAT_PLLE) != 0);    
	
	CCLKCFG = 0;						/* No CPU clock divider. */
	SCS = 0x20;							/* OSCEN. */
	while ((SCS & 0x40) == 0);
	
	CLKSRCSEL = 1;						/* Use main oscillator. */
	PLL0CFG = (PLLCFG_MUL16 | PLLCFG_DIV1);
	
	PLL0FEED = PLLFEED_FEED1;
	PLL0FEED = PLLFEED_FEED2;  
	
	/*  Activate the PLL by turning it on then feeding the correct 
	sequence of bytes. */
	PLL0CON  = PLLCON_PLLE;
	PLL0FEED = PLLFEED_FEED1;
	PLL0FEED = PLLFEED_FEED2;
	
	CCLKCFG = 5;						/* 6x CPU clock divider (72 MHz) */
	
	/*  Wait for the PLL to lock. */
	while ((PLL0STAT & PLLSTAT_PLOCK) == 0);
	
	/*  Connect the PLL. */
	PLL0CON  = PLLCON_PLLC | PLLCON_PLLE;
	PLL0FEED = PLLFEED_FEED1;
	PLL0FEED = PLLFEED_FEED2;
	
	/*  Setup the peripheral bus to be the same as the PLL output (72 MHz). */
	PCLKSEL0 = 0x05555555;

	/* Configure LED GPIOs as outputs. */
	FIO2DIR  = 0xff;
	FIO2CLR  = 0xff;
	FIO2MASK = 0;
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed portCHAR *pcTaskName )
{
	( void ) pxTask;
	( void ) pcTaskName;
	
	for( ;; );
}
/*-----------------------------------------------------------*/

void vConfigureTimerForRunTimeStats( void )
{
	PCONP |= 0x02UL;
	_PCLKSEL0 = (_PCLKSEL0 & (~(0x3<<2))) | (0x01 << 2);
	
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

void vLCDTask( void *pvParameters )
{
xLCDMessage xMessage;

	( void ) pvParameters;

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
