/*
	FreeRTOS.org V5.0.2 - Copyright (C) 2003-2008 Richard Barry.

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
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

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
 * documentation provides more details of the standard demo application tasks.
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Fast Interrupt Test" - A high frequency periodic interrupt is generated
 * using a free running timer to demonstrate the use of the
 * configKERNEL_INTERRUPT_PRIORITY configuration constant.  The interrupt
 * service routine measures the number of processor clocks that occur between
 * each interrupt - and in so doing measures the jitter in the interrupt timing.
 * The maximum measured jitter time is latched in the ulMaxJitter variable, and
 * displayed on the LCD by the 'Check' task as described below.  The
 * fast interrupt is configured and handled in the timertest.c source file.
 *
 * "LCD" task - the LCD task is a 'gatekeeper' task.  It is the only task that
 * is permitted to access the display directly.  Other tasks wishing to write a
 * message to the LCD send the message on a queue to the LCD task instead of
 * accessing the LCD themselves.  The LCD task just blocks on the queue waiting
 * for messages - waking and displaying the messages as they arrive.  Messages
 * can either be a text string to display, or an instruction to update MEMS
 * input.  The MEMS input is used to display a ball that can be moved around
 * LCD by tilting the STM32 Primer.  45% is taken as the neutral position.
 *
 * "Check" task -  This only executes every five seconds but has the highest
 * priority so is guaranteed to get processor time.  Its main function is to
 * check that all the standard demo tasks are still operational.  Should any
 * unexpected behaviour within a demo task be discovered the 'check' task will
 * write an error to the LCD (via the LCD task).  If all the demo tasks are
 * executing with their expected behaviour then the check task writes PASS
 * along with the max jitter time to the LCD (again via the LCD task), as
 * described above.
 *
 * Tick Hook - A tick hook is provided just for demonstration purposes.  In 
 * this case it is used to periodically send an instruction to updated the
 * MEMS input to the LCD task.
 *
 */

/* CircleOS includes.  Some of the CircleOS peripheral functionality is 
utilised, although CircleOS itself is not used. */
#include "circle.h"

/* Standard includes. */
#include <string.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo app includes. */
#include "BlockQ.h"
#include "blocktim.h"
#include "GenQTest.h"
#include "partest.h"
#include "QPeek.h"

/* The bitmap used to display the FreeRTOS.org logo is stored in 16bit format
and therefore takes up a large proportion of the Flash space.  Setting this
parameter to 0 excludes the bitmap from the build, freeing up Flash space for
extra code. */
#define mainINCLUDE_BITMAP 					1

#if mainINCLUDE_BITMAP == 1
	#include "bitmap.h"
#endif

/* Task priorities. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainGEN_Q_PRIORITY					( tskIDLE_PRIORITY + 0 )
#define mainFLASH_TASK_PRIORITY				( tskIDLE_PRIORITY + 2 )

/* Splash screen related constants. */
#define mainBITMAP_Y 						( 38 )
#define mainBITMAP_X						( 18 )
#define mainURL_Y							( 8 )
#define mainURL_X							( 78 )
#define mainSPLASH_SCREEN_DELAY		( 2000 / portTICK_RATE_MS )

/* Text drawing related constants. */
#define mainLCD_CHAR_HEIGHT			( 13 )
#define mainLCD_MAX_Y				( 110 )

/* The maximum number of message that can be waiting for display at any one
time. */
#define mainLCD_QUEUE_SIZE					( 3 )

/* The check task uses the sprintf function so requires a little more stack. */
#define mainCHECK_TASK_STACK_SIZE			( configMINIMAL_STACK_SIZE + 50 )

/* The LCD task calls some of the CircleOS functions (for MEMS and LCD access),
these can require a larger stack. */
#define configLCD_TASK_STACK_SIZE			( configMINIMAL_STACK_SIZE + 50 )

/* Dimensions the buffer into which the jitter time is written. */
#define mainMAX_MSG_LEN						25

/* The time between cycles of the 'check' task. */
#define mainCHECK_DELAY						( ( portTickType ) 5000 / portTICK_RATE_MS )

/* The period at which the MEMS input should be updated. */
#define mainMEMS_DELAY						( ( portTickType ) 100 / portTICK_RATE_MS )

/* The rate at which the flash task toggles the LED. */
#define mainFLASH_DELAY						( ( portTickType ) 1000 / portTICK_RATE_MS )

/* The number of nano seconds between each processor clock. */
#define mainNS_PER_CLOCK ( ( unsigned portLONG ) ( ( 1.0 / ( double ) configCPU_CLOCK_HZ ) * 1000000000.0 ) )

/* The two types of message that can be sent to the LCD task. */
#define mainUPDATE_BALL_MESSAGE				( 0 )
#define mainWRITE_STRING_MESSAGE			( 1 )

/* Type of the message sent to the LCD task. */
typedef struct
{
	portBASE_TYPE xMessageType;
	signed char *pcMessage;
} xLCDMessage;

/*-----------------------------------------------------------*/

/*
 * Configure the clocks, GPIO and other peripherals as required by the demo.
 */
static void prvSetupHardware( void );

/*
 * The LCD is written two by more than one task so is controlled by a
 * 'gatekeeper' task.  This is the only task that is actually permitted to
 * access the LCD directly.  Other tasks wanting to display a message send
 * the message to the gatekeeper.
 */
static void prvLCDTask( void *pvParameters );

/*
 * Checks the status of all the demo tasks then prints a message to the
 * display.  The message will be either PASS - and include in brackets the
 * maximum measured jitter time (as described at the to of the file), or a
 * message that describes which of the standard demo tasks an error has been
 * discovered in.
 *
 * Messages are not written directly to the terminal, but passed to prvLCDTask
 * via a queue.
 *
 * The check task also receives instructions to update the MEMS input, which
 * in turn can also lead to the LCD being updated.
 */
static void prvCheckTask( void *pvParameters );

/*
 * Configures the timers and interrupts for the fast interrupt test as
 * described at the top of this file.
 */
extern void vSetupTimerTest( void );

/*
 * A cut down version of sprintf() used to percent the HUGE GCC library
 * equivalent from being included in the binary image. 
 */
extern int sprintf(char *out, const char *format, ...);

/*
 * Simple toggle the LED periodically for timing verification.
 */
static void prvFlashTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* The queue used to send messages to the LCD task. */
xQueueHandle xLCDQueue;

/*-----------------------------------------------------------*/

int main( void )
{
	#ifdef DEBUG
		debug();
	#endif

	prvSetupHardware();

	/* Create the queue used by the LCD task.  Messages for display on the LCD
	are received via this queue. */
	xLCDQueue = xQueueCreate( mainLCD_QUEUE_SIZE, sizeof( xLCDMessage ) );
	
	/* Start the standard demo tasks. */
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
    vCreateBlockTimeTasks();
	vStartGenericQueueTasks( mainGEN_Q_PRIORITY );
	vStartQueuePeekTasks();
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );

	/* Start the tasks defined within this file/specific to this demo. */
    xTaskCreate( prvCheckTask, ( signed portCHAR * ) "Check", mainCHECK_TASK_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );	
	xTaskCreate( prvLCDTask, ( signed portCHAR * ) "LCD", configLCD_TASK_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvFlashTask, ( signed portCHAR * ) "Flash", configMINIMAL_STACK_SIZE, NULL, mainFLASH_TASK_PRIORITY, NULL );

	/* Configure the timers used by the fast interrupt timer test. */
	vSetupTimerTest();
	
	/* Start the scheduler. */
	vTaskStartScheduler();
	
	/* Will only get here if there was not enough heap space to create the
	idle task. */
	return 0;
}
/*-----------------------------------------------------------*/

void prvLCDTask( void *pvParameters )
{
xLCDMessage xMessage;
portCHAR cY = mainLCD_CHAR_HEIGHT;
const portCHAR * const pcString = "www.FreeRTOS.org";
const portCHAR * const pcBlankLine = "                  ";

	DRAW_Init();

	#if mainINCLUDE_BITMAP == 1
		DRAW_SetImage( pucImage, mainBITMAP_Y, mainBITMAP_X, bmpBITMAP_HEIGHT, bmpBITMAP_WIDTH );
	#endif

	LCD_SetScreenOrientation( V9 );
	DRAW_DisplayString( mainURL_Y, mainURL_X, pcString, strlen( pcString ) );
	vTaskDelay( mainSPLASH_SCREEN_DELAY );
	LCD_FillRect( 0, 0, CHIP_SCREEN_WIDTH, CHIP_SCREEN_HEIGHT, RGB_WHITE );

	for( ;; )
	{
		/* Wait for a message to arrive that requires displaying. */
		while( xQueueReceive( xLCDQueue, &xMessage, portMAX_DELAY ) != pdPASS );

		/* Check the message type. */
		if( xMessage.xMessageType == mainUPDATE_BALL_MESSAGE )
		{
			/* Read the MEMS and update the ball display on the LCD if required. */
			MEMS_Handler();
			POINTER_Handler();
		}
		else
		{
			/* A text string was sent.  First blank off the old text string, then
			draw the new text on the next line down. */
			DRAW_DisplayString( 0, cY, pcBlankLine, strlen( pcBlankLine ) );

			cY -= mainLCD_CHAR_HEIGHT;
			if( cY <= ( mainLCD_CHAR_HEIGHT - 1 ) )
			{			
				/* Wrap the line onto which we are going to write the text. */
				cY = mainLCD_MAX_Y;
			}
			
			/* Display the message. */
			DRAW_DisplayString( 0, cY, xMessage.pcMessage, strlen( xMessage.pcMessage ) );
		}
	}
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
portTickType xLastExecutionTime;
xLCDMessage xMessage;
static signed portCHAR cPassMessage[ mainMAX_MSG_LEN ];
extern unsigned portSHORT usMaxJitter;

	/* Initialise the xLastExecutionTime variable on task entry. */
	xLastExecutionTime = xTaskGetTickCount();

	/* Setup the message we are going to send to the LCD task. */
	xMessage.xMessageType = mainWRITE_STRING_MESSAGE;
	xMessage.pcMessage = cPassMessage;
	
    for( ;; )
	{
		/* Perform this check every mainCHECK_DELAY milliseconds. */
		vTaskDelayUntil( &xLastExecutionTime, mainCHECK_DELAY );

		/* Has an error been found in any task?   If so then point the text
		we are going to send to the LCD task to an error message instead of
		the PASS message. */
		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR IN GEN Q";
		}
        if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR IN BLOCK Q";
		}
		else if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR IN BLOCK TIME";
		}
        else if( xArePollingQueuesStillRunning() != pdTRUE )
        {
            xMessage.pcMessage = "ERROR IN POLL Q";
        }
		else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR IN PEEK Q";
		}
		else
		{
			/* No errors were found in any task, so send a pass message
			with the max measured jitter time also included (as per the
			fast interrupt test described at the top of this file and on
			the online documentation page for this demo application). */
			sprintf( ( portCHAR * ) cPassMessage, "PASS [%uns]", ( ( unsigned portLONG ) usMaxJitter ) * mainNS_PER_CLOCK );
		}

		/* Send the message to the LCD gatekeeper for display. */
		xQueueSend( xLCDQueue, &xMessage, portMAX_DELAY );
	}
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
static unsigned portLONG ulCallCount;
static const xLCDMessage xMemsMessage = { mainUPDATE_BALL_MESSAGE, NULL };
static portBASE_TYPE xHigherPriorityTaskWoken;

	/* Periodically send a message to the LCD task telling it to update
	the MEMS input, and then if necessary the LCD. */
	ulCallCount++;
	if( ulCallCount >= mainMEMS_DELAY )
	{
		ulCallCount = 0;
		xHigherPriorityTaskWoken = pdFALSE;
		xQueueSendFromISR( xLCDQueue, &xMemsMessage, &xHigherPriorityTaskWoken );
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Start with the clocks in their expected state. */
	RCC_DeInit();

	/* Enable HSE (high speed external clock). */
	RCC_HSEConfig( RCC_HSE_ON );

	/* Wait till HSE is ready. */
	while( RCC_GetFlagStatus( RCC_FLAG_HSERDY ) == RESET )
	{
	}

	/* 2 wait states required on the flash. */
	*( ( unsigned portLONG * ) 0x40022000 ) = 0x02;

	/* HCLK = SYSCLK */
	RCC_HCLKConfig( RCC_SYSCLK_Div1 );

	/* PCLK2 = HCLK */
	RCC_PCLK2Config( RCC_HCLK_Div1 );

	/* PCLK1 = HCLK/2 */
	RCC_PCLK1Config( RCC_HCLK_Div2 );

	/* PLLCLK = 12MHz * 6 = 72 MHz. */
	RCC_PLLConfig( RCC_PLLSource_HSE_Div1, RCC_PLLMul_6 );

	/* Enable PLL. */
	RCC_PLLCmd( ENABLE );

	/* Wait till PLL is ready. */
	while(RCC_GetFlagStatus(RCC_FLAG_PLLRDY) == RESET)
	{
	}

	/* Select PLL as system clock source. */
	RCC_SYSCLKConfig( RCC_SYSCLKSource_PLLCLK );

	/* Wait till PLL is used as system clock source. */
	while( RCC_GetSYSCLKSource() != 0x08 )
	{
	}

	/* Enable GPIOA, GPIOB, GPIOC, GPIOD, GPIOE and AFIO clocks */
	RCC_APB2PeriphClockCmd(	RCC_APB2Periph_GPIOA | RCC_APB2Periph_GPIOB |RCC_APB2Periph_GPIOC
							| RCC_APB2Periph_GPIOD | RCC_APB2Periph_GPIOE | RCC_APB2Periph_AFIO, ENABLE );

	/* SPI2 Periph clock enable */
	RCC_APB1PeriphClockCmd( RCC_APB1Periph_SPI2, ENABLE );


	/* Set the Vector Table base address at 0x08000000 */
	NVIC_SetVectorTable( NVIC_VectTab_FLASH, 0x0 );

	NVIC_PriorityGroupConfig( NVIC_PriorityGroup_4 );
	
	/* Configure HCLK clock as SysTick clock source. */
	SysTick_CLKSourceConfig( SysTick_CLKSource_HCLK );
	
	/* Misc initialisation, including some of the CircleOS features.  Note
	that CircleOS itself is not used. */
	vParTestInitialise();
	MEMS_Init();
	POINTER_Init();
	POINTER_SetMode( POINTER_RESTORE_LESS );
}
/*-----------------------------------------------------------*/

static void prvFlashTask( void *pvParameters )
{
portTickType xLastExecutionTime;

	/* Initialise the xLastExecutionTime variable on task entry. */
	xLastExecutionTime = xTaskGetTickCount();

    for( ;; )
	{
		/* Simple toggle the LED periodically.  This just provides some timing
		verification. */
		vTaskDelayUntil( &xLastExecutionTime, mainFLASH_DELAY );
		vParTestToggleLED( 0 );
	}
}
/*-----------------------------------------------------------*/

void starting_delay( unsigned long ul )
{
	vTaskDelay( ( portTickType ) ul );
}



