/*
    FreeRTOS V8.2.3 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Hardware specifics. */
#include "iodefine.h"
#include "lcd.h"

/* States used by the LCD tasks. */
#define	lcdRIGHT_TO_LEFT	0U
#define	lcdLEFT_TO_RIGHT	1U
#define	lcdRUNNING			0U

/* Characters on each line. */
#define lcdSTRING_LEN		8 

/* Commands sent from the IRQ to the task controlling the second line of the
display. */
#define lcdSHIFT_BACK_COMMAND		0x01U
#define lcdSTART_STOP_COMMAND		0x02U
#define lcdSHIFT_FORWARD_COMMAND	0x03U

/* The length of the queue used to send commands from the ISRs. */
#define lcdCOMMAND_QUEUE_LENGTH		32U

/* Defines the minimum time that must pass between consecutive button presses
to accept a button press as a unique press rather than just a bounce. */
#define lcdMIN_TIME_BETWEEN_INTERRUPTS_MS ( 125UL / portTICK_PERIOD_MS )

/* Button interrupt handlers. */
#pragma interrupt ( prvIRQ1_Handler( vect = 65, enable ) )
static void prvIRQ1_Handler( void );

#pragma interrupt ( prvIRQ3_Handler( vect = 67, enable ) )
static void prvIRQ3_Handler( void );

#pragma interrupt ( prvIRQ4_Handler(vect = 68, enable ) )
static void prvIRQ4_Handler( void );

/* 
 * Setup the IO needed for the buttons to generate interrupts. 
 */
static void prvSetupButtonIOAndInterrupts( void );

/*
 * A task that simply scrolls a string from left to right, then back from the
 * right to the left.  This is done on the first line of the display.
 */
static void prvLCDTaskLine1( void *pvParameters );

/*
 * If no buttons are pushed, then this task acts as per prvLCDTaskLine1(), but
 * using the second line of the display.
 *
 * Using the buttons, it is possible to start and stop the scrolling of the 
 * text.  Once the scrolling has been stopped, other buttons can be used to
 * manually scroll the text either left or right.
 */ 
static void prvLCDTaskLine2( void *pvParameters );

/*
 * Looks at the direction the string is currently being scrolled in, and moves
 * the index into the portion of the string that can be seen on the display
 * either forward or backward as appropriate. 
 */
static prvScrollString( unsigned char *pucDirection, unsigned short *pusPosition, size_t xStringLength );

/* 
 * Displays lcdSTRING_LEN characters starting from pcString on the line of the
 * display requested by ucLine.
 */
static void prvDisplayNextString( unsigned char ucLine, char *pcString );

/*
 * Called from the IRQ interrupts, which are generated on button pushes.  Send
 * ucCommand to the task on the button command queue if 
 * lcdMIN_TIME_BETWEEN_INTERRUPTS_MS milliseconds have passed since the button
 * was last pushed (for debouncing). 
 */
static portBASE_TYPE prvSendCommandOnDebouncedInput( TickType_t *pxTimeLastInterrupt, unsigned char ucCommand );

/*-----------------------------------------------------------*/

/* The queue used to pass commands from the button interrupt handlers to the
prvLCDTaskLine2() task. */
static QueueHandle_t xButtonCommandQueue = NULL;

/* The mutex used to ensure only one task writes to the display at any one
time. */
static SemaphoreHandle_t xLCDMutex = NULL;

/* The string that is scrolled up and down the first line of the display. */
static const char cDataString1[] = "        http://www.FreeRTOS.org        ";

/* The string that is scrolled/nudged up and down the second line of the 
display. */
static const char cDataString2[] = "........Rx210 Highlights....1.56 DMips/MHz....DSP functions....1.62V-5.5V operation....200 uA/MHz....Up to 512 kBytes Flash....up to 64 kbytes SRAM....EE Dataflash with 100k w/e....1.3 uA in Real Time Clock Mode....Powerful Motor control timer....4 x 16-bit timers....4 x 8-bit timers....Full Real Time Clock calendar with calibration and alarm functions....Up to 16 channels 1 uS 12-bit ADC, with Dual group programmable SCAN, 3 sample and holds, sample accumulate function....DMA controller....Data Transfer Controller....Up to 9 serial Channels....Up to 6 USARTs ( with Simple I2C / SPI )....USART ( with unique Frame based protocol support )....Multimaster IIC....RSPI....Temperature Sensor....Event Link Controller....Comparators....Safety features include CRC....March X....Dual watchdog Timers with window and independent oscillator....ADC self test....I/O Pin Test....Supported with E1 on chip debugger and RSK210 evaluation system....Rx210 Highlights........";

/* Structures passed into the two tasks to inform them which line to use on the
display, how long to delay for, and which string to use. */
struct _LCD_Params xLCDLine1 = 
{
	LCD_LINE1, 215, ( char * ) cDataString1	
};

struct _LCD_Params xLCDLine2 = 
{
	LCD_LINE2, 350, ( char * ) cDataString2
};


/*-----------------------------------------------------------*/

void vStartButtonAndLCDDemo( void )
{
	prvSetupButtonIOAndInterrupts();
	InitialiseDisplay();

	/* Create the mutex used to guard the LCD. */
	xLCDMutex = xSemaphoreCreateMutex();
	configASSERT( xLCDMutex );
	
	/* Create the queue used to pass commands from the IRQ interrupts to the
	prvLCDTaskLine2() task. */
	xButtonCommandQueue = xQueueCreate( lcdCOMMAND_QUEUE_LENGTH, sizeof( unsigned char ) );
	configASSERT( xButtonCommandQueue );

	/* Start the two tasks as described at the top of this file. */
	xTaskCreate( prvLCDTaskLine1, "LCD1", configMINIMAL_STACK_SIZE * 3, ( void * ) &xLCDLine1, tskIDLE_PRIORITY + 1, NULL );
	xTaskCreate( prvLCDTaskLine2, "LCD2", configMINIMAL_STACK_SIZE * 3, ( void * ) &xLCDLine2, tskIDLE_PRIORITY + 2, NULL );
}
/*-----------------------------------------------------------*/

static void prvLCDTaskLine1( void *pvParameters )
{
struct _LCD_Params *pxLCDParamaters = ( struct _LCD_Params * ) pvParameters;
unsigned short usPosition = 0U;
unsigned char ucDirection = lcdRIGHT_TO_LEFT;
	
	for( ;; )
	{
		vTaskDelay( pxLCDParamaters->Speed / portTICK_PERIOD_MS );		

		/* Write the string. */
		prvDisplayNextString( pxLCDParamaters->Line, &( pxLCDParamaters->ptr_str[ usPosition ] ) );

		/* Move the string in whichever direction the scroll is currently going
		in. */
		prvScrollString( &ucDirection, &usPosition, strlen( pxLCDParamaters->ptr_str ) );
	}
}
/*-----------------------------------------------------------*/

static void prvLCDTaskLine2( void *pvParameters )
{
struct _LCD_Params *pxLCDParamaters = ( struct _LCD_Params * ) pvParameters;
unsigned short usPosition = 0U;
unsigned char ucDirection = lcdRIGHT_TO_LEFT, ucStatus = lcdRUNNING, ucQueueData;
TickType_t xDelayTicks = ( pxLCDParamaters->Speed / portTICK_PERIOD_MS );
	
	for(;;)
	{
		/* Wait for a message from an IRQ handler. */
		if( xQueueReceive( xButtonCommandQueue, &ucQueueData, xDelayTicks ) != pdPASS )
		{
			/* A message was not received before xDelayTicks ticks passed, so
			generate the next string to display and display it. */
			prvDisplayNextString( pxLCDParamaters->Line, &( pxLCDParamaters->ptr_str[ usPosition ] ) );
			
			/* Move the string in whichever direction the scroll is currently 
			going in. */
			prvScrollString( &ucDirection, &usPosition, strlen( pxLCDParamaters->ptr_str ) );			
		}
		else
		{
			/* A command was received.  Process it. */
			switch( ucQueueData )
			{
				case lcdSTART_STOP_COMMAND :

					/* If the LCD is running, top it.  If the LCD is stopped, start
					it. */
					ucStatus = !ucStatus;
					
					if( ucStatus == lcdRUNNING )
					{
						xDelayTicks = ( pxLCDParamaters->Speed / portTICK_PERIOD_MS );
					}
					else
					{
						xDelayTicks = portMAX_DELAY;
					}
					break;

					
				case lcdSHIFT_BACK_COMMAND :

					if( ucStatus != lcdRUNNING )
					{
						/* If not already at the start of the display.... */
						if( usPosition != 0U )
						{
							/* ....move the display position back by one char. */
							usPosition--;												
							prvDisplayNextString( pxLCDParamaters->Line, &( pxLCDParamaters->ptr_str[ usPosition ] ) );
						}
					}
					break;
				
				
				case lcdSHIFT_FORWARD_COMMAND :

					if( ucStatus != lcdRUNNING )
					{
						/* If not already at the end of the display.... */
						if( usPosition != ( strlen( pxLCDParamaters->ptr_str ) - ( lcdSTRING_LEN - 1 ) ) )
						{
							/* ....move the display position forward by one 
							char. */
							usPosition++;
							prvDisplayNextString( pxLCDParamaters->Line, &( pxLCDParamaters->ptr_str[ usPosition ] ) );
						}
					}
					break;
			}
		}
	}
}
/*-----------------------------------------------------------*/

void prvSetupButtonIOAndInterrupts( void )
{
	/* Configure SW 1-3 pin settings */
	PORT3.PDR.BIT.B1 = 0;		/* Switch 1 - Port 3.1 - IRQ1 */
	PORT3.PDR.BIT.B3 = 0;		/* Switch 2 - Port 3.3 - IRQ3 */
	PORT3.PDR.BIT.B4 = 0;		/* Switch 3 - Port 3.4 - IRQ4 */

	PORT3.PMR.BIT.B1 = 1;
	PORT3.PMR.BIT.B3 = 1;
	PORT3.PMR.BIT.B4 = 1;

	MPC.PWPR.BIT.B0WI = 0;		/* Writing to the PFSWE bit is enabled */
	MPC.PWPR.BIT.PFSWE = 1;		/* Writing to the PFS register is enabled */
	MPC.P31PFS.BIT.ISEL = 1;
	MPC.P33PFS.BIT.ISEL = 1;
	MPC.P34PFS.BIT.ISEL = 1;

	/* IRQ1	*/
	ICU.IER[ 0x08 ].BIT.IEN1 = 1;	
	ICU.IPR[ 65 ].BIT.IPR = configMAX_SYSCALL_INTERRUPT_PRIORITY - 1;
	ICU.IR[ 65 ].BIT.IR = 0;
	ICU.IRQCR[ 1 ].BIT.IRQMD = 2;	/* Rising edge */

	/* IRQ3	*/
	ICU.IER[ 0x08 ].BIT.IEN3 = 1;	
	ICU.IPR[ 67 ].BIT.IPR = configMAX_SYSCALL_INTERRUPT_PRIORITY - 1;
	ICU.IR[ 67 ].BIT.IR = 0;
	ICU.IRQCR[ 3 ].BIT.IRQMD = 2;	/* Rising edge */

	/* IRQ4	*/
	ICU.IER[ 0x08 ].BIT.IEN4 = 1;	
	ICU.IPR[ 68 ].BIT.IPR = configMAX_SYSCALL_INTERRUPT_PRIORITY - 1;
	ICU.IR[ 68 ].BIT.IR = 0;
	ICU.IRQCR[ 4 ].BIT.IRQMD = 2;	/* Rising edge */
}
/*-----------------------------------------------------------*/

static prvScrollString( unsigned char *pucDirection, unsigned short *pusPosition, size_t xStringLength )
{
	/* Check which way to scroll. */
	if( *pucDirection == lcdRIGHT_TO_LEFT )
	{
		/* Move to the next character. */
		( *pusPosition )++;
		
		/* Has the end of the string been reached? */
		if( ( *pusPosition ) == ( xStringLength - ( lcdSTRING_LEN - 1 ) ) )
		{
			/* Switch direction. */
			*pucDirection = lcdLEFT_TO_RIGHT;
			( *pusPosition )--;				
		}
	}
	else
	{
		/* Move (backward) to the next character. */
		( *pusPosition )--;
		if( *pusPosition == 0U )
		{
			/* Switch Direction. */
			*pucDirection = lcdRIGHT_TO_LEFT;				
		}
	}
}
/*-----------------------------------------------------------*/

static void prvDisplayNextString( unsigned char ucLine, char *pcString )
{
static char cSingleLine[ lcdSTRING_LEN + 1 ];

	xSemaphoreTake( xLCDMutex, portMAX_DELAY );
	strncpy( cSingleLine, pcString, lcdSTRING_LEN );
	DisplayString( ucLine, cSingleLine );
	xSemaphoreGive( xLCDMutex );
}
/*-----------------------------------------------------------*/

static portBASE_TYPE prvSendCommandOnDebouncedInput( TickType_t *pxTimeLastInterrupt, unsigned char ucCommand )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
TickType_t xCurrentTickCount;
	
	/* Check the time now for debouncing purposes. */
	xCurrentTickCount = xTaskGetTickCountFromISR();
	
	/* Has enough time passed since the button was last push to accept it as a
	unique press? */
	if( ( xCurrentTickCount - *pxTimeLastInterrupt ) > lcdMIN_TIME_BETWEEN_INTERRUPTS_MS )
	{
		xQueueSendToBackFromISR( xButtonCommandQueue, &ucCommand, &xHigherPriorityTaskWoken );
	}

	/* Remember the time now, so debounce can be performed again on the next
	interrupt. */	
	*pxTimeLastInterrupt = xCurrentTickCount;
	
	return xHigherPriorityTaskWoken;
}
/*-----------------------------------------------------------*/

static void prvIRQ1_Handler( void )
{
static TickType_t xTimeLastInterrupt = 0UL;
static const unsigned char ucCommand = lcdSHIFT_BACK_COMMAND;
portBASE_TYPE xHigherPriorityTaskWoken;

	xHigherPriorityTaskWoken = prvSendCommandOnDebouncedInput( &xTimeLastInterrupt, ucCommand );
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void prvIRQ3_Handler(void)
{
static TickType_t xTimeLastInterrupt = 0UL;
static const unsigned char ucCommand = lcdSTART_STOP_COMMAND;
portBASE_TYPE xHigherPriorityTaskWoken;

	xHigherPriorityTaskWoken = prvSendCommandOnDebouncedInput( &xTimeLastInterrupt, ucCommand );
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void prvIRQ4_Handler(void)
{
static TickType_t xTimeLastInterrupt = 0UL;
static const unsigned char ucCommand = lcdSHIFT_FORWARD_COMMAND;
portBASE_TYPE xHigherPriorityTaskWoken;

	xHigherPriorityTaskWoken = prvSendCommandOnDebouncedInput( &xTimeLastInterrupt, ucCommand );
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}

