/*
 * FreeRTOS V202212.00
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/*
 * This demo application creates four tasks (five including the idle task).
 * The application is limited in size to allow its compilation using
 * the KickStart version of the IAR compiler.
 *
 * The 'LCD Task' waits on a message queue for messages informing it what and
 * where to display text.  This is the only task that accesses the LCD
 * so mutual exclusion is guaranteed.
 *
 * The 'LCD Message Task' periodically sends strings to the LCD Task using
 * the message queue.  The strings are rotated to form a short message and
 * are written to the top row of the LCD.
 *
 * A loopback connector is required to ensure that each character transmitted
 * on the UART is also received on the same UART.  For test purposes the UART
 * FIFO's are not utalised in order to maximise the interrupt overhead.  Also
 * a pseudo random interval is used between the start of each transmission in
 * order that the resultant interrupts are more randomly distributed and
 * therefore more likely to highlight any problems.
 *
 * In addition the idle task makes repetitive calls to
 * vSetAndCheckRegisters().  This simply loads the general purpose registers
 * with a known value, then checks each register to ensure the held value is
 * still correct.  As a low priority task this checking routine is likely to
 * get repeatedly swapped in and out.  A register being found to contain an
 * incorrect value is therefore indicative of an error in the task switching
 * mechanism.
 *
 */

/* standard include files. */
#include <stdio.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo application include files. */
#include "partest.h"
#include "commstest.h"

/* Library include files. */
#include "DriverLib.h"

/* The time to delay between writing each character to the LCD. */
#define mainCHAR_WRITE_DELAY		( 2 / portTICK_PERIOD_MS )

/* The time to delay between writing each string to the LCD. */
#define mainSTRING_WRITE_DELAY		( 400 / portTICK_PERIOD_MS )

#define mainADC_DELAY				( 200 / portTICK_PERIOD_MS )

/* The length of the queue used to send messages to the LCD task. */
#define mainLCD_QUEUE_LEN			( 3 )

/* The task priorities. */
#define mainLCD_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainMSG_TASK_PRIORITY		( mainLCD_TASK_PRIORITY - 1 )
#define mainCOMMS_RX_TASK_PRIORITY	( tskIDLE_PRIORITY + 1 )

/* The LCD had two rows. */
#define mainTOP_ROW		0
#define mainBOTTOM_ROW 	1

/* Dimension for the buffer into which the ADC value string is written. */
#define mainMAX_ADC_STRING_LEN	20

/* The LED that is lit should an error be detected in any of the tasks */
#define mainFAIL_LED			( 7 )

/*-----------------------------------------------------------*/

/*
 * The task that displays text on the LCD.
 */
static void prvLCDTask( void * pvParameters );

/*
 * The task that sends messages to be displayed on the top row of the LCD.
 */
static void prvLCDMessageTask( void * pvParameters );

/*
 * Function to simply set a known value into the general purpose registers
 * then read them back to ensure they remain set correctly.  An incorrect value
 * being indicative of an error in the task switching mechanism.
 */
extern void vSetAndCheckRegisters( void );

/*
 * Latch the LED that indicates that an error has occurred.
 */
void vSetErrorLED( void );

/*
 * Thread safe write to the PDC.
 */
static void prvPDCWrite( char cAddress, char cData );

/*
 * Sets up the hardware used by the demo.
 */
static void prvSetupHardware( void );


/*-----------------------------------------------------------*/

/* The structure that is passed on the LCD message queue. */
typedef struct
{
	char **ppcMessageToDisplay; /*<< Points to a char* pointing to the message to display. */
	portBASE_TYPE xRow;				/*<< The row on which the message should be displayed. */
} xLCDMessage;

/* Error flag set to pdFAIL if an error is encountered in the tasks
defined within this file. */
unsigned portBASE_TYPE uxErrorStatus = pdPASS;

/* The queue used to transmit messages to the LCD task. */
static QueueHandle_t xLCDQueue;

/*-----------------------------------------------------------*/

/*
 * Setup the hardware, create the tasks, then start the scheduler.
 */
void main( void )
{
	/* Create the queue used by tasks wanting to write to the LCD. */
	xLCDQueue = xQueueCreate( mainLCD_QUEUE_LEN, sizeof( xLCDMessage ) );

	/* Setup the ports used by the demo and the clock. */
	prvSetupHardware();

	xTaskCreate( vCommsRxTask, "CMS", configMINIMAL_STACK_SIZE, NULL, mainCOMMS_RX_TASK_PRIORITY, NULL );

	/* Create the task that waits for messages to display on the LCD, plus the
	task that sends messages for display (as described at the top
	of this file. */
	xTaskCreate( prvLCDTask, "LCD", configMINIMAL_STACK_SIZE, ( void * ) &xLCDQueue, mainLCD_TASK_PRIORITY, NULL );
	xTaskCreate( prvLCDMessageTask, "MSG", configMINIMAL_STACK_SIZE, ( void * ) &xLCDQueue, mainMSG_TASK_PRIORITY, NULL );

	/* Start the scheduler running the tasks just created. */
	vTaskStartScheduler();

	/* Should not get here unless we did not have enough memory to start the
	scheduler. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvLCDMessageTask( void * pvParameters )
{
/* The strings that are written to the LCD. */
char *pcStringsToDisplay[] = {
									"IAR             ",
									"Stellaris       ",
									"Demo            ",
									"www.FreeRTOS.org",
									""
								};

QueueHandle_t *pxLCDQueue;
xLCDMessage xMessageToSend;
portBASE_TYPE xIndex = 0;

	/* To test the parameter passing mechanism, the queue on which messages are
	posted is passed in as a parameter even though it is available as a file
	scope variable anyway. */
	pxLCDQueue = ( QueueHandle_t * ) pvParameters;

	for( ;; )
	{
		/* Wait until it is time to move onto the next string. */
		vTaskDelay( mainSTRING_WRITE_DELAY );

		/* Create the message object to send to the LCD task. */
		xMessageToSend.ppcMessageToDisplay = &pcStringsToDisplay[ xIndex ];
		xMessageToSend.xRow = mainTOP_ROW;

		/* Post the message to be displayed. */
		if( !xQueueSend( *pxLCDQueue, ( void * ) &xMessageToSend, 0 ) )
		{
			uxErrorStatus = pdFAIL;
		}

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
unsigned portBASE_TYPE uxIndex;
QueueHandle_t *pxLCDQueue;
xLCDMessage xReceivedMessage;
char *pcString;
const unsigned char ucCFGData[] = {
											0x30,   /* Set data bus to 8-bits. */
											0x30,
											0x30,
											0x3C,   /* Number of lines/font. */
											0x08,   /* Display off. */
											0x01,   /* Display clear. */
											0x06,   /* Entry mode [cursor dir][shift]. */
											0x0C	/* Display on [display on][curson on][blinking on]. */
									  };

	/* To test the parameter passing mechanism, the queue on which messages are
	received is passed in as a parameter even though it is available as a file
	scope variable anyway. */
	pxLCDQueue = ( QueueHandle_t * ) pvParameters;

	/* Configure the LCD. */
	uxIndex = 0;
	while( uxIndex < sizeof( ucCFGData ) )
	{
		prvPDCWrite( PDC_LCD_CSR, ucCFGData[ uxIndex ] );
		uxIndex++;
		vTaskDelay( mainCHAR_WRITE_DELAY );
	}

	/* Turn the LCD Backlight on. */
	prvPDCWrite( PDC_CSR, 0x01 );

	/* Clear display. */
	vTaskDelay( mainCHAR_WRITE_DELAY );
	prvPDCWrite( PDC_LCD_CSR, LCD_CLEAR );

	uxIndex = 0;
	for( ;; )
	{
		/* Wait for a message to arrive. */
		if( xQueueReceive( *pxLCDQueue, &xReceivedMessage, portMAX_DELAY ) )
		{
			/* Which row does the received message say to write to? */
			PDCLCDSetPos( 0, xReceivedMessage.xRow );

			/* Where is the string we are going to display? */
			pcString = *xReceivedMessage.ppcMessageToDisplay;

			while( *pcString )
			{
				/* Don't write out the string too quickly as LCD's are usually
				pretty slow devices. */
				vTaskDelay( mainCHAR_WRITE_DELAY );
				prvPDCWrite( PDC_LCD_RAM, *pcString );
				pcString++;
			}
		}
	}
}

/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Setup the PLL. */
	SysCtlClockSet( SYSCTL_SYSDIV_10 | SYSCTL_USE_PLL | SYSCTL_OSC_MAIN | SYSCTL_XTAL_6MHZ );

	/* Initialise the hardware used to talk to the LCD, LED's and UART. */
	PDCInit();
	vParTestInitialise();
	vSerialInit();

	/* The ADC is used to read the light sensor. */
	SysCtlPeripheralEnable( SYSCTL_PERIPH_ADC );
    ADCSequenceConfigure( ADC_BASE, 3, ADC_TRIGGER_PROCESSOR, 0);
    ADCSequenceStepConfigure( ADC_BASE, 0, 0, ADC_CTL_CH0 | ADC_CTL_END );
    ADCSequenceEnable( ADC_BASE, 0 );

}
/*-----------------------------------------------------------*/

static void prvPDCWrite( char cAddress, char cData )
{
	vTaskSuspendAll();
	{
		PDCWrite( cAddress, cData );
	}
	xTaskResumeAll();
}
/*-----------------------------------------------------------*/

void vSetErrorLED( void )
{
	vParTestSetLED( mainFAIL_LED, pdTRUE );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	for( ;; )
	{
		vSetAndCheckRegisters();

		/* See if the comms task has found any errors. */
		if( uxGetCommsStatus() != pdPASS )
		{
			vParTestSetLED( mainFAIL_LED, pdTRUE );
		}
	}
}
/*-----------------------------------------------------------*/
