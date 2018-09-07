/*
 * FreeRTOS Kernel V10.1.1
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * This demo application creates eight co-routines and four tasks (five 
 * including the idle task).  The co-routines execute as part of the idle task 
 * hook.  The application is limited in size to allow its compilation using
 * the KickStart version of the IAR compiler.
 *
 * Six of the created co-routines are the standard 'co-routine flash' 
 * co-routines contained within the Demo/Common/Minimal/crflash.c file and 
 * documented on the FreeRTOS.org WEB site.  
 *
 * The 'LCD Task' waits on a message queue for messages informing it what and
 * where to display text.  This is the only task that accesses the LCD
 * so mutual exclusion is guaranteed.
 *
 * The 'LCD Message Task' periodically sends strings to the LCD Task using
 * the message queue.  The strings are rotated to form a short message and
 * are written to the top row of the LCD.
 *
 * The 'ADC Co-routine' periodically reads the ADC input that is connected to
 * the light sensor, forms a short message from the value, and then sends this
 * message to the LCD Task using the same message queue.  The ADC readings are
 * displayed on the bottom row of the LCD.  
 *
 * The eighth co-routine and final task control the transmission and reception
 * of a string to UART 0.  The co-routine periodically sends the first 
 * character of the string to the UART, with the UART's TxEnd interrupt being
 * used to transmit the remaining characters.  The UART's RxEnd interrupt 
 * receives the characters and places them on a queue to be processed by the 
 * 'COMs Rx' task.  An error is latched should an unexpected character be 
 * received, or any character be received out of sequence.  
 *
 * A loopback connector is required to ensure that each character transmitted 
 * on the UART is also received on the same UART.  For test purposes the UART
 * FIFO's are not utalised in order to maximise the interrupt overhead.  Also
 * a pseudo random interval is used between the start of each transmission in 
 * order that the resultant interrupts are more randomly distributed and 
 * therefore more likely to highlight any problems.
 *
 * The flash co-routines control LED's zero to four.  LED five is toggled each
 * time the string is transmitted on the UART.  LED six is toggled each time
 * the string is CORRECTLY received on the UART.  LED seven is latched on 
 * should an error be detected in any task or co-routine.
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
#include "croutine.h"

/* Demo application include files. */
#include "partest.h"
#include "crflash.h"
#include "commstest.h"

/* Library include files. */
#include "DriverLib.h"

/* The time to delay between writing each character to the LCD. */
#define mainCHAR_WRITE_DELAY		( 2 / portTICK_PERIOD_MS )

/* The time to delay between writing each string to the LCD. */
#define mainSTRING_WRITE_DELAY		( 400 / portTICK_PERIOD_MS )

#define mainADC_DELAY				( 200 / portTICK_PERIOD_MS )

/* The number of flash co-routines to create. */
#define mainNUM_FLASH_CO_ROUTINES	( 5 )

/* The length of the queue used to send messages to the LCD task. */
#define mainLCD_QUEUE_LEN			( 3 )

/* The priority of the co-routine used to initiate the transmission of the 
string on UART 0. */
#define mainTX_CO_ROUTINE_PRIORITY	( 1 )
#define mainADC_CO_ROUTINE_PRIORITY 	( 2 )

/* Only one of each co-routine is created so its index is not important. */
#define mainTX_CO_ROUTINE_INDEX		( 0 )
#define mainADC_CO_ROUTINE_INDEX  	( 0 )

/* The task priorities. */
#define mainLCD_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainMSG_TASK_PRIORITY		( mainLCD_TASK_PRIORITY - 1 )
#define mainCOMMS_RX_TASK_PRIORITY	( tskIDLE_PRIORITY + 1 )

/* The LCD had two rows. */
#define mainTOP_ROW		0
#define mainBOTTOM_ROW 	1

/* Dimension for the buffer into which the ADC value string is written. */
#define mainMAX_ADC_STRING_LEN	20

/* The LED that is lit should an error be detected in any of the tasks or
co-routines. */
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
 * The co-routine that reads the ADC and sends messages for display on the
 * bottom row of the LCD.
 */
static void prvADCCoRoutine( CoRoutineHandle_t xHandle, unsigned portBASE_TYPE uxIndex );

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

/* Error flag set to pdFAIL if an error is encountered in the tasks/co-routines
defined within this file. */
unsigned portBASE_TYPE uxErrorStatus = pdPASS;

/* The queue used to transmit messages to the LCD task. */
static QueueHandle_t xLCDQueue;

/*-----------------------------------------------------------*/

/*
 * Setup the hardware, create the tasks/co-routines, then start the scheduler.
 */
void main( void )
{
	/* Create the queue used by tasks wanting to write to the LCD. */
	xLCDQueue = xQueueCreate( mainLCD_QUEUE_LEN, sizeof( xLCDMessage ) );

	/* Setup the ports used by the demo and the clock. */
	prvSetupHardware();

	/* Create the co-routines that flash the LED's. */
	vStartFlashCoRoutines( mainNUM_FLASH_CO_ROUTINES );

	/* Create the co-routine that initiates the transmission of characters
	on the UART and the task that receives them, as described at the top of
	this file. */
	xCoRoutineCreate( vSerialTxCoRoutine, mainTX_CO_ROUTINE_PRIORITY, mainTX_CO_ROUTINE_INDEX );
	xTaskCreate( vCommsRxTask, "CMS", configMINIMAL_STACK_SIZE, NULL, mainCOMMS_RX_TASK_PRIORITY, NULL );

	/* Create the task that waits for messages to display on the LCD, plus the
	task and co-routine that send messages for display (as described at the top
	of this file. */
	xTaskCreate( prvLCDTask, "LCD", configMINIMAL_STACK_SIZE, ( void * ) &xLCDQueue, mainLCD_TASK_PRIORITY, NULL );
	xTaskCreate( prvLCDMessageTask, "MSG", configMINIMAL_STACK_SIZE, ( void * ) &xLCDQueue, mainMSG_TASK_PRIORITY, NULL );
	xCoRoutineCreate( prvADCCoRoutine, mainADC_CO_ROUTINE_PRIORITY, mainADC_CO_ROUTINE_INDEX );

	/* Start the scheduler running the tasks and co-routines just created. */
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

static void prvADCCoRoutine( CoRoutineHandle_t xHandle, unsigned portBASE_TYPE uxIndex )
{
static unsigned long ulADCValue;
static char cMessageBuffer[ mainMAX_ADC_STRING_LEN ];
static char *pcMessage;
static xLCDMessage xMessageToSend;

	/* Co-routines MUST start with a call to crSTART(). */
	crSTART( xHandle );
	
	for( ;; )
	{
		/* Start an ADC conversion. */
		ADCProcessorTrigger( ADC_BASE, 0 );
		
		/* Simply delay - when we unblock the result should be available */	
		crDELAY( xHandle, mainADC_DELAY );
		
		/* Get the ADC result. */
		ADCSequenceDataGet( ADC_BASE, 0, &ulADCValue );

		/* Create a string with the result. */		
		sprintf( cMessageBuffer, "ADC = %d   ", ulADCValue );
		pcMessage = cMessageBuffer;

		/* Configure the message we are going to send for display. */
		xMessageToSend.ppcMessageToDisplay = ( char** ) &pcMessage;
		xMessageToSend.xRow = mainBOTTOM_ROW;
		
		/* Send the string to the LCD task for display.  We are sending
		on a task queue so do not have the option to block. */
		if( !xQueueSend( xLCDQueue, ( void * ) &xMessageToSend, 0 ) )
		{
			uxErrorStatus = pdFAIL;
		}		
	}
	
	/* Co-routines MUST end with a call to crEND(). */
	crEND();
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
	/* The co-routines are executed in the idle task using the idle task 
	hook. */
	for( ;; )
	{
		/* Schedule the co-routines. */
		vCoRoutineSchedule();

		/* Run the register check function between each co-routine. */
		vSetAndCheckRegisters();
		
		/* See if the comms task and co-routine has found any errors. */
		if( uxGetCommsStatus() != pdPASS )
		{
			vParTestSetLED( mainFAIL_LED, pdTRUE );
		}
	}
}
/*-----------------------------------------------------------*/
