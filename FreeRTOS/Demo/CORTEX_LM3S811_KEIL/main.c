/*
 * FreeRTOS V202112.00
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */


/*
 * This project contains an application demonstrating the use of the 
 * FreeRTOS.org mini real time scheduler on the Luminary Micro LM3S811 Eval
 * board.  See http://www.FreeRTOS.org for more information.
 *
 * main() simply sets up the hardware, creates all the demo application tasks, 
 * then starts the scheduler.  http://www.freertos.org/a00102.html provides
 * more information on the standard demo tasks. 
 *
 * In addition to a subset of the standard demo application tasks, main.c also
 * defines the following tasks: 
 *
 * + A 'Print' task.  The print task is the only task permitted to access the
 * LCD - thus ensuring mutual exclusion and consistent access to the resource.
 * Other tasks do not access the LCD directly, but instead send the text they
 * wish to display to the print task.  The print task spends most of its time
 * blocked - only waking when a message is queued for display.
 *
 * + A 'Button handler' task.  The eval board contains a user push button that
 * is configured to generate interrupts.  The interrupt handler uses a 
 * semaphore to wake the button handler task - demonstrating how the priority 
 * mechanism can be used to defer interrupt processing to the task level.  The
 * button handler task sends a message both to the LCD (via the print task) and
 * the UART where it can be viewed using a dumb terminal (via the UART to USB
 * converter on the eval board).  NOTES:  The dumb terminal must be closed in 
 * order to reflash the microcontroller.  A very basic interrupt driven UART
 * driver is used that does not use the FIFO.  19200 baud is used.
 *
 * + A 'check' task.  The check task only executes every five seconds but has a
 * high priority so is guaranteed to get processor time.  Its function is to
 * check that all the other tasks are still operational and that no errors have
 * been detected at any time.  If no errors have every been detected 'PASS' is
 * written to the display (via the print task) - if an error has ever been
 * detected the message is changed to 'FAIL'.  The position of the message is
 * changed for each write.
 */



/* Environment includes. */
#include "DriverLib.h"

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Demo app includes. */
#include "integer.h"
#include "PollQ.h"
#include "semtest.h"
#include "BlockQ.h"

/* Delay between cycles of the 'check' task. */
#define mainCHECK_DELAY						( ( TickType_t ) 5000 / portTICK_PERIOD_MS )

/* UART configuration - note this does not use the FIFO so is not very 
efficient. */
#define mainBAUD_RATE				( 19200 )
#define mainFIFO_SET				( 0x10 )

/* Demo task priorities. */
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + 3 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )

/* Demo board specifics. */
#define mainPUSH_BUTTON             GPIO_PIN_4

/* Misc. */
#define mainQUEUE_SIZE				( 3 )
#define mainDEBOUNCE_DELAY			( ( TickType_t ) 150 / portTICK_PERIOD_MS )
#define mainNO_DELAY				( ( TickType_t ) 0 )
/*
 * Configure the processor and peripherals for this demo. 
 */
static void prvSetupHardware( void );

/*
 * The 'check' task, as described at the top of this file.
 */
static void vCheckTask( void *pvParameters );

/*
 * The task that is woken by the ISR that processes GPIO interrupts originating
 * from the push button.
 */
static void vButtonHandlerTask( void *pvParameters );

/*
 * The task that controls access to the LCD.
 */
static void vPrintTask( void *pvParameter );

/* String that is transmitted on the UART. */
static char *cMessage = "Task woken by button interrupt! --- ";
static volatile char *pcNextChar;

/* The semaphore used to wake the button handler task from within the GPIO
interrupt handler. */
SemaphoreHandle_t xButtonSemaphore;

/* The queue used to send strings to the print task for display on the LCD. */
QueueHandle_t xPrintQueue;

/* Newer library version. */
extern void UARTConfigSetExpClk(unsigned long ulBase, unsigned long ulUARTClk, unsigned long ulBaud, unsigned long ulConfig);
/*-----------------------------------------------------------*/

int main( void )
{
	/* Configure the clocks, UART and GPIO. */
	prvSetupHardware();

	/* Create the semaphore used to wake the button handler task from the GPIO
	ISR. */
	vSemaphoreCreateBinary( xButtonSemaphore );
	xSemaphoreTake( xButtonSemaphore, 0 );

	/* Create the queue used to pass message to vPrintTask. */
	xPrintQueue = xQueueCreate( mainQUEUE_SIZE, sizeof( char * ) );

	/* Start the standard demo tasks. */
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );

	/* Start the tasks defined within the file. */
	xTaskCreate( vCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );
	xTaskCreate( vButtonHandlerTask, "Status", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY + 1, NULL );
	xTaskCreate( vPrintTask, "Print", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY - 1, NULL );

	/* Start the scheduler. */
	vTaskStartScheduler();

	/* Will only get here if there was insufficient heap to start the 
	scheduler. */

	return 0;
}
/*-----------------------------------------------------------*/

static void vCheckTask( void *pvParameters )
{
portBASE_TYPE xErrorOccurred = pdFALSE;
TickType_t xLastExecutionTime;
const char *pcPassMessage = "PASS";
const char *pcFailMessage = "FAIL";

	/* Initialise xLastExecutionTime so the first call to vTaskDelayUntil()
	works correctly. */
	xLastExecutionTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Perform this check every mainCHECK_DELAY milliseconds. */
		vTaskDelayUntil( &xLastExecutionTime, mainCHECK_DELAY );

		/* Has an error been found in any task? */

		if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
		{
			xErrorOccurred = pdTRUE;
		}
	
		if( xArePollingQueuesStillRunning() != pdTRUE )
		{
			xErrorOccurred = pdTRUE;
		}
	
		if( xAreSemaphoreTasksStillRunning() != pdTRUE )
		{
			xErrorOccurred = pdTRUE;
		}

		if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			xErrorOccurred = pdTRUE;
		}

		/* Send either a pass or fail message.  If an error is found it is
		never cleared again.  We do not write directly to the LCD, but instead
		queue a message for display by the print task. */
		if( xErrorOccurred == pdTRUE )
		{
			xQueueSend( xPrintQueue, &pcFailMessage, portMAX_DELAY );
		}
		else
		{
			xQueueSend( xPrintQueue, &pcPassMessage, portMAX_DELAY );
		}
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Setup the PLL. */
	SysCtlClockSet( SYSCTL_SYSDIV_10 | SYSCTL_USE_PLL | SYSCTL_OSC_MAIN | SYSCTL_XTAL_6MHZ );

	/* Setup the push button. */
	SysCtlPeripheralEnable(SYSCTL_PERIPH_GPIOC);
    GPIODirModeSet(GPIO_PORTC_BASE, mainPUSH_BUTTON, GPIO_DIR_MODE_IN);
	GPIOIntTypeSet( GPIO_PORTC_BASE, mainPUSH_BUTTON,GPIO_FALLING_EDGE );
	IntPrioritySet( INT_GPIOC, configKERNEL_INTERRUPT_PRIORITY );
	GPIOPinIntEnable( GPIO_PORTC_BASE, mainPUSH_BUTTON );
	IntEnable( INT_GPIOC );



	/* Enable the UART.  */
	SysCtlPeripheralEnable(SYSCTL_PERIPH_UART0);
	SysCtlPeripheralEnable(SYSCTL_PERIPH_GPIOA);

	/* Set GPIO A0 and A1 as peripheral function.  They are used to output the
	UART signals. */
	GPIODirModeSet( GPIO_PORTA_BASE, GPIO_PIN_0 | GPIO_PIN_1, GPIO_DIR_MODE_HW );

	/* Configure the UART for 8-N-1 operation. */
	UARTConfigSetExpClk( UART0_BASE, SysCtlClockGet(), mainBAUD_RATE, UART_CONFIG_WLEN_8 | UART_CONFIG_PAR_NONE | UART_CONFIG_STOP_ONE );

	/* We don't want to use the fifo.  This is for test purposes to generate
	as many interrupts as possible. */
	HWREG( UART0_BASE + UART_O_LCR_H ) &= ~mainFIFO_SET;

	/* Enable Tx interrupts. */
	HWREG( UART0_BASE + UART_O_IM ) |= UART_INT_TX;
	IntPrioritySet( INT_UART0, configKERNEL_INTERRUPT_PRIORITY );
	IntEnable( INT_UART0 );


	/* Initialise the LCD> */
    OSRAMInit( false );
    OSRAMStringDraw("www.FreeRTOS.org", 0, 0);
	OSRAMStringDraw("LM3S811 demo", 16, 1);
}
/*-----------------------------------------------------------*/

static void vButtonHandlerTask( void *pvParameters )
{
const char *pcInterruptMessage = "Int";

	for( ;; )
	{
		/* Wait for a GPIO interrupt to wake this task. */
		while( xSemaphoreTake( xButtonSemaphore, portMAX_DELAY ) != pdPASS );

		/* Start the Tx of the message on the UART. */
		UARTIntDisable( UART0_BASE, UART_INT_TX );
		{
			pcNextChar = cMessage;

			/* Send the first character. */
			if( !( HWREG( UART0_BASE + UART_O_FR ) & UART_FR_TXFF ) )
			{
				HWREG( UART0_BASE + UART_O_DR ) = *pcNextChar;
			}

			pcNextChar++;
		}
		UARTIntEnable(UART0_BASE, UART_INT_TX);

		/* Queue a message for the print task to display on the LCD. */
		xQueueSend( xPrintQueue, &pcInterruptMessage, portMAX_DELAY );

		/* Make sure we don't process bounces. */
		vTaskDelay( mainDEBOUNCE_DELAY );
		xSemaphoreTake( xButtonSemaphore, mainNO_DELAY );
	}
}

/*-----------------------------------------------------------*/

void vUART_ISR(void)
{
unsigned long ulStatus;

	/* What caused the interrupt. */
	ulStatus = UARTIntStatus( UART0_BASE, pdTRUE );

	/* Clear the interrupt. */
	UARTIntClear( UART0_BASE, ulStatus );

	/* Was a Tx interrupt pending? */
	if( ulStatus & UART_INT_TX )
	{
		/* Send the next character in the string.  We are not using the FIFO. */
		if( *pcNextChar != NULL )
		{
			if( !( HWREG( UART0_BASE + UART_O_FR ) & UART_FR_TXFF ) )
			{
				HWREG( UART0_BASE + UART_O_DR ) = *pcNextChar;
			}
			pcNextChar++;
		}
	}
}
/*-----------------------------------------------------------*/

void vGPIO_ISR( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* Clear the interrupt. */
	GPIOPinIntClear( GPIO_PORTC_BASE, mainPUSH_BUTTON );

	/* Wake the button handler task. */
	xSemaphoreGiveFromISR( xButtonSemaphore, &xHigherPriorityTaskWoken );
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void vPrintTask( void *pvParameters )
{
char *pcMessage;
unsigned portBASE_TYPE uxLine = 0, uxRow = 0;

	for( ;; )
	{
		/* Wait for a message to arrive. */
		xQueueReceive( xPrintQueue, &pcMessage, portMAX_DELAY );

		/* Write the message to the LCD. */
		uxRow++;
		uxLine++;
		OSRAMClear();
		OSRAMStringDraw( pcMessage, uxLine & 0x3f, uxRow & 0x01);
	}
}

