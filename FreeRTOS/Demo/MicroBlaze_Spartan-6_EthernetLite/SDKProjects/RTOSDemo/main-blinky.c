/*
    FreeRTOS V8.2.1 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

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

/*
 * main-blinky.c is included when the "Blinky" build configuration is used.
 * main-full.c is included when the "Full" build configuration is used.
 *
 * main-blinky.c (this file) defines a very simple demo that creates two tasks,
 * one queue, and one timer.  It also demonstrates how MicroBlaze interrupts
 * can interact with FreeRTOS tasks/timers.
 *
 * This simple demo project was developed and tested on the Spartan-6 SP605
 * development board, using the hardware configuration found in the hardware
 * project that is already included in the Eclipse project.
 *
 * The idle hook function:
 * The idle hook function demonstrates how to query the amount of FreeRTOS heap
 * space that is remaining (see vApplicationIdleHook() defined in this file).
 *
 * The main() Function:
 * main() creates one software timer, one queue, and two tasks.  It then starts
 * the scheduler.
 *
 * The Queue Send Task:
 * The queue send task is implemented by the prvQueueSendTask() function in
 * this file.  prvQueueSendTask() sits in a loop that causes it to repeatedly
 * block for 200 milliseconds, before sending the value 100 to the queue that
 * was created within main().  Once the value is sent, the task loops back
 * around to block for another 200 milliseconds.
 *
 * The Queue Receive Task:
 * The queue receive task is implemented by the prvQueueReceiveTask() function
 * in this file.  prvQueueReceiveTask() sits in a loop that causes it to
 * repeatedly attempt to read data from the queue that was created within
 * main().  When data is received, the task checks the value of the data, and
 * if the value equals the expected 100, toggles an LED.  The 'block time'
 * parameter passed to the queue receive function specifies that the task
 * should be held in the Blocked state indefinitely to wait for data to be
 * available on the queue.  The queue receive task will only leave the Blocked
 * state when the queue send task writes to the queue.  As the queue send task
 * writes to the queue every 200 milliseconds, the queue receive task leaves
 * the Blocked state every 200 milliseconds, and therefore toggles the LED
 * every 200 milliseconds.
 *
 * The LED Software Timer and the Button Interrupt:
 * The user buttons are configured to generate an interrupt each time one is
 * pressed.  The interrupt service routine switches an LED on, and resets the
 * LED software timer.  The LED timer has a 5000 millisecond (5 second) period,
 * and uses a callback function that is defined to just turn the LED off again.
 * Therefore, pressing the user button will turn the LED on, and the LED will
 * remain on until a full five seconds pass without the button being pressed.
 */

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"

/* BSP includes. */
#include "xtmrctr.h"
#include "xgpio.h"

/* Priorities at which the tasks are created. */
#define mainQUEUE_RECEIVE_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define	mainQUEUE_SEND_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )

/* The rate at which data is sent to the queue, specified in milliseconds, and
converted to ticks using the portTICK_PERIOD_MS constant. */
#define mainQUEUE_SEND_FREQUENCY_MS			( 200 / portTICK_PERIOD_MS )

/* The number of items the queue can hold.  This is 1 as the receive task
will remove items as they are added because it has the higher priority, meaning
the send task should always find the queue empty. */
#define mainQUEUE_LENGTH					( 1 )

/* The LED toggled by the queue receive task. */
#define mainTASK_CONTROLLED_LED				0x01UL

/* The LED turned on by the button interrupt, and turned off by the LED timer. */
#define mainTIMER_CONTROLLED_LED			0x02UL

/* A block time of 0 simply means, "don't block". */
#define mainDONT_BLOCK						( TickType_t ) 0

/*-----------------------------------------------------------*/

/*
 * Setup the NVIC, LED outputs, and button inputs.
 */
static void prvSetupHardware( void );

/*
 * The tasks as described in the comments at the top of this file.
 */
static void prvQueueReceiveTask( void *pvParameters );
static void prvQueueSendTask( void *pvParameters );

/*
 * The LED timer callback function.  This does nothing but switch off the
 * LED defined by the mainTIMER_CONTROLLED_LED constant.
 */
static void vLEDTimerCallback( TimerHandle_t xTimer );

/*
 * The handler executed each time a button interrupt is generated.  This ensures
 * the LED defined by mainTIMER_CONTROLLED_LED is on, and resets the timer so
 * the timer will not turn the LED off for a full 5 seconds after the button
 * interrupt occurred.
 */
static void prvButtonInputInterruptHandler( void *pvUnused );

/*-----------------------------------------------------------*/

/* The queue used by the queue send and queue receive tasks. */
static QueueHandle_t xQueue = NULL;

/* The LED software timer.  This uses vLEDTimerCallback() as its callback
function. */
static TimerHandle_t xLEDTimer = NULL;

/* Maintains the current LED output state. */
static volatile unsigned char ucGPIOState = 0U;

/*-----------------------------------------------------------*/

/* Structures that hold the state of the various peripherals used by this demo.
These are used by the Xilinx peripheral driver API functions. */
static XTmrCtr xTimer0Instance;
static XGpio xOutputGPIOInstance, xInputGPIOInstance;

/* Constants required by the Xilinx peripheral driver API functions that are
relevant to the particular hardware set up. */
static const unsigned long ulGPIOOutputChannel = 1UL, ulGPIOInputChannel = 1UL;

/*-----------------------------------------------------------*/

int main( void )
{
	/* *************************************************************************
	This is a very simple project suitable for getting started with FreeRTOS.
	If you would prefer a more complex project that demonstrates a lot more
	features and tests, then select the 'Full' build configuration within the
	SDK Eclipse IDE.
	***************************************************************************/

	/* Configure the interrupt controller, LED outputs and button inputs. */
	prvSetupHardware();

	/* Create the queue used by the queue send and queue receive tasks as
	described in the comments at the top of this file. */
	xQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( unsigned long ) );

	/* Sanity check that the queue was created. */
	configASSERT( xQueue );

	/* Start the two tasks as described in the comments at the top of this
	file. */
	xTaskCreate( prvQueueReceiveTask, "Rx", configMINIMAL_STACK_SIZE, NULL, mainQUEUE_RECEIVE_TASK_PRIORITY, NULL );
	xTaskCreate( prvQueueSendTask, "TX", configMINIMAL_STACK_SIZE, NULL, mainQUEUE_SEND_TASK_PRIORITY, NULL );

	/* Create the software timer that is responsible for turning off the LED
	if the button is not pushed within 5000ms, as described at the top of
	this file.  The timer is not actually started until a button interrupt is
	pushed, as it is not until that point that the LED is turned on. */
	xLEDTimer = xTimerCreate( 	"LEDTimer", 				/* A text name, purely to help debugging. */
								( 5000 / portTICK_PERIOD_MS ),/* The timer period, in this case 5000ms (5s). */
								pdFALSE,					/* This is a one shot timer, so xAutoReload is set to pdFALSE. */
								( void * ) 0,				/* The ID is not used, so can be set to anything. */
								vLEDTimerCallback			/* The callback function that switches the LED off. */
							);

	/* Start the tasks and timer running. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following line
	will never be reached.  If the following line does execute, then there was
	insufficient FreeRTOS heap memory available for the idle and/or timer tasks
	to be created.  See the memory management section on the FreeRTOS web site
	for more details. */
	for( ;; );
}
/*-----------------------------------------------------------*/

/* The callback is executed when the LED timer expires. */
static void vLEDTimerCallback( TimerHandle_t xTimer )
{
	/* The timer has expired - so no button pushes have occurred in the last
	five seconds - turn the LED off.  NOTE - accessing the LED port should use
	a critical section because it is accessed from multiple tasks, and the
	button interrupt - in this trivial case, for simplicity, the critical
	section is omitted. */
	ucGPIOState &= ~mainTIMER_CONTROLLED_LED;
	XGpio_DiscreteWrite( &xOutputGPIOInstance, ulGPIOOutputChannel, ucGPIOState );
}
/*-----------------------------------------------------------*/

/* The ISR is executed when the user button is pushed. */
static void prvButtonInputInterruptHandler( void *pvUnused )
{
long lHigherPriorityTaskWoken = pdFALSE;

	/* The button was pushed, so ensure the LED is on before resetting the
	LED timer.  The LED timer will turn the LED off if the button is not
	pushed within 5000ms. */
	ucGPIOState |= mainTIMER_CONTROLLED_LED;
	XGpio_DiscreteWrite( &xOutputGPIOInstance, ulGPIOOutputChannel, ucGPIOState );

	/* Ensure only the ISR safe reset API function is used, as this is executed
	in an interrupt context. */
	xTimerResetFromISR( xLEDTimer, &lHigherPriorityTaskWoken );

	/* Clear the interrupt before leaving. */
	XGpio_InterruptClear( &xInputGPIOInstance, ulGPIOInputChannel );

	/* If calling xTimerResetFromISR() caused a task (in this case the timer
	service/daemon task) to unblock, and the unblocked task has a priority
	higher than or equal to the task that was interrupted, then
	lHigherPriorityTaskWoken will now be set to pdTRUE, and calling
	portEND_SWITCHING_ISR() will ensure the unblocked task runs next. */
	portYIELD_FROM_ISR( lHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void prvQueueSendTask( void *pvParameters )
{
TickType_t xNextWakeTime;
const unsigned long ulValueToSend = 100UL;

	/* Initialise xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Place this task in the blocked state until it is time to run again.
		The block time is specified in ticks, the constant used converts ticks
		to ms.  While in the Blocked state this task will not consume any CPU
		time. */
		vTaskDelayUntil( &xNextWakeTime, mainQUEUE_SEND_FREQUENCY_MS );

		/* Send to the queue - causing the queue receive task to unblock and
		toggle an LED.  0 is used as the block time so the sending operation
		will not block - it shouldn't need to block as the queue should always
		be empty at this point in the code. */
		xQueueSend( xQueue, &ulValueToSend, mainDONT_BLOCK );
	}
}
/*-----------------------------------------------------------*/

static void prvQueueReceiveTask( void *pvParameters )
{
unsigned long ulReceivedValue;

	for( ;; )
	{
		/* Wait until something arrives in the queue - this task will block
		indefinitely provided INCLUDE_vTaskSuspend is set to 1 in
		FreeRTOSConfig.h. */
		xQueueReceive( xQueue, &ulReceivedValue, portMAX_DELAY );

		/*  To get here something must have been received from the queue, but
		is it the expected value?  If it is, toggle the green LED. */
		if( ulReceivedValue == 100UL )
		{
			/* NOTE - accessing the LED port should use a critical section
			because it is accessed from multiple tasks, and the button interrupt
			- in this trivial case, for simplicity, the critical section is
			omitted. */
			if( ( ucGPIOState & mainTASK_CONTROLLED_LED ) != 0 )
			{
				ucGPIOState &= ~mainTASK_CONTROLLED_LED;
			}
			else
			{
				ucGPIOState |= mainTASK_CONTROLLED_LED;
			}

			XGpio_DiscreteWrite( &xOutputGPIOInstance, ulGPIOOutputChannel, ucGPIOState );
		}
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
portBASE_TYPE xStatus;
const unsigned char ucSetToOutput = 0U;

	/* Initialize the GPIO for the LEDs. */
	xStatus = XGpio_Initialize( &xOutputGPIOInstance, XPAR_LEDS_4BITS_DEVICE_ID );
	if( xStatus == XST_SUCCESS )
	{
		/* All bits on this channel are going to be outputs (LEDs). */
		XGpio_SetDataDirection( &xOutputGPIOInstance, ulGPIOOutputChannel, ucSetToOutput );

		/* Start with all LEDs off. */
		ucGPIOState = 0U;
		XGpio_DiscreteWrite( &xOutputGPIOInstance, ulGPIOOutputChannel, ucGPIOState );
	}

	/* Initialise the GPIO for the button inputs. */
	if( xStatus == XST_SUCCESS )
	{
		xStatus = XGpio_Initialize( &xInputGPIOInstance, XPAR_PUSH_BUTTONS_4BITS_DEVICE_ID );
	}

	if( xStatus == XST_SUCCESS )
	{
		/* Install the handler defined in this task for the button input.
		*NOTE* The FreeRTOS defined xPortInstallInterruptHandler() API function
		must be used for this purpose. */
		xStatus = xPortInstallInterruptHandler( XPAR_MICROBLAZE_0_INTC_PUSH_BUTTONS_4BITS_IP2INTC_IRPT_INTR, prvButtonInputInterruptHandler, NULL );

		if( xStatus == pdPASS )
		{
			/* Set buttons to input. */
			XGpio_SetDataDirection( &xInputGPIOInstance, ulGPIOInputChannel, ~( ucSetToOutput ) );

			/* Enable the button input interrupts in the interrupt controller.
			*NOTE* The vPortEnableInterrupt() API function must be used for this
			purpose. */
			vPortEnableInterrupt( XPAR_MICROBLAZE_0_INTC_PUSH_BUTTONS_4BITS_IP2INTC_IRPT_INTR );

			/* Enable GPIO channel interrupts. */
			XGpio_InterruptEnable( &xInputGPIOInstance, ulGPIOInputChannel );
			XGpio_InterruptGlobalEnable( &xInputGPIOInstance );
		}
	}

	configASSERT( ( xStatus == pdPASS ) );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* vApplicationMallocFailedHook() will only be called if
	configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	function that will get called if a call to pvPortMalloc() fails.
	pvPortMalloc() is called internally by the kernel whenever a task, queue or
	semaphore is created.  It is also called by various parts of the demo
	application.  If heap_1.c or heap_2.c are used, then the size of the heap
	available to pvPortMalloc() is defined by configTOTAL_HEAP_SIZE in
	FreeRTOSConfig.h, and the xPortGetFreeHeapSize() API function can be used
	to query the size of free heap space that remains (although it does not
	provide information on how the remaining heap might be fragmented). */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* vApplicationStackOverflowHook() will only be called if
	configCHECK_FOR_STACK_OVERFLOW is set to either 1 or 2.  The handle and name
	of the offending task will be passed into the hook function via its
	parameters.  However, when a stack has overflowed, it is possible that the
	parameters will have been corrupted, in which case the pxCurrentTCB variable
	can be inspected directly. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
#ifdef EXAMPLE_CODE_ONLY

	The following code can only be included if heap_1.c or heap_2.c is used in
	the project.  By default, heap_3.c is used, so the example code is
	excluded.  See http://www.freertos.org/a00111.html for more information on
	memory management options.

	volatile size_t xFreeHeapSpace;

		/* vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set
		to 1 in FreeRTOSConfig.h.  It will be called on each iteration of the idle
		task.  It is essential that code added to this hook function never attempts
		to block in any way (for example, call xQueueReceive() with a block time
		specified, or call vTaskDelay()).  If the application makes use of the
		vTaskDelete() API function (as this demo application does) then it is also
		important that vApplicationIdleHook() is permitted to return to its calling
		function, because it is the responsibility of the idle task to clean up
		memory allocated by the kernel to any task that has since been deleted. */

		/* This implementation of vApplicationIdleHook() simply demonstrates how
		the xPortGetFreeHeapSize() function can be used. */
		xFreeHeapSpace = xPortGetFreeHeapSize();

		if( xFreeHeapSpace > 100 )
		{
			/* By now, the kernel has allocated everything it is going to, so
			if there is a lot of heap remaining unallocated then
			the value of configTOTAL_HEAP_SIZE in FreeRTOSConfig.h can be
			reduced accordingly. */
		}
#endif
}
/*-----------------------------------------------------------*/

/* This is an application defined callback function used to install the tick
interrupt handler.  It is provided as an application callback because the kernel
will run on lots of different MicroBlaze and FPGA configurations - not all of
which will have the same timer peripherals defined or available.  This example
uses the AXI Timer 0.  If that is available on your hardware platform then this
example callback implementation should not require modification.   The name of
the interrupt handler that should be installed is vPortTickISR(), which the
function below declares as an extern. */
void vApplicationSetupTimerInterrupt( void )
{
portBASE_TYPE xStatus;
const unsigned char ucTimerCounterNumber = ( unsigned char ) 0U;
const unsigned long ulCounterValue = ( ( XPAR_AXI_TIMER_0_CLOCK_FREQ_HZ / configTICK_RATE_HZ ) - 1UL );
extern void vPortTickISR( void *pvUnused );

	/* Initialise the timer/counter. */
	xStatus = XTmrCtr_Initialize( &xTimer0Instance, XPAR_AXI_TIMER_0_DEVICE_ID );

	if( xStatus == XST_SUCCESS )
	{
		/* Install the tick interrupt handler as the timer ISR.
		*NOTE* The xPortInstallInterruptHandler() API function must be used for
		this purpose. */
		xStatus = xPortInstallInterruptHandler( XPAR_INTC_0_TMRCTR_0_VEC_ID, vPortTickISR, NULL );
	}

	if( xStatus == pdPASS )
	{
		/* Enable the timer interrupt in the interrupt controller.
		*NOTE* The vPortEnableInterrupt() API function must be used for this
		purpose. */
		vPortEnableInterrupt( XPAR_INTC_0_TMRCTR_0_VEC_ID );

		/* Configure the timer interrupt handler. */
		XTmrCtr_SetHandler( &xTimer0Instance, ( void * ) vPortTickISR, NULL );

		/* Set the correct period for the timer. */
		XTmrCtr_SetResetValue( &xTimer0Instance, ucTimerCounterNumber, ulCounterValue );

		/* Enable the interrupts.  Auto-reload mode is used to generate a
		periodic tick.  Note that interrupts are disabled when this function is
		called, so interrupts will not start to be processed until the first
		task has started to run. */
		XTmrCtr_SetOptions( &xTimer0Instance, ucTimerCounterNumber, ( XTC_INT_MODE_OPTION | XTC_AUTO_RELOAD_OPTION | XTC_DOWN_COUNT_OPTION ) );

		/* Start the timer. */
		XTmrCtr_Start( &xTimer0Instance, ucTimerCounterNumber );
	}

	/* Sanity check that the function executed as expected. */
	configASSERT( ( xStatus == pdPASS ) );
}
/*-----------------------------------------------------------*/

/* This is an application defined callback function used to clear whichever
interrupt was installed by the the vApplicationSetupTimerInterrupt() callback
function - in this case the interrupt generated by the AXI timer.  It is
provided as an application callback because the kernel will run on lots of
different MicroBlaze and FPGA configurations - not all of which will have the
same timer peripherals defined or available.  This example uses the AXI Timer 0.
If that is available on your hardware platform then this example callback
implementation should not require modification provided the example definition
of vApplicationSetupTimerInterrupt() is also not modified. */
void vApplicationClearTimerInterrupt( void )
{
unsigned long ulCSR;

	/* Clear the timer interrupt */
	ulCSR = XTmrCtr_GetControlStatusReg( XPAR_AXI_TIMER_0_BASEADDR, 0 );
	XTmrCtr_SetControlStatusReg( XPAR_AXI_TIMER_0_BASEADDR, 0, ulCSR );
}
/*-----------------------------------------------------------*/

/* These functions are not used by the Blinky build configuration.  However,
they need to be defined because the Blinky and Full build configurations share
a FreeRTOSConifg.h configuration file. */
void vMainConfigureTimerForRunTimeStats( void ) {}
unsigned long ulMainGetRunTimeCounterValue( void ) { return 1; }
