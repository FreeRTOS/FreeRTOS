/*
    FreeRTOS V7.0.1 - Copyright (C) 2011 Real Time Engineers Ltd.


	FreeRTOS supports many tools and architectures. V7.0.0 is sponsored by:
	Atollic AB - Atollic provides professional embedded systems development
	tools for C/C++ development, code analysis and test automation.
	See http://www.atollic.com


    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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
 * main-blinky.c is included when the "Blinky" build configuration is used.
 * main-full.c is included when the "Full" build configuration is used.
 *
 * main-blinky.c (this file) defines a very simple demo that creates two tasks,
 * one queue, and one timer.  It also demonstrates how MicroBlaze interrupts
 * can interact with FreeRTOS tasks/timers.
 *
 * This simple demo project runs on the Spartan-6 SP605 development board.
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
 * if the value equals the expected 100, toggles the green LED.  The 'block
 * time' parameter passed to the queue receive function specifies that the task
 * should be held in the Blocked state indefinitely to wait for data to be
 * available on the queue.  The queue receive task will only leave the Blocked
 * state when the queue send task writes to the queue.  As the queue send task
 * writes to the queue every 200 milliseconds, the queue receive task leaves
 * the Blocked state every 200 milliseconds, and therefore toggles the LED
 * every 200 milliseconds.
 *
 * The LED Software Timer and the Button Interrupt:
 * The user button SW1 is configured to generate an interrupt each time it is
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
#include "xenv_standalone.h"
#include "xtmrctr.h"
#include "xil_exception.h"
#include "microblaze_exceptions_g.h"
#include "xgpio.h"

/* Priorities at which the tasks are created. */
#define mainQUEUE_RECEIVE_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define	mainQUEUE_SEND_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )

/* The rate at which data is sent to the queue, specified in milliseconds, and
converted to ticks using the portTICK_RATE_MS constant. */
#define mainQUEUE_SEND_FREQUENCY_MS			( 1000 / portTICK_RATE_MS ) //_RB_ should be 200

/* The number of items the queue can hold.  This is 1 as the receive task
will remove items as they are added, meaning the send task should always find
the queue empty. */
#define mainQUEUE_LENGTH					( 1 )

/* The LED toggle by the queue receive task. */
#define mainTASK_CONTROLLED_LED				0x01UL

/* The LED turned on by the button interrupt, and turned off by the LED timer. */
#define mainTIMER_CONTROLLED_LED			0x02UL

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
static void vLEDTimerCallback( xTimerHandle xTimer );

static void prvButtonInputInterruptHandler( void *pvUnused );

/*-----------------------------------------------------------*/

/* The queue used by both tasks. */
static xQueueHandle xQueue = NULL;

/* The LED software timer.  This uses vLEDTimerCallback() as its callback
function. */
static xTimerHandle xLEDTimer = NULL;

/* Maintains the current LED output state. */
static volatile unsigned char ucGPIOState = 0U;

/*-----------------------------------------------------------*/

static XTmrCtr xTimer0Instance;
static XGpio xOutputGPIOInstance, xInputGPIOInstance;
static const unsigned portBASE_TYPE uxGPIOOutputChannel = 1UL, uxGPIOInputChannel = 1UL;

/*-----------------------------------------------------------*/

int main( void )
{
	/* Configure the interrupt controller, LED outputs and button inputs. */
	prvSetupHardware();

	/* Create the queue. */
	xQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( unsigned long ) );

	if( xQueue != NULL )
	{
		/* Start the two tasks as described in the comments at the top of this
		file. */
		xTaskCreate( prvQueueReceiveTask, ( signed char * ) "Rx", configMINIMAL_STACK_SIZE, NULL, mainQUEUE_RECEIVE_TASK_PRIORITY, NULL );
		xTaskCreate( prvQueueSendTask, ( signed char * ) "TX", configMINIMAL_STACK_SIZE, NULL, mainQUEUE_SEND_TASK_PRIORITY, NULL );

		/* Create the software timer that is responsible for turning off the LED
		if the button is not pushed within 5000ms, as described at the top of
		this file. */
		xLEDTimer = xTimerCreate( 	( const signed char * ) "LEDTimer", /* A text name, purely to help debugging. */
									( 5000 / portTICK_RATE_MS ),		/* The timer period, in this case 5000ms (5s). */
									pdFALSE,							/* This is a one shot timer, so xAutoReload is set to pdFALSE. */
									( void * ) 0,						/* The ID is not used, so can be set to anything. */
									vLEDTimerCallback					/* The callback function that switches the LED off. */
								);

		/* Start the tasks and timer running. */
		vTaskStartScheduler();
	}

	/* If all is well, the scheduler will now be running, and the following line
	will never be reached.  If the following line does execute, then there was
	insufficient FreeRTOS heap memory available for the idle and/or timer tasks
	to be created.  See the memory management section on the FreeRTOS web site
	for more details. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void vLEDTimerCallback( xTimerHandle xTimer )
{
	/* The timer has expired - so no button pushes have occurred in the last
	five seconds - turn the LED off.  NOTE - accessing the LED port should use
	a critical section because it is accessed from multiple tasks, and the
	button interrupt - in this trivial case, for simplicity, the critical
	section is omitted. */
	ucGPIOState &= ~mainTIMER_CONTROLLED_LED;
	XGpio_DiscreteWrite( &xOutputGPIOInstance, uxGPIOOutputChannel, ucGPIOState );
}
/*-----------------------------------------------------------*/

/* The ISR executed when the user button is pushed. */
static void prvButtonInputInterruptHandler( void *pvUnused )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* The button was pushed, so ensure the LED is on before resetting the
	LED timer.  The LED timer will turn the LED off if the button is not
	pushed within 5000ms. */
	ucGPIOState |= mainTIMER_CONTROLLED_LED;
	XGpio_DiscreteWrite( &xOutputGPIOInstance, uxGPIOOutputChannel, ucGPIOState );

	/* This interrupt safe FreeRTOS function can be called from this interrupt
	because the interrupt priority is below the
	configMAX_SYSCALL_INTERRUPT_PRIORITY setting in FreeRTOSConfig.h. */
	xTimerResetFromISR( xLEDTimer, &xHigherPriorityTaskWoken );

	/* Clear the interrupt before leaving. */
	XGpio_InterruptClear( &xInputGPIOInstance, uxGPIOInputChannel );

	/* If calling xTimerResetFromISR() caused a task (in this case the timer
	service/daemon task) to unblock, and the unblocked task has a priority
	higher than or equal to the task that was interrupted, then
	xHigherPriorityTaskWoken will now be set to pdTRUE, and calling
	portEND_SWITCHING_ISR() will ensure the unblocked task runs next. */
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void prvQueueSendTask( void *pvParameters )
{
portTickType xNextWakeTime;
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
		xQueueSend( xQueue, &ulValueToSend, 0 );
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

			XGpio_DiscreteWrite( &xOutputGPIOInstance, uxGPIOOutputChannel, ucGPIOState );
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
		XGpio_SetDataDirection( &xOutputGPIOInstance, uxGPIOOutputChannel, ucSetToOutput );

		/* Start with all LEDs off. */
		ucGPIOState = 0U;
		XGpio_DiscreteWrite( &xOutputGPIOInstance, uxGPIOOutputChannel, ucGPIOState );
	}

	/* Initialise the GPIO for the button inputs. */
	if( xStatus == XST_SUCCESS )
	{
		xStatus = XGpio_Initialize( &xInputGPIOInstance, XPAR_PUSH_BUTTONS_4BITS_DEVICE_ID );
	}

	if( xStatus == XST_SUCCESS )
	{
		/* Install the handler defined in this task for the button input. */
		xStatus = xPortInstallInterruptHandler( XPAR_MICROBLAZE_0_INTC_PUSH_BUTTONS_4BITS_IP2INTC_IRPT_INTR, prvButtonInputInterruptHandler, NULL );

		if( xStatus == pdPASS )
		{
			/* Set buttons to input. */
			XGpio_SetDataDirection( &xInputGPIOInstance, uxGPIOInputChannel, ~( ucSetToOutput ) );


			vPortEnableInterrupt( XPAR_MICROBLAZE_0_INTC_PUSH_BUTTONS_4BITS_IP2INTC_IRPT_INTR );

			/* Enable GPIO channel interrupts. */
			XGpio_InterruptEnable( &xInputGPIOInstance, uxGPIOInputChannel ); //_RB_
			XGpio_InterruptGlobalEnable( &xInputGPIOInstance );
		}
	}

	configASSERT( ( xStatus == pdPASS ) );

	#ifdef MICROBLAZE_EXCEPTIONS_ENABLED
		microblaze_enable_exceptions();
	#endif
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues, software
	timers, and semaphores.  The size of the FreeRTOS heap is set by the
	configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h. */
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configconfigCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
volatile size_t xFreeHeapSpace;

	/* This function is called on each cycle of the idle task.  In this case it
	does nothing useful, other than report the amout of FreeRTOS heap that
	remains unallocated. */
	xFreeHeapSpace = xPortGetFreeHeapSize();

	if( xFreeHeapSpace > 100 )
	{
		/* By now, the kernel has allocated everything it is going to, so
		if there is a lot of heap remaining unallocated then
		the value of configTOTAL_HEAP_SIZE in FreeRTOSConfig.h can be
		reduced accordingly. */
	}
}
/*-----------------------------------------------------------*/

void vMainConfigureTimerForRunTimeStats( void )
{
	/* This function is not used by the Blinky build configuration, but needs
	to be defined as the Blinky and Full build configurations share a
	FreeRTOSConfig.h header file. */
}
/*-----------------------------------------------------------*/

unsigned long ulGetRunTimeCounterValue( void )
{
	/* This function is not used by the Blinky build configuration, but needs
	to be defined as the Blinky and Full build configurations share a
	FreeRTOSConfig.h header file. */
	return 0UL;
}
/*-----------------------------------------------------------*/

void vApplicationSetupTimerInterrupt( void )
{
portBASE_TYPE xStatus;
const unsigned char ucTimerCounterNumber = ( unsigned char ) 0U;
const unsigned long ulCounterValue = ( ( XPAR_AXI_TIMER_0_CLOCK_FREQ_HZ / configTICK_RATE_HZ ) - 1UL );
extern void vTickISR( void *pvUnused );

	/* Initialise the timer/counter. */
	xStatus = XTmrCtr_Initialize( &xTimer0Instance, XPAR_AXI_TIMER_0_DEVICE_ID );

	if( xStatus == XST_SUCCESS )
	{
		/* Install the tick interrupt handler as the timer ISR. */
		xStatus = xPortInstallInterruptHandler( XPAR_MICROBLAZE_0_INTC_AXI_TIMER_0_INTERRUPT_INTR, vTickISR, NULL );
	}

	if( xStatus == pdPASS )
	{
		vPortEnableInterrupt( XPAR_MICROBLAZE_0_INTC_AXI_TIMER_0_INTERRUPT_INTR );

		/* Configure the timer interrupt handler. */
		XTmrCtr_SetHandler( &xTimer0Instance, ( void * ) vTickISR, NULL );

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

	configASSERT( ( xStatus == pdPASS ) );
}
/*-----------------------------------------------------------*/

void vApplicationClearTimerInterrupt( void )
{
unsigned long ulCSR;

	/* Increment the RTOS tick - this might cause a task to unblock. */
	vTaskIncrementTick();

	/* Clear the timer interrupt */
	ulCSR = XTmrCtr_GetControlStatusReg( XPAR_AXI_TIMER_0_BASEADDR, 0 );
	XTmrCtr_SetControlStatusReg( XPAR_AXI_TIMER_0_BASEADDR, 0, ulCSR );
}

