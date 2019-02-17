/*
 * FreeRTOS Kernel V10.2.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * Create implementation of vPortSetupTimerInterrupt() if the CLINT is not
 * available, but make sure the configCLINT_BASE_ADDRESS constant is still
 * defined.
 *
 * Define vPortHandleInterrupt to whatever the interrupt handler is called.  In
 * this case done by defining vPortHandleInterrupt=SystemIrqHandler on the
 * assembler command line as SystemIrqHandler is referenced from both FreeRTOS
 * code and the libraries that come with the Vega board.
 */

/* FreeRTOS kernel includes. */
#include <FreeRTOS.h>
#include <task.h>

/* Vega includes. */
#include "fsl_device_registers.h"
#include "fsl_debug_console.h"
#include "board.h"
#include "pin_mux.h"
#include "clock_config.h"


/******************************************************************************
 * This project provides two demo applications.  A simple blinky style project,
 * and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting (defined in this file) is used to
 * select between the two.  The simply blinky demo is implemented and described
 * in main_blinky.c.  The more comprehensive test and demo application is
 * implemented and described in main_full.c.
 *
 * This file implements the code that is not demo specific, including the
 * hardware setup and standard FreeRTOS hook functions.
 *
 * ENSURE TO READ THE DOCUMENTATION PAGE FOR THIS PORT AND DEMO APPLICATION ON
 * THE http://www.FreeRTOS.org WEB SITE FOR FULL INFORMATION ON USING THIS DEMO
 * APPLICATION, AND ITS ASSOCIATE FreeRTOS ARCHITECTURE PORT!
 *
 */

/* Set mainCREATE_SIMPLE_BLINKY_DEMO_ONLY to one to run the simple blinky demo,
or 0 to run the more comprehensive test and demo application. */
#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY	0

/*
 * main_blinky() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 1.
 * main_full() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
#if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1
	extern void main_blinky( void );
#else
	extern void main_full( void );
#endif /* #if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 */

/* Prototypes for the standard FreeRTOS callback/hook functions implemented
within this file.  See https://www.freertos.org/a00016.html */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );

/* Prepare haredware to run the demo. */
static void prvSetupHardware( void );

/* Send a messaage to the UART initialised in prvSetupHardware. */
void vSendString( const char * const pcString );

/*-----------------------------------------------------------*/

void main( void )
{
	prvSetupHardware();

	/* The mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting is described at the top
	of this file. */
	#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 )
	{
		main_blinky();
	}
	#else
	{
		main_full();
	}
	#endif
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
gpio_pin_config_t mGpioPinConfigStruct;

	/* Init board hardware. */
	BOARD_InitPins();
	BOARD_BootClockRUN();
	BOARD_InitDebugConsole();

	/* For LED. */
	mGpioPinConfigStruct.outputLogic = 1U; /* High. */
	mGpioPinConfigStruct.pinDirection = kGPIO_DigitalOutput;
	GPIO_PinInit( BOARD_LED1_GPIO, BOARD_LED1_GPIO_PIN, &mGpioPinConfigStruct );
}
/*-----------------------------------------------------------*/

void vToggleLED( void )
{
	GPIO_TogglePinsOutput( BOARD_LED1_GPIO, 1U << BOARD_LED1_GPIO_PIN );
}
/*-----------------------------------------------------------*/

void vSendString( const char * const pcString )
{
	PRINTF( pcString );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* vApplicationMallocFailedHook() will only be called if
	configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	function that will get called if a call to pvPortMalloc() fails.
	pvPortMalloc() is called internally by the kernel whenever a task, queue,
	timer or semaphore is created.  It is also called by various parts of the
	demo application.  If heap_1.c or heap_2.c are used, then the size of the
	heap available to pvPortMalloc() is defined by configTOTAL_HEAP_SIZE in
	FreeRTOSConfig.h, and the xPortGetFreeHeapSize() API function can be used
	to query the size of free heap space that remains (although it does not
	provide information on how the remaining heap might be fragmented). */
	taskDISABLE_INTERRUPTS();
	__asm volatile( "ebreak" );
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set
	to 1 in FreeRTOSConfig.h.  It will be called on each iteration of the idle
	task.  It is essential that code added to this hook function never attempts
	to block in any way (for example, call xQueueReceive() with a block time
	specified, or call vTaskDelay()).  If the application makes use of the
	vTaskDelete() API function (as this demo application does) then it is also
	important that vApplicationIdleHook() is permitted to return to its calling
	function, because it is the responsibility of the idle task to clean up
	memory allocated by the kernel to any task that has since been deleted. */
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */
	taskDISABLE_INTERRUPTS();
	__asm volatile( "ebreak" );
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	/* The tests in the full demo expect some interaction with interrupts. */
	#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY != 1 )
	{
		extern void vFullDemoTickHook( void );
		vFullDemoTickHook();
	}
	#endif
}
/*-----------------------------------------------------------*/

void vPortSetupTimerInterrupt( void )
{
extern void SystemSetupSystick(uint32_t tickRateHz, uint32_t intPriority );

	/* No CLINT so use the LPIT (Low Power Interrupt Timer) to generate the tick
	interrupt. */
	CLOCK_SetIpSrc( kCLOCK_Lpit0, kCLOCK_IpSrcFircAsync );
	SystemSetupSystick( configTICK_RATE_HZ, configKERNEL_INTERRUPT_PRIORITY - 1 );
}
/*-----------------------------------------------------------*/

void LPIT0_IRQHandler( void )
{
BaseType_t xTaskIncrementTick( void );
void vTaskSwitchContext( void );

#warning requires critical section if interrpt nesting is used.

	/* vPortSetupTimerInterrupt() uses LPIT0 to generate the tick interrupt. */
	if( xTaskIncrementTick() != 0 )
	{
		vTaskSwitchContext();
	}

	/* Clear LPIT0 interrupt. */
	LPIT0->MSR = 1U;
}
/*-----------------------------------------------------------*/

/* At the time of writing, interrupt nesting is not supported, so do not use
the default SystemIrqHandler() implementation as that enables interrupts.  A
version that does not enable interrupts is provided below.  THIS INTERRUPT
HANDLER IS SPECIFIC TO THE VEGA BOARD WHICH DOES NOT INCLUDE A CLINT! */
void SystemIrqHandler( uint32_t mcause )
{
uint32_t ulInterruptNumber;
typedef void ( * irq_handler_t )( void );
extern const irq_handler_t isrTable[];

	ulInterruptNumber = mcause & 0x1FUL;

	/* Clear pending flag in EVENT unit .*/
	EVENT_UNIT->INTPTPENDCLEAR = ( 1U << ulInterruptNumber );

	/* Read back to make sure write finished. */
	(void)(EVENT_UNIT->INTPTPENDCLEAR);

	/* Now call the real irq handler for ulInterruptNumber */
	isrTable[ ulInterruptNumber ]();
}

