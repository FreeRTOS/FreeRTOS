/*
 * Copyright 2016-2019 NXP
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * o Redistributions of source code must retain the above copyright notice, this list
 *   of conditions and the following disclaimer.
 *
 * o Redistributions in binary form must reproduce the above copyright notice, this
 *   list of conditions and the following disclaimer in the documentation and/or
 *   other materials provided with the distribution.
 *
 * o Neither the name of NXP Semiconductor, Inc. nor the names of its
 *   contributors may be used to endorse or promote products derived from this
 *   software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
 
/**
 * @file    main.c
 * @brief   Application entry point.
 */
#include <stdio.h>

/* Board specific includes. */
#include "board.h"
#include "peripherals.h"
#include "pin_mux.h"
#include "clock_config.h"
#include "LPC51U68.h"
#include "fsl_debug_console.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

#include "compiler_attributes.h"

/*-----------------------------------------------------------*/
typedef enum LED_STATE {
	LED_RED_BLINK_ON = 1,
	LED_RED_BLINK_OFF,
	LED_GREEN_BLINK_ON,
	LED_GREEN_BLINK_OFF,
	LED_BLUE_BLINK_ON,
	LED_BLUE_BLINK_OFF,
} E_LED_STATE;

/* Static variable to keep track of LED color.
 * red -> green -> blue -> red -> ...
 * This variable is not intended for multi-threaded application.
 */
static E_LED_STATE eLedState = LED_RED_BLINK_ON;

/* Show iteration number in UART.
 * This variable is not intended for multi-threaded application.
 */
static int i = 0;

/* Track how many times tick interrupt has occurred. */
static unsigned int uTickInterruptCounter = 0;

/*
 * Perform any application specific hardware configuration.  The clocks,
 * memory, etc. are configured before main() is called.
 */
static void prvSetupHardware( void );

/**
 * Heap_5 is being used because the RAM is not contiguous, therefore the heap
 * needs to be initialized.  See http://www.freertos.org/a00111.html
 */
static void prvInitializeHeap( void );

/*
 * The hardware only has a single LED.  Simply toggle it.
 */
void vMainToggleLED( void );

/* main_blinky() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 1.
main_full() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0. */
void main_blinky( void );
void main_full( void );

/*
 * @brief   Application entry point.
 */
int main(void)
{

	/* Prepare the hardware to run this demo. */
	prvSetupHardware();

	/* Initialize heap regions. */
	prvInitializeHeap();

	/* Show something on UART.
	Serial port setup as baudrate: 115200, data: 8-bit, parity: none, stop bits: 1, flow control: none.
	sTerminal setup as receive: auto, transmit: CR+LF.*/
	PRINTF("FreeRTOS demo.\r\n");

	/* The mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting is described at the top
	of this file. */
	#if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1
	{
		main_blinky();
	}
	#else
	{
		main_full();
	}
	#endif

	return 0;
}

/*-----------------------------------------------------------*/
void vMainToggleLED( void )
{
	switch (eLedState)
	{
		case LED_RED_BLINK_ON:
			PRINTF("Iteration %d -- tick interrupt count %d.\r\n", i, uTickInterruptCounter);
			i++;

			LED_RED_ON();
			eLedState = LED_RED_BLINK_OFF;
			break;
		case LED_RED_BLINK_OFF:
			LED_RED_OFF();
			eLedState = LED_GREEN_BLINK_ON;
			break;
		case LED_GREEN_BLINK_ON:
			LED_GREEN_ON();
			eLedState = LED_GREEN_BLINK_OFF;
			break;
		case LED_GREEN_BLINK_OFF:
			LED_GREEN_OFF();
			eLedState = LED_BLUE_BLINK_ON;
			break;
		case LED_BLUE_BLINK_ON:
			LED_BLUE_ON();
			eLedState = LED_BLUE_BLINK_OFF;
			break;
		case LED_BLUE_BLINK_OFF:
			LED_BLUE_OFF();
			eLedState = LED_RED_BLINK_ON;
			break;
		default:
			/* Unexpected state. Let's reset to default color. */
			eLedState = LED_RED_BLINK_ON;
	}

	return;
}

/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Initialize board hardware. */
	BOARD_InitBootPins();
	BOARD_InitBootClocks();
	BOARD_InitBootPeripherals();

	/* Enable clock for GPIO. */
	CLOCK_EnableClock(kCLOCK_Gpio0);
	CLOCK_EnableClock(kCLOCK_Gpio1);

	/* Initialize FSL debug console. */
	BOARD_InitDebugConsole();

	/* Initialize tri-color LED. */
	LED_RED_INIT(LOGIC_LED_OFF);
	LED_GREEN_INIT(LOGIC_LED_OFF);
	LED_BLUE_INIT(LOGIC_LED_OFF);

	return;
}

/*-----------------------------------------------------------*/

static void prvInitializeHeap( void )
{
	/* Place the first block of the heap memory in the first bank of RAM. */
	static uint8_t ucHeap1[ configTOTAL_HEAP_SIZE ];

	/* Place the second block of the heap memory in the second bank of RAM. */
	static uint8_t ucHeap2[ 16 * 1024 ] COMPILER_ATTRIBUTE_PLACE_IN_2ND_MEMORY_BANK;
	
	/* Memory regions are defined in address order, and terminate with NULL. */
	static HeapRegion_t xHeapRegions[] =
	{
		{ ( unsigned char * ) ucHeap1, sizeof( ucHeap1 ) },
		{ ( unsigned char * ) ucHeap2, sizeof( ucHeap2 ) },
		{ NULL,                        0                 }
	};

	vPortDefineHeapRegions( xHeapRegions );

	return;
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
	for( ;; );
}

/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
#if mainCHECK_INTERRUPT_STACK == 1
extern unsigned long _pvHeapStart[];

	/* This function will be called by each tick interrupt if
	configUSE_TICK_HOOK is set to 1 in FreeRTOSConfig.h.  User code can be
	added here, but the tick hook is called from an interrupt context, so
	code must not attempt to block, and only the interrupt safe FreeRTOS API
	functions can be used (those that end in FromISR()). */

	/* Manually check the last few bytes of the interrupt stack to check they
	have not been overwritten.  Note - the task stacks are automatically
	checked for overflow if configCHECK_FOR_STACK_OVERFLOW is set to 1 or 2
	in FreeRTOSConifg.h, but the interrupt stack is not. */
	configASSERT( memcmp( ( void * ) _pvHeapStart, ucExpectedInterruptStackValues, sizeof( ucExpectedInterruptStackValues ) ) == 0U );
#endif /* mainCHECK_INTERRUPT_STACK */

	uTickInterruptCounter++;
}


