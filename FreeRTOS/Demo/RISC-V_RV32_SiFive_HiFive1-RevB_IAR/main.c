/*
 * FreeRTOS V202012.00
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
 * When running on the HiFive Rev B hardware:
 * When executing correctly the red LED will toggle every three seconds.  If
 * the red LED toggles every 500ms then one of the self-monitoring test tasks
 * discovered a potential issue.  If the red led stops toggling then a hardware
 * exception occurred or an assert was hit.
 *
 * ENSURE TO READ THE DOCUMENTATION PAGE FOR THIS PORT AND DEMO APPLICATION ON
 * THE http://www.FreeRTOS.org WEB SITE FOR FULL INFORMATION ON USING THIS DEMO
 * APPLICATION, AND ITS ASSOCIATE FreeRTOS ARCHITECTURE PORT!
 *
 */

/* FreeRTOS kernel includes. */
#include <FreeRTOS.h>
#include <task.h>

/* Standard includes. */
#include <stdio.h>

/* Set mainCREATE_SIMPLE_BLINKY_DEMO_ONLY to one to run the simple blinky demo,
or 0 to run the more comprehensive test and demo application. */
#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY	0

/* UART hardware constants. */
#define mainUART_BASE_ADDRESS				( *( volatile uint32_t * ) 0x20000000UL )
#define mainUART_TX_DATA					0x00
#define mainUART_TX_CTRL					0x08
#define mainUART_RX_CTRL					0x0c
#define mainUART_CLOCK_DIV					0x18
#define mainUART_TX_ENABLE_BIT				(1UL <<  0UL)
#define mainUART_RX_ENABLE_BIT				(1UL <<  0UL)
#define mainUART_TX_FULL_BIT				(1UL << 31UL)
#define mainUART_REGISTER( offset )			( ( mainUART_BASE_ADDRESS + offset ) )
#define mainUART_REGISTER_WORD( offset )	( *( ( uint32_t * ) mainUART_REGISTER( offset ) ) )

/* Hardware LED specifics. */
#define mainRED_LED_PIN 					( 1UL << 0x16UL )
#define mainLED_IO_BASE_ADDRESS				( 0x10012000UL )
#define mainRED_LED_INPUT_ENABLE_REG  		( * ( uint32_t * ) ( mainLED_IO_BASE_ADDRESS + 4UL ) )
#define mainRED_LED_OUTPUT_ENABLE_REG 		( * ( uint32_t * ) ( mainLED_IO_BASE_ADDRESS + 8UL ) )

/* Hardware LED specifics. */
#define mainUART_PINMUX_BASE_ADDRESS 	( 0x10012000 )
#define mainUART0_BASE_ADDRESS 			0x10013000UL
#define mainUART_CLOCK_RATE 			16000000UL
#define mainUART_BAUD_RATE 				115200UL
#define mainUART0_TX_DATA_REG			( * ( uint32_t * ) ( mainUART0_BASE_ADDRESS + 0UL ) )
#define mainUART0_TX_DATA_BYTE_REG		( * ( uint8_t * ) ( mainUART0_BASE_ADDRESS + 0UL ) )
#define mainUART0_DIV_REG 				( * ( uint32_t * ) ( mainUART0_BASE_ADDRESS + 24UL ) )
#define mainUART0_TXCTRL_REG			( * ( uint32_t * ) ( mainUART0_BASE_ADDRESS + 8UL ) )
#define mainUART0_RXCTRL_REG			( * ( uint32_t * ) ( mainUART0_BASE_ADDRESS + 12UL ) )
#define mainUART0_GPIO_SEL_REG			( * ( uint32_t * ) ( mainUART_PINMUX_BASE_ADDRESS + 60UL ) )
#define mainUART0_GPIO_SEL_EN			( * ( uint32_t * ) ( mainUART_PINMUX_BASE_ADDRESS + 56UL ) )
#define mainUART_TXEN_BIT				( 1UL )
#define mainUART0_PIN					( 0x30000UL )

/* Registers used to initialise the PLIC. */
#define mainPLIC_PENDING_0 ( * ( ( volatile uint32_t * ) 0x0C001000UL ) )
#define mainPLIC_PENDING_1 ( * ( ( volatile uint32_t * ) 0x0C001004UL ) )
#define mainPLIC_ENABLE_0  ( * ( ( volatile uint32_t * ) 0x0C002000UL ) )
#define mainPLIC_ENABLE_1  ( * ( ( volatile uint32_t * ) 0x0C002004UL ) )

/*-----------------------------------------------------------*/

/*
 * main_blinky() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 1.
 * main_full() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
#if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1
	extern void main_blinky( void );
#else
	extern void main_full( void );
#endif /* #if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 */

/*
 * Prototypes for the standard FreeRTOS callback/hook functions implemented
 * within this file.  See https://www.freertos.org/a00016.html
 */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );

/*
 * Setup the hardware to run this demo.
 */
static void prvSetupHardware( void );

/* Simple polling UART send function. */
void vSendString( const char * const pcString );

/* Toggle the red LED. */
void vTogglelED( void );

/*-----------------------------------------------------------*/

int main( void )
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
	/* Set all interrupt enable bits to 0. */
	mainPLIC_ENABLE_0 = 0UL;
	mainPLIC_ENABLE_1 = 0UL;

	/* Clear all pending interrupts. */
	mainPLIC_PENDING_0 = 0UL;
	mainPLIC_PENDING_1 = 0UL;

	/* Disable Red LED input. */
	mainRED_LED_INPUT_ENABLE_REG &= ~mainRED_LED_PIN;

	/* Enable Red LED output. */
	mainRED_LED_OUTPUT_ENABLE_REG |= mainRED_LED_PIN;

	/* Set UART baud rate. */
	mainUART0_DIV_REG = ( mainUART_CLOCK_RATE / mainUART_BAUD_RATE ) - 1;

	/* Enable UART Tx. */
	mainUART0_TXCTRL_REG |= mainUART_TXEN_BIT;
	mainUART0_GPIO_SEL_REG &= mainUART0_PIN;
	mainUART0_GPIO_SEL_EN |= mainUART0_PIN;
}
/*-----------------------------------------------------------*/

void vToggleLED( void )
{
static uint32_t ulLEDState = 0;

	if( ulLEDState == 0 )
	{
		mainRED_LED_OUTPUT_ENABLE_REG |= mainRED_LED_PIN;
	}
	else
	{
		mainRED_LED_OUTPUT_ENABLE_REG &= ~mainRED_LED_PIN;
	}
	ulLEDState = !ulLEDState;
}
/*-----------------------------------------------------------*/

void vSendString( const char * const pcString )
{
uint32_t ulIndex = 0;

	/* Crude polling UART Tx. */
	while( pcString[ ulIndex ] != 0x00 )
	{
		while( ( mainUART0_TX_DATA_REG & mainUART_TX_FULL_BIT ) != 0UL );
		mainUART0_TX_DATA_BYTE_REG = pcString[ ulIndex ];
		ulIndex++;
	}
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

/* Called from the kernel's port layer to handle device specific external
interrupts. */
void vApplicationHandleTrap( uint32_t mcause )
{
char pcCause[ 20 ];

	#warning vApplicationHandleTrap not implemented.
	/* Not implemented yet! */
	sprintf( pcCause, "%u", mcause );
	vSendString( pcCause );
	configASSERT( mcause == 0 );
}

/*-----------------------------------------------------------*/

void *malloc( size_t xSize )
{
	/* The linker script does not define a heap so artificially force an assert()
	if something unexpectedly uses the C library heap.  See
	https://www.freertos.org/a00111.html for more information. */
	configASSERT( xTaskGetTickCount() == 0x00 );
	return NULL;
}
/*-----------------------------------------------------------*/

