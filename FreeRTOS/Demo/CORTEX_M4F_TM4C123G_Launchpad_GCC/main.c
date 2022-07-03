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
 * https://www.FreeRTOS.org
 * https://aws.amazon.com/freertos
 *
 */

/* Standard includes. */
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Driver Lib includes*/
#include "driverlib/driverlib.h"



/*
 * Set up the hardware ready to run this demo.
 */
static void prvSetupHardware( void );

/*
 * main_blinky() is used when configCREATE_SIMPLE_TICKLESS_DEMO is set to 1.
 * main_full() is used when configCREATE_SIMPLE_TICKLESS_DEMO is set to 0.
 */
extern void main_blinky( void );
extern void main_full( void );

/*-----------------------------------------------------------*/

int main( void )
{
	/* See http://www.FreeRTOS.org/TI_MSP432_Free_RTOS_Demo.html for instructions. */

	/* Prepare the hardware to run this demo. */
	prvSetupHardware();

	/* The configCREATE_SIMPLE_TICKLESS_DEMO setting is described at the top
	of this file. */
	#if( configCREATE_SIMPLE_TICKLESS_DEMO == 1 )
	{
		main_blinky();
	}
	#else
	{
		//main_full();
	}
	#endif

	return 0;

}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
    /* Setup the PLL. 
     * CPU Clock : 50M hz
     */
    SysCtlClockSet( SYSCTL_SYSDIV_4 | SYSCTL_USE_PLL | SYSCTL_OSC_MAIN | SYSCTL_XTAL_16MHZ );
    
    /* Setup RGB LED. */
    SysCtlPeripheralEnable( SYSCTL_PERIPH_GPIOF );
    while(!SysCtlPeripheralReady(SYSCTL_PERIPH_GPIOF)){}
    GPIOPinTypeGPIOOutput( GPIO_PORTF_BASE, mainLED_RED|mainLED_BLUE|mainLED_GREEN );
	
    /* Setup the push button. */
    GPIOPinTypeGPIOInput( GPIO_PORTF_BASE, GPIO_PIN_4 );
	GPIOPadConfigSet(GPIO_PORTF_BASE, GPIO_PIN_4, GPIO_STRENGTH_2MA, GPIO_PIN_TYPE_STD_WPU);
    
    /* Setup Interrupt. */
    GPIOIntTypeSet( GPIO_PORTF_BASE, GPIO_PIN_4, GPIO_RISING_EDGE );
	IntPrioritySet( INT_GPIOF, configKERNEL_INTERRUPT_PRIORITY );
    GPIOIntEnable( GPIO_PORTF_BASE, GPIO_PIN_4 );
	IntEnable( INT_GPIOF );
	
    /* Enable the UART.  */
	SysCtlPeripheralEnable( SYSCTL_PERIPH_UART0 );
    while(!SysCtlPeripheralReady(SYSCTL_PERIPH_UART0)){}
	SysCtlPeripheralEnable( SYSCTL_PERIPH_GPIOA );
    while(!SysCtlPeripheralReady(SYSCTL_PERIPH_GPIOA)){}

	/* Set GPIO A0 and A1 as peripheral function.  They are used to output the
	UART signals. */
    GPIOPinTypeUART( GPIO_PORTA_BASE, GPIO_PIN_0 | GPIO_PIN_1 );
    GPIOPinConfigure( GPIO_PA0_U0RX);
    GPIOPinConfigure( GPIO_PA1_U0TX);
	
    /* Configure the UART for 8-N-1 operation. */
	UARTConfigSetExpClk( UART0_BASE, SysCtlClockGet(), mainBAUD_RATE, UART_CONFIG_WLEN_8 | UART_CONFIG_PAR_NONE | UART_CONFIG_STOP_ONE );
	
    /* We don't want to use the fifo.  This is for test purposes to generate
	as many interrupts as possible. */
	HWREG( UART0_BASE + UART_O_LCRH ) &= ~mainFIFO_SET;

	/* Enable Tx interrupts. */
	HWREG( UART0_BASE + UART_O_IM ) |= UART_INT_TX;
	IntPrioritySet( INT_UART0, configKERNEL_INTERRUPT_PRIORITY );
	IntEnable( INT_UART0 );


}
/*----------------------------------------------------------*/

void vApplicationMallocFailedHook( void );
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

void vApplicationIdleHook( void );
void vApplicationIdleHook( void )
{

}
/*----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char* pcTaskName )
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
