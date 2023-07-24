/*
 * FreeRTOS V202212.01
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

/* FreeRTOS kernel includes. */
#include <FreeRTOS.h>
#include <task.h>
#include <uart/uart.h>
static uart_instance_t * const gp_my_uart = &g_uart_0;
static int g_stdio_uart_init_done = 0;

#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY	0

/*-----------------------------------------------------------*/
#if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1
	extern void main_blinky( void );
#else
	extern void main_full( void );
#endif 
/*-----------------------------------------------------------*/

/* Prototypes for the standard FreeRTOS callback/hook functions implemented
within this file.  See https://www.freertos.org/a00016.html */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );

/* Prepare hardware to run the demo. */
static void prvSetupHardware( void );

/* Send a message to the UART initialised in prvSetupHardware. */
void vSendString( const char * const pcString );

/*-----------------------------------------------------------*/

#define LEDS_ADDR     0x40000000
#define LEDS (*((volatile unsigned int *) (LEDS_ADDR + 0x0)))
static int LED_STATE = 0xf;

uint8_t s_uart[12] = "init_uart\r\n";

/*-----------------------------------------------------------*/
void LEDInit( void )
{
    LEDS = LED_STATE;
}

static void prvSetupHardware( void )
{
    LEDInit();
    
    UART_init(gp_my_uart,
              STDIO_BAUD_RATE,
              UART_DATA_8_BITS | UART_NO_PARITY | UART_ONE_STOP_BIT);
                      
    g_stdio_uart_init_done = 1;
    UART_polled_tx_string(gp_my_uart, s_uart);


	//PLIC_init();
	//UART_init( &g_uart, COREUARTAPB0_BASE_ADDR, BAUD_VALUE_115200, ( DATA_8_BITS | NO_PARITY ) );
}
/*-----------------------------------------------------------*/


void LEDOn( void )
{
    LEDS = 0xf;
}

void LEDOff( void )
{
    LEDS = 0x0;
}

int dummy(int i)
{
    int j = i;
    return j;
}
void vToggleLED( void )
{
    LEDS = LED_STATE;
    LED_STATE = ~LED_STATE;
}

void flash_led()
{   int loop = 5;
    for(int k = 0; k < loop; k++)
    {
        for(int i = 0; i < 100000;)
        {
          i++;

        }
        vToggleLED();
    }
}


extern void freertos_risc_v_trap_handler( void );

#define mainVECTOR_MODE_DIRECT 1
int main( void )
{
	prvSetupHardware();
    flash_led();
	// trap handler initialization
    #if( mainVECTOR_MODE_DIRECT == 1 )
	{
		__asm__ volatile( "csrw mtvec, %0" :: "r"( freertos_risc_v_trap_handler ) );
	}
	#else
	{
		__asm__ volatile( "csrw mtvec, %0" :: "r"( ( uintptr_t )freertos_vector_table | 0x1 ) );
	}
	#endif

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
    return 0;
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

void vAssertCalled( void )
{
    uint8_t s_debug[16] = "vassert called\r\n";
    portENTER_CRITICAL();
    UART_polled_tx_string(gp_my_uart, s_debug);
    portEXIT_CRITICAL();
    volatile uint32_t ulSetTo1ToExitFunction = 0;

    taskDISABLE_INTERRUPTS();
	while( ulSetTo1ToExitFunction != 1 )
	{
		__asm volatile( "NOP" );
	}
}
