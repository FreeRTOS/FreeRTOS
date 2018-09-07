#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"

#include "hw_platform.h"
#include "riscv_hal.h"
#include "hal.h"
#include "core_gpio.h"
#include "core_timer.h"
#include "core_uart_apb.h"

const char * g_hello_msg = "\r\nFreeRTOS Example\r\n";


/*
 * Notes:
 * + Program the device using the flash project in
 *   MS-RISC-V\M2GL025-Creative-Board\Programming_The_Target_Device\PROC_SUBSYSTEM_MIV_RV32IMA_BaseDesign.
 *   See https://github.com/RISCV-on-Microsemi-FPGA/M2GL025-Creative-Board.
 * + Above referenced image sets the clock to 50MHz. *
 * + Debug configuration is critical.
 */


/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0UL )

/******************************************************************************
 * CoreUARTapb instance data.
 *****************************************************************************/
UART_instance_t g_uart;
/*-----------------------------------------------------------*/

static void vUartTestTask1( void *pvParameters );
static void vUartTestTask2( void *pvParameters );

/*
 * FreeRTOS hook for when malloc fails, enable in FreeRTOSConfig.
 */
void vApplicationMallocFailedHook( void );

/*
 * FreeRTOS hook for when FreeRtos is idling, enable in FreeRTOSConfig.
 */
void vApplicationIdleHook( void );

/*
 * FreeRTOS hook for when a stack overflow occurs, enable in FreeRTOSConfig.
 */
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );

/*_RB_
gpio_instance_t g_gpio0;
gpio_instance_t g_gpio1;
timer_instance_t g_timer0;
timer_instance_t g_timer1;


/*-----------------------------------------------------------*/
extern uint32_t SysTick_Config(uint32_t ticks);
extern void __enable_irq(void);

int main( void )
{
    PLIC_init();
//_RB_    GPIO_init(&g_gpio0, COREGPIO_IN_BASE_ADDR, GPIO_APB_32_BITS_BUS);
//_RB_    GPIO_init(&g_gpio1, COREGPIO_OUT_BASE_ADDR, GPIO_APB_32_BITS_BUS);

    /**************************************************************************
    * Initialize CoreUART with its base address, baud value, and line
    * configuration.
    *************************************************************************/
    UART_init(&g_uart, COREUARTAPB0_BASE_ADDR, BAUD_VALUE_115200,
             (DATA_8_BITS | NO_PARITY) );

    UART_polled_tx_string( &g_uart, (const uint8_t *)"\r\n\r\n		Sample Demonstration of FreeRTOS port for Mi-V processor.\r\n\r\n" );
    UART_polled_tx_string( &g_uart, (const uint8_t *)"		This project creates  two tasks and runs them at regular intervals.\r\n" );

    /* Create the two test tasks. */
	xTaskCreate( vUartTestTask1, "UArt1", 1000, NULL, uartPRIMARY_PRIORITY, NULL );
//	xTaskCreate( vUartTestTask2, "UArt2", 1000, NULL, uartPRIMARY_PRIORITY, NULL );

	/* Start the kernel.  From here on, only tasks and interrupts will run. */
	vTaskStartScheduler();

	/* Exit FreeRTOS */
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

static void vUartTestTask1( void *pvParameters )
{
	( void ) pvParameters;

	for( ;; )
	{
		UART_polled_tx_string( &g_uart, (const uint8_t *)"Task - 1\r\n" );
	    vTaskDelay( pdMS_TO_TICKS( 100 ) );
	}
}


/*-----------------------------------------------------------*/

static void vUartTestTask2( void *pvParameters )
{
	( void ) pvParameters;

	for( ;; )
	{
//		UART_polled_tx_string( &g_uart, (const uint8_t *)"Task - 2\r\n" );
	    vTaskDelay(5);
	}
}
