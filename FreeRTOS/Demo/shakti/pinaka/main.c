#include "FreeRTOS.h"
#include "task.h"
//#include "uart.h"
#include "utils.h"
#include "gpio.h"
#include "queue.h"
#include "timers.h"
#include <stdint.h>

/*
 * FreeRTOS hook for when malloc fails, enable in FreeRTOSConfig.
 */
void vApplicationMallocFailedHook( void );

/*
 * FreeRTOS hook for when freertos is idling, enable in FreeRTOSConfig.
 */
void vApplicationIdleHook( void );

/*
 * FreeRTOS hook for when a stackoverflow occurs, enable in FreeRTOSConfig.
 */
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );

void vTaskgpio(__attribute__((unused)) void *pvParameters);

/*-----------------------------------------------------------*/

int main( void )
{
	xTaskCreate(vTaskgpio,"Task 1",500,NULL,1,NULL);

	/* Task scheduledd with help of clint */
	vTaskStartScheduler();

	/* Exit FreeRTOS */
	return 0;
}

/*
   Control gpio2 through gpio 1
   Led is connected to gpio2 and button is connected to gpio1
 */
void vTaskgpio(__attribute__((unused)) void *pvParameters)
{
	const TickType_t xDelay1000ms = pdMS_TO_TICKS(100);

	write_word(GPIO_DIRECTION_CNTRL_REG, 0x2);

	/*
	   Read the value from GPIO0 and based on that value control the led connected to GPIO1
	 */
	for( ;; )
	{
		if(read_word(GPIO_DATA_REG) & 0X01)
		{
			write_word(GPIO_DATA_REG, 0x2);
		}else
		{
			write_word(GPIO_DATA_REG, 0x0);
		}
		vTaskDelay( xDelay1000ms );
		/* Delay for a period. */
	}
}

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
