// See LICENSE for license details.

#include <FreeRTOS.h>
#include <task.h>

#include <stdio.h>
#include <stdlib.h>
#include "platform.h"
#include <string.h>
#include "plic/plic_driver.h"
#include "encoding.h"
#include <unistd.h>
#include "stdatomic.h"



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



void vRegTest1Task( void *pvParameters );
void vRegTest2Task( void *pvParameters );


const char * const pcStartMessage = "FreeRTOS demo\r\n";
volatile uint32_t ulRegTest1LoopCounter = 0, ulRegTest2LoopCounter = 0;
static void prvCheckTask( void *pvParameters );
plic_instance_t g_plic;
uint32_t bitbang_mask = 0;

int main( void )
{
	#ifdef HAS_BOARD_BUTTONS
		GPIO_REG(GPIO_OUTPUT_EN)  &= ~((0x1 << BUTTON_0_OFFSET) | (0x1 << BUTTON_1_OFFSET) | (0x1 << BUTTON_2_OFFSET));
		GPIO_REG(GPIO_PULLUP_EN)  &= ~((0x1 << BUTTON_0_OFFSET) | (0x1 << BUTTON_1_OFFSET) | (0x1 << BUTTON_2_OFFSET));
		GPIO_REG(GPIO_INPUT_EN)   |=  ((0x1 << BUTTON_0_OFFSET) | (0x1 << BUTTON_1_OFFSET) | (0x1 << BUTTON_2_OFFSET));
	#endif

	GPIO_REG(GPIO_INPUT_EN)    &= ~((0x1<< RED_LED_OFFSET) | (0x1<< GREEN_LED_OFFSET) | (0x1 << BLUE_LED_OFFSET)) ;
	GPIO_REG(GPIO_OUTPUT_EN)   |=  ((0x1<< RED_LED_OFFSET)| (0x1<< GREEN_LED_OFFSET) | (0x1 << BLUE_LED_OFFSET)) ;
	GPIO_REG(GPIO_OUTPUT_VAL)  |=   (0x1 << BLUE_LED_OFFSET) ;
	GPIO_REG(GPIO_OUTPUT_VAL)  &=  ~((0x1<< RED_LED_OFFSET) | (0x1<< GREEN_LED_OFFSET)) ;

	/* For Bit-banging with Atomics demo. */
	#ifdef _SIFIVE_HIFIVE1_H
		bitbang_mask = (1 << PIN_19_OFFSET);
	#else
		#ifdef _SIFIVE_COREPLEXIP_ARTY_H
			bitbang_mask = (0x1 << JA_0_OFFSET);
		#endif
	#endif

	GPIO_REG(GPIO_OUTPUT_EN) |= bitbang_mask;

//	xTaskCreate( vRegTest1Task, "RegTest1", 1000, NULL, tskIDLE_PRIORITY, NULL );
//	xTaskCreate( vRegTest2Task, "RegTest2", 1000, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvCheckTask, "Check", 1000, NULL, configMAX_PRIORITIES - 1, NULL );

	vTaskStartScheduler();
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
const char *pcMessage = "PASS\r\n";
const TickType_t xCheckPeriod = pdMS_TO_TICKS( 3000UL );
uint32_t ulLastRegTest1LoopCounter = 0, ulLastRegTest2LoopCounter = 0;
volatile uintptr_t mstatus;

volatile uint32_t ulx;
__asm volatile ("csrr %0, mstatus" : "=r"(mstatus));
portENABLE_INTERRUPTS();
__asm volatile ("csrr %0, mstatus" : "=r"(mstatus));
for( ;; )
{
//	for( ulx = 0; ulx < 0xffff; ulx++ ) __asm volatile( "NOP" );
//	vPortSetupTimerInterrupt();
	vTaskDelay( xCheckPeriod );
	write( STDOUT_FILENO, "Blip\r\n", strlen( "Blip\r\n" ) );
}
#if 0
	for( ;; )
	{
		vTaskDelay( xCheckPeriod );

		if( ulLastRegTest1LoopCounter == ulRegTest1LoopCounter )
		{
			/* The RegTest1 loop counter is no longer incrementing, indicating
			the task failed its self check. */
			pcMessage = "FAIL: RegTest1\r\n";
		}
		else
		{
			ulLastRegTest1LoopCounter = ulRegTest1LoopCounter;
		}

		if( ulLastRegTest2LoopCounter == ulRegTest2LoopCounter )
		{
			/* The RegTest1 loop counter is no longer incrementing, indicating
			the task failed its self check. */
			pcMessage = "FAIL: RegTest2\r\n";
		}
		else
		{
			ulLastRegTest2LoopCounter = ulRegTest2LoopCounter;
		}

		vUARTWriteString( pcMessage );
	}
#endif
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

#define mainINTERRUPT_BIT_SET 0x80000000UL
#define mainENVIRONMENT_CALL	11UL
#define mainEXTERNAL_INTERRRUPT ( mainINTERRUPT_BIT_SET | 11UL )
#define mainTIMER_INTERRUPT		( mainINTERRUPT_BIT_SET | 7UL )
#define mainSOFTWARE_INTERRUPT	( mainINTERRUPT_BIT_SET | 3UL )

extern void Timer_IRQHandler( void );

uint32_t ulPortTrapHandler( uint32_t mcause, uint32_t mepc )
{
	if( mcause == mainENVIRONMENT_CALL )
	{
		vTaskSwitchContext();

		/* Ensure not to return to the instruction that generated the exception. */
		mepc += 4;
	}
	else if( mcause == mainEXTERNAL_INTERRRUPT )
	{
		for( ;; );
	}
	else if( mcause == mainTIMER_INTERRUPT )
	{
		Timer_IRQHandler();
	}
	else if( mcause == mainSOFTWARE_INTERRUPT )
	{
		for( ;; );
	}

	return mepc;
}
