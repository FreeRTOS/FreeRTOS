/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/*-----------------------------------------------------------*/

/* Perform any hardware initialisation necessary. */
static void prvSetupHardware( void );

/* Prototypes for the standard FreeRTOS callback/hook functions implemented
within this file. */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );

/*-----------------------------------------------------------*/

int main( void )
{
	prvSetupHardware();
	vTaskStartScheduler();
	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
extern uint8_t __cs3_interrupt_vector;
uint32_t ulSCTLR, ulVectorTable = ( uint32_t ) &__cs3_interrupt_vector;
const uint32_t ulVBit = 13U;

	alt_int_global_init();

	/* Clear SCTLR.V for low vectors and map the vector table to the beginning
	of the code. */
	__asm( "MRC p15, 0, %0, c1, c0, 0" : "=r" ( ulSCTLR ) );
	ulSCTLR &= ~( 1 << ulVBit );
	__asm( "MCR p15, 0, %0, c1, c0, 0" : : "r" ( ulSCTLR ) );
	__asm( "MCR p15, 0, %0, c12, c0, 0" : : "r" ( ulVectorTable ) );

	cache_init();
	mmu_init();
}
/*-----------------------------------------------------------*/

void vConfigureTickInterrupt( void )
{
alt_freq_t ulTempFrequency;
const alt_freq_t ulMicroSecondsPerSecond = 1000000UL;
void FreeRTOS_Tick_Handler( void );

	/* Interrupts are disabled when this function is called. */

	/* Initialise the general purpose timer modules. */
	alt_gpt_all_tmr_init();

	/* ALT_CLK_MPU_PERIPH = mpu_periph_clk */
	alt_clk_freq_get( ALT_CLK_MPU_PERIPH, &ulTempFrequency );

	/* Use the local private timer. */
	alt_gpt_counter_set( ALT_GPT_CPU_PRIVATE_TMR, ulTempFrequency / configTICK_RATE_HZ );

	/* Sanity check. */
	configASSERT( alt_gpt_time_microsecs_get( ALT_GPT_CPU_PRIVATE_TMR ) == ( ulMicroSecondsPerSecond / configTICK_RATE_HZ ) );

	/* Set to periodic mode. */
	alt_gpt_mode_set( ALT_GPT_CPU_PRIVATE_TMR, ALT_GPT_RESTART_MODE_PERIODIC );

	/* The timer can be started here as interrupts are disabled. */
	alt_gpt_tmr_start( ALT_GPT_CPU_PRIVATE_TMR );

	/* Register the standard FreeRTOS Cortex-A tick handler as the timer's
	interrupt handler.  The handler clears the interrupt using the
	configCLEAR_TICK_INTERRUPT() macro, which is defined in FreeRTOSConfig.h. */
	vRegisterIRQHandler( ALT_INT_INTERRUPT_PPI_TIMER_PRIVATE, ( alt_int_callback_t ) FreeRTOS_Tick_Handler, NULL );

	/* Ensure the interrupt is forwarded to the CPU. */
    alt_int_dist_enable( ALT_INT_INTERRUPT_PPI_TIMER_PRIVATE );

    /* Finally, enable the interrupt. */
	alt_gpt_int_clear_pending( ALT_GPT_CPU_PRIVATE_TMR );
	alt_gpt_int_enable( ALT_GPT_CPU_PRIVATE_TMR );

}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues, software
	timers, and semaphores.  The size of the FreeRTOS heap is set by the
	configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
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

void vApplicationIdleHook( void )
{
volatile size_t xFreeHeapSpace;

	/* This is just a trivial example of an idle hook.  It is called on each
	cycle of the idle task.  It must *NOT* attempt to block.  In this case the
	idle task just queries the amount of FreeRTOS heap that remains.  See the
	memory management section on the http://www.FreeRTOS.org web site for memory
	management options.  If there is a lot of heap memory free then the
	configTOTAL_HEAP_SIZE value in FreeRTOSConfig.h can be reduced to free up
	RAM. */
	xFreeHeapSpace = xPortGetFreeHeapSize();

	/* Remove compiler warning about xFreeHeapSpace being set but never used. */
	( void ) xFreeHeapSpace;
}
/*-----------------------------------------------------------*/

void vAssertCalled( const char * pcFile, unsigned long ulLine )
{
volatile unsigned long ul = 0;

	( void ) pcFile;
	( void ) ulLine;

	taskENTER_CRITICAL();
	{
		/* Set ul to a non-zero value using the debugger to step out of this
		function. */
		while( ul == 0 )
		{
			portNOP();
		}
	}
	taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	#if( mainSELECTED_APPLICATION == 1 )
	{
		/* The full demo includes a software timer demo/test that requires
		prodding periodically from the tick interrupt. */
		vTimerPeriodicISRTests();

		/* Call the periodic queue overwrite from ISR demo. */
		vQueueOverwritePeriodicISRDemo();

		/* Call the periodic event group from ISR demo. */
		vPeriodicEventGroupsProcessing();
	}
	#endif
}
/*-----------------------------------------------------------*/


#warning A separate array of handlers is maintained as the drivers array is static so cannot be reached and the handler is incompatible.
static INT_DISPATCH_t xISRHandlers[ ALT_INT_PROVISION_INT_COUNT ];

void vRegisterIRQHandler( uint32_t ulID, alt_int_callback_t pxHandlerFunction, void *pvContext )
{
	if( ulID < ALT_INT_PROVISION_INT_COUNT )
	{
		xISRHandlers[ ulID ].pxISR = pxHandlerFunction;
		xISRHandlers[ ulID ].pvContext = pvContext;
	}
}
/*-----------------------------------------------------------*/

void vApplicationIRQHandler( uint32_t ulICCIAR )
{
uint32_t ulInterruptID;
void *pvContext;
alt_int_callback_t pxISR;

	/* Re-enable interrupts. */
    __asm ( "cpsie i" );

	/* The ID of the interrupt is obtained by bitwise anding the ICCIAR value
	with 0x3FF. */
	ulInterruptID = ulICCIAR & 0x3FFUL;

	if( ulInterruptID < ALT_INT_PROVISION_INT_COUNT )
	{
		/* Call the function installed in the array of installed handler
		functions. */
		pxISR = xISRHandlers[ ulInterruptID ].pxISR;
		pvContext = xISRHandlers[ ulInterruptID ].pvContext;
		pxISR( ulICCIAR, pvContext );
	}
}

