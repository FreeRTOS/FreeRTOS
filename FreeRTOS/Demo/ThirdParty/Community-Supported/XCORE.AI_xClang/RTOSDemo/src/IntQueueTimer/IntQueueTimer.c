// Copyright (c) 2020, XMOS Ltd, All rights reserved

#include "FreeRTOS.h"
#include "task.h"

#include <xcore/hwtimer.h>
#include <xcore/triggerable.h>

#include "IntQueue.h"

DEFINE_RTOS_INTERRUPT_CALLBACK( pxIntQueueTimerISR, pvData )
{
	static int xCount0, xCount1;
	hwtimer_t xTimer = ( hwtimer_t ) pvData;
	uint32_t ulNow;
	int xYieldRequired;

	ulNow = hwtimer_get_time( xTimer );
    ulNow = hwtimer_get_trigger_time( xTimer );
	ulNow += configCPU_CLOCK_HZ / 50;

	if( ++xCount0 == 2 )
	{
		xCount0 = 0;
		taskENTER_CRITICAL_FROM_ISR();
		if( xFirstTimerHandler() != pdFALSE )
		{
			xYieldRequired = pdTRUE;
		}
		taskEXIT_CRITICAL_FROM_ISR( 0 );
	}

	if( ++xCount1 == 3 )
	{
		xCount1 = 0;
		taskENTER_CRITICAL_FROM_ISR();
		if( xSecondTimerHandler() != pdFALSE )
		{
			xYieldRequired = pdTRUE;
		}
		taskEXIT_CRITICAL_FROM_ISR( 0 );
	}

	hwtimer_change_trigger_time( xTimer, ulNow );

	portYIELD_FROM_ISR( xYieldRequired );
}

void vInitialiseTimerForIntQueueTest( void )
{
uint32_t ulNow;
uint32_t ulState;
hwtimer_t xIntQueueTimer;

	/*
	 * Disable interrupts here so we stay on the same core
	 */
	ulState = portDISABLE_INTERRUPTS();
	{
		xIntQueueTimer = hwtimer_alloc();
		ulNow = hwtimer_get_time( xIntQueueTimer );
		ulNow += configCPU_CLOCK_HZ / 50;
	    triggerable_setup_interrupt_callback( xIntQueueTimer, ( void * ) xIntQueueTimer, RTOS_INTERRUPT_CALLBACK( pxIntQueueTimerISR ) );
	    hwtimer_set_trigger_time( xIntQueueTimer, ulNow );
	    triggerable_enable_trigger( xIntQueueTimer );
	}
	portRESTORE_INTERRUPTS( ulState );
}

