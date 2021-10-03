/*
 * FreeRTOS V202107.00
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

/* Standard includes. */
#include "limits.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* SiLabs library includes. */
#include "em_cmu.h"
#include "em_burtc.h"
#include "em_rmu.h"
#include "em_int.h"
#include "sleep.h"

/* SEE THE COMMENTS ABOVE THE DEFINITION OF configCREATE_LOW_POWER_DEMO IN
FreeRTOSConfig.h
This file contains functions that will override the default implementations
in the RTOS port layer.  Therefore only build this file if the low power demo
is being built. */
#if( configCREATE_LOW_POWER_DEMO == 1 )

#define mainTIMER_FREQUENCY_HZ	( 2000UL )

/*
 * The low power demo does not use the SysTick, so override the
 * vPortSetupTickInterrupt() function with an implementation that configures
 * a low power clock source.  NOTE:  This function name must not be changed as
 * it is called from the RTOS portable layer.
 */
void vPortSetupTimerInterrupt( void );

/*
 * Override the default definition of vPortSuppressTicksAndSleep() that is
 * weakly defined in the FreeRTOS Cortex-M port layer with a version that
 * manages the BURTC clock, as the tick is generated from the low power BURTC
 * and not the SysTick as would normally be the case on a Cortex-M.
 */
void vPortSuppressTicksAndSleep( TickType_t xExpectedIdleTime );

/*-----------------------------------------------------------*/

/* Calculate how many clock increments make up a single tick period. */
static const uint32_t ulReloadValueForOneTick = ( mainTIMER_FREQUENCY_HZ / configTICK_RATE_HZ );

/* Will hold the maximum number of ticks that can be suppressed. */
static uint32_t xMaximumPossibleSuppressedTicks = 0;

/* Flag set from the tick interrupt to allow the sleep processing to know if
sleep mode was exited because of a timer interrupt or a different interrupt. */
static volatile uint32_t ulTickFlag = pdFALSE;

/* As the clock is only 2KHz, it is likely a value of 1 will be too much, so
use zero - but leave the value here to assist porting to different clock
speeds. */
static const uint32_t ulStoppedTimerCompensation = 0UL;

/*-----------------------------------------------------------*/

void vPortSetupTimerInterrupt( void )
{
BURTC_Init_TypeDef xBURTCInitStruct = BURTC_INIT_DEFAULT;

	/* Configure the BURTC to generate the RTOS tick interrupt. */

	xMaximumPossibleSuppressedTicks = ULONG_MAX / ulReloadValueForOneTick;

	/* Ensure LE modules are accessible. */
	CMU_ClockEnable( cmuClock_CORELE, true );

	/* Enable access to BURTC registers. */
	RMU_ResetControl( rmuResetBU, false );

	/* Generate the tick interrupt from BURTC. */
	xBURTCInitStruct.mode   = burtcModeEM3;		/* Operational in EM3. */
	xBURTCInitStruct.clkSel = burtcClkSelULFRCO;/* ULFRCO clock. */
	xBURTCInitStruct.clkDiv = burtcClkDiv_1;	/* 2kHz ULFRCO clock. */
	xBURTCInitStruct.compare0Top = true;		/* Wrap on COMP0. */
	BURTC_IntDisable( BURTC_IF_COMP0 );
	BURTC_Init( &xBURTCInitStruct );

	/* The tick interrupt must be set to the lowest priority possible. */
	NVIC_SetPriority( BURTC_IRQn, configLIBRARY_LOWEST_INTERRUPT_PRIORITY );
	NVIC_ClearPendingIRQ( BURTC_IRQn );
	NVIC_EnableIRQ( BURTC_IRQn );
	BURTC_CompareSet( 0, ulReloadValueForOneTick );
	BURTC_IntClear( BURTC_IF_COMP0 );
	BURTC_IntEnable( BURTC_IF_COMP0 );
	BURTC_CounterReset();
}
/*-----------------------------------------------------------*/

void vPortSuppressTicksAndSleep( TickType_t xExpectedIdleTime )
{
uint32_t ulReloadValue, ulCompleteTickPeriods, ulCountBeforeSleep, ulCountAfterSleep;
eSleepModeStatus eSleepAction;
TickType_t xModifiableIdleTime;

	/* THIS FUNCTION IS CALLED WITH THE SCHEDULER SUSPENDED. */

	/* Make sure the BURTC reload value does not overflow the counter. */
	if( xExpectedIdleTime > xMaximumPossibleSuppressedTicks )
	{
		xExpectedIdleTime = xMaximumPossibleSuppressedTicks;
	}

	/* Calculate the reload value required to wait xExpectedIdleTime tick
	periods. */
	ulReloadValue = ulReloadValueForOneTick * xExpectedIdleTime;
	if( ulReloadValue > ulStoppedTimerCompensation )
	{
		/* Compensate for the fact that the BURTC is going to be stopped
		momentarily. */
		ulReloadValue -= ulStoppedTimerCompensation;
	}

	/* Stop the BURTC momentarily.  The time the BURTC is stopped for is
	accounted for as best it can be, but using the tickless mode will inevitably
	result in some tiny drift of the time maintained by the kernel with respect
	to calendar time.  The count is latched before stopping the timer as
	stopping the timer appears to clear the count. */
	ulCountBeforeSleep = BURTC_CounterGet();
	BURTC_Enable( false );

	/* If this function is re-entered before one complete tick period then the
	reload value might be set to take into account a partial time slice, but
	just reading the count assumes it is counting up to a full ticks worth - so
	add in the difference if any. */
	ulCountBeforeSleep += ( ulReloadValueForOneTick - BURTC_CompareGet( 0 ) );

	/* Enter a critical section but don't use the taskENTER_CRITICAL() method as
	that will mask interrupts that should exit sleep mode. */
	INT_Disable();
	__asm volatile( "dsb" );
	__asm volatile( "isb" );

	/* The tick flag is set to false before sleeping.  If it is true when sleep
	mode is exited then sleep mode was probably exited because the tick was
	suppressed for the entire xExpectedIdleTime period. */
	ulTickFlag = pdFALSE;

	/* If a context switch is pending then abandon the low power entry as the
	context switch might have been pended by an external interrupt that	requires
	processing. */
	eSleepAction = eTaskConfirmSleepModeStatus();
	if( eSleepAction == eAbortSleep )
	{
		/* Restart tick and count up to whatever was left of the current time
		slice. */
		BURTC_CompareSet( 0, ( ulReloadValueForOneTick - ulCountBeforeSleep ) + ulStoppedTimerCompensation );
		BURTC_Enable( true );

		/* Re-enable interrupts - see comments above the INT_Enable() call
		above. */
		INT_Enable();
	}
	else
	{
		/* Adjust the reload value to take into account that the current time
		slice is already partially complete. */
		ulReloadValue -= ulCountBeforeSleep;
		BURTC_CompareSet( 0, ulReloadValue );

		/* Restart the BURTC. */
		BURTC_Enable( true );

		/* Allow the application to define some pre-sleep processing. */
		xModifiableIdleTime = xExpectedIdleTime;
		configPRE_SLEEP_PROCESSING( xModifiableIdleTime );

		/* xExpectedIdleTime being set to 0 by configPRE_SLEEP_PROCESSING()
		means the application defined code has already executed the WAIT
		instruction. */
		if( xModifiableIdleTime > 0 )
		{
			__asm volatile( "dsb" );
			SLEEP_Sleep();
			__asm volatile( "isb" );
		}

		/* Allow the application to define some post sleep processing. */
		configPOST_SLEEP_PROCESSING( xModifiableIdleTime );

		/* Stop BURTC.  Again, the time the SysTick is stopped for is accounted
		for as best it can be, but using the tickless mode will	inevitably
		result in some tiny drift of the time maintained by the	kernel with
		respect to calendar time.  The count value is latched before stopping
		the timer as stopping the timer appears to clear the count. */
		ulCountAfterSleep = BURTC_CounterGet();
		BURTC_Enable( false );

		/* Re-enable interrupts - see comments above the INT_Enable() call
		above. */
		INT_Enable();
		__asm volatile( "dsb" );
		__asm volatile( "isb" );

		if( ulTickFlag != pdFALSE )
		{
			/* The tick interrupt has already executed, although because this
			function is called with the scheduler suspended the actual tick
			processing will not occur until after this function has exited.
			Reset the reload value with whatever remains of this tick period. */
			ulReloadValue = ulReloadValueForOneTick - ulCountAfterSleep;
			BURTC_CompareSet( 0, ulReloadValue );

			/* The tick interrupt handler will already have pended the tick
			processing in the kernel.  As the pending tick will be processed as
			soon as this function exits, the tick value	maintained by the tick
			is stepped forward by one less than the	time spent sleeping.  The
			actual stepping of the tick appears later in this function. */
			ulCompleteTickPeriods = xExpectedIdleTime - 1UL;
		}
		else
		{
			/* Something other than the tick interrupt ended the sleep.  How
			many complete tick periods passed while the processor was
			sleeping?  Add back in the adjustment that was made to the reload
			value to account for the fact that a time slice was part way through
			when this function was called. */
			ulCountAfterSleep += ulCountBeforeSleep;
			ulCompleteTickPeriods = ulCountAfterSleep / ulReloadValueForOneTick;

			/* The reload value is set to whatever fraction of a single tick
			period remains. */
			ulCountAfterSleep -= ( ulCompleteTickPeriods * ulReloadValueForOneTick );
			ulReloadValue = ulReloadValueForOneTick - ulCountAfterSleep;

			if( ulReloadValue == 0 )
			{
				/* There is no fraction remaining. */
				ulReloadValue = ulReloadValueForOneTick;
				ulCompleteTickPeriods++;
			}

			BURTC_CompareSet( 0, ulReloadValue );
		}

		/* Restart the BURTC so it runs up to the alarm value.  The alarm value
		will get set to the value required to generate exactly one tick period
		the next time the BURTC interrupt executes. */
		BURTC_Enable( true );

		/* Wind the tick forward by the number of tick periods that the CPU
		remained in a low power state. */
		vTaskStepTick( ulCompleteTickPeriods );
	}
}
/*-----------------------------------------------------------*/

void BURTC_IRQHandler( void )
{
	ulTickFlag = pdTRUE;

	if( BURTC_CompareGet( 0 ) != ulReloadValueForOneTick )
	{
		/* Set BURTC interrupt to one RTOS tick period. */
		BURTC_Enable( false );
		BURTC_CompareSet( 0, ulReloadValueForOneTick );
		BURTC_Enable( true );
	}

	BURTC_IntClear( _BURTC_IFC_MASK );

	/* Critical section which protect incrementing the tick. */
	portDISABLE_INTERRUPTS();
	{
		if( xTaskIncrementTick() != pdFALSE )
		{
			/* Pend a context switch. */
			portNVIC_INT_CTRL_REG = portNVIC_PENDSVSET_BIT;
		}
	}
	portENABLE_INTERRUPTS();
}

#endif /* ( configCREATE_LOW_POWER_DEMO == 1 ) */

