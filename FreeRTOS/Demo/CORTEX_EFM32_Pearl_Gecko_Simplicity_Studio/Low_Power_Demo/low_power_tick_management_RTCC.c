/*
    FreeRTOS V9.0.0rc1 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/* Standard inlcludes. */
#include <limits.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* SiLabs library includes. */
#include "em_cmu.h"
#include "em_rtcc.h"
#include "em_rmu.h"
#include "em_int.h"
#include "sleep.h"

/* SEE THE COMMENTS ABOVE THE DEFINITION OF configCREATE_LOW_POWER_DEMO IN
FreeRTOSConfig.h
This file contains functions that will override the default implementations
in the RTOS port layer.  Therefore only build this file if the low power demo
is being built. */
#if( configCREATE_LOW_POWER_DEMO == 1 )

/* The RTCC channel used to generate the tick interrupt. */
#define lpRTCC_CHANNEL		( 1 )

/* 32768 clock divided by 1.  Don't use a prescale if errata RTCC_E201
applies. */
#define mainTIMER_FREQUENCY_HZ	( 32768UL )

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
 * manages the RTC clock, as the tick is generated from the low power RTC
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

/* As the clock is only 32KHz, it is likely a value of 1 will be enough. */
static const uint32_t ulStoppedTimerCompensation = 0UL;

/* RTCC configuration structures. */
static const RTCC_Init_TypeDef xRTCInitStruct =
{
	false,                /* Don't start counting when init complete. */
	false,                /* Disable counter during debug halt. */
	false,                /* Don't care. */
	true,                 /* Enable counter wrap on ch. 1 CCV value. */
	rtccCntPresc_1,       /* NOTE:  Do not use a pre-scale if errata RTCC_E201 applies. */
	rtccCntTickPresc,     /* Count using the clock input directly. */
#if defined(_RTCC_CTRL_BUMODETSEN_MASK)
	false,                /* Disable storing RTCC counter value in RTCC_CCV2 upon backup mode entry. */
#endif
	false,                /* Oscillator fail detection disabled. */
	rtccCntModeNormal,    /* Use RTCC in normal mode (increment by 1 on each tick) and not in calendar mode. */
	false                 /* Don't care. */
};

static const RTCC_CCChConf_TypeDef xRTCCChannel1InitStruct =
{
	rtccCapComChModeCompare,    /* Use Compare mode. */
	rtccCompMatchOutActionPulse,/* Don't care. */
	rtccPRSCh0,                 /* PRS not used. */
	rtccInEdgeNone,             /* Capture Input not used. */
	rtccCompBaseCnt,            /* Compare with Base CNT register. */
	0,                          /* Compare mask. */
	rtccDayCompareModeMonth     /* Don't care. */
};

/*-----------------------------------------------------------*/

void vPortSetupTimerInterrupt( void )
{
	/* Configure the RTCC to generate the RTOS tick interrupt. */

	/* The maximum number of ticks that can be suppressed depends on the clock
	frequency. */
	xMaximumPossibleSuppressedTicks = ULONG_MAX / ulReloadValueForOneTick;

	/* Ensure LE modules are accessible. */
	CMU_ClockEnable( cmuClock_CORELE, true );

	/* Use LFXO. */
	CMU_ClockSelectSet( cmuClock_LFE, cmuSelect_LFXO );

	/* Enable clock to the RTC module. */
	CMU_ClockEnable( cmuClock_RTCC, true );

	/* Use channel 1 to generate the RTOS tick interrupt. */
	RTCC_ChannelCCVSet( lpRTCC_CHANNEL, ulReloadValueForOneTick );

	RTCC_Init( &xRTCInitStruct );
	RTCC_ChannelInit( lpRTCC_CHANNEL, &xRTCCChannel1InitStruct );
	RTCC_EM4WakeupEnable( true );

	/* Disable RTCC interrupt. */
	RTCC_IntDisable( _RTCC_IF_MASK );
	RTCC_IntClear( _RTCC_IF_MASK );
	RTCC->CNT = _RTCC_CNT_RESETVALUE;

	/* The tick interrupt must be set to the lowest priority possible. */
	NVIC_SetPriority( RTCC_IRQn, configLIBRARY_LOWEST_INTERRUPT_PRIORITY );
	NVIC_ClearPendingIRQ( RTCC_IRQn );
	NVIC_EnableIRQ( RTCC_IRQn );
	RTCC_IntEnable( RTCC_IEN_CC1 );
	RTCC_Enable( true );
}
/*-----------------------------------------------------------*/

void vPortSuppressTicksAndSleep( TickType_t xExpectedIdleTime )
{
uint32_t ulReloadValue, ulCompleteTickPeriods, ulCountBeforeSleep, ulCountAfterSleep;
eSleepModeStatus eSleepAction;
TickType_t xModifiableIdleTime;

	/* THIS FUNCTION IS CALLED WITH THE SCHEDULER SUSPENDED. */

	/* Make sure the RTC reload value does not overflow the counter. */
	if( xExpectedIdleTime > xMaximumPossibleSuppressedTicks )
	{
		xExpectedIdleTime = xMaximumPossibleSuppressedTicks;
	}

	/* Calculate the reload value required to wait xExpectedIdleTime tick
	periods. */
	ulReloadValue = ulReloadValueForOneTick * xExpectedIdleTime;
	if( ulReloadValue > ulStoppedTimerCompensation )
	{
		/* Compensate for the fact that the RTC is going to be stopped
		momentarily. */
		ulReloadValue -= ulStoppedTimerCompensation;
	}

	/* Stop the RTC momentarily.  The time the RTC is stopped for is accounted
	for as best it can be, but using the tickless mode will inevitably result
	in some tiny drift of the time maintained by the kernel with respect to
	calendar time.  The count is latched before stopping the timer as stopping
	the timer appears to clear the count. */
	ulCountBeforeSleep = RTCC_CounterGet();
	RTCC_Enable( false );

	/* If this function is re-entered before one complete tick period then the
	reload value might be set to take into account a partial time slice, but
	just reading the count assumes it is counting up to a full ticks worth - so
	add in the difference if any. */
	ulCountBeforeSleep += ( ulReloadValueForOneTick - RTCC_ChannelCCVGet( lpRTCC_CHANNEL ) );

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
		RTCC_ChannelCCVSet( lpRTCC_CHANNEL, ( ulReloadValueForOneTick - ulCountBeforeSleep ) + ulStoppedTimerCompensation );
		RTCC_Enable( true );

		/* Re-enable interrupts - see comments above the cpsid instruction()
		above. */
		INT_Enable();
	}
	else
	{
		/* Adjust the reload value to take into account that the current time
		slice is already partially complete. */
		ulReloadValue -= ulCountBeforeSleep;
		RTCC_ChannelCCVSet( lpRTCC_CHANNEL, ulReloadValue );

		/* Restart the RTC. */
		RTCC_Enable( true );

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

		/* Stop RTC.  Again, the time the SysTick is stopped for is accounted
		for as best it can be, but using the tickless mode will	inevitably
		result in some tiny drift of the time maintained by the	kernel with
		respect to calendar time.  The count value is latched before stopping
		the timer as stopping the timer appears to clear the count. */
		ulCountAfterSleep = RTCC_CounterGet();
		RTCC_Enable( false );

		/* Re-enable interrupts - see comments above the cpsid instruction()
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
			RTCC_ChannelCCVSet( lpRTCC_CHANNEL, ulReloadValue );

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

			RTCC_ChannelCCVSet( lpRTCC_CHANNEL, ulReloadValue );
		}

		/* Restart the RTC so it runs up to the alarm value.  The alarm value
		will get set to the value required to generate exactly one tick period
		the next time the RTC interrupt executes. */
		RTCC_Enable( true );

		/* Wind the tick forward by the number of tick periods that the CPU
		remained in a low power state. */
		vTaskStepTick( ulCompleteTickPeriods );
	}
}
/*-----------------------------------------------------------*/

void RTCC_IRQHandler( void )
{
	ulTickFlag = pdTRUE;

	if( RTCC_ChannelCCVGet( lpRTCC_CHANNEL ) != ulReloadValueForOneTick )
	{
		/* Set RTC interrupt to one RTOS tick period. */
		RTCC_Enable( false );
		RTCC_ChannelCCVSet( lpRTCC_CHANNEL, ulReloadValueForOneTick );
		RTCC_Enable( true );
	}

	RTCC_IntClear( _RTCC_IF_MASK );

	/* Critical section which protect incrementing the tick*/
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
/*-----------------------------------------------------------*/

#endif /* ( configCREATE_LOW_POWER_DEMO == 1 ) */
