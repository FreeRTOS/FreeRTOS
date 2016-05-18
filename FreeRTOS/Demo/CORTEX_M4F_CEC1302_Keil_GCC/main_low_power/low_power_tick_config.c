/*
    FreeRTOS V9.0.0rc2 - Copyright (C) 2015 Real Time Engineers Ltd.
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

/* Standard includes. */
#include <limits.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Library includes. */
#include "common_lib.h"
#include "peripheral_library/interrupt/interrupt.h"
#include "peripheral_library/basic_timer/btimer.h"

/* This file contains functions that will override the default implementations
in the RTOS port layer.  Therefore only build this file if the low power demo
is being built. */
#if( configCREATE_LOW_POWER_DEMO == 1 )

/* ID of the hibernation timer used to generate the tick. */
#define mainTICK_HTIMER_ID	0

/* Written to the hibernation timer control register to configure the timer for
its higher resolution. */
#define mainHTIMER_HIGH_RESOLUTION	0

/* The frequency of the hibernation timer when it is running at its higher
resolution and low resolution respectively. */
#define mainHIGHER_RESOLUTION_TIMER_HZ	( 32787UL ) /* (1000000us / 30.5us) as each LSB is 30.5us. */
#define mainLOW_RESOLUTION_TIMER_HZ		( 8UL )	 /* ( 1000ms / 125ms ) as each LSB is 0.125s. */

/* When lpINCLUDE_TEST_TIMER is set to 1 a basic timer is used to generate
interrupts at a low frequency.  The purpose being to bring the CPU out of its
sleep mode by an interrupt other than the tick interrupt, and therefore
allowing an additional paths through the code to be tested. */
#define lpINCLUDE_TEST_TIMER			0

/* Registers and bits required to use the htimer in aggregated mode. */
#define lpHTIMER_PRELOAD_REGISTER		( * ( volatile uint16_t * ) 0x40009800 )
#define lpHTIMER_CONTROL_REGISTER		( * ( volatile uint16_t * ) 0x40009804 )
#define lpHTIMER_COUNT_REGISTER			( * ( volatile uint16_t * ) 0x40009808 )
#define lpEC_GIRQ17_ENABLE_SET			( * ( volatile uint32_t * ) 0x4000C0B8 )
#define lpEC_GIRQ17_SOURCE 				( * ( volatile uint32_t * ) 0x4000C0B4 )
#define lpEC_GIRQ17_ENABLE_CLEAR 		( * ( volatile uint32_t * ) 0x4000C0C0 )
#define lpBLOCK_ENABLE_SET 				( * ( volatile uint32_t * ) 0x4000c200 )
#define lpGIRQ17_BIT_HTIMER				( 1UL << 20UL )
#define lpHTIMER_GIRQ_BLOCK				( 1Ul << 17UL )

/* Registers and bits required to use btimer 0 in aggregated mode. */
#define lpGIRQ23_ENABLE_SET				( * ( volatile uint32_t * ) 0x4000C130 )
#define lpEC_GIRQ23_SOURCE 				( * ( volatile uint32_t * ) 0x4000C12C )
#define lpEC_GIRQ23_ENABLE_CLEAR 		( * ( volatile uint32_t * ) 0x4000C138 )
#define lpGIRQ23_BIT_TIMER0				( 1UL << 0UL )
#define lpBTIMER_GIRQ_BLOCK				( 1UL << 23UL )

/*
 * The low power demo does not use the SysTick, so override the
 * vPortSetupTickInterrupt() function with an implementation that configures
 * the low power clock.  NOTE:  This function name must not be changed as it
 * is called from the RTOS portable layer.
 */
void vPortSetupTimerInterrupt( void );

/*
 * To fully test the low power tick processing it is necessary to sometimes
 * bring the MCU out of its sleep state by a method other than the tick
 * interrupt.  Interrupts generated from a basic timer are used for this
 * purpose.
 */
#if( lpINCLUDE_TEST_TIMER == 1 )
	static void prvSetupBasicTimer( void );
#endif

/*-----------------------------------------------------------*/

/* The reload value to use in the timer to generate the tick interrupt -
assumes the timer is running at its higher resolution. */
static const uint32_t ulHighResolutionReloadValue = ( mainHIGHER_RESOLUTION_TIMER_HZ / configTICK_RATE_HZ );

/* Calculate how many clock increments make up a single tick period. */
static const uint32_t ulReloadValueForOneHighResolutionTick = ( mainHIGHER_RESOLUTION_TIMER_HZ / configTICK_RATE_HZ );

/* Calculate the maximum number of ticks that can be suppressed when using the
high resolution clock and low resolution clock respectively. */
static uint32_t ulMaximumPossibleSuppressedHighResolutionTicks = 0;

/* As the clock is only 2KHz, it is likely a value of 1 will be too much, so
use zero - but leave the value here to assist porting to different clock
speeds. */
static const uint32_t ulStoppedTimerCompensation = 0UL;

/* Flag set from the tick interrupt to allow the sleep processing to know if
sleep mode was exited because of an timer interrupt or a different interrupt. */
static volatile uint32_t ulTickFlag = pdFALSE;

/*-----------------------------------------------------------*/

void NVIC_Handler_GIRQ17( void )
{
	/* The low power demo is using aggregated interrupts, so although in the
	demo the htimer is the only peripheral that will generate interrupts on
	this vector, in a real application it would be necessary to first check the
	interrupt source. */
	if( ( lpEC_GIRQ17_SOURCE & lpGIRQ17_BIT_HTIMER ) != 0 )
	{
		/* The htimer interrupted.  Clear the interrupt. */
		lpEC_GIRQ17_SOURCE = lpGIRQ17_BIT_HTIMER;
		lpHTIMER_PRELOAD_REGISTER = ( uint16_t ) ulHighResolutionReloadValue;

		/* Increment the RTOS tick. */
		if( xTaskIncrementTick() != pdFALSE )
		{
			/* A context switch is required.  Context switching is performed in
			the PendSV interrupt.  Pend the PendSV interrupt. */
			portNVIC_INT_CTRL_REG = portNVIC_PENDSVSET_BIT;
		}

		/* The CPU woke because of a tick. */
		ulTickFlag = pdTRUE;
	}
	else
	{
		/* Don't expect any other interrupts to use this vector in this
		demo.  Force an assert. */
		configASSERT( lpEC_GIRQ17_SOURCE == 0 );
	}
}
/*-----------------------------------------------------------*/

#if( lpINCLUDE_TEST_TIMER == 1 )

	static void prvSetupBasicTimer( void )
	{
	const uint8_t ucTimerChannel = 0;
	const uint32_t ulTimer0Count = configCPU_CLOCK_HZ / 10;

		/* Enable btimer 0 interrupt in the aggregated GIRQ23 block. */
		lpEC_GIRQ23_SOURCE = lpGIRQ23_BIT_TIMER0;
		lpEC_GIRQ23_ENABLE_CLEAR = lpGIRQ23_BIT_TIMER0;
		lpBLOCK_ENABLE_SET = lpBTIMER_GIRQ_BLOCK;
		lpGIRQ23_ENABLE_SET = lpGIRQ23_BIT_TIMER0;

		/* To fully test the low power tick processing it is necessary to sometimes
		bring the MCU out of its sleep state by a method other than the tick
		interrupt.  Interrupts generated from a basic timer are used for this
		purpose. */
		btimer_init( ucTimerChannel, BTIMER_AUTO_RESTART | BTIMER_COUNT_DOWN | BTIMER_INT_EN, 0, ulTimer0Count, ulTimer0Count );
		btimer_interrupt_status_get_clr( ucTimerChannel );
		NVIC_SetPriority( GIRQ23_IRQn, ucTimerChannel );
		NVIC_ClearPendingIRQ( GIRQ23_IRQn );
		NVIC_EnableIRQ( GIRQ23_IRQn );
		btimer_start( ucTimerChannel );
	}

#endif /* lpINCLUDE_TEST_TIMER */
/*-----------------------------------------------------------*/

void vPortSetupTimerInterrupt( void )
{
ulMaximumPossibleSuppressedHighResolutionTicks = ( ( uint32_t ) USHRT_MAX ) / ulReloadValueForOneHighResolutionTick;

	/* Set up the hibernation timer to start at the value required by the
	tick interrupt. */
	lpHTIMER_PRELOAD_REGISTER = ulHighResolutionReloadValue;
	lpHTIMER_CONTROL_REGISTER = mainHTIMER_HIGH_RESOLUTION;

	/* Enable the HTIMER interrupt in the aggregated GIR17 block. */
	lpEC_GIRQ17_SOURCE = lpGIRQ17_BIT_HTIMER;
	lpEC_GIRQ17_ENABLE_CLEAR = lpGIRQ17_BIT_HTIMER;
	lpBLOCK_ENABLE_SET = lpHTIMER_GIRQ_BLOCK;
	lpEC_GIRQ17_ENABLE_SET = lpGIRQ17_BIT_HTIMER;

	/* The hibernation timer is not an auto-reload timer, so gets reset
	from within the ISR itself.  For that reason it's interrupt is set
	to the highest possible priority to ensure clock slippage is minimised. */
	NVIC_SetPriority( GIRQ17_IRQn, configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY );
	NVIC_ClearPendingIRQ( GIRQ17_IRQn );
	NVIC_EnableIRQ( GIRQ17_IRQn );

	/* A basic timer is also started, purely for test purposes.  Its only
	purpose is to bring the CPU out of its sleep mode by an interrupt other
	than the tick interrupt in order to get more code test coverage. */
	#if( lpINCLUDE_TEST_TIMER == 1 )
	{
		prvSetupBasicTimer();
	}
	#endif
}
/*-----------------------------------------------------------*/

/* Override the default definition of vPortSuppressTicksAndSleep() that is
weakly defined in the FreeRTOS Cortex-M port layer with a version that manages
the hibernation timer, as the tick is generated from the low power hibernation
timer and not the SysTick as would normally be the case on a Cortex-M. */
void vPortSuppressTicksAndSleep( TickType_t xExpectedIdleTime )
{
uint32_t ulCompleteTickPeriods, ulReloadValue, ulCompletedTimerDecrements, ulCountAfterSleep, ulCountBeforeSleep;
eSleepModeStatus eSleepAction;
TickType_t xModifiableIdleTime;

	/* THIS FUNCTION IS CALLED WITH THE SCHEDULER SUSPENDED. */

	/* Make sure the hibernation timer reload value does not overflow the
	counter. */
	if( xExpectedIdleTime > ( TickType_t ) ulMaximumPossibleSuppressedHighResolutionTicks )
	{
		xExpectedIdleTime = ( TickType_t ) ulMaximumPossibleSuppressedHighResolutionTicks;
	}

	/* Stop the timer momentarily.  The time the timer is stopped for is
	accounted for as best it can be, but using the tickless mode will
	inevitably result in some tiny drift of the time maintained by the kernel
	with respect to calendar time.  Take the count value first as clearing
	the preload value also seems to clear the count. */
	ulCountBeforeSleep = ( uint32_t ) lpHTIMER_COUNT_REGISTER;
	lpHTIMER_PRELOAD_REGISTER = 0;

	/* Calculate the reload value required to wait xExpectedIdleTime tick
	periods.  -1 is used as the current time slice will already be part way
	through, the part value coming from the current timer count value. */
	ulReloadValue = ulCountBeforeSleep + ( ulReloadValueForOneHighResolutionTick * ( xExpectedIdleTime - 1UL ) );

	if( ulReloadValue > ulStoppedTimerCompensation )
	{
		/* Compensate for the fact that the timer is going to be stopped
		momentarily. */
		ulReloadValue -= ulStoppedTimerCompensation;
	}

	/* Enter a critical section but don't use the taskENTER_CRITICAL() method as
	that will mask interrupts that should exit sleep mode. */
	__asm volatile( "cpsid i" );
	__asm volatile( "dsb" );
	__asm volatile( "isb" );

	/* The tick flag is set to false before sleeping.  If it is true when sleep
	mode is exited then sleep mode was probably exited because the tick was
	suppressed for the entire xExpectedIdleTime period. */
	ulTickFlag = pdFALSE;

	/* If a context switch is pending then abandon the low power entry as
	the context switch might have been pended by an external interrupt that
	requires processing. */
	eSleepAction = eTaskConfirmSleepModeStatus();
	if( eSleepAction == eAbortSleep )
	{
		/* Restart the timer from whatever remains in the counter register,
		but 0 is not a valid value. */
		ulReloadValue = ulCountBeforeSleep - ulStoppedTimerCompensation;

		if( ulReloadValue == 0 )
		{
			ulReloadValue = ulReloadValueForOneHighResolutionTick;
			ulCompleteTickPeriods = 1UL;
		}
		else
		{
			ulCompleteTickPeriods = 0UL;
		}

		lpHTIMER_PRELOAD_REGISTER = ( uint16_t ) ulReloadValue;

		/* Re-enable interrupts - see comments above the cpsid instruction()
		above. */
		__asm volatile( "cpsie i" );
		__asm volatile( "dsb" );
		__asm volatile( "isb" );
	}
	else
	{
		/* Write the calculated reload value, which will also start the
		timer. */
		lpHTIMER_PRELOAD_REGISTER = ( uint16_t ) ulReloadValue;

		/* Allow the application to define some pre-sleep processing. */
		xModifiableIdleTime = xExpectedIdleTime;
		configPRE_SLEEP_PROCESSING( xModifiableIdleTime );

		/* xExpectedIdleTime being set to 0 by configPRE_SLEEP_PROCESSING()
		means the application defined code has already executed the sleep
		instructions. */
		if( xModifiableIdleTime > 0 )
		{
			__asm volatile( "dsb" );
			__asm volatile( "wfi" );
			__asm volatile( "isb" );
		}

		/* Allow the application to define some post sleep processing. */
		configPOST_SLEEP_PROCESSING( xModifiableIdleTime );

		/* Stop the hibernation timer.  Again, the time the timer is stopped
		for is accounted for as best it can be, but using the tickless mode
		will inevitably result in some tiny drift of the time maintained by the
		kernel with respect to calendar time.  Take the count value first as
		setting the preload to zero also seems to clear the count. */
		ulCountAfterSleep = lpHTIMER_COUNT_REGISTER;
		lpHTIMER_PRELOAD_REGISTER = 0;

		/* Re-enable interrupts - see comments above the cpsid instruction()
		above. */
		__asm volatile( "cpsie i" );
		__asm volatile( "dsb" );
		__asm volatile( "isb" );

		if( ulTickFlag != pdFALSE )
		{
			/* The tick interrupt has already executed, although because this
			function is called with the scheduler suspended the actual tick
			processing will not occur until after this function has exited.
			The timer has already been reloaded to count in ticks, and can just
			continue counting down from its current value. */
			ulReloadValue = ulCountAfterSleep;

			/* Sanity check that the timer's reload value has indeed been
			reset. */
			configASSERT( ( uint32_t ) lpHTIMER_PRELOAD_REGISTER == ulReloadValueForOneHighResolutionTick );

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
			sleeping? */
			ulCompletedTimerDecrements = ulReloadValue - ulCountAfterSleep;

			/* Undo the adjustment that was made to the reload value to account
			for the fact that a time slice was part way through when this
			function was called before working out how many complete tick
			periods this represents.  (could have used [ulExpectedIdleTime *
			ulReloadValueForOneHighResolutionTick] instead of ulReloadValue on
			the previous line, but this way avoids the multiplication). */
			ulCompletedTimerDecrements += ( ulReloadValueForOneHighResolutionTick - ulCountBeforeSleep );
			ulCompleteTickPeriods = ulCompletedTimerDecrements / ulReloadValueForOneHighResolutionTick;

			/* The reload value is set to whatever fraction of a single tick
			period remains. */
			ulReloadValue = ( ( ulCompleteTickPeriods + 1UL ) * ulReloadValueForOneHighResolutionTick ) - ulCompletedTimerDecrements;
		}

		/* Cannot use a reload value of 0 - it will not start the timer. */
		if( ulReloadValue == 0 )
		{
			/* There is no fraction remaining. */
			ulReloadValue = ulReloadValueForOneHighResolutionTick;
			ulCompleteTickPeriods++;
		}

		/* Restart the timer so it runs down from the reload value.  The reload
		value will get set to the value required to generate exactly one tick
		period the next time the tick interrupt executes. */
		lpHTIMER_PRELOAD_REGISTER = ( uint16_t ) ulReloadValue;
	}

	/* Wind the tick forward by the number of tick periods that the CPU
	remained in a low power state. */
	vTaskStepTick( ulCompleteTickPeriods );
}
/*-----------------------------------------------------------*/

void NVIC_Handler_GIRQ23( void )
{
static volatile uint32_t ulTimerCounts = 0;

	/* The low power demo is using aggregated interrupts, so although in the
	demo btimer 0 is the only peripheral that will generate interrupts on
	this vector, in a real application it would be necessary to first check the
	interrupt source. */
	if( ( lpEC_GIRQ23_SOURCE & lpGIRQ23_BIT_TIMER0 ) != 0 )
	{
		/* Btimer0 interrupted.  Clear the interrupt. */
		lpEC_GIRQ23_SOURCE = lpGIRQ23_BIT_TIMER0;

		/* This timer is used for test purposes.  Its only function is to
		generate interrupts while the MCU is sleeping, so the MCU is sometimes
		brought out of sleep by a means other than the tick interrupt. */
		ulTimerCounts++;
	}
	else
	{
		/* Don't expect any other interrupts to use this vector in this
		demo.  Force an assert. */
		configASSERT( lpEC_GIRQ23_SOURCE == 0 );
	}
}
/*-----------------------------------------------------------*/

#endif /* configCREATE_LOW_POWER_DEMO == 1 */
