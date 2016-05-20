/*
    FreeRTOS V9.0.0 - Copyright (C) 2015 Real Time Engineers Ltd.
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
#include "htimer.h"

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
#define mainHIGHER_RESOLUTION_TIMER_HZ	( 32787 ) /* (1000000us / 30.5us) as each LSB is 30.5us. */
#define mainLOW_RESOLUTION_TIMER_HZ		( 8UL )	 /* ( 1000ms / 125ms ) as each LSB is 0.125s. */

/* Some registers are accessed directly as the library is not compatible with
all the compilers used. */
#define lpHTIMER_PRELOAD_REGISTER		( * ( volatile uint16_t * ) 0x40009800 )
#define lpHTIMER_COUNT_REGISTER			( * ( volatile uint16_t * ) 0x40009808 )
#define lpEC_GIRQ17_ENABLE_SET			( * ( volatile uint32_t * ) 0x4000C0B8 )
#define lpHTIMER_INTERRUPT_CONTROL_BIT	( 1UL << 20UL )

/*
 * The low power demo does not use the SysTick, so override the
 * vPortSetupTickInterrupt() function with an implementation that configures
 * the low power clock.  NOTE:  This function name must not be changed as it
 * is called from the RTOS portable layer.
 */
void vPortSetupTimerInterrupt( void );

/*-----------------------------------------------------------*/

/* The reload value to use in the timer to generate the tick interrupt -
assumes the timer is running at its higher resolution. */
static const uint16_t usHighResolutionReloadValue = ( mainHIGHER_RESOLUTION_TIMER_HZ / ( uint16_t ) configTICK_RATE_HZ );

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

void NVIC_Handler_HIB_TMR( void ) iv IVT_INT_HTIMER ics ICS_AUTO
{
	lpHTIMER_PRELOAD_REGISTER = usHighResolutionReloadValue;

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
/*-----------------------------------------------------------*/

void vPortSetupTimerInterrupt( void )
{
	/* Cannot be a const when using the MikroC compiler. */
	ulMaximumPossibleSuppressedHighResolutionTicks = ( ( uint32_t ) USHRT_MAX ) / ulReloadValueForOneHighResolutionTick;

	/* Set up the hibernation timer to start at the value required by the
	tick interrupt. */
	htimer_enable( mainTICK_HTIMER_ID, usHighResolutionReloadValue, mainHTIMER_HIGH_RESOLUTION );

	/* Enable the HTIMER interrupt.  Equivalent to enable_htimer0_irq(); */
	lpEC_GIRQ17_ENABLE_SET |= lpHTIMER_INTERRUPT_CONTROL_BIT;

	/* The hibernation timer is not an auto-reload timer, so gets reset
	from within the ISR itself.  For that reason it's interrupt is set
	to the highest possible priority to ensure clock slippage is minimised. */
	NVIC_SetIntPriority( IVT_INT_HTIMER, configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY );
	NVIC_IntEnable( IVT_INT_HTIMER );
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
	__asm { cpsid i
			dsb
			isb };

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
		/* Resetart the timer from whatever remains in the counter register,
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
		__asm {	cpsie i
				dsb
				isb };

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
			__asm {	dsb
					wfi
					isb };
		}

		/* Allow the application to define some post sleep processing. */
		configPOST_SLEEP_PROCESSING( xModifiableIdleTime );

		/* Stop the hibernation timer.  Again, the time the tiemr is stopped
		for is accounted for as best it can be, but using the tickless mode
		will inevitably result in some tiny drift of the time maintained by the
		kernel with respect to calendar time.  Take the count value first as
		setting the preload to zero also seems to clear the count. */
		ulCountAfterSleep = ( uint32_t ) lpHTIMER_COUNT_REGISTER;
		lpHTIMER_PRELOAD_REGISTER = 0;

		/* Re-enable interrupts - see comments above the cpsid instruction()
		above. */
		__asm {	cpsie i
				dsb
				isb };


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


#endif /* configCREATE_LOW_POWER_DEMO */

