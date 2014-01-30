/*
    FreeRTOS V8.0.0:rc1 - Copyright (C) 2014 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo includes. */
#include "IntQueueTimer.h"
#include "IntQueue.h"

/* Xilinx includes. */
#include "xstatus.h"
#include "xil_io.h"
#include "xil_exception.h"
#include "xttcps.h"
#include "xscugic.h"

#define tmrTIMER_0_FREQUENCY	( 2000UL )
#define tmrTIMER_1_FREQUENCY	( 2001UL )

#define TTC_TICK_DEVICE_ID	XPAR_XTTCPS_0_DEVICE_ID
#define TTC_TICK_INTR_ID	XPAR_XTTCPS_0_INTR
#define INTC_DEVICE_ID		XPAR_SCUGIC_SINGLE_DEVICE_ID

/*
 * Constants to set the basic operating parameters.
 * PWM_DELTA_DUTY is critical to the running time of the test. Smaller values
 * make the test run longer.
 */
#define	TICK_TIMER_FREQ_HZ	100  /* Tick timer counter's output frequency */

#define TICKS_PER_CHANGE_PERIOD	TICK_TIMER_FREQ_HZ /* Tick signals per update */

#define TIMERS_USED	2

static void TickHandler(void *CallBackRef);

static volatile uint8_t UpdateFlag;	/* Flag to update the seconds counter */
static uint32_t TickCount;		/* Ticker interrupts between seconds change */
static XTtcPs TtcPsInst[ TIMERS_USED ];  /* Timer counter instance */

typedef struct {
	u32 OutputHz;	/* Output frequency */
	u16 Interval;	/* Interval value */
	u8 Prescaler;	/* Prescaler value */
	u16 Options;	/* Option settings */
} TmrCntrSetup;

static const TmrCntrSetup SettingsTable[ TIMERS_USED ] = {	{ tmrTIMER_0_FREQUENCY, 0, 0, XTTCPS_OPTION_INTERVAL_MODE | XTTCPS_OPTION_WAVE_DISABLE },
															{ tmrTIMER_1_FREQUENCY, 0, 0, XTTCPS_OPTION_INTERVAL_MODE | XTTCPS_OPTION_WAVE_DISABLE } };

BaseType_t DeviceIDs[ TIMERS_USED ] = { XPAR_XTTCPS_0_DEVICE_ID, XPAR_XTTCPS_1_DEVICE_ID };
BaseType_t InterruptIDs[ TIMERS_USED ] = { XPAR_XTTCPS_0_INTR, XPAR_XTTCPS_1_INTR };

void vInitialiseTimerForIntQueueTest( void )
{
int Status;
TmrCntrSetup *TimerSetup;
XTtcPs *TtcPsTick;
extern XScuGic xInterruptController;
BaseType_t xTimer;
XTtcPs *Timer;
XTtcPs_Config *Config;

	for( xTimer = 0; xTimer < TIMERS_USED; xTimer++ )
	{

		TimerSetup = &( SettingsTable[ xTimer ] );
		Timer = &TtcPsInst[ xTimer ];

		/*
		 * Look up the configuration based on the device identifier
		 */
		Config = XTtcPs_LookupConfig(DeviceIDs[ xTimer ]);
		configASSERT( Config );

		/*
		 * Initialize the device
		 */
		Status = XTtcPs_CfgInitialize(Timer, Config, Config->BaseAddress);
		configASSERT(Status == XST_SUCCESS);

		/*
		 * Stop the timer first
		 */
		XTtcPs_Stop( Timer );

		/*
		 * Set the options
		 */
		XTtcPs_SetOptions(Timer, TimerSetup->Options);

		/*
		 * Timer frequency is preset in the TimerSetup structure,
		 * however, the value is not reflected in its other fields, such as
		 * IntervalValue and PrescalerValue. The following call will map the
		 * frequency to the interval and prescaler values.
		 */
		XTtcPs_CalcIntervalFromFreq(Timer, TimerSetup->OutputHz,
			&(TimerSetup->Interval), &(TimerSetup->Prescaler));

		/*
		 * Set the interval and prescale
		 */
		XTtcPs_SetInterval(Timer, TimerSetup->Interval);
		XTtcPs_SetPrescaler(Timer, TimerSetup->Prescaler);


		/*
		 * Connect to the interrupt controller
		 */
		Status = XScuGic_Connect(&xInterruptController, InterruptIDs[ xTimer ], (Xil_InterruptHandler)TickHandler, (void *)Timer);
		configASSERT( Status == XST_SUCCESS);

		/*
		 * Enable the interrupt for the Timer counter
		 */
		XScuGic_Enable(&xInterruptController, InterruptIDs[ xTimer ]);

		/*
		 * Enable the interrupts for the tick timer/counter
		 * We only care about the interval timeout.
		 */
		XTtcPs_EnableInterrupts(Timer, XTTCPS_IXR_INTERVAL_MASK);

		/*
		 * Start the tick timer/counter
		 */
		XTtcPs_Start(Timer);
	}
}
/*-----------------------------------------------------------*/

void vT2InterruptHandler( void )
{
	portEND_SWITCHING_ISR( xFirstTimerHandler() );
}
/*-----------------------------------------------------------*/

void vT3InterruptHandler( void )
{
	portEND_SWITCHING_ISR( xSecondTimerHandler() );
}
/*-----------------------------------------------------------*/

volatile uint32_t ulTimer1Count = 0, ulTimer2Count = 0;

static void TickHandler(void *CallBackRef)
{
uint32_t StatusEvent;
XTtcPs *pxTtcPs = (XTtcPs *)CallBackRef;
	/*
	 * Read the interrupt status, then write it back to clear the interrupt.
	 */
	StatusEvent = XTtcPs_GetInterruptStatus(pxTtcPs);
	XTtcPs_ClearInterruptStatus(pxTtcPs, StatusEvent);

	if (0 != (XTTCPS_IXR_INTERVAL_MASK & StatusEvent)) {
		if( pxTtcPs->Config.DeviceId == DeviceIDs[ 0 ] )
		{
			ulTimer1Count++;
		}
		else
		{
			ulTimer2Count++;
		}
		TickCount++;
	}
}

#if 0
int SetupTimer(int DeviceID)
{
	int Status;
	XTtcPs_Config *Config;
	XTtcPs *Timer;
	TmrCntrSetup *TimerSetup;

	TimerSetup = &SettingsTable;

	Timer = &TtcPsInst;
	/*
	 * Stop the timer first
	 */
	XTtcPs_Stop( &TtcPsInst );

	/*
	 * Look up the configuration based on the device identifier
	 */
	Config = XTtcPs_LookupConfig(DeviceIDs[ DeviceID ]);
	configASSERT( Config );

	/*
	 * Initialize the device
	 */
	Status = XTtcPs_CfgInitialize(Timer, Config, Config->BaseAddress);
	configASSERT(Status == XST_SUCCESS);

	/*
	 * Set the options
	 */
	XTtcPs_SetOptions(Timer, TimerSetup->Options);

	/*
	 * Timer frequency is preset in the TimerSetup structure,
	 * however, the value is not reflected in its other fields, such as
	 * IntervalValue and PrescalerValue. The following call will map the
	 * frequency to the interval and prescaler values.
	 */
	XTtcPs_CalcIntervalFromFreq(Timer, TimerSetup->OutputHz,
		&(TimerSetup->Interval), &(TimerSetup->Prescaler));

	/*
	 * Set the interval and prescale
	 */
	XTtcPs_SetInterval(Timer, TimerSetup->Interval);
	XTtcPs_SetPrescaler(Timer, TimerSetup->Prescaler);

	return XST_SUCCESS;
}
#endif

