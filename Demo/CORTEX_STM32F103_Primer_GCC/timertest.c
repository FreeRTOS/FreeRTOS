/*
    FreeRTOS V6.0.0 - Copyright (C) 2009 Real Time Engineers Ltd.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it    under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation and modified by the FreeRTOS exception.
    **NOTE** The exception to the GPL is included to allow you to distribute a
    combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    Alternative commercial license and support terms are also available upon
    request.  See the licensing section of http://www.FreeRTOS.org for full
    license details.

    FreeRTOS is distributed in the hope that it will be useful,    but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details.

    You should have received a copy of the GNU General Public License along
    with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
    Temple Place, Suite 330, Boston, MA  02111-1307  USA.


    ***************************************************************************
    *                                                                         *
    * The FreeRTOS eBook and reference manual are available to purchase for a *
    * small fee. Help yourself get started quickly while also helping the     *
    * FreeRTOS project! See http://www.FreeRTOS.org/Documentation for details *
    *                                                                         *
    ***************************************************************************

    1 tab == 4 spaces!

    Please ensure to read the configuration and relevant port sections of the
    online documentation.

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/

/* High speed timer test as described in main.c. */

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Library includes. */
#include "stm32f10x_lib.h"
#include "stm32f10x_tim.h"
#include "stm32f10x_map.h"

/* The set frequency of the interrupt.  Deviations from this are measured as
the jitter. */
#define timerINTERRUPT_FREQUENCY		( ( unsigned portSHORT ) 20000 )

/* The expected time between each of the timer interrupts - if the jitter was
zero. */
#define timerEXPECTED_DIFFERENCE_VALUE	( configCPU_CLOCK_HZ / timerINTERRUPT_FREQUENCY )

/* The highest available interrupt priority. */
#define timerHIGHEST_PRIORITY			( 0 )

/* Misc defines. */
#define timerMAX_32BIT_VALUE			( 0xffffffffUL )
#define timerTIMER_1_COUNT_VALUE		( * ( ( unsigned long * ) ( TIMER1_BASE + 0x48 ) ) )

/* The number of interrupts to pass before we start looking at the jitter. */
#define timerSETTLE_TIME			5

/*-----------------------------------------------------------*/

/*
 * Configures the two timers used to perform the test.
 */
void vSetupTimerTest( void );

/* Interrupt handler in which the jitter is measured. */
void vTimer2IntHandler( void );

/* Stores the value of the maximum recorded jitter between interrupts. */
volatile unsigned portSHORT usMaxJitter = 0;

/*-----------------------------------------------------------*/

void vSetupTimerTest( void )
{
unsigned long ulFrequency;
TIM_TimeBaseInitTypeDef  TIM_TimeBaseStructure;
NVIC_InitTypeDef NVIC_InitStructure;


	/* Enable timer clocks */
	RCC_APB1PeriphClockCmd( RCC_APB1Periph_TIM2, ENABLE );
	RCC_APB1PeriphClockCmd( RCC_APB1Periph_TIM3, ENABLE );

	/* Initialise data. */
	TIM_DeInit( TIM2 );
	TIM_DeInit( TIM3 );
	TIM_TimeBaseStructInit( &TIM_TimeBaseStructure );

	/* Time base configuration for timer 2 - which generates the interrupts. */
	ulFrequency = configCPU_CLOCK_HZ / timerINTERRUPT_FREQUENCY;	
	TIM_TimeBaseStructure.TIM_Period = ( unsigned portSHORT ) ( ulFrequency & 0xffffUL );
	TIM_TimeBaseStructure.TIM_Prescaler = 0x0;
	TIM_TimeBaseStructure.TIM_ClockDivision = 0x0;
	TIM_TimeBaseStructure.TIM_CounterMode = TIM_CounterMode_Up;
	TIM_TimeBaseInit( TIM2, &TIM_TimeBaseStructure );
	TIM_ARRPreloadConfig( TIM2, ENABLE );

	
	/* Configuration for timer 3 which is used as a high resolution time
	measurement. */
	TIM_TimeBaseStructure.TIM_Period = ( unsigned portSHORT ) 0xffff;
	TIM_TimeBaseInit( TIM3, &TIM_TimeBaseStructure );
	TIM_ARRPreloadConfig( TIM3, ENABLE );
	
	/* Enable TIM2 IT.  TIM3 does not generate an interrupt. */
	NVIC_InitStructure.NVIC_IRQChannel = TIM2_IRQChannel;
	NVIC_InitStructure.NVIC_IRQChannelSubPriority = 0;
	NVIC_InitStructure.NVIC_IRQChannelPreemptionPriority = timerHIGHEST_PRIORITY;
	NVIC_InitStructure.NVIC_IRQChannelCmd = ENABLE;
	NVIC_Init( &NVIC_InitStructure );	
	TIM_ITConfig( TIM2, TIM_IT_Update, ENABLE );

	/* Finally, enable both timers. */
	TIM_Cmd( TIM2, ENABLE );
	TIM_Cmd( TIM3, ENABLE );
}
/*-----------------------------------------------------------*/

void vTimer2IntHandler( void )
{
static unsigned portSHORT usLastCount = 0, usSettleCount = 0, usMaxDifference = 0;
unsigned portSHORT usThisCount, usDifference;

	/* Capture the free running timer 3 value as we enter the interrupt. */
	usThisCount = TIM3->CNT;
	
	if( usSettleCount >= timerSETTLE_TIME )
	{
		/* What is the difference between the timer value in this interrupt
		and the value from the last interrupt. */
		usDifference = usThisCount - usLastCount;

		/* Store the difference in the timer values if it is larger than the
		currently stored largest value.  The difference over and above the
		expected difference will give the 'jitter' in the processing of these
		interrupts. */
		if( usDifference > usMaxDifference )
		{
			usMaxDifference = usDifference;
			usMaxJitter = usMaxDifference - timerEXPECTED_DIFFERENCE_VALUE;
		}
	}
	else
	{
		/* Don't bother storing any values for the first couple of
		interrupts. */
		usSettleCount++;
	}

	/* Remember what the timer value was this time through, so we can calculate
	the difference the next time through. */
	usLastCount = usThisCount;

    TIM_ClearITPendingBit( TIM2, TIM_IT_Update );
}








