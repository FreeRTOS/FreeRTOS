/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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

/* High speed timer test as described in main.c. */

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Library includes. */
#include "stm32f10x_lib.h"
#include "stm32f10x_tim.h"
#include "stm32f10x_map.h"

/* The set frequency of the interrupt.  Deviations from this are measured as
the jitter. */
#define timerINTERRUPT_FREQUENCY		( ( unsigned short ) 20000 )

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
void vSetupHighFrequencyTimer( void );

/* Stores the value of the maximum recorded jitter between interrupts. */
volatile unsigned short usMaxJitter = 0;

/* Variable that counts at 20KHz to provide the time base for the run time
stats. */
unsigned long ulRunTimeStatsClock = 0UL;

/*-----------------------------------------------------------*/

void vSetupHighFrequencyTimer( void )
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
	TIM_TimeBaseStructure.TIM_Period = ( unsigned short ) ( ulFrequency & 0xffffUL );
	TIM_TimeBaseStructure.TIM_Prescaler = 0x0;
	TIM_TimeBaseStructure.TIM_ClockDivision = 0x0;
	TIM_TimeBaseStructure.TIM_CounterMode = TIM_CounterMode_Up;
	TIM_TimeBaseInit( TIM2, &TIM_TimeBaseStructure );
	TIM_ARRPreloadConfig( TIM2, ENABLE );


	/* Configuration for timer 3 which is used as a high resolution time
	measurement. */
	TIM_TimeBaseStructure.TIM_Period = ( unsigned short ) 0xffff;
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

void TIM2_IRQHandler( void )
{
static unsigned short usLastCount = 0, usSettleCount = 0, usMaxDifference = 0;
unsigned short usThisCount, usDifference;

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

	/* Keep a count of the number of interrupts as a time base for the run time
	stats collection. */
	ulRunTimeStatsClock++;

    TIM_ClearITPendingBit( TIM2, TIM_IT_Update );
}








