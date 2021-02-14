/*
 * FreeRTOS V202012.00
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

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo includes. */
#include "IntQueueTimer.h"
#include "IntQueue.h"

/* Library includes. */
#include "SMM_MPS2.h"

#define tmrTIMER_0_FREQUENCY	( 2000UL )
#define tmrTIMER_1_FREQUENCY	( 2001UL )

volatile uint32_t ulNest, ulMaxNext, ulNestCount;

void TIMER0_Handler( void )
{
	CMSDK_TIMER0->INTCLEAR = (1ul <<  0);    /* clear interrupt                 */
	if( ulNest > 0 )
	{
		ulNestCount++;
	}
	portEND_SWITCHING_ISR( xSecondTimerHandler() );
}

void TIMER1_Handler( void )
{
	ulNest++;
	CMSDK_TIMER1->INTCLEAR = (1ul <<  0);    /* clear interrupt                 */
	portEND_SWITCHING_ISR( xFirstTimerHandler() );
	ulNest--;
}

void vInitialiseTimerForIntQueueTest( void )
{
  CMSDK_TIMER0->INTCLEAR = (1ul <<  0);   /* clear interrupt                 */
  CMSDK_TIMER0->RELOAD   = ( configCPU_CLOCK_HZ / tmrTIMER_0_FREQUENCY ) + 1UL;   /* set reload value                */
  CMSDK_TIMER0->CTRL     = ((1ul <<  3) |  /* enable Timer interrupt          */
                           (1ul <<  0) ); /* enable Timer                    */

  CMSDK_TIMER1->INTCLEAR = (1ul <<  0);   /* clear interrupt                 */
  CMSDK_TIMER1->RELOAD   = ( configCPU_CLOCK_HZ / tmrTIMER_1_FREQUENCY ) + 1UL;   /* set reload value                */
  CMSDK_TIMER1->CTRL     = ((1ul <<  3) |  /* enable Timer interrupt          */
                           (1ul <<  0) ); /* enable Timer                    */

  NVIC_SetPriority( TIMER0_IRQn, configMAX_SYSCALL_INTERRUPT_PRIORITY );
  NVIC_SetPriority( TIMER1_IRQn, configMAX_SYSCALL_INTERRUPT_PRIORITY + 1 );
  NVIC_EnableIRQ(TIMER0_IRQn);             /* Enable interrupt in NVIC        */
  NVIC_EnableIRQ(TIMER1_IRQn);             /* Enable interrupt in NVIC        */
}
/*-----------------------------------------------------------*/

