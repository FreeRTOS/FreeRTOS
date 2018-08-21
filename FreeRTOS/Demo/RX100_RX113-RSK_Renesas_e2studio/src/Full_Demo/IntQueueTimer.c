/*
 * FreeRTOS Kernel V10.1.0
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

/*
 * This file contains the non-portable and therefore RX62N specific parts of
 * the IntQueue standard demo task - namely the configuration of the timers
 * that generate the interrupts and the interrupt entry points.
 */

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "IntQueueTimer.h"
#include "IntQueue.h"

/* Hardware specifics. */
#include "iodefine.h"

#define tmrTIMER_0_1_FREQUENCY	( 2000UL )
#define tmrTIMER_2_3_FREQUENCY	( 2407UL )

void vInitialiseTimerForIntQueueTest( void )
{
	/* Ensure interrupts do not start until full configuration is complete. */
	portENTER_CRITICAL();
	{
		SYSTEM.PRCR.WORD = 0xa502;

		/* Cascade two 8bit timer channels to generate the interrupts. 
		8bit timer unit 1 (TMR0 and TMR1) and 8bit timer unit 2 (TMR2 and TMR3 are
		utilised for this test. */

		/* Enable the timers. */
		SYSTEM.MSTPCRA.BIT.MSTPA5 = 0;
		SYSTEM.MSTPCRA.BIT.MSTPA4 = 0;

		/* Enable compare match A interrupt request. */
		TMR0.TCR.BIT.CMIEA = 1;
		TMR2.TCR.BIT.CMIEA = 1;

		/* Clear the timer on compare match A. */
		TMR0.TCR.BIT.CCLR = 1;
		TMR2.TCR.BIT.CCLR = 1;

		/* Set the compare match value. */
		TMR01.TCORA = ( unsigned short ) ( ( ( configPERIPHERAL_CLOCK_HZ / tmrTIMER_0_1_FREQUENCY ) -1 ) / 8 );
		TMR23.TCORA = ( unsigned short ) ( ( ( configPERIPHERAL_CLOCK_HZ / tmrTIMER_0_1_FREQUENCY ) -1 ) / 8 );

		/* 16 bit operation ( count from timer 1,2 ). */
		TMR0.TCCR.BIT.CSS = 3;
		TMR2.TCCR.BIT.CSS = 3;
	
		/* Use PCLK as the input. */
		TMR1.TCCR.BIT.CSS = 1;
		TMR3.TCCR.BIT.CSS = 1;
	
		/* Divide PCLK by 8. */
		TMR1.TCCR.BIT.CKS = 2;
		TMR3.TCCR.BIT.CKS = 2;

		/* Enable TMR 0, 2 interrupts. */
		TMR0.TCR.BIT.CMIEA = 1;
		TMR2.TCR.BIT.CMIEA = 1;

		/* Set interrupt priority and enable. */
		IPR( TMR0, CMIA0 ) = configMAX_SYSCALL_INTERRUPT_PRIORITY - 1;
		IR( TMR0, CMIA0 ) = 0U;
		IEN( TMR0, CMIA0 ) = 1U;

		/* Do the same for TMR2, but to vector 129. */
		IPR( TMR2, CMIA2 ) = configMAX_SYSCALL_INTERRUPT_PRIORITY - 2;
		IR( TMR2, CMIA2 ) = 0U;
		IEN( TMR2, CMIA2 ) = 1U;
	}
	portEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

#pragma interrupt r_tmr_cmia0_interrupt(vect=VECT(TMR0,CMIA0))
void r_tmr_cmia0_interrupt( void )
{
	portYIELD_FROM_ISR( xFirstTimerHandler() );
}
/*-----------------------------------------------------------*/

#pragma interrupt r_tmr_cmia2_interrupt(vect=VECT(TMR2,CMIA2))
void r_tmr_cmia2_interrupt( void )
{
	portYIELD_FROM_ISR( xSecondTimerHandler() );
}




