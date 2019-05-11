/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#include <device.h>
#include "FreeRTOS.h"
#include "task.h"
/*---------------------------------------------------------------------------*/

extern portBASE_TYPE xFirstTimerHandler( void );
extern portBASE_TYPE xSecondTimerHandler( void );
/*---------------------------------------------------------------------------*/

CY_ISR_PROTO( vHighFrequencyFirstISR );
CY_ISR_PROTO( vHighFrequencySecondISR );
/*---------------------------------------------------------------------------*/

/**
 * Installs and starts the ISRs that drive the Interupt Queue Tests.
 */
void vInitialiseTimerForIntQueueTest( void )
{
	taskENTER_CRITICAL();
	{
		/* Initialise and start the First Timer ISR. */
		isr_High_Frequency_2000Hz_ClearPending();
		isr_High_Frequency_2000Hz_StartEx( ( cyisraddress ) vHighFrequencyFirstISR );

		/* Initialise and start the Second Timer ISR. */
		isr_High_Frequency_2001Hz_ClearPending();
		isr_High_Frequency_2001Hz_StartEx( ( cyisraddress ) vHighFrequencySecondISR );
	}
	taskEXIT_CRITICAL();
}
/*---------------------------------------------------------------------------*/

CY_ISR(vHighFrequencyFirstISR)
{
	/* Call back into the test code and context switch if necessary. */
	portEND_SWITCHING_ISR( xFirstTimerHandler() );
}
/*---------------------------------------------------------------------------*/

CY_ISR(vHighFrequencySecondISR)
{
	/* Call back into the test code and context switch if necessary. */
	portEND_SWITCHING_ISR( xSecondTimerHandler() );
}
/*---------------------------------------------------------------------------*/
