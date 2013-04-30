/*
    FreeRTOS V7.4.2 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not it can be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

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
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High 
    Integrity Systems, who sell the code with commercial support, 
    indemnification and middleware, under the OpenRTOS brand.
    
    http://www.SafeRTOS.com - High Integrity Systems also provide a safety 
    engineered and independently SIL3 certified version for use in safety and 
    mission critical applications that require provable dependability.
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
