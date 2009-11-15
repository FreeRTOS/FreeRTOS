/*
    FreeRTOS V6.0.1 - Copyright (C) 2009 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Constants required for interrupt management. */
#define tcpCLEAR_VIC_INTERRUPT	( 0 )
#define tcpEINT0_VIC_CHANNEL_BIT	( ( unsigned long ) 0x4000 )

/* EINT0 interrupt handler.  This processes interrupts from the WIZnet device. */
void vEINT0_ISR_Wrapper( void ) __attribute__((naked));

/* The handler that goes with the EINT0 wrapper. */
void vEINT0_ISR_Handler( void );

/* Variable is required for its address, but does not otherwise get used. */
static long lDummyVariable;

/*
 * When the WIZnet device asserts an interrupt we send an (empty) message to
 * the TCP task.  This wakes the task so the interrupt can be processed.  The
 * source of the interrupt has to be ascertained by the TCP task as this 
 * requires an I2C transaction which cannot be performed from this ISR.
 * Note this code predates the introduction of semaphores, a semaphore should
 * be used in place of the empty queue message.
 */
void vEINT0_ISR_Handler( void )
{
extern xQueueHandle xTCPISRQueue;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* Just wake the TCP task so it knows an ISR has occurred. */
	xQueueSendFromISR( xTCPISRQueue, ( void * ) &lDummyVariable, &xHigherPriorityTaskWoken );	

	/* We cannot carry on processing interrupts until the TCP task has 
	processed this one - so for now interrupts are disabled.  The TCP task will
	re-enable it. */
	VICIntEnClear |= tcpEINT0_VIC_CHANNEL_BIT;

	/* Clear the interrupt bit. */	
	VICVectAddr = tcpCLEAR_VIC_INTERRUPT;

	if( xHigherPriorityTaskWoken )
	{
		portYIELD_FROM_ISR();
	}
}
/*-----------------------------------------------------------*/

void vEINT0_ISR_Wrapper( void )
{
	/* Save the context of the interrupted task. */
	portSAVE_CONTEXT();

	/* The handler must be a separate function from the wrapper to
	ensure the correct stack frame is set up. */
	vEINT0_ISR_Handler();

	/* Restore the context of whichever task is going to run next. */
	portRESTORE_CONTEXT();
}


