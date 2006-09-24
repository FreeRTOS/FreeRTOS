/*
	FreeRTOS.org V4.1.1 - copyright (C) 2003-2006 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	See http://www.FreeRTOS.org for documentation, latest information, license 
	and contact details.  Please ensure to read the configuration and relevant 
	port sections of the online documentation.
	***************************************************************************
*/

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Constants required for interrupt management. */
#define tcpCLEAR_VIC_INTERRUPT	( 0 )
#define tcpEINT0_VIC_CHANNEL_BIT	( ( unsigned portLONG ) 0x4000 )

/* EINT0 interrupt handler.  This processes interrupts from the WIZnet device. */
void vEINT0_ISR( void ) __attribute__((naked));

/* Variable is required for its address, but does not otherwise get used. */
static portLONG lDummyVariable;

/*
 * When the WIZnet device asserts an interrupt we send an (empty) message to
 * the TCP task.  This wakes the task so the interrupt can be processed.  The
 * source of the interrupt has to be ascertained by the TCP task as this 
 * requires an I2C transaction which cannot be performed from this ISR.
 */
void vEINT0_ISR( void )
{
	portENTER_SWITCHING_ISR();

	extern xQueueHandle xTCPISRQueue;
	portBASE_TYPE xTaskWoken = pdFALSE;

	/* Just wake the TCP task so it knows an ISR has occurred. */
	xQueueSendFromISR( xTCPISRQueue, ( void * ) &lDummyVariable, xTaskWoken );	

	/* We cannot carry on processing interrupts until the TCP task has 
	processed this one - so for now interrupts are disabled.  The TCP task will
	re-enable it. */
	VICIntEnClear |= tcpEINT0_VIC_CHANNEL_BIT;

	/* Clear the interrupt bit. */	
	VICVectAddr = tcpCLEAR_VIC_INTERRUPT;

	/* Switch to the TCP task immediately so the cause of the interrupt can
	be ascertained.  It is the responsibility of the TCP task to clear the
	interrupts. */
	portEXIT_SWITCHING_ISR( ( xTaskWoken ) );
}


