/*
	FreeRTOS V5.4.2 - Copyright (C) 2009 Real Time Engineers Ltd.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
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

/*
Changes from V3.0.0
	+ ISRcode pulled inline to reduce stack-usage.

	+ Added functionality to only call vTaskSwitchContext() once
	  when handling multiple interruptsources in a single interruptcall.

	+ Filename changed to a .c extension to allow stepping through code
	  using F7.

Changes from V3.0.1
*/

#ifndef _FREERTOS_SERIAL_ISRSERIALRX_C
#define _FREERTOS_SERIAL_ISRSERIALRX_C

#define serCONTINUOUS_RX		( 1 )
#define serCLEAR_OVERRUN		( 0 )

{
	/*
	 * Was the interrupt a byte being received?
	 */
	if( bRCIF && bRCIE)
	{
		/*
		 * Queue to interface between comms API and interrupt routine.
		*/
		extern xQueueHandle xRxedChars;
		
		/*
		 * Because we are not allowed to use local variables here,
		 * PRODL is (ab)used as temporary storage.  This is allowed
		 * because this SFR will be restored before exiting the ISR.
		 */
		extern portCHAR			cChar;
		extern portBASE_TYPE xHigherPriorityTaskWoken;
		#pragma locate cChar	&PRODL

		/*
		 * If there was a framing error, just get and ignore
		 * the character
		 */
		if( bFERR )
		{
			cChar = RCREG;
		}
		else
		{
			/*
			 * Get the character and post it on the queue of Rxed
			 * characters. If the post causes a task to wake ask
			 * for a context switch as the woken task may have a
			 * higher priority than the task we have interrupted.
			 */
			cChar = RCREG;

			/*
			 * Clear any overrun errors.
			 */
			if( bOERR )
			{
				bCREN = serCLEAR_OVERRUN;
				bCREN = serCONTINUOUS_RX;	
			}

			xHigherPriorityTaskWoken = pdFALSE;
			xQueueSendFromISR( xRxedChars, ( const void * ) &cChar, &xHigherPriorityTaskWoken );

			if( xHigherPriorityTaskWoken )
			{
				uxSwitchRequested = pdTRUE;
			}
		}
	}
}

#endif	/* _FREERTOS_SERIAL_ISRSERIALRX_C */
