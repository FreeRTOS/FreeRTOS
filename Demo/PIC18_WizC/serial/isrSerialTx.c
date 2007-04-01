/*
	FreeRTOS.org V4.2.1 - Copyright (C) 2003-2007 Richard Barry.

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

	Also see http://www.SafeRTOS.com for an IEC 61508 compliant version along
	with commercial development and support options.
	***************************************************************************
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

#ifndef _FREERTOS_SERIAL_ISRSERIALTX_C
#define _FREERTOS_SERIAL_ISRSERIALTX_C

#define serINTERRUPT_DISABLED	( 0 )


{
	/*
	 * Was the interrupt the Tx register becoming empty?
	 */
	if( bTXIF && bTXIE)
	{
		/*
		 * Queue to interface between comms API and interrupt routine.
		*/
		extern xQueueHandle xCharsForTx;

		/*
		 * Because we are not allowed to use local variables here,
		 * PRODL and PRODH are (ab)used as temporary storage. This
		 * is allowed because these SFR's will be restored before
		 * exiting the ISR.
		 */
		extern portCHAR				cChar;
		#pragma locate cChar		&PRODL
		extern portBASE_TYPE		pxTaskWoken;
		#pragma locate pxTaskWoken	&PRODH

		if( xQueueReceiveFromISR( xCharsForTx, &cChar, &pxTaskWoken ) == pdTRUE )
		{
			/*
			 * Send the next character queued for Tx.
			 */
			TXREG = cChar;
		}
		else
		{
			/*
			 * Queue empty, nothing to send.
			 */
			bTXIE = serINTERRUPT_DISABLED;
		}

		/*
		 * If we woke another task, ask for a contextswitch
		 */
		if( pxTaskWoken == pdTRUE )
		{
			uxSwitchRequested = pdTRUE;
		}
	}
}

#endif	/* _FREERTOS_SERIAL_ISRSERIALTX_C */
