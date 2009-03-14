/*
	FreeRTOS.org V5.2.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it 
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or 
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for 
	more details.

	You should have received a copy of the GNU General Public License along 
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59 
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.

	A special exception to the GPL is included to allow you to distribute a 
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
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
