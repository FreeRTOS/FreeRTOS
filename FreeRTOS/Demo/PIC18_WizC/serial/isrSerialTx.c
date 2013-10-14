/*
    FreeRTOS V7.5.3 - Copyright (C) 2013 Real Time Engineers Ltd. 
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

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
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
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
		extern char				cChar;
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
