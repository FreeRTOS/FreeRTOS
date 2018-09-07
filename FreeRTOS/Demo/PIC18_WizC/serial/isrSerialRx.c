/*
 * FreeRTOS Kernel V10.1.1
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
		extern QueueHandle_t xRxedChars;
		
		/*
		 * Because we are not allowed to use local variables here,
		 * PRODL is (ab)used as temporary storage.  This is allowed
		 * because this SFR will be restored before exiting the ISR.
		 */
		extern char			cChar;
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
