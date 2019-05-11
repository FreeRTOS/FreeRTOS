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

#include "FreeRTOSConfig.h"
#include "portasm.h"

/* These wrappers are only used when interrupt method 2 is being used.  See
FreeRTOSConfig.h for an explanation. */
#if configINTERRUPT_EXAMPLE_METHOD == 2

.CODE





/* Wrapper for the Rx UART interrupt. */
_vUARTRx_Wrapper

	portSAVE_CONTEXT
	call #_vRxISR
	portRESTORE_CONTEXT

/*-----------------------------------------------------------*/

/* Wrapper for the Tx UART interrupt. */
_vUARTTx_Wrapper

	portSAVE_CONTEXT
	call #_vTxISR
	portRESTORE_CONTEXT

/*-----------------------------------------------------------*/


      		

	/* Place the UART ISRs in the correct vectors. */

	.VECTORS

	.KEEP

	ORG		UART1RX_VECTOR
	DW		_vUARTRx_Wrapper

	ORG		UART1TX_VECTOR
	DW		_vUARTTx_Wrapper		
		

#endif /* configINTERRUPT_EXAMPLE_METHOD */

	END
	
		
