/*
    FreeRTOS V6.0.3 - Copyright (C) 2010 Real Time Engineers Ltd.

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
	
		
