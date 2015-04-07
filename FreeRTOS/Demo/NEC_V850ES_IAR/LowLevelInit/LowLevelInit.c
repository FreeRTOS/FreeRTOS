/*
    FreeRTOS V8.2.1 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

#include "FreeRTOS.h"

/*-----------------------------------------------------------*/

/* Called by the startup code to initialise the run time system. */
unsigned char __low_level_init(void);

/*-----------------------------------------------------------*/

unsigned char __low_level_init(void)
{
unsigned char resetflag = RESF;
unsigned char psval = 0;
unsigned portBASE_TYPE i = 0;        

	/* Setup provided by NEC. */

	portDISABLE_INTERRUPTS();         /* disable global interrupts */                      

	PRCMD = 0x00;                     /* On-chip debug mode */
	OCDM = 0x00;
	VSWC = 0x00;                      /* set system wait control register */
	WDTM2 = 0x00;                     /* WDT2 setting */
	PLLON = 0;                        /* PLL stop mode */
	psval = 0x0A | 0x00;
	PRCMD = psval;                    /* set Command Register */
	CKC = psval;                      /* set Clock Control Register */
	PLLS = 0x03;
	psval = 0x80;                     /* Set fXX and fCPU */
	PRCMD = psval;
	PCC = psval;
	PLLON = 1;                        /* activate PLL */
	for( i = 0; i <= 2000; i++ )      /* Wait for stabilisation */
	{
	portNOP();
	}
	while( LOCK )                     /* Wait for PLL frequency stabiliasation */
	{
	;
	}
	SELPLL = 1;                       /* Set PLL mode active */
	RSTOP = 0;                        /* Set fR (enable) */
	BGCE0 = 0;                        /* Set fBRG(disable) */
	psval = 0x00;                     /* Stand-by setting */
	PRCMD = psval;                    /* set Command Register */
	PSC = psval;                      /* set Power Save Control Register */

	return pdTRUE;
}
/*-----------------------------------------------------------*/
