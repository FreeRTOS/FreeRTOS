/*
    FreeRTOS V7.6.0 - Copyright (C) 2013 Real Time Engineers Ltd. 
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
