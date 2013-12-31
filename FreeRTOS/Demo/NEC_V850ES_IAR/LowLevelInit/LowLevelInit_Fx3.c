/*
    FreeRTOS V8.0.0:rc1 - Copyright (C) 2014 Real Time Engineers Ltd. 
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

	/* Setup provided by NEC. */

	/* Disable global interrupts to ensure no interrupts occur during system
	setup. */
	portDISABLE_INTERRUPTS();

	PRCMD = 0x00;
	OCDM = 0x00;
	VSWC = 0x12;
	VSWC = 18;

	/* Set main system clock */
	OSTS = 0x06;
	psval = 0x80;
	PRCMD = psval;
	PCC = psval;
	while (!OSTC)
	{
		;
	}

	PLLS = 0x03;
	PLLON = 1;
	while (LOCKR)
	{
		;
	}

	psval = 0x01;
	PRCMD = psval;
	MCM = psval;
	SELPLL = 1;

	/* Set fCPU */
	psval = PCC | 0x00;
	PRCMD = psval;
	PCC = psval;
	RCM = 0x83;

	/* Set fXP1 */
	SELCNT4 = 0x00;

	/* Set fBRG */
	PRSM0 = 0x00;

	/* Stand-by setting */
	psval = 0x00;
	PRCMD = psval;
	PSC = psval;

	/* WDT2 setting */
	WDTM2 = 0x1F;

	/* PCL setting */
	PCLM = 0x00;

	/* disable dma0 - dma3 */
	E00 = 0;	
	E11 = 0;
	E22 = 0;
	E33 = 0;	

	return pdTRUE;
}
/*-----------------------------------------------------------*/
