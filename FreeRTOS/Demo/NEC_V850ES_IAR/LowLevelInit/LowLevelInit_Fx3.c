/*
 * FreeRTOS Kernel V10.2.0
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
