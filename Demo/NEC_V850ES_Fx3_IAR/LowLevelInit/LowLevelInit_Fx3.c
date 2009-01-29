/*
	FreeRTOS.org V5.1.1 - Copyright (C) 2003-2008 Richard Barry.

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
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
*/

#include "FreeRTOS.h"

/*-----------------------------------------------------------*/

/* Called by the startup code to initialise the run time system. */
unsigned portCHAR __low_level_init(void);

/*-----------------------------------------------------------*/

unsigned portCHAR __low_level_init(void)
{
unsigned portCHAR resetflag = RESF;
unsigned portCHAR psval = 0;

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
