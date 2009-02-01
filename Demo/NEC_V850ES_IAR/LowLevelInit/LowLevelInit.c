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
