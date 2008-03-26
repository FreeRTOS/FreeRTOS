/*
	FreeRTOS.org V4.8.0 - Copyright (C) 2003-2008 Richard Barry.

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

/** 
 * ParTest.c controls bits (LEDs) for GCC/HCS12 version of FreeRTOS Demo
 *
 * Modified from CodeWarrior/HCS12 by Jefferson L Smith, Robotronics Inc.
 */

#include <sys/ports.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "portable.h"

/* Demo application include files. */
#include "partest.h"

#define LEDIO	PORTIO_8(PORT_LED)

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	/* This function is required as it is called from the standard demo 
	application files.  It manipulates a bit to control one LED. */
	portENTER_CRITICAL();

	if (xValue) {                       /* Is it one to be written? */
		LEDIO |= (1<<uxLED);            /* Set appropriate bit on port */
	}
	else {                             /* Is it zero to be written? */
		LEDIO &= ~(1<<uxLED);          /* Clear appropriate bit on port */
	}
	portEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	/* This function is required as it is called from the standard demo
	application files.  It manipulates a bit to control one LED. */
	portENTER_CRITICAL();
		LEDIO ^= (1<<uxLED);           /* Invert appropriate bit on port */
	portEXIT_CRITICAL();
}

