/*
	FreeRTOS.org V5.1.0 - Copyright (C) 2003-2008 Richard Barry.

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
#include "task.h"
#include "partest.h"

#define partstNUM_LEDs	4

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

void vParTestInitialise( void )
{
    /* Ensure LED outputs are set to GPIO */
    MCF_GPIO_PTCPAR = MCF_GPIO_PTCPAR_DTIN3_GPIO | MCF_GPIO_PTCPAR_DTIN2_GPIO | MCF_GPIO_PTCPAR_DTIN1_GPIO | MCF_GPIO_PTCPAR_DTIN0_GPIO;

    /* Set GPIO to outputs. */
    MCF_GPIO_DDRTC = MCF_GPIO_DDRTC_DDRTC3 | MCF_GPIO_DDRTC_DDRTC2 | MCF_GPIO_DDRTC_DDRTC1 | MCF_GPIO_DDRTC_DDRTC0;

    /* Start with all LEDs off. */
	MCF_GPIO_PORTTC = 0x00;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < partstNUM_LEDs )
	{
		if( xValue != 0 )
		{
			taskENTER_CRITICAL();
				MCF_GPIO_PORTTC |= ( 1 << uxLED );
			taskEXIT_CRITICAL();
		}
		else
		{
			taskENTER_CRITICAL();
				MCF_GPIO_PORTTC &= ~( 1 << uxLED );
			taskEXIT_CRITICAL();
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstNUM_LEDs )
	{
		taskENTER_CRITICAL();
		{
			if( ( MCF_GPIO_PORTTC & ( 1 << uxLED ) ) == ( unsigned portCHAR ) 0 )
			{
				MCF_GPIO_PORTTC |= ( 1 << uxLED );
			}
			else
			{
				MCF_GPIO_PORTTC &= ~( 1 << uxLED );
			}
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

