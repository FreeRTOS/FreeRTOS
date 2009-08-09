/*
	FreeRTOS V5.4.2 - Copyright (C) 2009 Real Time Engineers Ltd.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

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
 * Simple LED IO routines for the tower LEDs LED1 to LED4.
 *-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* Enable pull and output drive. */
	PTHPE_PTHPE3 = 1;
	PTHDD_PTHDD3 = 1;

	PTEPE_PTEPE5 = 1;
	PTEDD_PTEDD5 = 1;

	PTGPE_PTGPE5 = 1;
	PTGDD_PTGDD5 = 1;

	PTEPE_PTEPE3 = 1;
	PTEDD_PTEDD3 = 1;
	
	/* Enable clock to ports. */
	SCGC3_PTE = 1;
	SCGC3_PTF = 1;
	SCGC3_PTG = 1;

	/* Ensure the LEDs are off. */
	vParTestSetLED( 0, 0 );
	vParTestSetLED( 1, 0 );
	vParTestSetLED( 2, 0 );
	vParTestSetLED( 3, 0 );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	switch( uxLED )
	{
		case 0:	PTHD_PTHD3 = xValue;
				break;
		case 1:	PTED_PTED5 = xValue;
				break;
		case 2:	PTGD_PTGD5 = xValue;
				break;
		case 3:	PTED_PTED3 = xValue;
				break;
		default : /* There are no other LEDs. */
				break;
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	portENTER_CRITICAL();
	{
		switch( uxLED )
		{
			case 0:	PTHD_PTHD3 = !PTHD_PTHD3;
					break;
			case 1:	PTED_PTED5 = !PTED_PTED5;
					break;
			case 2:	PTGD_PTGD5 = !PTGD_PTGD5;
					break;
			case 3:	PTED_PTED3 = !!PTED_PTED3;
					break;
			default : /* There are no other LEDs. */
					break;
		}
	}
	portEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

unsigned portBASE_TYPE uxParTestGetLED( unsigned portBASE_TYPE uxLED )
{
	/* We ignore the parameter as in this simple example we simply return the
	state of LED3. */
	( void ) uxLED;
	
	return PTED_PTED3;
}


