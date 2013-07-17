/*
    FreeRTOS V7.5.0 - Copyright (C) 2013 Real Time Engineers Ltd.

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


