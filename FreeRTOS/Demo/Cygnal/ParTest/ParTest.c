/*
    FreeRTOS V8.1.2 - Copyright (C) 2014 Real Time Engineers Ltd. 
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

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

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
#include <c8051f120.h>

#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"

#define partstPUSH_PULL			( ( unsigned char ) 0xff )
#define partstALL_OUTPUTS_OFF	( ( unsigned char ) 0xff )

/* LED to output is dependent on how the LED's are wired. */
#define partstOUTPUT_0			( ( unsigned char ) 0x02 )
#define partstOUTPUT_1			( ( unsigned char ) 0x08 )
#define partstOUTPUT_2			( ( unsigned char ) 0x20 )
#define partstOUTPUT_3			( ( unsigned char ) 0x01 )
#define partstOUTPUT_4			( ( unsigned char ) 0x04 )
#define partstOUTPUT_5			( ( unsigned char ) 0x10 )
#define partstOUTPUT_6			( ( unsigned char ) 0x40 )
#define partstOUTPUT_7			( ( unsigned char ) 0x80 )

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

void vParTestInitialise( void )
{
unsigned char ucOriginalSFRPage;

	/* Remember the SFR page before it is changed so it can get set back
	before the function exits. */
	ucOriginalSFRPage = SFRPAGE;

	/* Setup the SFR page to access the config SFR's. */
	SFRPAGE = CONFIG_PAGE;

	/* Set the on board LED to push pull. */
	P3MDOUT |= partstPUSH_PULL;

	/* Return the SFR page. */
	SFRPAGE = ucOriginalSFRPage;

	P3 = partstALL_OUTPUTS_OFF;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, portBASE_TYPE xValue )
{
portBASE_TYPE xError = pdFALSE;

	vTaskSuspendAll();
	{
		if( xValue == pdFALSE )
		{
			switch( uxLED )
			{
				case 0	:	P3 |= partstOUTPUT_0;
							break;
				case 1	:	P3 |= partstOUTPUT_1;
							break;
				case 2	:	P3 |= partstOUTPUT_2;
							break;
				case 3	:	P3 |= partstOUTPUT_3;
							break;
				case 4	:	P3 |= partstOUTPUT_4;
							break;
				case 5	:	P3 |= partstOUTPUT_5;
							break;
				case 6	:	P3 |= partstOUTPUT_6;
							break;
				case 7	:	P3 |= partstOUTPUT_7;
							break;
				default	:	/* There are no other LED's wired in. */
							xError = pdTRUE;
							break;
			}
		}
		else
		{
			switch( uxLED )
			{
				case 0	:	P3 &= ~partstOUTPUT_0;
							break;
				case 1	:	P3 &= ~partstOUTPUT_1;
							break;
				case 2	:	P3 &= ~partstOUTPUT_2;
							break;
				case 3	:	P3 &= ~partstOUTPUT_3;
							break;
				case 4	:	P3 &= ~partstOUTPUT_4;
							break;
				case 5	:	P3 &= ~partstOUTPUT_5;
							break;
				case 6	:	P3 &= ~partstOUTPUT_6;
							break;
				case 7	:	P3 &= ~partstOUTPUT_7;
							break;
				default	:	/* There are no other LED's wired in. */
							break;
			}
		}
	}
	xTaskResumeAll();
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned char ucBit;
portBASE_TYPE xError = pdFALSE;

	vTaskSuspendAll();
	{
		switch( uxLED )
		{
			case 0	:	ucBit = partstOUTPUT_0;
						break;
			case 1	:	ucBit = partstOUTPUT_1;
						break;
			case 2	:	ucBit = partstOUTPUT_2;
						break;
			case 3	:	ucBit = partstOUTPUT_3;
						break;
			case 4	:	ucBit = partstOUTPUT_4;
						break;
			case 5	:	ucBit = partstOUTPUT_5;
						break;
			case 6	:	ucBit = partstOUTPUT_6;
						break;
			case 7	:	ucBit = partstOUTPUT_7;
						break;
			default	:	/* There are no other LED's wired in. */
						xError = pdTRUE;
						break;
		}

		if( xError != pdTRUE )
		{
			if( P3 & ucBit )
			{
				P3 &= ~ucBit;
			}
			else
			{
				P3 |= ucBit;
			}
		}
	}
	xTaskResumeAll();
}


