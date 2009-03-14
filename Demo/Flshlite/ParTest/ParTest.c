/*
	FreeRTOS.org V5.2.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it 
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or 
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for 
	more details.

	You should have received a copy of the GNU General Public License along 
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59 
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.

	A special exception to the GPL is included to allow you to distribute a 
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
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

/*
Changes from V1.01:

	+ Types used updated.
	+ Add vParTestToggleLED();

Changes from V2.0.0

	+ Use scheduler suspends in place of critical sections.
*/


#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"

#define partstALL_OUTPUTS_OFF			( ( unsigned portSHORT) 0x00 )
#define partstMAX_OUTPUT_LED			( ( unsigned portCHAR ) 7 )
#define partstPORT_F_ADDR				( ( unsigned portSHORT ) 0x605 )
#define partstPORT_DIRECTION_REG		( ( unsigned portSHORT ) 0x606 )
#define partstPORT_F_DIR_BIT			( ( unsigned portSHORT ) 0x20 )

/*lint -e956 File scope parameters okay here. */
static volatile unsigned portCHAR ucCurrentOutputValue = partstALL_OUTPUTS_OFF;
/*lint +e956 */

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

void vParTestInitialise( void )
{
unsigned portSHORT usInput;

	ucCurrentOutputValue = partstALL_OUTPUTS_OFF;

	/* Set the direction to output for port F. */
	usInput = portINPUT_BYTE( partstPORT_DIRECTION_REG );
	usInput |= partstPORT_F_DIR_BIT;
	portOUTPUT_BYTE( partstPORT_DIRECTION_REG, usInput );

	/* Start with all outputs off. */
	portOUTPUT_BYTE( partstPORT_F_ADDR, partstALL_OUTPUTS_OFF );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, portBASE_TYPE xValue )
{
unsigned portCHAR ucBit = ( unsigned portCHAR ) 1;

	if( uxLED <= partstMAX_OUTPUT_LED )
	{
		ucBit <<= uxLED;
	}	

	vTaskSuspendAll();
	{
		if( xValue == pdTRUE )
		{
			ucBit ^= ( unsigned portCHAR ) 0xff;
			ucCurrentOutputValue &= ucBit;
		}
		else
		{
			ucCurrentOutputValue |= ucBit;
		}

		portOUTPUT_BYTE( partstPORT_F_ADDR, ( unsigned ) ucCurrentOutputValue );
	}
	xTaskResumeAll();
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned portCHAR ucBit;

	if( uxLED <= partstMAX_OUTPUT_LED )
	{
		ucBit = ( ( unsigned portCHAR ) 1 ) << uxLED;

		vTaskSuspendAll();
		{
			if( ucCurrentOutputValue & ucBit )
			{
				ucCurrentOutputValue &= ~ucBit;
			}
			else
			{
				ucCurrentOutputValue |= ucBit;
			}

			portOUTPUT_BYTE( partstPORT_F_ADDR, ( unsigned ) ucCurrentOutputValue );
		}
		xTaskResumeAll();			
	}
}

