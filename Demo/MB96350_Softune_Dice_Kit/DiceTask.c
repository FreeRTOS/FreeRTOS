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
#include "task.h"
#include "semphr.h"

#define diceMIN    1
#define diceMAX    6
#define diceRUN_MIN  600000L
#define diceRUN_MAX 1200000L

#define diceSTATE_STOPPED		0
#define diceSTATE_STARTUP		1
#define diceSTATE_RUNNING		2

#define diceEND_DELAY			( 5000 / portTICK_RATE_MS )

#define dice7SEG_Value( x )		*( pucDisplayOutput[ x ] )

#define prvButtonHit( ucIndex, xTicksToWait ) xSemaphoreTake( xSemaphores[ ucIndex ], xTicksToWait )

static const char cDisplaySegments[ 2 ][ 11 ] =
{
	{ 0x48, 0xeb, 0x8c, 0x89, 0x2b, 0x19, 0x18, 0xcb, 0x08, 0x09, 0xf7 },
	{ 0xa0, 0xf3, 0xc4, 0xc1, 0x93, 0x89, 0x88, 0xe3, 0x80, 0x81, 0x7f }
};

static xSemaphoreHandle xSemaphores[ 2 ] = { 0 };

extern volatile unsigned char *pucDisplayOutput[ 2 ];

/*-----------------------------------------------------------*/

void vDiceTask( void *pvParameters )
{
char cDiceState = diceSTATE_STOPPED;
unsigned char ucDiceValue, ucIndex;
unsigned long ulDiceRunTime, ulDiceDelay, ulDiceDelayReload;
extern void vToggleFlashTaskSuspendState( void );

	ucIndex = ( unsigned char ) pvParameters;
	vSemaphoreCreateBinary( xSemaphores[ ucIndex ] );
	srand( ( unsigned char ) diceRUN_MIN );

	for( ;; )
	{
		switch( cDiceState )
		{
			case diceSTATE_STOPPED:

				prvButtonHit( ucIndex, portMAX_DELAY );
				ulDiceRunTime = diceRUN_MIN;				
				cDiceState = diceSTATE_RUNNING;
				ulDiceDelay = 1;
				ulDiceDelayReload = 1;
				cDiceState = diceSTATE_RUNNING;
				if( ucIndex == 0 )
				{
					vToggleFlashTaskSuspendState();
				}

				break;

			case diceSTATE_RUNNING:

				ulDiceRunTime--;
				ulDiceDelay--;

				if( !ulDiceDelay )
				{
					ucDiceValue = rand() % 6 + 1;
					dice7SEG_Value( ucIndex ) = ( dice7SEG_Value( ucIndex ) | 0xf7 ) & cDisplaySegments[ ucIndex ][ ucDiceValue ];
					ulDiceDelayReload = ulDiceDelayReload + 100;
					ulDiceDelay = ulDiceDelayReload;
				}

				if( ulDiceRunTime == 0 )
				{
					dice7SEG_Value( ucIndex ) = ( dice7SEG_Value( ucIndex ) | 0xf7 ) & cDisplaySegments[ ucIndex ][ rand() % 6 + 1 ];
					cDiceState = diceSTATE_STOPPED;

					if( ucIndex == 0 )
					{
						vTaskDelay( diceEND_DELAY );
						*pucDisplayOutput[ ucIndex ] = 0xff;
						vToggleFlashTaskSuspendState();
					}
				}

				break;
		}
	}
}
/*-----------------------------------------------------------*/

__interrupt void vExternalInt8Handler( void )
{
short sHigherPriorityTaskWoken = pdFALSE;

	/* Reset the interrupt. */
	EIRR1_ER8 = 0;

	xSemaphoreGiveFromISR( xSemaphores[ 0 ], &sHigherPriorityTaskWoken );

	if( sHigherPriorityTaskWoken != pdFALSE )
	{
		portYIELD_FROM_ISR();
	}
}
/*-----------------------------------------------------------*/

__interrupt void vExternalInt9Handler( void )
{
short sHigherPriorityTaskWoken = pdFALSE;

	/* Reset the interrupt. */
	EIRR1_ER9 = 0;

	xSemaphoreGiveFromISR( xSemaphores[ 1 ], &sHigherPriorityTaskWoken );

	if( sHigherPriorityTaskWoken != pdFALSE )
	{
		portYIELD_FROM_ISR();
	}
}







