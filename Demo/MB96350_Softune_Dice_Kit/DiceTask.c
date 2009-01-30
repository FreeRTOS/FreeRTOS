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

#define diceMIN    1
#define diceMAX    6
#define diceRUN_MIN  600000L
#define diceRUN_MAX 1200000L

#define diceSTATE_STOPPED		0
#define diceSTATE_STARTUP		1
#define diceSTATE_RUNNING		2

static unsigned char prvButtonHit( unsigned char ucIndex );

static const char cDisplaySegments[ 2 ][ 11 ] =
{
	{ 0x48, 0xeb, 0x8c, 0x89, 0x2b, 0x19, 0x18, 0xcb, 0x08, 0x09, 0xf7 },
	{ 0xa0, 0xf3, 0xc4, 0xc1, 0x93, 0x89, 0x88, 0xe3, 0x80, 0x81, 0x7f }
};

/*-----------------------------------------------------------*/

void vDiceTask( void *pvParameters )
{
char cDiceState = diceSTATE_STOPPED;
unsigned char ucDiceValue, ucIndex;
unsigned long ulDice1RunTime, ulDiceDelay, ulDiceDelayReload;

	ucIndex = ( unsigned char ) pvParameters;

	for( ;; )
	{
		switch( cDiceState )
		{
			case diceSTATE_STOPPED:

				if( prvButtonHit( ucIndex ) == pdTRUE )
				{
					ulDice1RunTime = diceRUN_MIN;
					srand( ( unsigned char ) ulDice1RunTime );
					cDiceState = diceSTATE_STARTUP;
				}
				break;

			case diceSTATE_STARTUP:

				if( ulDice1RunTime < diceRUN_MAX )     // variable running time
				{
					ulDice1RunTime++;
				}
				else
				{
					ulDice1RunTime = diceRUN_MIN;
				}

				if( PDR00_P0 == 0 )              // Key SW2:INT8 released
				{
					ulDiceDelay    = 1;
					ulDiceDelayReload = 1;
					cDiceState = diceSTATE_RUNNING;
				}          
				break;

			case diceSTATE_RUNNING:

				ulDice1RunTime--;
				ulDiceDelay--;

				if( !ulDiceDelay )
				{
					ucDiceValue = rand() % 6 + 1;
					PDR03 = ( PDR03 | 0xf7 ) & cDisplaySegments[ ucIndex ][ ucDiceValue ];
					ulDiceDelayReload = ulDiceDelayReload + 100;
					ulDiceDelay = ulDiceDelayReload;
				}

				if( ulDice1RunTime == 0 )         // dice stopped
				{
					PDR03 = ( PDR03 | 0xf7 ) & cDisplaySegments[ ucIndex ][ rand() % 6 + 1 ];
					cDiceState = diceSTATE_STOPPED;
				}
				break;
		}
	}
}
/*-----------------------------------------------------------*/

static unsigned char prvButtonHit( unsigned char ucIndex )
{
	if( ( ucIndex == 0 ) && PDR00_P0 )
	{
		return pdTRUE;
	}
	else if( ( ucIndex == 1 ) && PDR00_P1 )
	{
		return pdTRUE;
	}
	else
	{
		return pdFALSE;
	}
}
/*-----------------------------------------------------------*/


#if 0
      
    // DICE 2
      
    switch (dice2state)
    {
      case 0x00: // dice2 stopped
                 if( PDR00_P1 == 1)              // Key SW3:INT9 pressed
                 {
                   dice2run = diceRUN_MIN;
                   srand((unsigned char)ulDice1RunTime);
                   dice2state = 0x01;
                 }

                 break;
                
      case 0x01: // dice2 startup
                 if( dice2run < diceRUN_MAX)     // variable running time
                   dice2run++;
                 else
                   dice2run = diceRUN_MIN;
            
                 if( dice2 == diceMAX)          // simple 'random' number
                   dice2 = diceMIN;
                 else dice2++;

                 if( PDR00_P1 == 0)              // Key SW3:INT9 released
                 {
                   dice2delay    = 1;
                   dice2delayrld = 1;
                   dice2state = 0x02;
                 }
                                  
                 break;

      case 0x02: // dice2 running
                 dice2run--;
                 dice2delay--;

                 if( !dice2delay)
                 {
                   do                       // get new random number
                   {
                    temp = rand() % 6 + 1;
                   }
                   while (temp == dice2);
                   dice2 = temp;
                   
                   PDR05 = DICE7SEG2[dice2];
                   dice2delayrld = dice2delayrld + 100;
                   dice2delay = dice2delayrld;
                 }

                 if( dice2run == 0)         // dice stopped
                 {
                   PDR05 = DICE7SEG2[rand() % 6 + 1];
                   dice2state = 0x00;
                 }

                 break;

    }//switch (dice2state)
    
  } // while(1)
#endif

