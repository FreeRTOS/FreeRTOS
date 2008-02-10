/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
/* ELIGIBILITY FOR ANY PURPOSES.											 */
/*				 (C) Fujitsu Microelectronics Europe GmbH				  */
/*------------------------------------------------------------------------
  MAIN.C
  - description
  - See README.TXT for project description and disclaimer.
-------------------------------------------------------------------------*/
/*************************@INCLUDE_START************************/


/* TODO: Add comment here regarding the behaviour of the demo. */


/* Hardware specific includes. */
#include "mb91467d.h"

/* Scheduler includes. */
#include "FreeRTOS.h"


static unsigned portSHORT sState[ ledNUMBER_OF_LEDS ] = { pdFALSE };
static unsigned portSHORT sState1[ ledNUMBER_OF_LEDS ] = { pdFALSE };

/*-----------------------------------------------------------*/
static void vPartestInitialise( void )
{
	DDR16=0xFF;
	DDR25=0xFF;
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if (uxLED < ledNUMBER_OF_LEDS)
	{
		vTaskSuspendAll();
		
		/* Toggle the state of the single genuine on board LED. */
		if( sState[uxLED])	
		{
			PDR25 |= (1 << uxLED);
		}
		else
		{
			PDR25 &= ~(1 << uxLED);
		}
	
		sState[uxLED] = !(sState[uxLED]);
		
		xTaskResumeAll();
	}
	else
	{
		uxLED -= ledNUMBER_OF_LEDS;
		
		vTaskSuspendAll();
		
		/* Toggle the state of the single genuine on board LED. */
		if( sState1[uxLED])	
		{
			PDR16 |= (1 << uxLED);
		}
		else
		{
			PDR16 &= ~(1 << uxLED);
		}
	
		sState1[uxLED] = !(sState1[uxLED]);
		
		xTaskResumeAll();
	}
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	/* Set or clear the output [in this case show or hide the '*' character. */
	if( uxLED < ledNUMBER_OF_LEDS )
	{
		vTaskSuspendAll();
		{
			if( xValue )
			{
				PDR25 |= (1 << uxLED);
				sState[uxLED] = 1;
			}
			else
			{
				PDR25 &= ~(1 << uxLED);
				sState[uxLED] = 0;
			}
		}
		xTaskResumeAll();
	}
	else 
	{
		uxLED -= ledNUMBER_OF_LEDS;
		vTaskSuspendAll();
		{
			if( xValue )
			{
				PDR16 |= (1 << uxLED);
				sState1[uxLED] = 1;
			}
			else
			{
				PDR16 &= ~(1 << uxLED);
				sState1[uxLED] = 0;
			}
		}
		xTaskResumeAll();
	}
}
/*-----------------------------------------------------------*/

