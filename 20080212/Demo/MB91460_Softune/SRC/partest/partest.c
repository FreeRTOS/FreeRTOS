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



/* Hardware specific includes. */
#include "mb91467d.h"

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

#define partstNUM_LEDs	8

static unsigned portSHORT sState[ partstNUM_LEDs ] = { pdFALSE };

/*-----------------------------------------------------------*/
void vParTestInitialise( void )
{
	/* Set port for LED outputs. */
	DDR16 = 0xFF;

	/* Start with LEDs off. */
	PDR25 = 0x00;
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstNUM_LEDs )
	{
		taskENTER_CRITICAL();
		
		/* Toggle the state of the single genuine on board LED. */
		if( sState[ uxLED ])	
		{
			PDR25 |= ( 1 << uxLED );
		}
		else
		{
			PDR25 &= ~( 1 << uxLED );
		}
	
		sState[ uxLED ] = !( sState[ uxLED ] );
		
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	/* Set or clear the output [in this case show or hide the '*' character. */
	if( uxLED < partstNUM_LEDs )
	{
		taskENTER_CRITICAL();
		{
			if( xValue )
			{
				PDR25 |= ( 1 << uxLED );
				sState[ uxLED ] = 1;
			}
			else
			{
				PDR25 &= ~( 1 << uxLED );
				sState[ uxLED ] = 0;
			}
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

