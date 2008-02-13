/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
/* ELIGIBILITY FOR ANY PURPOSES.                                             */
/*                 (C) Fujitsu Microelectronics Europe GmbH                  */

/*------------------------------------------------------------------------
  watchdog.c
  - This file contains the function deefinition for hardware watchdog.
-------------------------------------------------------------------------*/
#include "mb96348hs.h"
#include "FreeRTOS.h"
#include "task.h"
#include "watchdog.h"

/*---------------------------------------------------------------------------
 * Setup Watchdog
 *---------------------------------------------------------------------------*/
#if WATCHDOG != WTC_NONE
void InitWatchdog( void )
{
	WDTC_WTI = WTC_PER_2_23;	/* 2^23/CLKWT */
	WDTC_WTCS = WTC_CLKMC;		/* CLKWT=CLKMC, Watchdog expiration delay = 2.097s @ 4MHZ CLKMC*/
	WDTCP = 0x00;				/* Activate Watchdog, Clear Pattern 0x00 */
}

#endif

/*---------------------------------------------------------------------------
 * The below task clears the watchdog and blocks itself for WTC_CLR_PER ticks.
 *---------------------------------------------------------------------------*/
#if WATCHDOG == WTC_IN_TASK
static void prvWatchdogTask( void *pvParameters )
{
	const portTickType	xFrequency = WTC_CLR_PER;
	portTickType		xLastWakeTime;
	( void ) pvParameters;

	/* Get currrent tick count */
	xLastWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Get currrent tick count */
		xLastWakeTime = xTaskGetTickCount();

		Kick_Watchdog();

		/* Block the task for WTC_CLR_PER ticks (1s) at watchdog overflow period of WTC_PER_2_23 CLKMC cycles */
		vTaskDelayUntil( &xLastWakeTime, xFrequency );
	}
}

#endif

/*---------------------------------------------------------------------------
 * The below function creates hardware watchdog task.
 *---------------------------------------------------------------------------*/
#if WATCHDOG == WTC_IN_TASK
void vStartWatchdogTask( unsigned portBASE_TYPE uxPriority )
{
	xTaskCreate( prvWatchdogTask, (signed portCHAR *) "KickWTC", portMINIMAL_STACK_SIZE, ( void * ) NULL, uxPriority, ( xTaskHandle * ) NULL );
}

#endif
