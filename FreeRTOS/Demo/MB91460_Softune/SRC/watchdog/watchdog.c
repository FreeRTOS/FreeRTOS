/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
/* ELIGIBILITY FOR ANY PURPOSES.											 */
/*				 (C) Fujitsu Microelectronics Europe GmbH				  */
/*------------------------------------------------------------------------
  watchdog.c
  - This file contains the function deefinition for hardware watchdog.
-------------------------------------------------------------------------*/

#include "mb91467d.h"
#include "FreeRTOS.h"
#include "task.h"
#include "watchdog.h"

/*---------------------------------------------------------------------------
 * Setup Watchdog
 *---------------------------------------------------------------------------*/
#if WATCHDOG != WTC_NONE
void InitWatchdog(void)
{
	HWWDE_ED = WTC_PER_2_16;	/* Set the watchdog period as 655.36 ms */
}
#endif

/*---------------------------------------------------------------------------
 * The below task clears the watchdog and blocks itself for WTC_CLR_PER ticks.
 *---------------------------------------------------------------------------*/
#if WATCHDOG == WTC_IN_TASK
static void prvWatchdogTask	( void *pvParameters )
{
 	const portTickType xFrequency = WTC_CLR_PER;
	portTickType xLastWakeTime;

	/* Get currrent tick count */
	xLastWakeTime = xTaskGetTickCount();

	for( ; ; )
	{
		Kick_Watchdog();

		/* Block the task for WTC_CLR_PER ticks (300 ms) at watchdog overflow
		period of WTC_PER_2_16 CLKRC cycles (655.36 ms) */
		vTaskDelayUntil( &xLastWakeTime, xFrequency );
	}
}
#endif

/*---------------------------------------------------------------------------
 * The below function creates hardware watchdog task.
 *---------------------------------------------------------------------------*/
#if WATCHDOG == WTC_IN_TASK
void vStartWatchdogTask( unsigned short uxPriority )
{
	xTaskCreate( prvWatchdogTask , "KickWTC",   portMINIMAL_STACK_SIZE, ( void * ) NULL, uxPriority, ( xTaskHandle * ) NULL );
}
#endif
