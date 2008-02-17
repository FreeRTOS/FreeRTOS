/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
/* ELIGIBILITY FOR ANY PURPOSES.                                             */
/*                 (C) Fujitsu Microelectronics Europe GmbH                  */
/*------------------------------------------------------------------------
  watchdog.h
  - This file contains the defines and function declaration for hardware watchdog.
-------------------------------------------------------------------------*/

#ifndef WATCHDOG_H
#define WATCHDOG_H

/* 
 * Clear watchdog defines 
 */
#define	WTC_NONE	0		/* Don't initialize and clear watchdog */
#define	WTC_IN_TASK	1		/* Clear Watchdog in dedicated task */
#define	WTC_IN_TICK	2		/* Clear Watchdog in TICK Hook */
#define	WTC_IN_IDLE	3		/* Clear Watchdog in Idle Hook */

#define WATCHDOG WTC_NONE	/* Clear Watchdog in vWatchdogTask() */
/*------------------------------------------------------------------------*/
/* 
 * Watchdog period defines
 */
#define	WTC_PER_2_16	0	/* The watchdog period is 2^16 CLKRC cycles */
#define	WTC_PER_2_17	1	/* The watchdog period is 2^17 CLKRC cycles */
#define	WTC_PER_2_18	2	/* The watchdog period is 2^18 CLKRC cycles */
#define	WTC_PER_2_19	3	/* The watchdog period is 2^19 CLKRC cycles */
/*------------------------------------------------------------------------*/
/* 
 * After every WTC_CLR_PER ticks the watchdog would be cleared in the prvWatchdogTask(). 
 * This period needs to be chosen in accordance with the current CLKRC (100KHz or 2MHz)
 * and the above setting WTC_PER_2_XX.
 */
#define	WTC_CLR_PER		30	/* The watchdog clear period in RTOS ticks */
/*------------------------------------------------------------------------*/
/* 
 * Kick_watchdog Macro to clear watchdog 
 */
#define Kick_Watchdog()							\
	{		HWWD = 0x10;						\
	}
/*------------------------------------------------------------------------*/
/* 
 * Watchdog function declarations 
 */
void InitWatchdog (void);
void vStartWatchdogTask(unsigned portSHORT);

#endif

