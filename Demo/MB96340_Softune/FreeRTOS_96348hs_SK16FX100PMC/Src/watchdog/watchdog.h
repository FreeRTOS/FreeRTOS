/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
/* ELIGIBILITY FOR ANY PURPOSES.                                             */
/*                 (C) Fujitsu Microelectronics Europe GmbH                  */
/*------------------------------------------------------------------------
  watchdog.h
  - This file contains the defines and function declaration for hardware watchdog.
-------------------------------------------------------------------------*/
/* 
 * Clear watchdog defines 
 */
#define	WTC_NONE	0		/* Don't initialize and clear watchdog */
#define	WTC_IN_TASK	1		/* Clear Watchdog in dedicated task */
#define	WTC_IN_TICK	2		/* Clear Watchdog in TICK Hook */
#define	WTC_IN_IDLE	3		/* Clear Watchdog in Idle Hook */

#define WATCHDOG WTC_IN_TASK	/* Clear Watchdog in vWatchdogTask() */
/*------------------------------------------------------------------------*/
/* 
 * Watchdog period defines
 */
#define	WTC_PER_2_9		0	/* The watchdog period is 2^9/CLKWT */
#define	WTC_PER_2_10	1	/* The watchdog period is 2^10/CLKWT */
#define	WTC_PER_2_11	2	/* The watchdog period is 2^11/CLKWT */
#define	WTC_PER_2_12	3	/* The watchdog period is 2^12/CLKWT */
#define	WTC_PER_2_13	4	/* The watchdog period is 2^13/CLKWT */
#define	WTC_PER_2_14	5	/* The watchdog period is 2^14/CLKWT */
#define	WTC_PER_2_15	6	/* The watchdog period is 2^15/CLKWT */
#define	WTC_PER_2_16	7	/* The watchdog period is 2^16/CLKWT */
#define	WTC_PER_2_17	8	/* The watchdog period is 2^17/CLKWT */
#define	WTC_PER_2_18	9	/* The watchdog period is 2^18/CLKWT */
#define	WTC_PER_2_19	10	/* The watchdog period is 2^19/CLKWT */
#define	WTC_PER_2_20	11	/* The watchdog period is 2^20/CLKWT */
#define	WTC_PER_2_21	12	/* The watchdog period is 2^21/CLKWT */
#define	WTC_PER_2_22	13	/* The watchdog period is 2^22/CLKWT */
#define	WTC_PER_2_23	14	/* The watchdog period is 2^23/CLKWT */
#define	WTC_PER_2_24	15	/* The watchdog period is 2^24/CLKWT */
/*------------------------------------------------------------------------*/
/* 
 * Watchdog Clock source defines
 */
#define	WTC_CLKRC0		0	/* The watchdog clock is CLKRC */
#define	WTC_CLKRC1		1	/* The watchdog clock is CLKRC, 
							   changing RC clock while watchdog opeation causes reset */
#define	WTC_CLKMC		2	/* The watchdog clock is CLKMC */
#define	WTC_CLKSC		3	/* The watchdog clock is CLKSC */
/*------------------------------------------------------------------------*/
/* 
 * Watchdog Reset at transition to Stop mode defines
 */
#define	WTC_RSTP_0		0	/* No watchdog reset at transition to Stop mode */
#define	WTC_RSTP_1		1	/* watchdog reset at transition to Stop mode */ 
/*------------------------------------------------------------------------*/
/* 
 * After every WTC_CLR_PER ticks the watchdog would be cleared in the prvWatchdogTask(). 
 * This period needs to be chosed in accordance with the current CLKWT and the above 
 * setting WTC_PER_2_XX.
 */
#define	WTC_CLR_PER		100 /* The watchdog clear period in RTOS ticks */
/*------------------------------------------------------------------------*/
/* 
 * Kick_watchdog Macro to clear watchdog 
 */
#define Kick_Watchdog()							\
	{		WDTCP = 0x00;						\
	}
/*------------------------------------------------------------------------*/
/* 
 * Watchdog function declarations 
 */
void InitWatchdog (void);
void vStartWatchdogTask(unsigned portBASE_TYPE uxPriority);

