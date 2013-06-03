/*
 * @brief	Windowed Watchdog Timer Registers and functions
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * All rights reserved.
 *
 * @par
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licensor disclaim any and
 * all warranties, express or implied, including all implied warranties of
 * merchantability, fitness for a particular purpose and non-infringement of
 * intellectual property rights.  NXP Semiconductors assumes no responsibility
 * or liability for the use of the software, conveys no license or rights under any
 * patent, copyright, mask work right, or any other intellectual property rights in
 * or to any products. NXP Semiconductors reserves the right to make changes
 * in the software without notification. NXP Semiconductors also makes no
 * representation or warranty that such application will be suitable for the
 * specified use without further testing or modification.
 *
 * @par
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
 */

#ifndef __WWDT_001_H_
#define __WWDT_001_H_

#include "sys_config.h"
#include "cmsis.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup IP_WWDT_001 IP: WWDT register block and driver
 * @ingroup IP_Drivers
 * Windowed Watchdog
 * @{
 */
#if !defined(CHIP_LPC175X_6X) && !defined(CHIP_LPC11CXX) && !defined(CHIP_LPC1343)
#define WATCHDOG_WINDOW_SUPPORT
#endif

#if defined(CHIP_LPC11AXX) || defined(CHIP_LPC11EXX) || defined(CHIP_LPC11UXX) || defined(CHIP_LPC175X_6X) \
	|| defined(CHIP_LPC1347)
#define WATCHDOG_CLKSEL_SUPPORT
#endif

/**
 * @brief Windowed Watchdog register block structure
 */
typedef struct {				/*!< WWDT Structure         */
	__IO uint32_t  MOD;			/*!< Watchdog mode register. This register contains the basic mode and status of the Watchdog Timer. */
	__IO uint32_t  TC;			/*!< Watchdog timer constant register. This register determines the time-out value. */
	__O  uint32_t  FEED;		/*!< Watchdog feed sequence register. Writing 0xAA followed by 0x55 to this register reloads the Watchdog timer with the value contained in WDTC. */
	__I  uint32_t  TV;			/*!< Watchdog timer value register. This register reads out the current value of the Watchdog timer. */
#ifdef WATCHDOG_CLKSEL_SUPPORT
	__IO uint32_t CLKSEL;		/*!< Watchdog clock select register. */
#else
	__I  uint32_t  RESERVED0;
#endif
#ifdef WATCHDOG_WINDOW_SUPPORT
	__IO uint32_t  WARNINT;		/*!< Watchdog warning interrupt register. This register contains the Watchdog warning interrupt compare value. */
	__IO uint32_t  WINDOW;		/*!< Watchdog timer window register. This register contains the Watchdog window value. */
#endif
} IP_WWDT_001_T;

/**
 * @brief Watchdog Mode register definitions
 */
/** Watchdog Mode Bitmask */
#define WWDT_WDMOD_BITMASK          ((uint32_t) 0x1F)
/** WWDT interrupt enable bit */
#define WWDT_WDMOD_WDEN             ((uint32_t) (1 << 0))
/** WWDT interrupt enable bit */
#define WWDT_WDMOD_WDRESET          ((uint32_t) (1 << 1))
/** WWDT time out flag bit */
#define WWDT_WDMOD_WDTOF            ((uint32_t) (1 << 2))
/** WDT Time Out flag bit */
#define WWDT_WDMOD_WDINT            ((uint32_t) (1 << 3))
#if !defined(CHIP_LPC175X_6X)
/** WWDT Protect flag bit */
#define WWDT_WDMOD_WDPROTECT        ((uint32_t) (1 << 4))
#endif
#if defined(WATCHDOG_CLKSEL_SUPPORT)
/**
 * @brief Watchdog Timer Clock Source Selection register definitions
 */
/** Clock source select bitmask */
#define WWDT_CLKSEL_BITMASK         ((uint32_t) 0x10000003)
/** Clock source select */
#define WWDT_CLKSEL_SOURCE(n)       ((uint32_t) (n & 0x03))
/** Lock the clock source selection */
#define WWDT_CLKSEL_LOCK            ((uint32_t) (1 << 31))
#endif /* defined(WATCHDOG_CLKSEL_SUPPORT) */

/**
 * @brief	Initialize the Watchdog Timer
 * @param	pWWDT	: pointer to WWDT register block
 * @return	None
 */
void IP_WWDT_Init(IP_WWDT_001_T *pWWDT);

/**
 * @brief	De-initialize the Watchdog Timer
 * @param	pWWDT	: pointer to WWDT register block
 * @return	None
 */
STATIC INLINE void IP_WWDT_DeInit(IP_WWDT_001_T *pWWDT)
{}

/**
 * @brief	Set WDT timeout constant value used for feed
 * @param	pWWDT	: pointer to WWDT register block
 * @param	timeout	: WDT timeout in ticks
 * @return	none
 */
STATIC INLINE void IP_WWDT_SetTimeOut(IP_WWDT_001_T *pWWDT, uint32_t timeout)
{
	pWWDT->TC = timeout;
}

#if defined(WATCHDOG_CLKSEL_SUPPORT)
/**
 * @brief	Clock selection for Watchdog Timer
 * @param	pWWDT	: pointer to WWDT register block
 * @param	src	: Clock source selection (Or-ed value of WWDT_CLKSEL_*)
 * @return	none
 */
STATIC INLINE void IP_WWDT_SelClockSource(IP_WWDT_001_T *pWWDT, uint32_t src)
{
	pWWDT->CLKSEL = src & WWDT_CLKSEL_BITMASK;
}

#endif /*WATCHDOG_CLKSEL_SUPPORT*/

/**
 * @brief	Feed watchdog timer
 * @param	pWWDT	: pointer to WWDT register block
 * @return	None
 * @note	If this function isn't called, a watchdog timer warning will occur.
 * After the warning, a timeout will occur if a feed has happened.
 */
STATIC INLINE void IP_WWDT_Feed(IP_WWDT_001_T *pWWDT)
{
	pWWDT->FEED = 0xAA;
	pWWDT->FEED = 0x55;
}

#if defined(WATCHDOG_WINDOW_SUPPORT)
/**
 * @brief	Set WWDT warning interrupt
 * @param	pWWDT	: pointer to WWDT register block
 * @param	timeout	: WDT warning in ticks, between 0 and 1023
 * @return	None
 * @note	This is the number of ticks after the watchdog interrupt that the
 * warning interrupt will be generated.
 */
STATIC INLINE void IP_WWDT_SetWarning(IP_WWDT_001_T *pWWDT, uint32_t timeout)
{
	pWWDT->WARNINT = timeout;
}

/**
 * @brief	Set WWDT window time
 * @param	pWWDT	: pointer to WWDT register block
 * @param	timeout	: WDT timeout in ticks
 * @return	none
 * @note	The watchdog timer must be fed between the timeout from the IP_WWDT_SetTimeOut()
 * function and this function, with this function defining the last tick before the
 * watchdog window interrupt occurs.
 */
STATIC INLINE void IP_WWDT_SetWindow(IP_WWDT_001_T *pWWDT, uint32_t timeout)
{
	pWWDT->WINDOW = timeout;
}

#endif /* defined(WATCHDOG_WINDOW_SUPPORT) */

/**
 * @brief	Enable watchdog timer options
 * @param	pWWDT	: pointer to WWDT register block
 * @param	options : An or'ed set of options of values
 *						WWDT_WDMOD_WDEN, WWDT_WDMOD_WDRESET, and WWDT_WDMOD_WDPROTECT
 * @return	None
 * @note	You can enable more than one option at once (ie, WWDT_WDMOD_WDRESET |
 * WWDT_WDMOD_WDPROTECT), but use the WWDT_WDMOD_WDEN after all other options
 * are set (or unset) with no other options.
 */
STATIC INLINE void IP_WWDT_SetOption(IP_WWDT_001_T *pWWDT, uint32_t options)
{
	pWWDT->MOD |= options;
}

/**
 * @brief	Disable/clear watchdog timer options
 * @param	pWWDT	: pointer to WWDT register block
 * @param	options : An or'ed set of options of values
 *						WWDT_WDMOD_WDEN, WWDT_WDMOD_WDRESET, and WWDT_WDMOD_WDPROTECT
 * @return	None
 * @note	You can disable more than one option at once (ie, WWDT_WDMOD_WDRESET |
 * WWDT_WDMOD_WDTOF).
 */
STATIC INLINE void IP_WWDT_UnsetOption(IP_WWDT_001_T *pWWDT, uint32_t options)
{
	pWWDT->MOD &= (~options) & WWDT_WDMOD_BITMASK;
}

/**
 * @brief	Enable WWDT activity
 * @param	pWWDT	: pointer to WWDT register block
 * @return	None
 */
STATIC INLINE void IP_WWDT_Start(IP_WWDT_001_T *pWWDT)
{
	IP_WWDT_SetOption(pWWDT, WWDT_WDMOD_WDEN);
	IP_WWDT_Feed(pWWDT);
}

/**
 * @brief	Read WWDT status flag
 * @param	pWWDT	: pointer to WWDT register block
 * @return	Watchdog status, an Or'ed value of WWDT_WDMOD_*
 */
STATIC INLINE uint32_t IP_WWDT_GetStatus(IP_WWDT_001_T *pWWDT)
{
	return pWWDT->MOD;
}

/**
 * @brief	Clear WWDT interrupt status flags
 * @param	pWWDT	: pointer to WWDT register block
 * @param	status	: Or'ed value of status flag(s) that you want to clear, should be:
 *              - WWDT_WDMOD_WDTOF: Clear watchdog timeout flag
 *              - WWDT_WDMOD_WDINT: Clear watchdog warning flag
 * @return	None
 */
void IP_WWDT_ClearStatusFlag(IP_WWDT_001_T *pWWDT, uint32_t status);

/**
 * @brief	Get the current value of WDT
 * @return	current value of WDT
 */
STATIC INLINE uint32_t IP_WWDT_GetCurrentCount(IP_WWDT_001_T *pWWDT)
{
	return pWWDT->TV;
}

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __WWDT_001_H_ */
