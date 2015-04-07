/**********************************************************************
* $Id$		lpc18xx_wwdt.c		2011-06-02
*//**
* @file		lpc18xx_wwdt.c
* @brief	Contains all functions support for WDT firmware library
* 			on LPC18xx
* @version	1.0
* @date		02. June. 2011
* @author	NXP MCU SW Application Team
*
* Copyright(C) 2011, NXP Semiconductor
* All rights reserved.
*
***********************************************************************
* Software that is described herein is for illustrative purposes only
* which provides customers with programming information regarding the
* products. This software is supplied "AS IS" without any warranties.
* NXP Semiconductors assumes no responsibility or liability for the
* use of the software, conveys no license or title under any patent,
* copyright, or mask work right to the product. NXP Semiconductors
* reserves the right to make changes in the software without
* notification. NXP Semiconductors also make no representation or
* warranty that such application will be suitable for the specified
* use without further testing or modification.
**********************************************************************/

/* Peripheral group ----------------------------------------------------------- */
/** @addtogroup WWDT
 * @{
 */

/* Includes ------------------------------------------------------------------- */
#include "lpc18xx_wwdt.h"

/* If this source file built with example, the LPC18xx FW library configuration
 * file in each example directory ("lpc18xx_libcfg.h") must be included,
 * otherwise the default FW library configuration file must be included instead
 */
#ifdef __BUILD_WITH_EXAMPLE__
#include "lpc18xx_libcfg.h"
#else
#include "lpc18xx_libcfg_default.h"
#endif /* __BUILD_WITH_EXAMPLE__ */


#ifdef _WWDT

void WWDT_SetTimeOut(uint32_t timeout);

/*********************************************************************//**
 * @brief 		Update WDT timeout value and feed
 * @param[in]	timeout	WDT timeout (us)
 * @return		none
 **********************************************************************/
void WWDT_SetTimeOut(uint32_t timeout)
{
	uint32_t timeoutVal;

	timeoutVal = WDT_GET_FROM_USEC(timeout);

	if(timeoutVal < WWDT_TIMEOUT_MIN)
	{
		timeoutVal = WWDT_TIMEOUT_MIN;
	}
	else if (timeoutVal > WWDT_TIMEOUT_MAX)
	{
		timeoutVal = WWDT_TIMEOUT_MAX;
	}

	LPC_WWDT->TC = timeoutVal;
}
/* Public Functions ----------------------------------------------------------- */
/** @addtogroup WDT_Public_Functions
 * @{
 */

/*********************************************************************//**
* @brief 		Initial for Watchdog function
* @param[in]	none
* @return 		None
 **********************************************************************/
void WWDT_Init(void)
{
	LPC_WWDT->MOD 	= 0;					// Clear time out and interrupt flags
	LPC_WWDT->TC 	= WWDT_TIMEOUT_MIN; 	// Reset time out
	LPC_WWDT->WARNINT= 0;					// Reset warning value
	LPC_WWDT->WINDOW = WWDT_WINDOW_MAX;		// Reset window value
}

/********************************************************************//**
 * @brief 		Update WDT timeout value and feed
 * @param[in]	TimeOut	TimeOut value to be updated, should be in range:
 * 				2048 .. 134217728
 * @return		None
 *********************************************************************/
void WDT_UpdateTimeOut(uint32_t TimeOut)
{
	/* check WDPROTECT,
	 * if it is enable, wait until the counter is below the value of
	 * WDWARNINT and WDWINDOW
	 */
	if(LPC_WWDT->MOD & (1<<4))
	{
		while((LPC_WWDT->TV <(LPC_WWDT->WARNINT & WWDT_WDWARNINT_MASK))\
						&&(LPC_WWDT->TV <(LPC_WWDT->WINDOW & WWDT_WDTC_MASK)));
	}

	WWDT_SetTimeOut(TimeOut);
}
/********************************************************************//**
 * @brief 		After set WDTEN, call this function to start Watchdog
 * 				or reload the Watchdog timer
 * @param[in]	None
 * @return		None
 *********************************************************************/
void WWDT_Feed (void)
{
	LPC_WWDT->FEED = 0xAA;

	LPC_WWDT->FEED = 0x55;
}

/********************************************************************//**
 * @brief 		Update WDT timeout value and feed
 * @param[in]	WarnTime	time to generate watchdog warning interrupt(us)
 * 				should be in range: 2048 .. 8192
 * @return		None
 *********************************************************************/
void WWDT_SetWarning(uint32_t WarnTime)
{
	uint32_t warnVal;

	warnVal = WDT_GET_FROM_USEC(WarnTime);

	if(warnVal <= WWDT_WARNINT_MIN)
	{
		warnVal = WWDT_WARNINT_MIN;
	}
	else if (warnVal >= WWDT_WARNINT_MAX)
	{
		warnVal = WWDT_WARNINT_MAX;
	}

	LPC_WWDT->WARNINT = warnVal;
}

/********************************************************************//**
 * @brief 		Update WDT timeout value and feed
 * @param[in]	WindowedTime	expected time to set watchdog window event(us)
 * @return		none
 *********************************************************************/
void WWDT_SetWindow(uint32_t WindowedTime)
{
	uint32_t wndVal;

	wndVal = WDT_GET_FROM_USEC(WindowedTime);

	if(wndVal <= WWDT_WINDOW_MIN)
	{
		wndVal = WWDT_WINDOW_MIN;
	}
	else if (wndVal >= WWDT_WINDOW_MAX)
	{
		wndVal = WWDT_WINDOW_MAX;
	}

	LPC_WWDT->WINDOW = wndVal;
}
/*********************************************************************//**
* @brief 		Enable/Disable WWDT activity
* @param[in]	None
* @return 		None
 **********************************************************************/
void WWDT_Configure(st_Wdt_Config wdtCfg)
{
	WWDT_SetTimeOut(wdtCfg.wdtTmrConst);

	if(wdtCfg.wdtReset)
	{
		LPC_WWDT->MOD |= WWDT_WDMOD_WDRESET;
	}
	else
	{
		LPC_WWDT->MOD &= ~WWDT_WDMOD_WDRESET;
	}

	if(wdtCfg.wdtProtect)
	{
		LPC_WWDT->MOD |= WWDT_WDMOD_WDPROTECT;
	}
	else
	{
		LPC_WWDT->MOD &= ~WWDT_WDMOD_WDPROTECT;
	}
}

/*********************************************************************//**
* @brief 		Enable WWDT activity
* @param[in]	None
* @return 		None
 **********************************************************************/
void WWDT_Start(void)
{
	LPC_WWDT->MOD |= WWDT_WDMOD_WDEN;
	WWDT_Feed();
}

/********************************************************************//**
 * @brief 		Read WWDT status flag
 * @param[in]	Status kind of status flag that you want to get, should be:
 * 				- WWDT_WARNINT_FLAG: watchdog interrupt flag
 * 				- WWDT_TIMEOUT_FLAG: watchdog time-out flag
 * @return		Time out flag status of WDT
 *********************************************************************/
FlagStatus WWDT_GetStatus (uint8_t Status)
{
	if(Status == WWDT_WARNINT_FLAG)
	{
		return ((FlagStatus)(LPC_WWDT->MOD & (1<<3)));
	}
	else if (Status == WWDT_TIMEOUT_FLAG)
	{
		return ((FlagStatus)(LPC_WWDT->MOD & (1<<2)));
	}
	return (FlagStatus)RESET;
}

/********************************************************************//**
 * @brief 		Read WWDT status flag
 * @param[in]	Status kind of status flag that you want to get, should be:
 * 				- WWDT_WARNINT_FLAG: watchdog interrupt flag
 * 				- WWDT_TIMEOUT_FLAG: watchdog time-out flag
 * @return		Time out flag status of WDT
 *********************************************************************/
void WWDT_ClearStatusFlag (uint8_t flag)
{
	if(flag == WWDT_WARNINT_FLAG)
	{
		// Write 1 to this bit to clear itself
		LPC_WWDT->MOD |= WWDT_WDMOD_WDINT;
	}
	else if(flag == WWDT_TIMEOUT_FLAG)
	{
		// Write 0 to this bit to clear itself
		LPC_WWDT->MOD &= ~ WWDT_WDMOD_WDTOF;
	}
}

/********************************************************************//**
 * @brief 		Get the current value of WDT
 * @param[in]	None
 * @return		current value of WDT
 *********************************************************************/
uint32_t WWDT_GetCurrentCount(void)
{
	return LPC_WWDT->TV;
}

/**
 * @}
 */

#endif /* _WWDT */
/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
