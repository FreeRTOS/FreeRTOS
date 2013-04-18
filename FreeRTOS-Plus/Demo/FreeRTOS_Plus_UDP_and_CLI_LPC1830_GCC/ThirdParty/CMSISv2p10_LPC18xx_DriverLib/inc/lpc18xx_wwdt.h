/**********************************************************************
* $Id$		lpc18xx_wwdt.h		2011-06-02
*//**
* @file		lpc18xx_wwdt.h
* @brief	Contains all macro definitions and function prototypes
* 			support for WWDT firmware library on LPC18xx
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
/** @defgroup WWDT	WWDT (Windowed WatchDog Timer)
 * @ingroup LPC1800CMSIS_FwLib_Drivers
 * @{
 */


#ifndef LPC18XX_WWDT_H_
#define LPC18XX_WWDT_H_

/* Includes ------------------------------------------------------------------- */
#include "LPC18xx.h"
#include "lpc_types.h"


#ifdef __cplusplus
extern "C"
{
#endif

/* Public Macros -------------------------------------------------------------- */
/** @defgroup WWDT_Public_Macros  WWDT Public Macros
 * @{
 */
/** WDT oscillator frequency value */
#define WDT_OSC		(12000000UL)		/* WWDT uses IRC clock */

/**
 * @}
 */


/* Private Macros ------------------------------------------------------------- */
/** @defgroup WWDT_Private_Macros WWDT Private Macros
 * @{
 */
// time is calculated by usec
#define WDT_GET_FROM_USEC(time)		((time*10)/((WWDT_US_INDEX *10 * 4)/WDT_OSC))
#define WDT_GET_USEC(counter)		((counter * ((WWDT_US_INDEX *10 * 4)/WDT_OSC))/10)


/* --------------------- BIT DEFINITIONS -------------------------------------- */
/** WWDT interrupt enable bit */
#define WWDT_WDMOD_WDEN			    ((uint32_t)(1<<0))
/** WWDT interrupt enable bit */
#define WWDT_WDMOD_WDRESET			((uint32_t)(1<<1))
/** WWDT time out flag bit */
#define WWDT_WDMOD_WDTOF			((uint32_t)(1<<2))
/** WDT Time Out flag bit */
#define WWDT_WDMOD_WDINT			((uint32_t)(1<<3))
/** WWDT Protect flag bit */
#define WWDT_WDMOD_WDPROTECT		((uint32_t)(1<<4))

/** Define divider index for microsecond ( us ) */
#define WWDT_US_INDEX		((uint32_t)(1000000))

/** WWDT Time out minimum value */
#define WWDT_TIMEOUT_MIN	((uint32_t)(0xFF))
/** WWDT Time out maximum value */
#define WWDT_TIMEOUT_MAX	((uint32_t)(0x00FFFFFF))

/** WWDT Warning minimum value */
#define WWDT_WARNINT_MIN	((uint32_t)(0xFF))
/** WWDT Warning maximum value */
#define WWDT_WARNINT_MAX	((uint32_t)(0x000003FF))

/** WWDT Windowed minimum value */
#define WWDT_WINDOW_MIN		((uint32_t)(0xFF))
/** WWDT Windowed minimum value */
#define WWDT_WINDOW_MAX		((uint32_t)(0x00FFFFFF))

/** WWDT timer constant register mask */
#define WWDT_WDTC_MASK			((uint32_t)(0x00FFFFFF))
/** WWDT warning value register mask */
#define WWDT_WDWARNINT_MASK		((uint32_t)(0x000003FF))
/** WWDT feed sequence register mask */
#define WWDT_WDFEED_MASK 		((uint32_t)(0x000000FF))

/** WWDT flag */
#define WWDT_WARNINT_FLAG		((uint8_t)(0))
#define WWDT_TIMEOUT_FLAG		((uint8_t)(1))

/** WWDT mode definitions */
#define WWDT_PROTECT_MODE		((uint8_t)(0))
#define WWDT_RESET_MODE			((uint8_t)(1))


/* WWDT Timer value definition (us) */
#define WWDT_TIMEOUT_USEC_MIN			((uint32_t)(WDT_GET_USEC(WWDT_TIMEOUT_MIN)))//microseconds
#define WWDT_TIMEOUT_USEC_MAX			((uint32_t)(WDT_GET_USEC(WWDT_TIMEOUT_MAX)))

#define WWDT_TIMEWARN_USEC_MIN			((uint32_t)(WDT_GET_USEC(WWDT_WARNINT_MIN)))
#define WWDT_TIMEWARN_USEC_MAX			((uint32_t)(WDT_GET_USEC(WWDT_WARNINT_MAX)))

#define WWDT_TIMEWINDOWED_USEC_MIN		((uint32_t)(WDT_GET_USEC(WWDT_WINDOW_MIN)))
#define WWDT_TIMEWINDOWED_USEC_MAX		((uint32_t)(WDT_GET_USEC(WWDT_WINDOW_MAX)))


/**
 * @}
 */

/* Public Types --------------------------------------------------------------- */
/** @defgroup WWDT_Public_Types WWDT Public Types
 * @{
 */
/********************************************************************//**
 * @brief WWDT structure definitions
 **********************************************************************/
typedef struct Wdt_Config
{
	uint8_t wdtReset;			/**< if ENABLE -> the Reset bit is enabled				*/
	uint8_t wdtProtect;			/**< if ENABLE -> the Protect bit is enabled			*/
	uint32_t wdtTmrConst;		/**< Set the constant value to timeout the WDT (us)		*/
	uint32_t wdtWarningVal;		/**< Set the value to warn the WDT with interrupt (us)	*/
	uint32_t wdtWindowVal;		/**< Set a window vaule for WDT (us)					*/
}st_Wdt_Config;

/**
 * @}
 */

/* Public Functions ----------------------------------------------------------- */
/** @defgroup WWDT_Public_Functions WWDT Public Functions
 * @{
 */

void WWDT_Init(void);
void WWDT_UpdateTimeOut(uint32_t TimeOut);
void WWDT_Feed (void);
void WWDT_SetWarning(uint32_t WarnTime);
void WWDT_SetWindow(uint32_t WindowedTime);
void WWDT_Configure(st_Wdt_Config wdtCfg);
void WWDT_Start(void);
FlagStatus WWDT_GetStatus (uint8_t Status);
void WWDT_ClearStatusFlag (uint8_t flag);
uint32_t WWDT_GetCurrentCount(void);
/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* LPC18XX_WWDT_H_ */

/**
 * @}
 */
/* --------------------------------- End Of File ------------------------------ */
