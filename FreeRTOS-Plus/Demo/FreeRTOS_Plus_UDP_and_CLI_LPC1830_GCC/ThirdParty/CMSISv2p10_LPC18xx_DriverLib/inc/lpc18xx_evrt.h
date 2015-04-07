/**********************************************************************
* $Id$		lpc18xx_evrt.h			2011-06-02
*//**
* @file		lpc18xx_evrt.h
* @brief	Contains all macro definitions and function prototypes
* 			support for Event Router firmware library on LPC18xx
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
/** @defgroup EVRT EVRT (Event Router)
 * @ingroup LPC1800CMSIS_FwLib_Drivers
 * @{
 */

#ifndef LPC18XX_EVRT_H_
#define LPC18XX_EVRT_H_

/* Includes ------------------------------------------------------------------- */
#include "LPC18xx.h"
#include "lpc_types.h"


#ifdef __cplusplus
extern "C"
{
#endif


/* Private Macros ------------------------------------------------------------- */
/** @defgroup EVRT_Private_Macros EVRT Private Macros
 * @{
 */

/* ---------------- CHECK PARAMETER DEFINITIONS ---------------------------- */
/** Macro to determine if it is valid EVRT peripheral */
#define PARAM_EVRTx(x)	(((uint32_t *)x)==((uint32_t *)LPC_EVENTROUTER))

/* Macro check EVRT source */
#define PARAM_EVRT_SOURCE(n)	((n==EVRT_SRC_WAKEUP0) || (n==EVRT_SRC_WAKEUP1) \
|| (n==EVRT_SRC_WAKEUP2) || (n==EVRT_SRC_WAKEUP3) \
|| (n==EVRT_SRC_ATIMER) || (n==EVRT_SRC_RTC) \
|| (n==EVRT_SRC_BOD1) || (n==EVRT_SRC_WWDT) \
|| (n==EVRT_SRC_ETHERNET) || (n==EVRT_SRC_USB0) \
|| (n==EVRT_SRC_USB1) || (n==EVRT_SRC_CCAN) || (n==EVRT_SRC_SDIO) \
|| (n==EVRT_SRC_COMBINE_TIMER2) || (n==EVRT_SRC_COMBINE_TIMER6) \
|| (n==EVRT_SRC_QEI) || (n==EVRT_SRC_COMBINE_TIMER14) \
|| (n==EVRT_SRC_RESET)) \

/* Macro check EVRT source active type*/
#define PARAM_EVRT_SOURCE_ACTIVE_TYPE(n) ((n==EVRT_SRC_ACTIVE_LOW_LEVEL) || (n==EVRT_SRC_ACTIVE_HIGH_LEVEL) \
		 || (n==EVRT_SRC_ACTIVE_FALLING_EDGE) || (n==EVRT_SRC_ACTIVE_RISING_EDGE))

/**
 * @}
 */


/* Public Types --------------------------------------------------------------- */
/** @defgroup EVRT_Public_Types EVRT Public Types
 * @{
 */

/** @brief EVRT input sources */
typedef enum {
	EVRT_SRC_WAKEUP0,				/**< WAKEUP0 event router source		*/
	EVRT_SRC_WAKEUP1,				/**< WAKEUP1 event router source		*/
	EVRT_SRC_WAKEUP2,				/**< WAKEUP2 event router source		*/
	EVRT_SRC_WAKEUP3,				/**< WAKEUP3 event router source		*/
	EVRT_SRC_ATIMER,				/**< Alarm timer event router source	*/
	EVRT_SRC_RTC,					/**< RTC event router source			*/
	EVRT_SRC_BOD1,					/**< BOD event router source			*/
	EVRT_SRC_WWDT,					/**< WWDT event router source			*/
	EVRT_SRC_ETHERNET,				/**< Ethernet event router source		*/
	EVRT_SRC_USB0,					/**< USB0 event router source			*/
	EVRT_SRC_USB1,					/**< USB1 event router source			*/
	EVRT_SRC_SDIO,					/**< Reserved							*/
	EVRT_SRC_CCAN,					/**< C_CAN event router source			*/
	EVRT_SRC_COMBINE_TIMER2,		/**< Combined timer 2 event router source	*/
	EVRT_SRC_COMBINE_TIMER6,		/**< Combined timer 6 event router source	*/
	EVRT_SRC_QEI,					/**< QEI event router source			*/
	EVRT_SRC_COMBINE_TIMER14,		/**< Combined timer 14 event router source	*/
	EVRT_SRC_RESERVED1,				/**< Reserved 							*/
	EVRT_SRC_RESERVED2,				/**< Reserved							*/
	EVRT_SRC_RESET					/**< Reset event router source			*/
} EVRT_SRC_ENUM;


/** @brief EVRT input sources detecting type */
typedef enum {
	EVRT_SRC_ACTIVE_LOW_LEVEL,		/**< Active low level 		*/
	EVRT_SRC_ACTIVE_HIGH_LEVEL,		/**< Active high level		*/
	EVRT_SRC_ACTIVE_FALLING_EDGE,	/**< Active falling edge	*/
	EVRT_SRC_ACTIVE_RISING_EDGE	/**< Active rising edge		*/
}EVRT_SRC_ACTIVE_TYPE;
/**
 * @}
 */



/* Public Functions ----------------------------------------------------------- */
/** @defgroup EVRT_Public_Functions EVRT Public Functions
 * @{
 */

void EVRT_Init (LPC_EVENTROUTER_Type *EVRTx);
void EVRT_DeInit(LPC_EVENTROUTER_Type *EVRTx);

void EVRT_ConfigIntSrcActiveType(LPC_EVENTROUTER_Type *EVRTx, EVRT_SRC_ENUM EVRT_Src, EVRT_SRC_ACTIVE_TYPE type);
void EVRT_SetUpIntSrc(LPC_EVENTROUTER_Type *EVRTx, EVRT_SRC_ENUM EVRT_Src, FunctionalState state);
Bool EVRT_IsSourceInterrupting(LPC_EVENTROUTER_Type *EVRTx, EVRT_SRC_ENUM EVRT_Src);
void EVRT_ClrPendIntSrc(LPC_EVENTROUTER_Type *EVRTx, EVRT_SRC_ENUM EVRT_Src);

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* LPC18XX_EVRT_H_ */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
