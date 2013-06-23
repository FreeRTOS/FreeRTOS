/**********************************************************************
* $Id$		lpc18xx_sct.h		2011-06-02
*//**
* @file		lpc18xx_sct.h
* @brief	Contains all macro definitions and function prototypes
* 			support for SCT firmware library on LPC18xx
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
/** @defgroup SCT SCT (State Configurable Timer)
 * @ingroup LPC1800CMSIS_FwLib_Drivers
 * @{
 */

#ifndef LPC18XX_SCT_H_
#define LPC18XX_SCT_H_

/* Includes ------------------------------------------------------------------- */
#include "LPC18xx.h"
#include "lpc_types.h"


#ifdef __cplusplus
extern "C"
{
#endif

/* Private macros ------------------------------------------------------------- */
/** @defgroup SCT_Private_Macros SCT Private Macros
 * @{
 */

/* -------------------------- BIT DEFINITIONS ----------------------------------- */
/*********************************************************************//**
 * Macro defines for SCT  configuration register
 **********************************************************************/
/**  Selects 16/32 bit counter */
#define SCT_CONFIG_16BIT_COUNTER		0x00000000
#define SCT_CONFIG_32BIT_COUNTER		0x00000001

/*********************************************************************//**
 * Macro defines for SCT control register
 **********************************************************************/
/**  Stop low counter */
#define SCT_CTRL_STOP_L					(1<<1)
/**  Halt low counter */
#define SCT_CTRL_HALT_L					(1<<2)
/**  Clear low or unified counter */
#define SCT_CTRL_CLRCTR_L				(1<<3)
/**  Direction for low or unified counter */
#define COUNTUP_TO_LIMIT_THEN_CLEAR_TO_ZERO		0
#define COUNTUP_TO LIMIT_THEN_COUNTDOWN_TO_ZERO	1
#define SCT_CTRL_BIDIR_L(x)				(((x)&0x01)<<4)
/**  Prescale clock for low or unified counter */
#define SCT_CTRL_PRE_L(x)				(((x)&0xFF)<<5)

/**  Stop high counter */
#define SCT_CTRL_STOP_H					(1<<17)
/**  Halt high counter */
#define SCT_CTRL_HALT_H					(1<<18)
/**  Clear high counter */
#define SCT_CTRL_CLRCTR_H				(1<<19)
/**  Direction for high counter */
#define COUNTUP_TO_LIMIT_THEN_CLEAR_TO_ZERO		0
#define COUNTUP_TO LIMIT_THEN_COUNTDOWN_TO_ZERO	1
#define SCT_CTRL_BIDIR_H(x)				(((x)&0x01)<<20)
/**  Prescale clock for high counter */
#define SCT_CTRL_PRE_H(x)				(((x)&0xFF)<<21)
/*********************************************************************//**
 * Macro defines for SCT Conflict resolution register
**********************************************************************/
/**  Define conflict solution */
#define SCT_RES_NOCHANGE				(0)
#define SCT_RES_SET_OUTPUT				(1)
#define SCT_RES_CLEAR_OUTPUT			(2)
#define SCT_RES_TOGGLE_OUTPUT			(3)

/* ------------------- CHECK PARAM DEFINITIONS ------------------------- */
/** Check SCT output number */
#define PARAM_SCT_OUTPUT_NUM(n)    ((n)<= CONFIG_SCT_nOU )

/** Check SCT counter type */
#define PARAM_SCT_CONFIG_COUNTER_TYPE(n)    ((n==SCT_CONFIG_16BIT_COUNTER)||(n==SCT_CONFIG_32BIT_COUNTER))

/** Check SCT conflict solution */
#define PARAM_SCT_RES(n)    ((n==SCT_RES_NOCHANGE)||(n==SCT_RES_SET_OUTPUT)\
								||(n==SCT_RES_CLEAR_OUTPUT)||(n==SCT_RES_TOGGLE_OUTPUT))

/** Check SCT event number */
#define PARAM_SCT_EVENT(n)	((n) <= 15)

/**
 * @}
 */



/* Public Functions ----------------------------------------------------------- */
/** @defgroup SCT_Public_Functions SCT Public Functions
 * @{
 */

void SCT_Config(uint32_t value);
void SCT_ControlSet(uint32_t value, FunctionalState ena);
void SCT_ConflictResolutionSet(uint8_t outnum, uint8_t value);
void SCT_EventFlagClear(uint8_t even_num);

/**
 * @}
 */


#ifdef __cplusplus
}
#endif


#endif /* LPC18XX_SCT_H_ */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
