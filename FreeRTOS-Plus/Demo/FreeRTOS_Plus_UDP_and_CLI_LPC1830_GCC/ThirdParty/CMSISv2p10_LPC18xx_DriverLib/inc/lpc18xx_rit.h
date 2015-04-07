/**********************************************************************
* $Id$		lpc18xx_rit.h		2011-06-02
*//**
* @file		lpc18xx_rit.h
* @brief	Contains all macro definitions and function prototypes
* 			support for RIT firmware library on LPC18xx
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
/** @defgroup RIT RIT (Repetitive Interrupt Timer)
 * @ingroup LPC1800CMSIS_FwLib_Drivers
 * @{
 */

#ifndef LPC18XX_RIT_H_
#define LPC18XX_RIT_H_

/* Includes ------------------------------------------------------------------- */
#include "LPC18xx.h"
#include "lpc_types.h"


#ifdef __cplusplus
extern "C"
{
#endif


/* Private Macros ------------------------------------------------------------- */
/** @defgroup RIT_Private_Macros RIT Private Macros
 * @{
 */

/* --------------------- BIT DEFINITIONS -------------------------------------- */
/*********************************************************************//**
 * Macro defines for RIT control register
 **********************************************************************/
/**	Set interrupt flag when the counter value equals the masked compare value */
#define RIT_CTRL_INTEN	((uint32_t) (1))
/** Set timer enable clear to 0 when the counter value equals the masked compare value  */
#define RIT_CTRL_ENCLR 	((uint32_t) _BIT(1))
/** Set timer enable on debug */
#define RIT_CTRL_ENBR	((uint32_t) _BIT(2))
/** Set timer enable */
#define RIT_CTRL_TEN	((uint32_t) _BIT(3))

/** Macro to determine if it is valid RIT peripheral */
#define PARAM_RITx(n)	(((uint32_t *)n)==((uint32_t *)LPC_RITIMER))
/**
 * @}
 */



/* Public Functions ----------------------------------------------------------- */
/** @defgroup RIT_Public_Functions RIT Public Functions
 * @{
 */
/* RIT Init/DeInit functions */
void RIT_Init(LPC_RITIMER_Type *RITx);
void RIT_DeInit(LPC_RITIMER_Type *RITx);

/* RIT config timer functions */
void RIT_TimerConfig(LPC_RITIMER_Type *RITx, uint32_t time_interval);

/* Enable/Disable RIT functions */
void RIT_TimerClearCmd(LPC_RITIMER_Type *RITx, FunctionalState NewState);
void RIT_Cmd(LPC_RITIMER_Type *RITx, FunctionalState NewState);
void RIT_TimerDebugCmd(LPC_RITIMER_Type *RITx, FunctionalState NewState);

/* RIT Interrupt functions */
IntStatus RIT_GetIntStatus(LPC_RITIMER_Type *RITx);

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* LPC18XX_RIT_H_ */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
