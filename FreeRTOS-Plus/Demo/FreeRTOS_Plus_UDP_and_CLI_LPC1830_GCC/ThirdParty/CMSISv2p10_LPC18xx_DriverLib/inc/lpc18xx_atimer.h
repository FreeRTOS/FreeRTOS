/**********************************************************************
* $Id$		lpc18xx_atimer.h			2011-06-02
*//**
* @file		lpc18xx_atimer.h
* @brief	Contains all functions support for Alarm Timer firmware
* 			library on LPC18xx
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
/** @defgroup ATIMER ATIMER (Alarm Timer)
 * @ingroup LPC1800CMSIS_FwLib_Drivers
 * @{
 */

#ifndef __LPC18XX_ATIMER_H_
#define __LPC18XX_ATIMER_H_

/* Includes ------------------------------------------------------------------- */
#include "LPC18xx.h"
#include "lpc_types.h"

#ifdef __cplusplus
extern "C"
{
#endif

/* Private Macros ------------------------------------------------------------- */
/** @defgroup ATIMER_Private_Macros ALARM Timer Private Macros
 * @{
 */

/* ---------------- CHECK PARAMETER DEFINITIONS ---------------------------- */
/** Macro to determine if it is valid ALARM TIMER peripheral */
#define PARAM_ATIMERx(n)	(((uint32_t *)n)==((uint32_t *)LPC_ATIMER))


/**
 * @}
 */


/* Public Functions ----------------------------------------------------------- */
/** @defgroup ATIMER_Public_Functions ATIMER Public Functions
 * @{
 */


/* Init/DeInit ATIMER functions -----------*/
void ATIMER_Init(LPC_ATIMER_Type *ATIMERx, uint32_t PresetValue);
void ATIMER_DeInit(LPC_ATIMER_Type *ATIMERx);

/* ATIMER interrupt functions -------------*/
void ATIMER_IntEnable(LPC_ATIMER_Type *ATIMERx);
void ATIMER_IntDisable(LPC_ATIMER_Type *ATIMERx);
void ATIMER_ClearIntStatus(LPC_ATIMER_Type *ATIMERx);
void ATIMER_SetIntStatus(LPC_ATIMER_Type *ATIMERx);

/* ATIMER configuration functions --------*/
void ATIMER_UpdatePresetValue(LPC_ATIMER_Type *ATIMERx,uint32_t PresetValue);
uint32_t ATIMER_GetPresetValue(LPC_ATIMER_Type *ATIMERx);

/**
 * @}
 */
#ifdef __cplusplus
}
#endif

#endif /* __LPC18XX_ATIMER_H_ */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
