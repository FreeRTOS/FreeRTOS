/**********************************************************************
* $Id$		lpc18xx_pwr.h		2011-06-02
*//**
* @file		lpc18xx_pwr.h
* @brief	Contains all macro definitions and function prototypes
* 			support for Power Control firmware library on LPC18xx
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
/** @defgroup PWR PWR (Power Control)
 * @ingroup LPC1800CMSIS_FwLib_Drivers
 * @{
 */

#ifndef LPC18XX_PWR_H_
#define LPC18XX_PWR_H_

/* Includes ------------------------------------------------------------------- */
#include "LPC18xx.h"
#include "lpc_types.h"

#ifdef __cplusplus
extern "C"
{
#endif

/* Public Macros -------------------------------------------------------------- */
/** @defgroup PWR_Private_Macros PWR Private Macros
 * @{
 */
#define PWR_SLEEP_MODE_DEEP_SLEEP	0x3F00AA
#define PWR_SLEEP_MODE_POWER_DOWN	0x30FCBA
#define PWR_SLEEP_MODE_DEEP_POWER_DOWN	0x3FFF7F

/**
 * @}
 */


/* Public Functions ----------------------------------------------------------- */
/** @defgroup PWR_Public_Functions PWR Public Functions
 * @{
 */
/* Clock Generator */
void PWR_Sleep(void);
void PWR_DeepSleep(void);
void PWR_PowerDown(void);
void PWR_DeepPowerDown(void);

/**
 * @}
 */


#ifdef __cplusplus
}
#endif

#endif /* LPC18XX_PWR_H_ */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
