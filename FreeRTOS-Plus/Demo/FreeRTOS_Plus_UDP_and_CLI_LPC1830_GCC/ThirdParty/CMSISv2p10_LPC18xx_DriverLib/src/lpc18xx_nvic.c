/**********************************************************************
* $Id$		lpc18xx_nvic.c		2011-06-02
*//**
* @file		lpc18xx_nvic.c
* @brief	Contains all expansion functions support for NVIC firmware
* 			library on LPC18XX. The main NVIC functions are defined in
* 			core_cm3.h
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
/** @addtogroup NVIC
 * @{
 */

/* Includes ------------------------------------------------------------------- */
#include "lpc18xx_nvic.h"


/* Private Macros ------------------------------------------------------------- */
/** @addtogroup NVIC_Private_Macros
 * @{
 */

/* Vector table offset bit mask */
#define NVIC_VTOR_MASK              0x3FFFFF80

/**
 * @}
 */


/* Public Functions ----------------------------------------------------------- */
/** @addtogroup NVIC_Public_Functions
 * @{
 */

/*****************************************************************************//**
 * @brief		Set Vector Table Offset value
 * @param		offset Offset value
 * @return      None
 *******************************************************************************/
void NVIC_SetVTOR(uint32_t offset)
{
//	SCB->VTOR  = (offset & NVIC_VTOR_MASK);
	SCB->VTOR  = offset;
}

/**
 * @}
 */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
