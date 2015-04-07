/**********************************************************************
* $Id$		lpc18xx_pwr.c		2011-06-02
*//**
* @file		lpc18xx_pwr.c
* @brief	Contains all functions support for Power Control
* 			firmware library on LPC18xx
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
/** @addtogroup PWR
 * @{
 */

/* Includes ------------------------------------------------------------------- */
#include "lpc_types.h"
#include "lpc18xx_scu.h"
#include "lpc18xx_pwr.h"

/*********************************************************************//**
 * @brief 		Enter Sleep mode with co-operated instruction by the Cortex-M3.
 * @param[in]	None
 * @return		None
 **********************************************************************/
void PWR_Sleep(void)
{
	//LPC_PMC->SLEEP0_MODE = 0x00;
	/* Sleep Mode*/
	__WFI();
}


/*********************************************************************//**
 * @brief 		Enter Deep Sleep mode with co-operated instruction by the Cortex-M3.
 * @param[in]	None
 * @return		None
 **********************************************************************/
void PWR_DeepSleep(void)
{
    /* Deep-Sleep Mode, set SLEEPDEEP bit */
	SCB->SCR = 0x4;
	LPC_PMC->PD0_SLEEP0_MODE = PWR_SLEEP_MODE_DEEP_SLEEP;
	/* Deep Sleep Mode*/
	__WFI();
}


/*********************************************************************//**
 * @brief 		Enter Power Down mode with co-operated instruction by the Cortex-M3.
 * @param[in]	None
 * @return		None
 **********************************************************************/
void PWR_PowerDown(void)
{
    /* Deep-Sleep Mode, set SLEEPDEEP bit */
	SCB->SCR = 0x4;
	LPC_PMC->PD0_SLEEP0_MODE = PWR_SLEEP_MODE_POWER_DOWN;
	/* Power Down Mode*/
	__WFI();
}


/*********************************************************************//**
 * @brief 		Enter Deep Power Down mode with co-operated instruction by the Cortex-M3.
 * @param[in]	None
 * @return		None
 **********************************************************************/
void PWR_DeepPowerDown(void)
{
    /* Deep-Sleep Mode, set SLEEPDEEP bit */
	SCB->SCR = 0x4;
	LPC_PMC->PD0_SLEEP0_MODE = PWR_SLEEP_MODE_DEEP_POWER_DOWN;
	/* Deep Power Down Mode*/
	__WFI();
}

/**
 * @}
 */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
