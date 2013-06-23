/**********************************************************************
* $Id$		lpc18xx_atimer.c		2011-06-02
*//**
* @file		lpc18xx_atimer.c
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
/** @addtogroup ATIMER
 * @{
 */

/* Includes ------------------------------------------------------------------- */
#include "lpc18xx_atimer.h"
#include "lpc18xx_cgu.h"

/* If this source file built with example, the LPC18xx FW library configuration
 * file in each example directory ("lpc18xx_libcfg.h") must be included,
 * otherwise the default FW library configuration file must be included instead
 */
#ifdef __BUILD_WITH_EXAMPLE__
#include "lpc18xx_libcfg.h"
#else
#include "lpc18xx_libcfg_default.h"
#endif /* __BUILD_WITH_EXAMPLE__ */

#ifdef _ATIMER

/* Private Functions ---------------------------------------------------------- */

/*********************************************************************//**
 * @brief 		Initial Alarm Timer device
 * @param[in]	ATIMERx  Timer selection, should be: LPC_ATIMER
 * @param[in]	PresetValue Count of 1/1024s for Alarm
 * @return 		None
 **********************************************************************/
void ATIMER_Init(LPC_ATIMER_Type *ATIMERx, uint32_t PresetValue)
{
	CHECK_PARAM(PARAM_ATIMERx(ATIMERx));

	//set power
	if (ATIMERx== LPC_ATIMER)
	{
		/*Set Clock Here */
		CGU_EnableEntity(CGU_CLKSRC_32KHZ_OSC, ENABLE);
	}

	ATIMER_UpdatePresetValue(ATIMERx, PresetValue);
	// Clear interrupt pending
	ATIMER_ClearIntStatus(ATIMERx);

}

/*********************************************************************//**
 * @brief 		Close ATIMER device
 * @param[in]	ATIMERx  Pointer to timer device, should be: LPC_ATIMER
 * @return 		None
 **********************************************************************/
void ATIMER_DeInit (LPC_ATIMER_Type *ATIMERx)
{
	CHECK_PARAM(PARAM_ATIMERx(ATIMERx));
	// Disable atimer
	ATIMER_ClearIntStatus(ATIMERx);
	ATIMER_IntDisable(ATIMERx);

	// Disable power
//	if (ATIMERx== LPC_ATIMER0)
//		CGU_ConfigPPWR (CGU_PCONP_PCATIMER0, DISABLE);

}

/*********************************************************************//**
 * @brief 		Clear ATIMER Interrupt Status
 * @param[in]	ATIMERx Pointer to timer device, should be: LPC_ATIMER
 * @return 		None
 **********************************************************************/
void ATIMER_ClearIntStatus(LPC_ATIMER_Type *ATIMERx)
{
	CHECK_PARAM(PARAM_ATIMERx(ATIMERx));
	ATIMERx->CLR_STAT = 1;
	while((ATIMERx->STATUS & 1) == 1);
}

/*********************************************************************//**
 * @brief 		Set ATIMER Interrupt Status
 * @param[in]	ATIMERx Pointer to timer device, should be: LPC_ATIMER
 * @return 		None
 **********************************************************************/
void ATIMER_SetIntStatus(LPC_ATIMER_Type *ATIMERx)
{
	CHECK_PARAM(PARAM_ATIMERx(ATIMERx));
	ATIMERx->SET_STAT = 1;
	while((ATIMERx->STATUS & 1) == 0);
}

/*********************************************************************//**
 * @brief 		Enable ATIMER Interrupt
 * @param[in]	ATIMERx Pointer to timer device, should be: LPC_ATIMER
 * @return 		None
 **********************************************************************/
void ATIMER_IntEnable(LPC_ATIMER_Type *ATIMERx)
{
	CHECK_PARAM(PARAM_ATIMERx(ATIMERx));
	ATIMERx->SET_EN = 1;
	while((ATIMERx->ENABLE & 1) == 0);
}

/*********************************************************************//**
 * @brief 		Disable ATIMER Interrupt
 * @param[in]	ATIMERx Pointer to timer device, should be: LPC_ATIMER
 * @return 		None
 **********************************************************************/
void ATIMER_IntDisable(LPC_ATIMER_Type *ATIMERx)
{
	CHECK_PARAM(PARAM_ATIMERx(ATIMERx));
	ATIMERx->CLR_EN = 1;
	while((ATIMERx->ENABLE & 1) == 1);
}
/*********************************************************************//**
 * @brief 		Update Preset value
 * @param[in]	ATIMERx Pointer to timer device, should be: LPC_ATIMER
 * @param[in]	PresetValue	updated preset value
 * @return 		None
 **********************************************************************/
void ATIMER_UpdatePresetValue(LPC_ATIMER_Type *ATIMERx,uint32_t PresetValue)
{
	CHECK_PARAM(PARAM_ATIMERx(ATIMERx));
	ATIMERx->PRESET = PresetValue;
}

/*********************************************************************//**
 * @brief 		Read value of preset register
 * @param[in]	ATIMERx Pointer to timer/counter device, should be: LPC_ATIMER
 * @return 		Value of capture register
 **********************************************************************/
uint32_t ATIMER_GetPresetValue(LPC_ATIMER_Type *ATIMERx)
{
	CHECK_PARAM(PARAM_ATIMERx(ATIMERx));
	return ATIMERx->PRESET;
}
/**
 * @}
 */

#endif /* _ATIMER */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
