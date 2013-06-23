/**********************************************************************
* $Id$		lpc18xx_dac.c		2011-06-02
*//**
* @file		lpc18xx_dac.c
* @brief	Contains all functions support for DAC firmware library on LPC18xx
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
/** @addtogroup DAC
 * @{
 */

/* Includes ------------------------------------------------------------------- */
#include "lpc18xx_dac.h"
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


#ifdef _DAC

/* Public Functions ----------------------------------------------------------- */
/** @addtogroup DAC_Public_Functions
 * @{
 */

/*********************************************************************//**
 * @brief 		Initial ADC configuration
 * 					- Maximum	current is 700 uA
 * 					- Value to AOUT is 0
 * @param[in] 	DACx pointer to LPC_DAC_Type, should be: LPC_DAC
 * @return 		None
 ***********************************************************************/
void DAC_Init(LPC_DAC_Type *DACx)
{
	CHECK_PARAM(PARAM_DACx(DACx));
	/* Set default clock divider for DAC */
	//LPC_CGU->BASE_VPB3_CLK = (SRC_PL160M_0<<24) | (1<<11);	// ABP3 base clock use PLL1 and auto block
	CGU_EntityConnect(CGU_CLKSRC_PLL1, CGU_BASE_APB3);
	//Set maximum current output
	DAC_SetBias(LPC_DAC,DAC_MAX_CURRENT_700uA);
}

/*********************************************************************//**
 * @brief 		Update value to DAC
 * @param[in] 	DACx pointer to LPC_DAC_Type, should be: LPC_DAC
 * @param[in] 	dac_value  value 10 bit to be converted to output
 * @return 		None
 ***********************************************************************/
void DAC_UpdateValue (LPC_DAC_Type *DACx,uint32_t dac_value)
{
	uint32_t tmp;
	CHECK_PARAM(PARAM_DACx(DACx));
	tmp = DACx->CR & DAC_BIAS_EN;
	tmp |= DAC_VALUE(dac_value);
	// Update value
	DACx->CR = tmp;
}

/*********************************************************************//**
 * @brief 		Set Maximum current for DAC
 * @param[in] 	DACx pointer to LPC_DAC_Type, should be: LPC_DAC
 * @param[in] 	bias	Using Bias value, should be:
 * 				- 0 is 700 uA
 * 				- 1 is 350 uA
 * @return 		None
 ***********************************************************************/
void DAC_SetBias (LPC_DAC_Type *DACx,uint32_t bias)
{
	CHECK_PARAM(PARAM_DAC_CURRENT_OPT(bias));
	DACx->CR &=~DAC_BIAS_EN;
	if (bias  == DAC_MAX_CURRENT_350uA)
	{
		DACx->CR |= DAC_BIAS_EN;
	}
}

/*********************************************************************//**
 * @brief 		To enable the DMA operation and control DMA timer
 * @param[in]	DACx pointer to LPC_DAC_Type, should be: LPC_DAC
 * @param[in] 	DAC_ConverterConfigStruct pointer to DAC_CONVERTER_CFG_Type
 * 					- DBLBUF_ENA :enable/disable DACR double buffering feature
 * 					- CNT_ENA    :enable/disable timer out counter
 * 					- DMA_ENA    :enable/disable DMA access
 * @return 		None
 ***********************************************************************/
void DAC_ConfigDAConverterControl (LPC_DAC_Type *DACx,DAC_CONVERTER_CFG_Type *DAC_ConverterConfigStruct)
{
	CHECK_PARAM(PARAM_DACx(DACx));
	DACx->CTRL &= ~DAC_DACCTRL_MASK;
	if (DAC_ConverterConfigStruct->DBLBUF_ENA)
		DACx->CTRL	|= DAC_DBLBUF_ENA;
	if (DAC_ConverterConfigStruct->CNT_ENA)
		DACx->CTRL	|= DAC_CNT_ENA;
	if (DAC_ConverterConfigStruct->DMA_ENA)
		DACx->CTRL	|= DAC_DMA_ENA;
}

/*********************************************************************//**
 * @brief 		Set reload value for interrupt/DMA counter
 * @param[in] 	DACx pointer to LPC_DAC_Type, should be: LPC_DAC
 * @param[in] 	time_out time out to reload for interrupt/DMA counter
 * @return 		None
 ***********************************************************************/
void DAC_SetDMATimeOut(LPC_DAC_Type *DACx, uint32_t time_out)
{
	CHECK_PARAM(PARAM_DACx(DACx));
	DACx->CNTVAL = DAC_CCNT_VALUE(time_out);
}

/**
 * @}
 */

#endif /* _DAC */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
