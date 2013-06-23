/**********************************************************************
* $Id$		lpc18xx_adc.c		2011-06-02
*//**
* @file		lpc18xx_adc.c
* @brief	Contains all functions support for ADC firmware library on LPC18xx
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
/** @addtogroup ADC
 * @{
 */

/* Includes ------------------------------------------------------------------- */
#include "lpc18xx_adc.h"
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


#ifdef _ADC
/* Public Functions ----------------------------------------------------------- */
/** @addtogroup ADC_Public_Functions
 * @{
 */

/*********************************************************************//**
 * @brief 		Initial for ADC
 * 					+ Set bit PCADC
 * 					+ Set clock for ADC
 * 					+ Set Clock Frequency
 * @param[in]	ADCx pointer to LPC_ADCn_Type, should be: LPC_ADC
 * @param[in]	rate ADC conversion rate, should be <=200KHz
 * @param[in]	bits_accuracy number of bits accuracy, should be <=10 bits and >=3bits
 * @return 		None
 **********************************************************************/
void ADC_Init(LPC_ADCn_Type *ADCx, uint32_t rate, uint8_t bits_accuracy)
{
	uint32_t temp, tmpreg, ADCbitrate;

	CHECK_PARAM(PARAM_ADCx(ADCx));
	CHECK_PARAM(PARAM_ADC_RATE(rate));

	// Turn on power and clock
	//CGU_ConfigPPWR (CGU_PCONP_PCAD, ENABLE);

	ADCx->CR = 0;

	//Enable PDN bit
	tmpreg = ADC_CR_PDN;
	// Set clock frequency
	if(ADCx == LPC_ADC0)
		temp = CGU_GetPCLKFrequency(CGU_PERIPHERAL_ADC0);
	else if(ADCx == LPC_ADC1)
		temp = CGU_GetPCLKFrequency(CGU_PERIPHERAL_ADC1);
	/* The APB clock (PCLK_ADC0) is divided by (CLKDIV+1) to produce the clock for
	 * A/D converter, which should be less than or equal to 13MHz.
	 * A fully conversion requires (bits_accuracy+1) of these clocks.
	 * ADC clock = PCLK_ADC0 / (CLKDIV + 1);
	 * ADC rate = ADC clock / (bits_accuracy+1);
	 */
	 ADCbitrate = (rate * (bits_accuracy+1));
	temp = ((temp*2 + ADCbitrate) / (ADCbitrate*2)) - 1;//get the round value by fomular: (2*A + B)/(2*B)
	tmpreg |=  ADC_CR_CLKDIV(temp) | ADC_CR_BITACC(10 - bits_accuracy);

	ADCx->CR = tmpreg;
}


/*********************************************************************//**
* @brief 		Close ADC
* @param[in]	ADCx pointer to LPC_ADCn_Type, should be: LPC_ADC
* @return 		None
**********************************************************************/
void ADC_DeInit(LPC_ADCn_Type *ADCx)
{
	CHECK_PARAM(PARAM_ADCx(ADCx));

	// Clear PDN bit
	ADCx->CR &= ~ADC_CR_PDN;
	// Turn on power and clock
	//CGU_ConfigPPWR (CGU_PCONP_PCAD, DISABLE);
}


///*********************************************************************//**
//* @brief 		Get Result conversion from A/D data register
//* @param[in]	channel number which want to read back the result
//* @return 		Result of conversion
//*********************************************************************/
//uint32_t ADC_GetData(uint32_t channel)
//{
//	uint32_t adc_value;
//
//	CHECK_PARAM(PARAM_ADC_CHANNEL_SELECTION(channel));
//
//	adc_value = *(uint32_t *)((&LPC_ADC->DR0) + channel);
//	return ADC_GDR_RESULT(adc_value);
//}

/*********************************************************************//**
* @brief 		Set start mode for ADC
* @param[in]	ADCx pointer to LPC_ADCn_Type, should be: LPC_ADC
* @param[in]	start_mode Start mode choose one of modes in
* 				'ADC_START_OPT' enumeration type definition, should be:
* 					- ADC_START_CONTINUOUS
* 					- ADC_START_NOW
* 					- ADC_START_ON_EINT0
* 					- ADC_START_ON_CAP01
*					- ADC_START_ON_MAT01
*					- ADC_START_ON_MAT03
*					- ADC_START_ON_MAT10
*					- ADC_START_ON_MAT11
* @return 		None
*********************************************************************/
void ADC_StartCmd(LPC_ADCn_Type *ADCx, uint8_t start_mode)
{
	CHECK_PARAM(PARAM_ADCx(ADCx));
	CHECK_PARAM(PARAM_ADC_START_OPT(start_mode));

	ADCx->CR &= ~ADC_CR_START_MASK;
	ADCx->CR |=ADC_CR_START_MODE_SEL((uint32_t)start_mode);
}


/*********************************************************************//**
* @brief 		ADC Burst mode setting
* @param[in]	ADCx pointer to LPC_ADCn_Type, should be: LPC_ADC
* @param[in]	NewState
* 					- 1: Set Burst mode
* 					- 0: reset Burst mode
* @return 		None
**********************************************************************/
void ADC_BurstCmd(LPC_ADCn_Type *ADCx, FunctionalState NewState)
{
	CHECK_PARAM(PARAM_ADCx(ADCx));

	ADCx->CR &= ~ADC_CR_BURST;
	if (NewState){
		ADCx->CR |= ADC_CR_BURST;
	}
}

/*********************************************************************//**
* @brief 		Set AD conversion in power mode
* @param[in]	ADCx pointer to LPC_ADCn_Type, should be: LPC_ADC
* @param[in]	NewState
* 					- 1: AD converter is optional
* 					- 0: AD Converter is in power down mode
* @return 		None
**********************************************************************/
void ADC_PowerdownCmd(LPC_ADCn_Type *ADCx, FunctionalState NewState)
{
	CHECK_PARAM(PARAM_ADCx(ADCx));

	ADCx->CR &= ~ADC_CR_PDN;
	if (NewState){
		ADCx->CR |= ADC_CR_PDN;
	}
}

/*********************************************************************//**
* @brief 		Set Edge start configuration
* @param[in]	ADCx pointer to LPC_ADCn_Type, should be: LPC_ADC
* @param[in]	EdgeOption is ADC_START_ON_RISING and ADC_START_ON_FALLING
* 					- 0: ADC_START_ON_RISING
* 					- 1: ADC_START_ON_FALLING
* @return 		None
**********************************************************************/
void ADC_EdgeStartConfig(LPC_ADCn_Type *ADCx, uint8_t EdgeOption)
{
	CHECK_PARAM(PARAM_ADCx(ADCx));
	CHECK_PARAM(PARAM_ADC_START_ON_EDGE_OPT(EdgeOption));

	ADCx->CR &= ~ADC_CR_EDGE;
	if (EdgeOption){
		ADCx->CR |= ADC_CR_EDGE;
	}
}

/*********************************************************************//**
* @brief 		ADC interrupt configuration
* @param[in]	ADCx pointer to LPC_ADCn_Type, should be: LPC_ADC
* @param[in]	IntType: type of interrupt, should be:
* 					- ADC_ADINTEN0: Interrupt channel 0
* 					- ADC_ADINTEN1: Interrupt channel 1
* 					...
* 					- ADC_ADINTEN7: Interrupt channel 7
* 					- ADC_ADGINTEN: Individual channel/global flag done generate an interrupt
* @param[in]	NewState:
* 					- SET : enable ADC interrupt
* 					- RESET: disable ADC interrupt
* @return 		None
**********************************************************************/
void ADC_IntConfig (LPC_ADCn_Type *ADCx, ADC_TYPE_INT_OPT IntType, FunctionalState NewState)
{
	CHECK_PARAM(PARAM_ADCx(ADCx));
	CHECK_PARAM(PARAM_ADC_TYPE_INT_OPT(IntType));

	ADCx->INTEN &= ~ADC_INTEN_CH(IntType);
	if (NewState){
		ADCx->INTEN |= ADC_INTEN_CH(IntType);
	}
}

/*********************************************************************//**
* @brief 		Enable/Disable ADC channel number
* @param[in]	ADCx pointer to LPC_ADCn_Type, should be: LPC_ADC
* @param[in]	Channel channel number
* @param[in]	NewState	New state, should be:
* 					- ENABLE
* 					- DISABLE
* @return 		None
**********************************************************************/
void ADC_ChannelCmd (LPC_ADCn_Type *ADCx, uint8_t Channel, FunctionalState NewState)
{
	CHECK_PARAM(PARAM_ADCx(ADCx));
	CHECK_PARAM(PARAM_ADC_CHANNEL_SELECTION(Channel));

	if (NewState == ENABLE) {
		ADCx->CR |= ADC_CR_CH_SEL(Channel);
	} else {
		ADCx->CR &= ~ADC_CR_CH_SEL(Channel);
	}
}

/*********************************************************************//**
* @brief 		Get ADC result
* @param[in]	ADCx pointer to LPC_ADCn_Type, should be: LPC_ADC
* @param[in]	channel channel number, should be 0...7
* @return 		Converted data
**********************************************************************/
uint16_t ADC_ChannelGetData(LPC_ADCn_Type *ADCx, uint8_t channel)
{
	uint32_t adc_value;

	CHECK_PARAM(PARAM_ADCx(ADCx));
	CHECK_PARAM(PARAM_ADC_CHANNEL_SELECTION(channel));

	adc_value = *(uint32_t *) ((&(ADCx->DR[0])) + channel);
	return ADC_DR_RESULT(adc_value);
}

/*********************************************************************//**
* @brief 		Get ADC Channel status from ADC data register
* @param[in]	ADCx pointer to LPC_ADCn_Type, should be: LPC_ADC
* @param[in]	channel: channel number, should be 0..7
* @param[in]  	StatusType
*              		- 0: Burst status
*               	- 1: Done status
* @return 		Channel status, could be:
* 					- SET
* 					- RESET
**********************************************************************/
FlagStatus ADC_ChannelGetStatus(LPC_ADCn_Type *ADCx, uint8_t channel, uint32_t StatusType)
{
	uint32_t temp;

	CHECK_PARAM(PARAM_ADCx(ADCx));
	CHECK_PARAM(PARAM_ADC_CHANNEL_SELECTION(channel));
	CHECK_PARAM(PARAM_ADC_DATA_STATUS(StatusType));

	temp =  *(uint32_t *) ((&ADCx->DR[0]) + channel);
	if (StatusType) {
		temp &= ADC_DR_DONE_FLAG;
	}else{
		temp &= ADC_DR_OVERRUN_FLAG;
	}
	if (temp) {
		return SET;
	} else {
		return RESET;
	}

}

/*********************************************************************//**
* @brief 		Get ADC Data from AD Global register
* @param[in]	ADCx pointer to LPC_ADCn_Type, should be: LPC_ADC
* @return 		Result of conversion
**********************************************************************/
uint32_t ADC_GlobalGetData(LPC_ADCn_Type *ADCx)
{
	CHECK_PARAM(PARAM_ADCx(ADCx));

	return ((uint32_t)(ADCx->GDR));
}

/*********************************************************************//**
* @brief 		Get ADC Chanel status from AD global data register
* @param[in]	ADCx pointer to LPC_ADCn_Type, should be: LPC_ADC
* @param[in]  	StatusType
*              		- 0: Burst status
*               	- 1: Done status
* @return 		SET / RESET
**********************************************************************/
FlagStatus	ADC_GlobalGetStatus(LPC_ADCn_Type *ADCx, uint32_t StatusType)
{
	uint32_t temp;

	CHECK_PARAM(PARAM_ADCx(ADCx));
	CHECK_PARAM(PARAM_ADC_DATA_STATUS(StatusType));

	temp =  ADCx->GDR;
	if (StatusType){
		temp &= ADC_DR_DONE_FLAG;
	}else{
		temp &= ADC_DR_OVERRUN_FLAG;
	}
	if (temp){
		return SET;
	}else{
		return RESET;
	}
}

/**
 * @}
 */

#endif /* _ADC */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */

