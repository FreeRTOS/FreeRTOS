/*
 * @brief LPC18xx/43xx D/A conversion driver
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * All rights reserved.
 *
 * @par
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licensor disclaim any and
 * all warranties, express or implied, including all implied warranties of
 * merchantability, fitness for a particular purpose and non-infringement of
 * intellectual property rights.  NXP Semiconductors assumes no responsibility
 * or liability for the use of the software, conveys no license or rights under any
 * patent, copyright, mask work right, or any other intellectual property rights in
 * or to any products. NXP Semiconductors reserves the right to make changes
 * in the software without notification. NXP Semiconductors also makes no
 * representation or warranty that such application will be suitable for the
 * specified use without further testing or modification.
 *
 * @par
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
 */

#ifndef __DAC_18XX_43XX_H_
#define __DAC_18XX_43XX_H_

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup DAC_18XX_43XX CHIP: LPC18xx/43xx D/A conversion driver
 * @ingroup CHIP_18XX_43XX_Drivers
 * @{
 */

// FIXME LPC_DAC_T *pDAC argument not needed for 18xx/43xx CHIP driver

/**
 * @brief	Initial DAC configuration
 *              - Maximum	current is 700 uA
 *              - Value to AOUT is 0
 * @param	pDAC : pointer to LPC_DAC_T
 * @return	Nothing
 */
void Chip_DAC_Init(LPC_DAC_T *pDAC);

/**
 * @brief	Shutdown DAC
 * @param	pDAC : pointer to LPC_DAC_T
 * @return	Nothing
 */
void Chip_DAC_DeInit(LPC_DAC_T *pDAC);

/**
 * @brief	Update value to DAC buffer
 * @param	pDAC		: pointer to LPC_DAC_T
 * @param	dac_value	: value 10 bit to be converted to output
 * @return	Nothing
 */
STATIC INLINE void Chip_DAC_UpdateValue(LPC_DAC_T *pDAC, uint32_t dac_value)
{
	IP_DAC_UpdateValue(pDAC, dac_value);
}

/**
 * @brief	Set maximum update rate for DAC
 * @param	pDAC	: pointer to LPC_DAC_T
 * @param	bias	: Using Bias value, should be:
 *              - 0 is 1MHz
 *              - 1 is 400kHz
 * @return	Nothing
 */
STATIC INLINE void Chip_DAC_SetBias(LPC_DAC_T *pDAC, uint32_t bias)
{
	IP_DAC_SetBias(pDAC, bias);
}

/**
 * @brief	Enables the DMA operation and controls DMA timer
 * @param	pDAC        : pointer to the DAC peripheral block
 * @param	dacFlags	: An Or'ed value of the following DAC values:
 *                  - DAC_DBLBUF_ENA :enable/disable DACR double buffering feature
 *                  - DAC_CNT_ENA    :enable/disable timer out counter
 *                  - DAC_DMA_ENA    :enable/disable DMA access
 * @return	Nothing
 * @note	Pass an Or'ed value of the DAC flags to enable those options.
 */
STATIC INLINE void Chip_DAC_ConfigDAConverterControl(IP_DAC_001_T *pDAC, uint32_t dacFlags)
{
	IP_DAC_ConfigDAConverterControl(pDAC, dacFlags);
}

/**
 * @brief	Set reload value for interrupt/DMA counter
 * @param	pDAC		: pointer to LPC_DAC_T
 * @param	time_out	: time out to reload for interrupt/DMA counter
 * @return	Nothing
 */
STATIC INLINE void Chip_DAC_SetDMATimeOut(LPC_DAC_T *pDAC, uint32_t time_out)
{
	IP_DAC_SetDMATimeOut(pDAC, time_out);
}

/**
 * @brief	Get status for interrupt/DMA time out
 * @param	pDAC		: pointer to LPC_DAC_T
 * @return	interrupt/DMA time out status, should be SET or RESET
 */
STATIC INLINE IntStatus Chip_DAC_GetIntStatus(LPC_DAC_T *pDAC)
{
	return IP_DAC_GetIntStatus(pDAC);
}

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __DAC_18XX_43XX_H_ */
