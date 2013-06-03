/*
 * @brief LPC18xx/43xx SD/SDIO driver
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

#ifndef __SDIF_18XX_43XX_H_
#define __SDIF_18XX_43XX_H_

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup SDIF_18XX_43XX CHIP: LPC18xx/43xx SD/SDIO driver
 * @ingroup CHIP_18XX_43XX_Drivers
 * @{
 */

/** @brief Setup options for the SDIO driver
 */
#define US_TIMEOUT            1000000		/*!< give 1 atleast 1 sec for the card to respond */
#define MS_ACQUIRE_DELAY      (10)			/*!< inter-command acquire oper condition delay in msec*/
#define INIT_OP_RETRIES       50			/*!< initial OP_COND retries */
#define SET_OP_RETRIES        1000			/*!< set OP_COND retries */
#define SDIO_BUS_WIDTH        4				/*!< Max bus width supported */
#define SD_MMC_ENUM_CLOCK       400000		/*!< Typical enumeration clock rate */
#define MMC_MAX_CLOCK           20000000	/*!< Max MMC clock rate */
#define MMC_LOW_BUS_MAX_CLOCK   26000000	/*!< Type 0 MMC card max clock rate */
#define MMC_HIGH_BUS_MAX_CLOCK  52000000	/*!< Type 1 MMC card max clock rate */
#define SD_MAX_CLOCK            25000000	/*!< Max SD clock rate */

/**
 * @brief	Detect if an SD card is inserted
 * @param	pSDMMC	: SDMMC peripheral selected
 * @return	Returns 0 if a card is detected, otherwise 1
 * @note	Detect if an SD card is inserted
 * (uses SD_CD pin, returns 0 on card detect)
 */
STATIC INLINE int32_t Chip_SDIF_CardNDetect(LPC_SDMMC_T *pSDMMC)
{
	return IP_SDMMC_CardNDetect(pSDMMC);
}

/**
 * @brief	Detect if write protect is enabled
 * @param	pSDMMC	: SDMMC peripheral selected
 * @return	Returns 1 if card is write protected, otherwise 0
 * @note	Detect if write protect is enabled
 * (uses SD_WP pin, returns 1 if card is write protected)
 */
STATIC INLINE int32_t Chip_SDIF_CardWpOn(LPC_SDMMC_T *pSDMMC)
{
	return IP_SDMMC_CardWpOn(pSDMMC);
}

/**
 * @brief	Initializes the SD/MMC card controller
 * @param	pSDMMC	: SDMMC peripheral selected
 * @return	None
 */
void Chip_SDIF_Init(LPC_SDMMC_T *pSDMMC);

/**
 * @brief	Shutdown the SD/MMC card controller
 * @param	pSDMMC	: SDMMC peripheral selected
 * @return	None
 */
void Chip_SDIF_DeInit(LPC_SDMMC_T *pSDMMC);

/**
 * @brief	Disable slot power
 * @param	pSDMMC	: SDMMC peripheral selected
 * @return	None
 * @note	Uses SD_POW pin, set to low.
 */
STATIC INLINE void Chip_SDIF_PowerOff(LPC_SDMMC_T *pSDMMC)
{
	IP_SDMMC_PowerOff(pSDMMC);
}

/**
 * @brief	Enable slot power
 * @param	pSDMMC	: SDMMC peripheral selected
 * @return	None
 * @note	Uses SD_POW pin, set to high.
 */
STATIC INLINE void Chip_SDIF_PowerOn(LPC_SDMMC_T *pSDMMC)
{
	IP_SDMMC_PowerOn(pSDMMC);
}

/**
 * @brief	Sets the SD interface interrupt mask
 * @param	pSDMMC	: SDMMC peripheral selected
 * @param	iVal	: Interrupts to enable, Or'ed values MCI_INT_*
 * @return	None
 */
STATIC INLINE void Chip_SDIF_SetIntMask(LPC_SDMMC_T *pSDMMC, uint32_t iVal)
{
	IP_SDMMC_SetIntMask(pSDMMC, iVal);
}

/**
 * @brief	Returns the current SD status, clears pending ints, and disables all ints
 * @param	pSDMMC	: SDMMC peripheral selected
 * @return	Current pending interrupt status of Or'ed values MCI_INT_*
 */
uint32_t Chip_SDIF_GetIntStatus(LPC_SDMMC_T *pSDMMC);

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __SDIF_18XX_43XX_H_ */
