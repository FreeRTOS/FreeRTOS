/*
 * @brief LPC18xx/43xx Power Management Controller driver
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

#ifndef __PMC_18XX_43XX_H_
#define __PMC_18XX_43XX_H_

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup PMC_18XX_43XX CHIP: LPC18xx/43xx Power Management Controller driver
 * @ingroup CHIP_18XX_43XX_Drivers
 * @{
 */

/*
 * @brief PMC power states
 */
typedef enum CHIP_PMC_PWR_STATE {
	PMC_DeepSleep = PMC_PWR_DEEP_SLEEP_MODE,			/*!< Deep sleep state */
	PMC_PowerDown = PMC_PWR_POWER_DOWN_MODE,			/*!< Power Down state */
	PMC_DeepPowerDown = PMC_PWR_DEEP_POWER_DOWN_MODE,	/*!< Power Down state */
} CHIP_PMC_PWR_STATE_T;

/**
 * @brief	Set to sleep power state
 * @return	Nothing
 */
void Chip_PMC_Sleep(void);

/**
 * @brief	Set to sleep power mode
 * @param	PwrState	: Power State as specified in /a CHIP_PMC_PWR_STATE_T enum
 * @return	Nothing
 */
void Chip_PMC_Set_PwrState(CHIP_PMC_PWR_STATE_T PwrState);

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __PMC_18XX_43XX_H_ */
