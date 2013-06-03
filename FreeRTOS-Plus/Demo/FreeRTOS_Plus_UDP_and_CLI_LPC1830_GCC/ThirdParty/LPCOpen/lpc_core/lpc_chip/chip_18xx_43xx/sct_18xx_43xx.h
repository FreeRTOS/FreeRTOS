/*
 * @brief LPC18xx/43xx State Configurable Timer driver
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

#ifndef __SCT_18XX_43XX_H_
#define __SCT_18XX_43XX_H_

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup SCT_18XX_43XX CHIP: LPC18xx/43xx State Configurable Timer driver
 * @ingroup CHIP_18XX_43XX_Drivers
 * @{
 */

/**
 * @brief	Initialize SCT
 * @param	pSCT			: Pointer to SCT register block
 * @return	Nothing
 */
void Chip_SCT_Init(LPC_SCT_T *pSCT);

/**
 * @brief	Shutdown SCT
 * @param	pSCT			: Pointer to SCT register block
 * @return	Nothing
 */
void Chip_SCT_DeInit(LPC_SCT_T *pSCT);

/**
 * @brief	Configure SCT
 * @param	pSCT			: Pointer to SCT register block
 * @param	value			: SCT Configuration register value
 * @return	Nothing
 * Initialise the SCT configuration register with \a value
 */
STATIC INLINE void Chip_SCT_Config(LPC_SCT_T *pSCT, uint32_t value)
{
	IP_SCT_Config(pSCT, value);
}

/**
 * @brief	Set or Clear the Control register
 * @param	pSCT			: Pointer to SCT register block
 * @param	value			: SCT Control register value
 * @param	ena             : ENABLE - To set the fields specified by value
 *                          : DISABLE - To clear the field specified by value
 * @return	Nothing
 * Set or clear the control register bits as specified by the \a value
 * parameter. If \a ena is set to ENABLE, the mentioned register fields
 * will be set. If \a ena is set to DISABLE, the mentioned register
 * fields will be cleared
 */
STATIC INLINE void Chip_SCT_ControlSetClr(LPC_SCT_T *pSCT, uint32_t value, FunctionalState ena)
{
	IP_SCT_ControlSetClr(pSCT, value, ena);
}

/**
 * @brief	Set the conflict resolution
 * @param	pSCT			: Pointer to SCT register block
 * @param	outnum			: Output number
 * @param	value           : Output value
 *                          - SCT_RES_NOCHANGE		:No change
 *					        - SCT_RES_SET_OUTPUT	:Set output
 *					        - SCT_RES_CLEAR_OUTPUT	:Clear output
 *					        - SCT_RES_TOGGLE_OUTPUT :Toggle output
 *                          : SCT_RES_NOCHANGE
 *                          : DISABLE - To clear the field specified by value
 * @return	Nothing
 * Set conflict resolution for the output \a outnum
 */
STATIC INLINE void Chip_SCT_ConflictResolutionSet(LPC_SCT_T *pSCT, uint8_t outnum, uint8_t value)
{
	IP_SCT_ConflictResolutionSet(pSCT, outnum, value);
}

/**
 * @brief	Clear the SCT event flag
 * @param	pSCT			: Pointer to SCT register block
 * @param	even_num		: SCT Event number
 * @return	Nothing
 * Clear the SCT event flag for the specified event \a even_num
 */
STATIC INLINE void Chip_SCT_EventFlagClear(LPC_SCT_T *pSCT, uint8_t even_num)
{
	IP_SCT_EventFlagClear(pSCT, even_num);
}

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __SCT_18XX_43XX_H_ */
