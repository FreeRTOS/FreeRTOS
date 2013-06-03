/*
 * @brief Analog comparator driver
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * All rights reserved.
 *
 * @par
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licenser disclaim any and
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

#ifndef __ACMP_001_H_
#define __ACMP_001_H_

#include "sys_config.h"
#include "cmsis.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup IP_ACMP_001 IP: Analog comparator driver
 * @ingroup IP_Drivers
 * @{
 */

/**
 * @brief Analog Comparator register block structure
 */
typedef struct {			/*!< ACMP Structure */
	__IO uint32_t  CTRL;	/*!< Comparator control register */
	__IO uint32_t  LAD;		/*!< Voltage ladder register */
} ACMP_001_T;

#define ACMP_COMPSA_BIT     (1 << 6)	/* Comparator output control bit */
#define ACMP_COMPSTAT_BIT   (1 << 21)	/* Comparator status, reflects the state of the comparator output */
#define ACMP_COMPEDGE_BIT   (1 << 23)	/* Comparator edge-detect status */
#define ACMP_LADENAB_BIT    (1 << 0)	/* Voltage ladder enable bit */

/** Edge selection for comparator */
typedef enum IP_ACMP_001_EDGESEL {
	ACMP_EDGESEL_FALLING = (0 << 3),	/* Set the COMPEDGE bit on falling edge */
	ACMP_EDGESEL_RISING  = (1 << 3),	/* Set the COMPEDGE bit on rising edge */
	ACMP_EDGESEL_BOTH    = (2 << 3)		/* Set the COMPEDGE bit on falling and rising edges */
} IP_ACMP_001_EDGESEL_T;

/** Hysteresis selection for comparator */
typedef enum IP_ACMP_HYS_001 {
	ACMP_HYS_NONE = (0 << 25),	/* No hysteresis (the output will switch as the voltages cross) */
	ACMP_HYS_5MV  = (1 << 25),	/* 5mV hysteresis */
	ACMP_HYS_10MV = (2 << 25),	/* 10mV hysteresis */
	ACMP_HYS_20MV = (3 << 25)	/* 20mV hysteresis */
} IP_ACMP_HYS_001_T;

/**
 * @brief	Initializes the ACMP
 * @param	pACMP	: Pointer to Analog Comparator block
 * @return	Nothing
 */
STATIC INLINE void IP_ACMP_Init(ACMP_001_T *pACMP) {}

/**
 * @brief	De-initializes the ACMP
 * @param	pACMP	: Pointer to Analog Comparator block
 * @return	Nothing
 */
STATIC INLINE void IP_ACMP_Deinit(ACMP_001_T *pACMP) {}

/**
 * @brief	Returns the current comparator status
 * @param	pACMP	: Pointer to Analog Comparator block
 * @return	Status is an Or'ed value of ACMP_COMPSTAT_BIT or ACMP_COMPEDGE_BIT
 */
STATIC INLINE uint32_t IP_ACMP_GetCompStatus(ACMP_001_T *pACMP)
{
	return pACMP->CTRL & (ACMP_COMPSTAT_BIT | ACMP_COMPEDGE_BIT);
}

/**
 * @brief	Clears the ACMP interrupt (EDGECLR bit)
 * @param	pACMP	: Pointer to Analog Comparator block
 * @return	Nothing
 */
void IP_ACMP_EdgeClear(ACMP_001_T *pACMP);

/**
 * @brief	Sets up ACMP edge selection
 * @param	pACMP	: Pointer to Analog Comparator block
 * @param	edgeSel	: Edge selection value
 * @return	Nothing
 */
void IP_ACMP_SetEdgeSelection(ACMP_001_T *pACMP, IP_ACMP_001_EDGESEL_T edgeSel);

/**
 * @brief	Synchronizes Comparator output to bus clock
 * @param	pACMP	: Pointer to Analog Comparator block
 * @return	Nothing
 */
STATIC INLINE void IP_ACMP_EnableSyncCompOut(ACMP_001_T *pACMP)
{
	pACMP->CTRL |= ACMP_COMPSA_BIT;
}

/**
 * @brief	Sets comparator output to be used directly (no sync)
 * @param	pACMP	: Pointer to Analog Comparator block
 * @return	Nothing
 */
STATIC INLINE void IP_ACMP_DisableSyncCompOut(ACMP_001_T *pACMP)
{
	pACMP->CTRL &= ~ACMP_COMPSA_BIT;
}

/**
 * @brief	Selects positive voltage input
 * @param	pACMP		: Pointer to Analog Comparator block
 * @param   Posinput	: one of the positive input voltage sources
 * @return	Nothing
 * @note	The caller must pre-shift the Posinput value to the
 * correct bitfield location in the CTRL register.
 */
void IP_ACMP_SetPosVoltRef(ACMP_001_T *pACMP, uint32_t Posinput);

/**
 * @brief	Selects negative voltage input
 * @param	pACMP		: Pointer to Analog Comparator block
 * @param   Neginput	: one of the negative input voltage sources
 * @return	Nothing
 * @note	The caller must pre-shift the Neginput value to the
 * correct bitfield location in the CTRL register.
 */
void IP_ACMP_SetNegVoltRef(ACMP_001_T *pACMP, uint32_t Neginput);

/**
 * @brief	Selects hysteresis level
 * @param	pACMP	: Pointer to Analog Comparator block
 * @param   hys		: Selected Hysteresis level
 * @return	Nothing
 */
void IP_ACMP_SetHysteresis(ACMP_001_T *pACMP, IP_ACMP_HYS_001_T hys);

/**
 * @brief	Helper function for setting up ACMP control
 * @param	pACMP		: Pointer to Analog Comparator block
 * @param	edgeSel		: Edge selection value
 * @param   Posinput	: one of the positive input voltage sources
 * @param   Neginput	: one of the negative input voltage sources
 * @param   hys         : Selected Hysteresis level
 * @return	Nothing
 * @note	The caller must pre-shift the Posinput and Neginput values to the
 * correct bitfield location in the CTRL register.
 */
void IP_ACMP_SetupAMCPRefs(ACMP_001_T *pACMP, IP_ACMP_001_EDGESEL_T edgeSel,
						   uint32_t Posinput, uint32_t Neginput, IP_ACMP_HYS_001_T hys);

/**
 * @brief	Sets up voltage ladder
 * @param	pACMP			: Pointer to Analog Comparator block
 * @param   ladsel			: Voltage ladder value
 * @param	ladrefVDDCMP	: Selects the reference voltage Vref for the voltage ladder
 *							: false for VDD, true for VDDCMP pin
 * @return	Nothing
 * @note	The caller must pre-shift the ladsel value to the
 * correct bitfield location in the LAD register.
 */
void IP_ACMP_SetupVoltLadder(ACMP_001_T *pACMP, uint32_t ladsel, bool ladrefVDDCMP);

/**
 * @brief	Enables voltage ladder
 * @param	pACMP	: Pointer to Analog Comparator block
 * @return	Nothing
 */
STATIC INLINE void IP_ACMP_EnableVoltLadder(ACMP_001_T *pACMP)
{
	pACMP->LAD |= ACMP_LADENAB_BIT;
}

/**
 * @brief	Disables voltage ladder
 * @param	pACMP	: Pointer to Analog Comparator block
 * @return	Nothing
 */
STATIC INLINE void IP_ACMP_DisableVoltLadder(ACMP_001_T *pACMP)
{
	pACMP->LAD &= ~ACMP_LADENAB_BIT;
}

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __ACMP_001_H_ */
