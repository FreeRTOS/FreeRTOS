/*
 * @brief CMP Registers and control functions
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

#ifndef __CMP_001_H_
#define __CMP_001_H_

#include "sys_config.h"
#include "cmsis.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup IP_CMP_001 IP: Comparator register block and driver
 * @ingroup IP_Drivers
 * Comparator
 * @{
 */
/** The number of embeded comparators supported */
#define CMP_NUM         2

/**
 * @brief Comparator (CMP) register block structure
 */
typedef struct {										/*!< Comparator structure                                   */
	__IO uint32_t  CMP_CTRL;							/*!< Comparator block control register                      */
	__IO uint32_t  CMP_CTRLx[CMP_NUM];					/*!< Specific comparator control register                          */
} IP_CMP_001_T;

/**
 * @brief Comparator control definition
 */
typedef enum IP_CMP_ENCTRL {
	CMP_ENCTRL_DISABLE,			/*!< Disable */
	CMP_ENCTRL_DIS_IN_DS_PWD,	/*!< Disable in deep sleep mode and power down mode*/
	CMP_ENCTRL_DIS_IN_PWD,		/*!< Disable in power down mode*/
	CMP_ENCTRL_ENABLE,			/*!< Enable/Power-up*/
} IP_CMP_ENCTRL_T;

/*!< Comparator control register Bitmask */
#define CMP_CTRL_BITMASK     (0xF30F)
/*!< The comparator current source control bitmask*/
#define CMP_CTRL_PD_IREF_BITMASK            (0x03)
/*!< Control the comparator current source (n is IP_CMP_ENCTRL_T value)*/
#define CMP_CTRL_PD_IREF(n)                 ((((uint32_t) (n)) & 0x03))
/*!< The comparator bandgap reference control bitmask*/
#define CMP_CTRL_PD_VBG_BITMASK             (((uint32_t) 0x03) << 2)
/*!< Control the comparator  bandgap reference (n is IP_CMP_ENCTRL_T value)*/
#define CMP_CTRL_PD_VBG(n)                  ((((uint32_t) (n)) & 0x03) << 2)
/*!< The CMP_ROSC ouput control bitmask */
#define CMP_CTRL_ROSC_BITMASK               ((uint32_t) 0x300)
/*!< The CMP_ROSC output is set by CMP1, reset by CMP0 */
#define CMP_CTRL_ROSCCTL_CMP1               (0x00)
/*!< The CMP_ROSC output is set by CMP0, reset by CMP1 */
#define CMP_CTRL_ROSCCTL_CMP0               (((uint32_t) 0x01) << 8)
/*!< The CMP_ROSC output is reset by the internal chip reset */
#define CMP_CTRL_EXT_RESET_INTERNAL         (0x00)
/*!< The CMP_ROSC output is reset by the CMP_RESET input */
#define CMP_CTRL_EXT_RESET_CMPRESET         (((uint32_t) 0x01) << 9)
/*!< Timer Capture input control bitmask */
#define CMP_CTRL_TIMERCAPTURE_BITMASK       ((uint32_t) 0xF000)
/*!< Selects the comparator 0 level output as the input for Timer0 capture input 2 */
#define CMP_CTRL_T0CAP2_0LEVEL              (0x00)
/*!< Selects the comparator 1 level output as the input for Timer0 capture input 2 */
#define CMP_CTRL_T0CAP2_1LEVEL              (((uint32_t) 0x01) << 12)
/*!< Selects the comparator 0 edge output as the input for Timer0 capture input 3 */
#define CMP_CTRL_T0CAP3_0EDGE               (0x00)
/*!< Selects the comparator 1 edge output as the input for Timer0 capture input 3 */
#define CMP_CTRL_T0CAP3_1EDGE               (((uint32_t) 0x01) << 13)
/*!< Selects the comparator 1 edge output as the input for Timer1 capture input 2 */
#define CMP_CTRL_T1CAP2_1EDGE               (0x00)
/*!< Selects the comparator 0 level output as the input for Timer1 capture input 2 */
#define CMP_CTRL_T1CAP2_0LEVEL              (((uint32_t) 0x01) << 14)
/*!< Selects the comparator 1 level output as the input for Timer1 capture input 3 */
#define CMP_CTRL_T1CAP3_1LEVEL              (0x00)
/*!< Selects the comparator 0 edge output as the input for Timer1 capture input 3 */
#define CMP_CTRL_T1CAP3_0EDGE               (((uint32_t) 0x01) << 15)

/*!< The comparator x control register Bitmask */
#define CMP_CTRLx_BITMASK           ((uint32_t) 0x1F7FF77F)
/*!< The comparator x enable bitmask*/
#define CMP_CTRLx_EN_BITMASK            (0x03)
/*!< Control the comparator x (n is IP_CMP_ENCTRL_T value)*/
#define CMP_CTRLx_EN(n)                 ((((uint32_t) (n)) & 0x03))
/*!< Enable the output of compartor x */
#define CMP_CTRLx_OE                    (((uint32_t) 0x01) << 2)
/*!< The status of compartor x, reflects the comparator x output*/
#define CMP_CTRLx_STAT                  (((uint32_t) 0x01) << 3)
/*!< Comparator VM input control bitmask */
#define CMP_CTRLx_VM_BITMASK            (((uint32_t) 0x07) << 4)
/*!< Select the VM input*/
#define CMP_CTRLx_VM(n)                 ((((uint32_t) (n)) & 0x07) << 4)
/*!< Comparator VP input control bitmask */
#define CMP_CTRLx_VP_BITMASK            (((uint32_t) 0x07) << 8)
/*!< Select the VP input */
#define CMP_CTRLx_VP(n)                 ((((uint32_t) (n)) & 0x07) << 8)
/*!< Synchronize the Comparator x output with the internal bus clock for outpur to other peripherals */
#define CMP_CTRLx_SYNC                  (((uint32_t) 0x01) << 12)
/*!< Comparator Hysteresis control bitmask */
#define CMP_CTRLx_HYS_BITMASK           (((uint32_t) 0x03) << 13)
/*!< Determine the difference required between  the comparator inputs before the comparator output switch*/
#define CMP_CTRLx_HYS(n)                ((((uint32_t) (n)) & 0x03) << 13)
/*!< Interrupt control bitmask */
#define CMP_CTRLx_INTCTRL_BITMASK       ((uint32_t) 0x78000)
/*!< Comparator output is used as-is for generating interrupts. */
#define CMP_CTRLx_INTPOL_NORMAL         (0x00)
/*!< Comparator output is used inverted for generating interrupts. */
#define CMP_CTRLx_INTPOL_INV            (((uint32_t) 0x01) << 15)
/*!< Comparator x interrupt is edge triggered. */
#define CMP_CTRLx_INTTYPE_EDGE          (0x00)
/*!< Comparator x interrupt is level triggered.*/
#define CMP_CTRLx_INTTYPE_LEVEL         (((uint32_t) 0x01) << 16)
/*!< Comparator x interrupt edge control bitmask */
#define CMP_CTRLx_INTEDGE_BITMASK       (((uint32_t) 0x03) << 17)
/*!< Select edge on which triggered interrupt is active*/
#define CMP_CTRLx_INTEDGE(n)            ((((uint32_t) (n)) & 0x03) << 17)
/*!< Comparator interrupt flag */
#define CMP_CTRLx_INTFLAG               (((uint32_t) 0x01) << 19)
/*!< The VLAD Enable bitmask*/
#define CMP_CTRLx_VLADEN_BITMASK        (((uint32_t) 0x03) << 20)
/*!< Control the comparator x  (n is IP_CMP_ENCTRL_T value)*/
#define CMP_CTRLx_VLADEN(n)             ((((uint32_t) (n)) & 0x03) << 20)
/*!< Select VREF_CMP pin as voltage reference for comparator voltage ladder */
#define CMP_CTRLx_VLADREF_VREFCMP       (0x00)
/*!< Select VDDA pin as voltage reference for comparator voltage ladder */
#define CMP_CTRLx_VLADREF_VDDA          (((uint32_t) 0x01) << 22)
/*!< Volatge ladder value bitmask */
#define CMP_CTRLx_VSEL_BITMASK          ((uint32_t) ((0x1F) << 24))
/*!< Voltage ladder value for Comparator */
#define CMP_CTRLx_VSEL(n)               ((((uint32_t) (n)) & 0x1F) << 24)

/**
 * @brief Comparator VM/VP input definitions
 */
typedef enum IP_CMP_INPUT {
	CMP_INPUT_VREF_DIV,			/*!< Vref divider.*/
	CMP_INPUT_CMPx_IN0,			/*!< Use the input 0 of the comparator*/
	CMP_INPUT_CMPx_IN1,			/*!< Use the input 1 of the comparator*/
	CMP_INPUT_CMPx_IN2,			/*!< Use the input 2 of the comparator*/
	CMP_INPUT_CMPx_IN3,			/*!< Use the input 3 of the comparator*/
	CMP_INPUT_CMP_OTHER_IN0,	/*!< Use the input 0 of the other comparator.*/
	CMP_INPUT_INTERNAL_09VBG,	/*!< internal 0.9 V band gap reference.*/
} IP_CMP_INPUT_T;

/**
 * @brief Comparator hysteresis selection definitions
 */
typedef enum IP_CMP_HYS {
	CMP_HYS_NONE = CMP_CTRLx_HYS(0),		/*!<No hysteresis (the output will switch as the voltages cross) */
	CMP_HYS_5MV  = CMP_CTRLx_HYS(1),		/*!< 5mV hysteresis */
	CMP_HYS_10MV = CMP_CTRLx_HYS(2),		/*!< 10mV hysteresis */
	CMP_HYS_15MV = CMP_CTRLx_HYS(3),		/*!< 15mV hysteresis */
} IP_CMP_HYS_T;

/**
 * @brief Comparator interrupt edge selection definitions
 */
typedef enum IP_CMP_INTEDGE {
	CMP_INTEDGE_FALLING = CMP_CTRLx_INTEDGE(0),	/*!< Interrupt is active on falling edge */
	CMP_INTEDGE_RISING  = CMP_CTRLx_INTEDGE(1),	/*!< Interrupt is active on rising edge */
	CMP_INTEDGE_BOTH    = CMP_CTRLx_INTEDGE(2),	/*!< Interrupt is active on falling and rising edges */
} IP_CMP_INTEDGE_T;

/**
 * @brief	Initializes the CMP
 * @param	pCMP	: Pointer to Comparator Register block
 * @return	Nothing
 */
STATIC INLINE void IP_CMP_Init(IP_CMP_001_T *pCMP) {}

/**
 * @brief	De-initializes the CMP
 * @param	pCMP	: Pointer to Comparator Register block
 * @return	Nothing
 */
STATIC INLINE void IP_CMP_DeInit(IP_CMP_001_T *pCMP) {}

/**
 * @brief	Enables comparator current source
 * @param	pCMP	: Pointer to Comparator Register block
 * @param	en		: Enable mode
 * @return	Nothing
 */
STATIC INLINE void IP_CMP_EnableCurrentSrc(IP_CMP_001_T *pCMP,  IP_CMP_ENCTRL_T en)
{
	pCMP->CMP_CTRL = (pCMP->CMP_CTRL & (~CMP_CTRL_PD_IREF_BITMASK)) | CMP_CTRL_PD_IREF(en);
}

/**
 * @brief	Enables comparator bandgap reference
 * @param	pCMP	: Pointer to Comparator Register block
 * @param	en		: Enable mode
 * @return	Nothing
 */
STATIC INLINE void IP_CMP_EnableBandGap(IP_CMP_001_T *pCMP,  IP_CMP_ENCTRL_T en)
{
	pCMP->CMP_CTRL = (pCMP->CMP_CTRL & (~CMP_CTRL_PD_VBG_BITMASK)) | CMP_CTRL_PD_VBG(en);
}

/**
 * @brief	Control CMP_ROSC
 * @param	pCMP	: Pointer to Comparator Register block
 * @param	flag		: Or-ed bit value of CMP_CTRL_ROSCCTL_* and CMP_CTRL_EXT_RESET_*
 * @return	Nothing
 */
STATIC INLINE void IP_CMP_ControlROSC(IP_CMP_001_T *pCMP,  uint32_t flag)
{
	pCMP->CMP_CTRL = (pCMP->CMP_CTRL & (~CMP_CTRL_ROSC_BITMASK)) | flag;
}

/**
 * @brief	Control CMP_ROSC
 * @param	pCMP	: Pointer to Comparator Register block
 * @param	flag		: Or-ed bit value of CMP_CTRL_T*CAP*
 * @return	Nothing
 */
STATIC INLINE void IP_CMP_SetTimerCapInput(IP_CMP_001_T *pCMP,  uint32_t flag)
{
	pCMP->CMP_CTRL = (pCMP->CMP_CTRL & (~CMP_CTRL_TIMERCAPTURE_BITMASK)) | flag;
}

/**
 * @brief	Sets up voltage ladder
 * @param	pCMP			: Pointer to Comparator Register block
 * @param	id				: Comparator ID
 * @param	ladSel			: Voltage ladder value (0~31).
 * @param	flag				:0(CMP_VREF used)/CMP_CTRLx_VLADREF_VDDA (VDDA used)
 * @return	Nothing
 * @note		VREF divider 0 = ladSel*VRef0/31
 */
STATIC INLINE void IP_CMP_SetupVoltLadder(IP_CMP_001_T *pCMP,  uint8_t id,
										  uint16_t ladSel, uint32_t flag)
{
	pCMP->CMP_CTRLx[id] = (pCMP->CMP_CTRLx[id] & (~(CMP_CTRLx_VSEL_BITMASK | CMP_CTRLx_VLADREF_VDDA))) | CMP_CTRLx_VSEL(
		ladSel) | flag;
}

/**
 * @brief	Enables voltage ladder
 * @param	pCMP	: Pointer to Comparator Register block
 * @param	id		: Comparator ID
 * @param	en		: Enable mode
 * @return	Nothing
 */
STATIC INLINE void IP_CMP_EnableVoltLadder(IP_CMP_001_T *pCMP,  uint8_t id, IP_CMP_ENCTRL_T en)
{
	pCMP->CMP_CTRLx[id] = (pCMP->CMP_CTRLx[id] & (~CMP_CTRLx_VLADEN_BITMASK)) | CMP_CTRLx_VLADEN(en);
}

/**
 * @brief	Selects positive voltage input
 * @param	pCMP	: Pointer to Comparator Register block
 * @param	id		: Comparator ID
 * @param       input	: Selected input
 * @return	Nothing
 */
STATIC INLINE void IP_CMP_SetPosVoltRef(IP_CMP_001_T *pCMP, uint8_t id, IP_CMP_INPUT_T input)
{
	pCMP->CMP_CTRLx[id] = (pCMP->CMP_CTRLx[id] & (~CMP_CTRLx_VP_BITMASK)) | CMP_CTRLx_VP(input);
}

/**
 * @brief	Selects negative voltage input
 * @param	pCMP	: Pointer to Comparator Register block
 * @param	id		: Comparator ID
 * @param	input	: Selected input
 * @return	Nothing
 */
STATIC INLINE void IP_CMP_SetNegVoltRef(IP_CMP_001_T *pCMP, uint8_t id, IP_CMP_INPUT_T input)
{
	pCMP->CMP_CTRLx[id] = (pCMP->CMP_CTRLx[id] & (~CMP_CTRLx_VM_BITMASK)) | CMP_CTRLx_VM(input);
}

/**
 * @brief	Selects hysteresis level
 * @param	pCMP	: Pointer to Comparator Register block
 * @param	id		: Comparator ID
 * @param	hys		: Selected Hysteresis level
 * @return	Nothing
 */
STATIC INLINE void IP_CMP_SetHysteresis(IP_CMP_001_T *pCMP, uint8_t id, IP_CMP_HYS_T hys)
{
	pCMP->CMP_CTRLx[id] = (pCMP->CMP_CTRLx[id] & (~CMP_CTRLx_HYS_BITMASK)) | hys;
}

/**
 * @brief	Enables specified comparator
 * @param	pCMP	: Pointer to Comparator Register block
 * @param	id		: Comparator ID
 * @param	en		: Enable mode
 * @return	Nothing
 */
STATIC INLINE void IP_CMP_Enable(IP_CMP_001_T *pCMP,  uint8_t id, IP_CMP_ENCTRL_T en)
{
	pCMP->CMP_CTRLx[id] = (pCMP->CMP_CTRLx[id] & (~CMP_CTRLx_EN_BITMASK)) | CMP_CTRLx_EN(en);
}

/**
 * @brief	Returns the current comparator status
 * @param	pCMP	: Pointer to Comparator Register block
 * @param	id	: Comparator Id (0/1)
 * @return	SET/RESET
 */
STATIC INLINE FlagStatus IP_CMP_GetCmpStatus(IP_CMP_001_T *pCMP, uint8_t id)
{
	return (pCMP->CMP_CTRLx[id] & CMP_CTRLx_STAT) ? SET : RESET;
}

/**
 * @brief	Enable comparator output
 * @param	pCMP	: Pointer to Comparator Register block
 * @param	id		: Comparator ID
 * @return	Nothing
 */
STATIC INLINE void IP_CMP_EnableOuput(IP_CMP_001_T *pCMP, uint8_t id)
{
	pCMP->CMP_CTRLx[id] |= CMP_CTRLx_OE;
}

/**
 * @brief		Disable comparator output
 * @param	pCMP	: Pointer to Comparator Register block
 * @param	id		: Comparator ID
 * @return	Nothing
 */
STATIC INLINE void IP_CMP_DisableOutput(IP_CMP_001_T *pCMP, uint8_t id)
{
	pCMP->CMP_CTRLx[id] &= ~CMP_CTRLx_OE;
}

/**
 * @brief	Synchronizes Comparator output to bus clock
 * @param	pCMP	: Pointer to Comparator Register block
 * @param	id		: Comparator ID
 * @return	Nothing
 */
STATIC INLINE void IP_CMP_EnableSyncCmpOut(IP_CMP_001_T *pCMP, uint8_t id)
{
	pCMP->CMP_CTRLx[id] |= CMP_CTRLx_SYNC;
}

/**
 * @brief	Sets comparator output to be used directly (no sync)
 * @param	pCMP	: Pointer to Comparator Register block
 * @param	id		: Comparator ID
 * @return	Nothing
 */
STATIC INLINE void IP_CMP_DisableSyncCmpOut(IP_CMP_001_T *pCMP, uint8_t id)
{
	pCMP->CMP_CTRLx[id] &= ~CMP_CTRLx_SYNC;
}

/**
 * @brief	Sets up comparator interrupt
 * @param	pCMP	: Pointer to Comparator Register block
 * @param	id		: Comparator ID
 * @param	intFlag	: Or-ed value of CMP_CTRLx_INTTYPE_*, CMP_CTRLx_INTPOL_*
 * @param	edgeSel	: the edge on which interrupt occurs.
 * @return	Nothing
 */
STATIC INLINE void IP_CMP_ConfigInt(IP_CMP_001_T *pCMP, uint8_t id,
									uint32_t intFlag,
									IP_CMP_INTEDGE_T edgeSel)
{
	pCMP->CMP_CTRLx[id] = (pCMP->CMP_CTRLx[id] & (~CMP_CTRLx_INTCTRL_BITMASK)) | intFlag | edgeSel;
}

/**
 * @brief	Get the CMP interrupt status
 * @param	pCMP	: Pointer to Comparator Register block
 * @param	id		: Comparator ID
 * @return	SET/RESET
 */
STATIC INLINE FlagStatus IP_CMP_GetIntStatus(IP_CMP_001_T *pCMP, uint8_t id)
{
	return (pCMP->CMP_CTRLx[id] & CMP_CTRLx_INTFLAG) ? SET : RESET;
}

/**
 * @brief	Clears the CMP interrupt status
 * @param	pCMP	: Pointer to Comparator Register block
 * @param	id		: Comparator ID
 * @return	Nothing
 */
STATIC INLINE void IP_CMP_CMP_ClearIntStatus(IP_CMP_001_T *pCMP, uint8_t id)
{
	pCMP->CMP_CTRLx[id] |= CMP_CTRLx_INTFLAG;
}

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __CMP_001_H_ */
