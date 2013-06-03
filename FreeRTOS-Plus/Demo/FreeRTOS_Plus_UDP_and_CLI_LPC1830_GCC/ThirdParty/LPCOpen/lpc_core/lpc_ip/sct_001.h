/*
 * @brief State Configurable Timer registers and control functions
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

#ifndef __SCT_001_H_
#define __SCT_001_H_

#include "sys_config.h"
#include "cmsis.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup IP_SCT_001 IP: SCT register block and driver
 * @ingroup IP_Drivers
 * State Configurable Timer
 * @{
 */

/**
 * @brief SCT Module configuration
 */
#define CONFIG_SCT_nEV   (16)			/*!< Number of events */
#define CONFIG_SCT_nRG   (16)			/*!< Number of match/compare registers */
#define CONFIG_SCT_nOU   (16)			/*!< Number of outputs */

/**
 * @brief State Configurable Timer register block structure
 */
typedef struct {
	__IO  uint32_t CONFIG;				/*!< Configuration Register */
	union {
		__IO uint32_t CTRL_U;			/*!< Control Register */
		struct {
			__IO uint16_t CTRL_L;		/*!< Low control register */
			__IO uint16_t CTRL_H;		/*!< High control register */
		};

	};

	__IO uint16_t LIMIT_L;				/*!< limit register for counter L */
	__IO uint16_t LIMIT_H;				/*!< limit register for counter H */
	__IO uint16_t HALT_L;				/*!< halt register for counter L */
	__IO uint16_t HALT_H;				/*!< halt register for counter H */
	__IO uint16_t STOP_L;				/*!< stop register for counter L */
	__IO uint16_t STOP_H;				/*!< stop register for counter H */
	__IO uint16_t START_L;				/*!< start register for counter L */
	__IO uint16_t START_H;				/*!< start register for counter H */
	uint32_t RESERVED1[10];				/*!< 0x03C reserved */
	union {
		__IO uint32_t COUNT_U;			/*!< counter register */
		struct {
			__IO uint16_t COUNT_L;		/*!< counter register for counter L */
			__IO uint16_t COUNT_H;		/*!< counter register for counter H */
		};

	};

	__IO uint16_t STATE_L;				/*!< state register for counter L */
	__IO uint16_t STATE_H;				/*!< state register for counter H */
	__I  uint32_t INPUT;				/*!< input register */
	__IO uint16_t REGMODE_L;			/*!< match - capture registers mode register L */
	__IO uint16_t REGMODE_H;			/*!< match - capture registers mode register H */
	__IO uint32_t OUTPUT;				/*!< output register */
	__IO uint32_t OUTPUTDIRCTRL;		/*!< output counter direction Control Register */
	__IO uint32_t RES;					/*!< conflict resolution register */
	__IO uint32_t DMA0REQUEST;			/*!< DMA0 Request Register */
	__IO uint32_t DMA1REQUEST;			/*!< DMA1 Request Register */
	uint32_t RESERVED2[35];
	__IO uint32_t EVEN;					/*!< event enable register */
	__IO uint32_t EVFLAG;				/*!< event flag register */
	__IO uint32_t CONEN;				/*!< conflict enable register */
	__IO uint32_t CONFLAG;				/*!< conflict flag register */
	union {
		__IO union {					/*!< ... Match / Capture value */
			uint32_t U;					/*!<       SCTMATCH[i].U  Unified 32-bit register */
			struct {
				uint16_t L;				/*!<       SCTMATCH[i].L  Access to L value */
				uint16_t H;				/*!<       SCTMATCH[i].H  Access to H value */
			};

		} MATCH[CONFIG_SCT_nRG];

		__I union {
			uint32_t U;					/*!<       SCTCAP[i].U  Unified 32-bit register */
			struct {
				uint16_t L;				/*!<       SCTCAP[i].L  Access to L value */
				uint16_t H;				/*!<       SCTCAP[i].H  Access to H value */
			};

		} CAP[CONFIG_SCT_nRG];

	};

	uint32_t RESERVED3[32 - CONFIG_SCT_nRG];		/*!< ...-0x17C reserved */
	union {
		__IO uint16_t MATCH_L[CONFIG_SCT_nRG];		/*!< 0x180-... Match Value L counter */
		__I  uint16_t CAP_L[CONFIG_SCT_nRG];		/*!< 0x180-... Capture Value L counter */
	};

	uint16_t RESERVED4[32 - CONFIG_SCT_nRG];		/*!< ...-0x1BE reserved */
	union {
		__IO uint16_t MATCH_H[CONFIG_SCT_nRG];		/*!< 0x1C0-... Match Value H counter */
		__I  uint16_t CAP_H[CONFIG_SCT_nRG];		/*!< 0x1C0-... Capture Value H counter */
	};

	uint16_t RESERVED5[32 - CONFIG_SCT_nRG];		/*!< ...-0x1FE reserved */
	union {
		__IO union {					/*!< 0x200-... Match Reload / Capture Control value */
			uint32_t U;					/*!<       SCTMATCHREL[i].U  Unified 32-bit register */
			struct {
				uint16_t L;				/*!<       SCTMATCHREL[i].L  Access to L value */
				uint16_t H;				/*!<       SCTMATCHREL[i].H  Access to H value */
			};

		} MATCHREL[CONFIG_SCT_nRG];

		__IO union {
			uint32_t U;					/*!<       SCTCAPCTRL[i].U  Unified 32-bit register */
			struct {
				uint16_t L;				/*!<       SCTCAPCTRL[i].L  Access to L value */
				uint16_t H;				/*!<       SCTCAPCTRL[i].H  Access to H value */
			};

		} CAPCTRL[CONFIG_SCT_nRG];

	};

	uint32_t RESERVED6[32 - CONFIG_SCT_nRG];		/*!< ...-0x27C reserved */
	union {
		__IO uint16_t MATCHREL_L[CONFIG_SCT_nRG];	/*!< 0x280-... Match Reload value L counter */
		__IO uint16_t CAPCTRL_L[CONFIG_SCT_nRG];	/*!< 0x280-... Capture Control value L counter */
	};

	uint16_t RESERVED7[32 - CONFIG_SCT_nRG];		/*!< ...-0x2BE reserved */
	union {
		__IO uint16_t MATCHREL_H[CONFIG_SCT_nRG];	/*!< 0x2C0-... Match Reload value H counter */
		__IO uint16_t CAPCTRL_H[CONFIG_SCT_nRG];	/*!< 0x2C0-... Capture Control value H counter */
	};

	uint16_t RESERVED8[32 - CONFIG_SCT_nRG];		/*!< ...-0x2FE reserved */
	__IO struct {						/*!< 0x300-0x3FC  SCTEVENT[i].STATE / SCTEVENT[i].CTRL*/
		uint32_t STATE;					/*!< Event State Register */
		uint32_t CTRL;					/*!< Event Control Register */
	} EVENT[CONFIG_SCT_nEV];

	uint32_t RESERVED9[128 - 2 * CONFIG_SCT_nEV];	/*!< ...-0x4FC reserved */
	__IO struct {						/*!< 0x500-0x57C  SCTOUT[i].SET / SCTOUT[i].CLR */
		uint32_t SET;					/*!< Output n Set Register */
		uint32_t CLR;					/*!< Output n Clear Register */
	} OUT[CONFIG_SCT_nOU];

	uint32_t RESERVED10[191 - 2 * CONFIG_SCT_nOU];	/*!< ...-0x7F8 reserved */
	__I  uint32_t MODULECONTENT;		/*!< 0x7FC Module Content */
} IP_SCT_001_T;

/**
 * @brief Macro defines for SCT configuration register
 */
#define SCT_CONFIG_16BIT_COUNTER        0x00000000	/*!< Operate as 2 16-bit counters */
#define SCT_CONFIG_32BIT_COUNTER        0x00000001	/*!< Operate as 1 32-bit counter */

#define SCT_CONFIG_CLKMODE_BUSCLK       (0x0 << 1)	/*!< Bus clock */
#define SCT_CONFIG_CLKMODE_SCTCLK       (0x1 << 1)	/*!< SCT clock */
#define SCT_CONFIG_CLKMODE_INCLK        (0x2 << 1)	/*!< Input clock selected in CLKSEL field */
#define SCT_CONFIG_CLKMODE_INEDGECLK    (0x3 << 1)	/*!< Input clock edge selected in CLKSEL field */

#define SCT_CONFIG_NORELOADL_U          (0x1 << 7)	/*!< Operate as 1 32-bit counter */
#define SCT_CONFIG_NORELOADH            (0x1 << 8)	/*!< Operate as 1 32-bit counter */

/*
 * @brief Macro defines for SCT control register
 */
#define COUNTUP_TO_LIMIT_THEN_CLEAR_TO_ZERO     0			/*!< Direction for low or unified counter */
#define COUNTUP_TO LIMIT_THEN_COUNTDOWN_TO_ZERO 1

#define SCT_CTRL_STOP_L                 (1 << 1)				/*!< Stop low counter */
#define SCT_CTRL_HALT_L                 (1 << 2)				/*!< Halt low counter */
#define SCT_CTRL_CLRCTR_L               (1 << 3)				/*!< Clear low or unified counter */
#define SCT_CTRL_BIDIR_L(x)             (((x) & 0x01) << 4)		/*!< Bidirectional bit */
#define SCT_CTRL_PRE_L(x)               (((x) & 0xFF) << 5)		/*!< Prescale clock for low or unified counter */

#define COUNTUP_TO_LIMIT_THEN_CLEAR_TO_ZERO     0			/*!< Direction for high counter */
#define COUNTUP_TO LIMIT_THEN_COUNTDOWN_TO_ZERO 1
#define SCT_CTRL_STOP_H                 (1 << 17)				/*!< Stop high counter */
#define SCT_CTRL_HALT_H                 (1 << 18)				/*!< Halt high counter */
#define SCT_CTRL_CLRCTR_H               (1 << 19)				/*!< Clear high counter */
#define SCT_CTRL_BIDIR_H(x)             (((x) & 0x01) << 20)
#define SCT_CTRL_PRE_H(x)               (((x) & 0xFF) << 21)	/*!< Prescale clock for high counter */

/*
 * @brief Macro defines for SCT Conflict resolution register
 */
#define SCT_RES_NOCHANGE                (0)
#define SCT_RES_SET_OUTPUT              (1)
#define SCT_RES_CLEAR_OUTPUT            (2)
#define SCT_RES_TOGGLE_OUTPUT           (3)

/**
 * @brief	Set the value in SCT unified count register
 * @param	pSCT	: Pointer to SCT register block
 * @param	count	: SCT count value
 * @return	Nothing
 * @note	Writes 32-bit value into SCT unified count register
 */
STATIC INLINE void IP_SCT_SetCount(IP_SCT_001_T *pSCT, uint32_t count)
{
	pSCT->COUNT_U = count;
}

/**
 * @brief	Set the value in SCT Lower count register
 * @param	pSCT	: Pointer to SCT register block
 * @param	count	: SCT count value
 * @return	Nothing
 * @note	Writes 16-bit value into SCT Lower count register
 */
STATIC INLINE void IP_SCT_SetCountL(IP_SCT_001_T *pSCT, uint16_t count)
{
	pSCT->COUNT_L = count;
}

/**
 * @brief	Set the value in SCT Higher count register
 * @param	pSCT	: Pointer to SCT register block
 * @param	count	: SCT count value
 * @return	Nothing
 * @note	Writes 16-bit value into SCT Higher count register
 */
STATIC INLINE void IP_SCT_SetCountH(IP_SCT_001_T *pSCT, uint16_t count)
{
	pSCT->COUNT_H = count;
}

/**
 * @brief	Set the match value in SCT Unified match register
 * @param	pSCT	: Pointer to SCT register block
 * @param   n		: Match register number
 * @param	count	: SCT match count value
 * @return	Nothing
 * @note	Writes 32-bit value into SCT unified match register
 */
STATIC INLINE void IP_SCT_SetMatchCount(IP_SCT_001_T *pSCT, uint32_t n, uint32_t count)
{
	pSCT->MATCH[n].U = count;
}

/**
 * @brief	Set the match reload value in SCT Unified match reload register
 * @param	pSCT	: Pointer to SCT register block
 * @param   n		: Match register number
 * @param	count	: SCT match reload count value
 * @return	Nothing
 */
STATIC INLINE void IP_SCT_SetMatchReload(IP_SCT_001_T *pSCT, uint32_t n, uint32_t count)
{
	pSCT->MATCHREL[n].U = count;
}

/**
 * @brief	Enable the interrupt for the specified event
 * @param	pSCT	: Pointer to SCT register block
 * @param   evt		: Event value
 * @return	Nothing
 */
STATIC INLINE void IP_SCT_EventIntEnable(IP_SCT_001_T *pSCT, uint32_t evt)
{
	pSCT->EVEN |= evt;
}

/**
 * @brief	Disable the interrupt for the specified event
 * @param	pSCT	: Pointer to SCT register block
 * @param   evt		: Event value
 * @return	Nothing
 */
STATIC INLINE void IP_SCT_EventIntDisable(IP_SCT_001_T *pSCT, uint32_t evt)
{
	pSCT->EVEN &= ~(evt);
}

/**
 * @brief	Clear the specified event flag
 * @param	pSCT	: Pointer to SCT register block
 * @param   evt		: Event value
 * @return	Nothing
 */
STATIC INLINE void IP_SCT_ClearEventFlag(IP_SCT_001_T *pSCT, uint32_t evt)
{
	pSCT->EVFLAG |= evt;
}

/**
 * @brief	Configure SCT
 * @param	pSCT	: Pointer to SCT register block
 * @param	value	: SCT Configuration register value
 * @return	Nothing
 * @note Initialise the SCT configuration register with the \a value
 */
void IP_SCT_Config(IP_SCT_001_T *pSCT, uint32_t value);

/**
 * @brief	Set or Clear the Control register
 * @param	pSCT	: Pointer to SCT register block
 * @param	value	: SCT Control register value
 * @param	ena		: ENABLE - To set the fields specified by value
 *					: DISABLE - To clear the field specified by value
 * @return	Nothing
 * @note Set or clear the control register bits as specified by \a value.
 * If \a ena is set to ENABLE, the mentioned register fields
 * will be set. If a\ ena is set to DISABLE, the mentioned register
 * fields will be cleared
 */
void IP_SCT_ControlSetClr(IP_SCT_001_T *pSCT, uint32_t value, FunctionalState ena);

/**
 * @brief	Set the conflict resolution
 * @param	pSCT	: Pointer to SCT register block
 * @param	outnum	: Output number
 * @param	value	: Output value
 *                          - SCT_RES_NOCHANGE		:No change
 *					        - SCT_RES_SET_OUTPUT	:Set output
 *					        - SCT_RES_CLEAR_OUTPUT	:Clear output
 *					        - SCT_RES_TOGGLE_OUTPUT :Toggle output
 *                          : SCT_RES_NOCHANGE
 *                          : DISABLE - To clear the field specified by value
 * @return	Nothing
 * @note	Set conflict resolution value for the output \a outnum
 */
void IP_SCT_ConflictResolutionSet(IP_SCT_001_T *pSCT, uint8_t outnum, uint8_t value);

/**
 * @brief	Clear the SCT event flag
 * @param	pSCT		: Pointer to SCT register block
 * @param	even_num	: SCT Event number
 * @return	Nothing
 * @note	Clear the SCT event flag for the event \a even_num
 */
void IP_SCT_EventFlagClear(IP_SCT_001_T *pSCT, uint8_t even_num);

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __SCT_001_H_ */
