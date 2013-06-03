/*
 * @brief EEPROM registers and driver functions
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

#ifndef __EEPROM_002_H_
#define __EEPROM_002_H_

#include "sys_config.h"
#include "cmsis.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup IP_EEPROM_002 IP: EEPROM register block and driver (002) 
 * @ingroup IP_Drivers
 * @{
 */

/**
 * @brief EEPROM register block structure
 */
typedef struct {				/* EEPROM Structure */
	__IO uint32_t CMD;			/*!< EEPROM command register */
	uint32_t RESERVED0;
	__IO uint32_t RWSTATE;		/*!< EEPROM read wait state register */
	__IO uint32_t AUTOPROG;		/*!< EEPROM auto programming register */
	__IO uint32_t WSTATE;		/*!< EEPROM wait state register */
	__IO uint32_t CLKDIV;		/*!< EEPROM clock divider register */
	__IO uint32_t PWRDWN;		/*!< EEPROM power-down register */
	uint32_t RESERVED2[1007];
	__O  uint32_t INTENCLR;		/*!< EEPROM interrupt enable clear */
	__O  uint32_t INTENSET;		/*!< EEPROM interrupt enable set */
	__I  uint32_t INTSTAT;		/*!< EEPROM interrupt status */
	__I  uint32_t INTEN;		/*!< EEPROM interrupt enable */
	__O  uint32_t INTSTATCLR;	/*!< EEPROM interrupt status clear */
	__O  uint32_t INTSTATSET;	/*!< EEPROM interrupt status set */
} IP_EEPROM_002_T;

/*
 * @brief Macro defines for EEPROM command register
 */
#define EEPROM_CMD_ERASE_PRG_PAGE       (6)		/*!< EEPROM erase/program command */

/*
 * @brief Macro defines for EEPROM Auto Programming register
 */
#define EEPROM_AUTOPROG_OFF     (0)		/*!<Auto programming off */
#define EEPROM_AUTOPROG_AFT_1WORDWRITTEN     (1)		/*!< Erase/program cycle is triggered after 1 word is written */
#define EEPROM_AUTOPROG_AFT_LASTWORDWRITTEN  (2)		/*!< Erase/program cycle is triggered after a write to AHB
														   address ending with ......1111100 (last word of a page) */

/*
 * @brief Macro defines for EEPROM power down register
 */
#define EEPROM_PWRDWN                   (1 << 0)

/*
 * @brief Macro defines for EEPROM interrupt related registers
 */
#define EEPROM_INT_ENDOFPROG               (1 << 2)

/**
 * @brief	Select an EEPROM command
 * @param	pEEPROM	: pointer to EEPROM peripheral block
 * @param	cmd	: EEPROM command.
 * @return	Nothing
 * @note	    cmd is or-ed bits value of  EEPROM_CMD_*
 */
STATIC INLINE void IP_EEPROM_SetCmd(IP_EEPROM_002_T *pEEPROM, uint32_t cmd)
{
	pEEPROM->CMD = cmd;
}

/**
 * @brief	Set Auto programming mode
 * @param	pEEPROM	: pointer to EEPROM peripheral block
 * @param	mode	: Auto programming Mode (Value of EEPROM_AUTOPROG_).
 * @return	Nothing
 */
STATIC INLINE void IP_EEPROM_SetAutoProg(IP_EEPROM_002_T *pEEPROM, uint32_t mode)
{
	pEEPROM->AUTOPROG = mode;
}

/**
 * @brief	Set EEPROM Read Wait State value
 * @param	pEEPROM	: pointer to EEPROM peripheral block
 * @param	ws	: Wait State value.
 * @return	Nothing
 */
STATIC INLINE void IP_EEPROM_SetReadWaitState(IP_EEPROM_002_T *pEEPROM, uint32_t ws)
{
	pEEPROM->RWSTATE = ws;
}

/**
 * @brief	Set EEPROM Wait State value
 * @param	pEEPROM	: pointer to EEPROM peripheral block
 * @param	ws	: Wait State value.
 * @return	Nothing
 */
STATIC INLINE void IP_EEPROM_SetWaitState(IP_EEPROM_002_T *pEEPROM, uint32_t ws)
{
	pEEPROM->WSTATE = ws;
}

/**
 * @brief	Put EEPROM device in power down mode
 * @param	pEEPROM		: pointer to EEPROM peripheral block
 * @return	Nothing
 */
STATIC INLINE void IP_EEPROM_EnablePowerDown(IP_EEPROM_002_T *pEEPROM)
{
	pEEPROM->PWRDWN = EEPROM_PWRDWN;
}

/**
 * @brief	Bring EEPROM device out of power down mode
 * @param	pEEPROM		: pointer to EEPROM peripheral block
 * @return	Nothing
 * @note	Any EEPROM operation has to be suspended for 100us while the EEPROM wakes up.
 */
STATIC INLINE void IP_EEPROM_DisablePowerDown(IP_EEPROM_002_T *pEEPROM)
{
	pEEPROM->PWRDWN = 0;
}

/**
 * @brief	Enable EEPROM interrupt
 * @param	pEEPROM		: pointer to EEPROM peripheral block
 * @param	mask		: interrupt mask (or-ed bits value of EEPROM_INT_*)
 * @return	Nothing
 */
STATIC INLINE void IP_EEPROM_EnableInt(IP_EEPROM_002_T *pEEPROM, uint32_t mask)
{
	pEEPROM->INTENSET =  mask;
}

/**
 * @brief	Disable EEPROM interrupt
 * @param	pEEPROM		: pointer to EEPROM peripheral block
 * @param	mask		: interrupt mask (or-ed bits value of EEPROM_INT_*)
 * @return	Nothing
 */
STATIC INLINE void IP_EEPROM_DisableInt(IP_EEPROM_002_T *pEEPROM, uint32_t mask)
{
	pEEPROM->INTENCLR =  mask;
}

/**
 * @brief	Get the value of the EEPROM interrupt enable register
 * @param	pEEPROM		: pointer to EEPROM peripheral block
 * @return	Or-ed bits value of EEPROM_INT_*
 */
STATIC INLINE uint32_t IP_EEPROM_GetIntEnable(IP_EEPROM_002_T *pEEPROM)
{
	return pEEPROM->INTEN;
}

/**
 * @brief	Get EEPROM interrupt status
 * @param	pEEPROM		: pointer to EEPROM peripheral block
 * @return	Or-ed bits value of EEPROM_INT_*
 */
STATIC INLINE uint32_t IP_EEPROM_GetIntStatus(IP_EEPROM_002_T *pEEPROM)
{
	return pEEPROM->INTSTAT;
}

/**
 * @brief	Set EEPROM interrupt status
 * @param	pEEPROM		: pointer to EEPROM peripheral block
 * @param	mask		: interrupt mask (or-ed bits value of EEPROM_INT_*)
 * @return	Nothing
 */
STATIC INLINE void IP_EEPROM_SetIntStatus(IP_EEPROM_002_T *pEEPROM, uint32_t mask)
{
	pEEPROM->INTSTATSET =  mask;
}

/**
 * @brief	Clear EEPROM interrupt status
 * @param	pEEPROM		: pointer to EEPROM peripheral block
 * @param	mask		: interrupt mask (or-ed bits value of EEPROM_INT_*)
 * @return	Nothing
 */
STATIC INLINE void IP_EEPROM_ClearIntStatus(IP_EEPROM_002_T *pEEPROM, uint32_t mask)
{
	pEEPROM->INTSTATCLR =  mask;
}

/**
 * @brief	Initializes EEPROM
 * @param	pEEPROM	: pointer to EEPROM peripheral block
 * @param	div	: clock divide value (pre-minus 1)
 * @return	Nothing
 */
void IP_EEPROM_Init(IP_EEPROM_002_T *pEEPROM, uint32_t div);

/**
 * @brief	De-initializes EEPROM
 * @param	pEEPROM	: pointer to EEPROM peripheral block
 * @return	Nothing
 */
STATIC INLINE void IP_EEPROM_DeInit(IP_EEPROM_002_T *pEEPROM)
{
	/* Enable EEPROM power down mode */
	IP_EEPROM_EnablePowerDown(pEEPROM);
}

/**
 * @brief	Erase/Program an EEPROM page
 * @param	pEEPROM			: pointer to EEPROM peripheral block
 * @return	Nothing
 */
void IP_EEPROM_EraseProgramPage(IP_EEPROM_002_T *pEEPROM);

/**
 * @brief	Wait for interrupt occurs
 * @param	pEEPROM			: pointer to EEPROM peripheral block
 * @param	mask			: expected interrupt
 * @return	Nothing
 */
void IP_EEPROM_WaitForIntStatus(IP_EEPROM_002_T *pEEPROM, uint32_t mask);

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __EEPROM_002_H_ */
