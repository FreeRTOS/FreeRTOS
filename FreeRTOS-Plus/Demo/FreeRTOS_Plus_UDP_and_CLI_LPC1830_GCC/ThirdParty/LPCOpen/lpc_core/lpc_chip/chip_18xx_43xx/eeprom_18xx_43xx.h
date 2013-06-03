/*
 * @brief LPC18xx/40xx EEPROM driver
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

#ifndef EEPROM_18XX_43XX_H_
#define EEPROM_18XX_43XX_H_

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup EEPROM_18XX_43XX CHIP: LPC18xx/40xx EEPROM Driver
 * @ingroup CHIP_18XX_43XX_Drivers
 * @{
 */
/** EEPROM start address */
#define EEPROM_START                    (0x20040000)
/** EEPROM byes per page */
#define EEPROM_PAGE_SIZE                (128)
/**The number of EEPROM pages. The last page is not writable.*/
#define EEPROM_PAGE_NUM                 (128)
/** Get the eeprom address */
#define EEPROM_ADDRESS(page, offset)     (EEPROM_START + (EEPROM_PAGE_SIZE * (page)) + offset)

/**
 * @brief	Initializes EEPROM
 * @param	pEEPROM	: Pointer to EEPROM peripheral block structure
 * @return	Nothing
 */
void Chip_EEPROM_Init(LPC_EEPROM_T *pEEPROM);

/**
 * @brief	De-initializes EEPROM
 * @param	pEEPROM	: Pointer to EEPROM peripheral block structure
 * @return	Nothing
 */
STATIC INLINE void Chip_EEPROM_DeInit(LPC_EEPROM_T *pEEPROM)
{
	IP_EEPROM_DeInit(pEEPROM);
}

/**
 * @brief	Set Auto program mode
 * @param	pEEPROM	: Pointer to EEPROM peripheral block structure
 * @param	mode	: Auto Program Mode (One of EEPROM_AUTOPROG_* value)
 * @return	Nothing
 */
STATIC INLINE void Chip_EEPROM_SetAutoProg(LPC_EEPROM_T *pEEPROM, uint32_t mode)
{
	IP_EEPROM_SetAutoProg(pEEPROM, mode);
}

/**
 * @brief	Set EEPROM Read Wait State
 * @param	pEEPROM	: Pointer to EEPROM peripheral block structure
 * @param	ws   	: Wait State value
 * @return	Nothing
 * @note    Bits 7:0 represents wait state for Read Phase 2 and 
 *          Bits 15:8 represents wait state for Read Phase1
 */
STATIC INLINE void Chip_EEPROM_SetReadWaitState(LPC_EEPROM_T *pEEPROM, uint32_t ws)
{
	IP_EEPROM_SetReadWaitState(pEEPROM, ws);
}

/**
 * @brief	Set EEPROM wait state
 * @param	pEEPROM	: Pointer to EEPROM peripheral block structure
 * @param	ws	    : Wait State value
 * @return	Nothing
 * @note    Bits 7:0 represents wait state for Phase 3,
 *          Bits 15:8 represents wait state for Phase2, and
 *          Bits 23:16 represents wait state for Phase1
 */
STATIC INLINE void Chip_EEPROM_SetWaitState(LPC_EEPROM_T *pEEPROM, uint32_t ws)
{
	IP_EEPROM_SetWaitState(pEEPROM, ws);
}

/**
 * @brief	Select an EEPROM command
 * @param	pEEPROM	: Pointer to EEPROM peripheral block structure
 * @param	cmd	    : EEPROM command
 * @return	Nothing
 * @note	The cmd is OR-ed bits value of  EEPROM_CMD_*
 */
STATIC INLINE void Chip_EEPROM_SetCmd(LPC_EEPROM_T *pEEPROM, uint32_t cmd)
{
	IP_EEPROM_SetCmd(pEEPROM, cmd);
}

/**
 * @brief	Erase/Program an EEPROM page
 * @param	pEEPROM	: Pointer to EEPROM peripheral block structure
 * @return	Nothing
 */
STATIC INLINE void Chip_EEPROM_EraseProgramPage(LPC_EEPROM_T *pEEPROM)
{
	IP_EEPROM_EraseProgramPage(pEEPROM);
}

/**
 * @brief	Wait for interrupt occurs
 * @param	pEEPROM	: Pointer to EEPROM peripheral block structure
 * @param	mask	: Expected interrupt
 * @return	Nothing
 */
STATIC INLINE void Chip_EEPROM_WaitForIntStatus(IP_EEPROM_002_T *pEEPROM, uint32_t mask)
{
	IP_EEPROM_WaitForIntStatus(pEEPROM, mask);
}

/**
 * @brief	Put EEPROM device in power down mode
 * @param	pEEPROM	: Pointer to EEPROM peripheral block structure
 * @return	Nothing
 */
STATIC INLINE void Chip_EEPROM_EnablePowerDown(LPC_EEPROM_T *pEEPROM)
{
	IP_EEPROM_EnablePowerDown(pEEPROM);
}

/**
 * @brief	Bring EEPROM device out of power down mode
 * @param	pEEPROM	: Pointer to EEPROM peripheral block structure
 * @return	Nothing
 */
STATIC INLINE void Chip_EEPROM_DisablePowerDown(LPC_EEPROM_T *pEEPROM)
{
	IP_EEPROM_DisablePowerDown(pEEPROM);
}

/**
 * @brief	Enable EEPROM interrupt
 * @param	pEEPROM	: Pointer to EEPROM peripheral block structure
 * @param	mask	: Interrupt mask (or-ed bits value of EEPROM_INT_*)
 * @return	Nothing
 */
STATIC INLINE void Chip_EEPROM_EnableInt(LPC_EEPROM_T *pEEPROM, uint32_t mask)
{
	IP_EEPROM_EnableInt(pEEPROM, mask);
}

/**
 * @brief	Disable EEPROM interrupt
 * @param	pEEPROM	: Pointer to EEPROM peripheral block structure
 * @param	mask	: Interrupt mask (or-ed bits value of EEPROM_INT_*)
 * @return	Nothing
 */
STATIC INLINE void Chip_EEPROM_DisableInt(LPC_EEPROM_T *pEEPROM, uint32_t mask)
{
	IP_EEPROM_DisableInt(pEEPROM, mask);
}

/**
 * @brief	Get the value of the EEPROM interrupt enable register
 * @param	pEEPROM	: Pointer to EEPROM peripheral block structure
 * @return	OR-ed bits value of EEPROM_INT_*
 */
STATIC INLINE uint32_t Chip_EEPROM_GetIntEnable(LPC_EEPROM_T *pEEPROM)
{
	return IP_EEPROM_GetIntEnable(pEEPROM);
}

/**
 * @brief	Get EEPROM interrupt status
 * @param	pEEPROM	: Pointer to EEPROM peripheral block structure
 * @return	OR-ed bits value of EEPROM_INT_*
 */
STATIC INLINE uint32_t Chip_EEPROM_GetIntStatus(LPC_EEPROM_T *pEEPROM)
{
	return IP_EEPROM_GetIntStatus(pEEPROM);
}

/**
 * @brief	Set EEPROM interrupt status
 * @param	pEEPROM	: Pointer to EEPROM peripheral block structure
 * @param	mask	: Interrupt mask (or-ed bits value of EEPROM_INT_*)
 * @return	Nothing
 */
STATIC INLINE void Chip_EEPROM_SetIntStatus(LPC_EEPROM_T *pEEPROM, uint32_t mask)
{
	IP_EEPROM_SetIntStatus(pEEPROM, mask);
}

/**
 * @brief	Clear EEPROM interrupt status
 * @param	pEEPROM	: Pointer to EEPROM peripheral block structure
 * @param	mask	: Interrupt mask (or-ed bits value of EEPROM_INT_*)
 * @return	Nothing
 */
STATIC INLINE void Chip_EEPROM_ClearIntStatus(LPC_EEPROM_T *pEEPROM, uint32_t mask)
{
	IP_EEPROM_ClearIntStatus(pEEPROM, mask);
}

/**
 * @}
 */

 #ifdef __cplusplus
}
#endif

#endif /* EEPROM_18XX_43XX_H_ */
