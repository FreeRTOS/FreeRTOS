/**********************************************************************
* $Id$		lpc18xx_scu.c		2011-06-02
*//**
* @file		lpc18xx_scu.c
* @brief	Contains all functions support for SCU firmware library on LPC18xx
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
/** @addtogroup SCU
 * @{
 */

/* Includes ------------------------------------------------------------------- */
#include "LPC18xx.h"                    /* LPC18xx definitions                */
#include "lpc_types.h"
#include "lpc18xx_scu.h"


/*********************************************************************//**
 * @brief 		Configure pin function
 * @param[in]	port	Port number, should be: 0..15
 * @param[in]	pin		Pin number, should be: 0..31
 * @param[in]	mode	Pin mode, should be:
 * 					- MD_PUP	:Pull-up enabled
 * 					- MD_BUK	:Plain input
 * 					- MD_PLN	:Repeater mode
 * 					- MD_PDN	:Pull-down enabled
 * @param[in]	func 	Function mode, should be:
 * 					- FUNC0		:Function 0
 * 					- FUNC1		:Function 1
 * 					- FUNC2		:Function 2
 * 					- FUNC3		:Function 3
 * @return		None
 **********************************************************************/
void scu_pinmux(uint8_t port, uint8_t pin, uint8_t mode, uint8_t func)
{
  uint32_t * scu_base=(uint32_t*)(LPC_SCU_BASE);
  scu_base[(PORT_OFFSET*port+PIN_OFFSET*pin)/4]=mode+func;
} /* scu_pinmux */

/**
 * @}
 */
/* --------------------------------- End Of File ------------------------------ */
