/*
 * @brief This file contains common macros, APIs for upper layer (DCD, HCD) call,
 *		  relating to init/deinit USB core, enable/disable USB interrupt...
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

/** @ingroup Group_USB
*  @defgroup Group_HAL_LPC Hardware Abstraction Layer
*  @brief Hardware Abstraction Layer for LPC architecture
*  @{
*/
 
#ifndef __LPC_HAL_H__
#define __LPC_HAL_H__

/* Macros: */
/** These macros used to declare a variable in a defined section (ex: USB RAM section). */
#ifdef __CODE_RED
	#include <cr_section_macros.h>
#endif
/* Chip Includes: */
#if defined(__LPC18XX__) || defined(__LPC43XX__)
	#include "LPC18XX/HAL_LPC18xx.h"
#elif defined(__LPC175X_6X__) || defined(__LPC177X_8X__) || defined(__LPC407X_8X__)
	#include "LPC17XX/HAL_LPC17xx.h"
#elif defined(__LPC11U1X__) || defined(__LPC11U2X_3X__) || defined(__LPC1347__)
	#include "LPC11UXX/HAL_LPC11Uxx.h"
#endif
/* Function Prototypes: */
/**
 * @brief  	This function is called by void USB_Init(void) to do the initialization for chip's USB core.
 *  		Normally, this function will do the following:
 *     			- Configure USB pins
 *     			- Setup USB core clock
 *     			- Call HAL_RESET to setup needed USB operating registers, set device address 0 if running device mode
 * @param  	corenum		: USB port number
 * @return 	Nothing
 */
void HAL_USBInit(uint8_t corenum);

/**
 * @brief  	This function usage is opposite to HAL_USBInit
 * @param  	corenum		: USB port number
 * @param  	mode		: USB mode
 * @return 	Nothing
 */
void HAL_USBDeInit(uint8_t corenum, uint8_t mode);

/**
 * @brief  	This function used to enable USB interrupt
 * @param  	corenum		: USB port number
 * @return 	Nothing
 */
void HAL_EnableUSBInterrupt(uint8_t corenum);

/**
 * @brief  	This function usage is opposite to HAL_EnableUSBInterrupt
 * @param  	corenum		: USB port number
 * @return 	Nothing
 */
void HAL_DisableUSBInterrupt(uint8_t corenum);

/** This function is used in device mode to pull up resistor on USB pin D+
 *  Normally, this function is called when every setup or initial are done.
 */
/**
* @brief  	This function is used in device mode to pull up resistor on USB pin D+
*  			Normally, this function is called when every setup or initial are done.
* @param  	corenum		: USB port number
* @param  	con			: connect or disconect
* @return 	Nothing
*/
void HAL_USBConnect (uint8_t corenum, uint32_t con);

/* Selected USB Port Number */
extern uint8_t USBPortNum;
#endif /*__LPC_HAL_H__*/
/* --------------------------------- End Of File ------------------------------ */

/** @} */
