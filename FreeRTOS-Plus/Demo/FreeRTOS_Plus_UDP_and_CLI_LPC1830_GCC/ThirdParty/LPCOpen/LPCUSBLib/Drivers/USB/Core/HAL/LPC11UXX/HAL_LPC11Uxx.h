/*
 * @brief HAL USB functions for the LPC11Uxx microcontrollers
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

#ifndef __HAL_LPC11UXX_H__
#define __HAL_LPC11UXX_H__
#include "chip.h"
#define  __INCLUDE_FROM_USB_DRIVER

#include "../../USBMode.h"

#define USBRAM_SECTION RAM2
/** This macro is used to declare a variable in a defined section. */
#if defined(__CC_ARM)
	#define __BSS(x)   __attribute__ ((section("usbram")))
#endif
#if defined(__ICCARM__)
	#define __BSS(x)   @ "USB_PACKET_MEMORY"
#endif

/* Terminated Link Mask of USB DMA. */
#define LINK_TERMINATE                          0x01

typedef struct {
	uint16_t BufferAddrOffset;

	__IO uint16_t NBytes : 10;
	uint16_t Type : 1;
	uint16_t RateFeedback_Toogle : 1;
	uint16_t ToogleReset : 1;
	__IO uint16_t Stall : 1;
	uint16_t Disabled : 1;
	__IO uint16_t Active : 1;

} /* __attribute__ ((packed)) */ USB_CMD_STAT;

void HAL_Reset (void);

void HAL_SetDeviceAddress (uint8_t Address);

#endif	// __HAL_LPC11UXX_H__

