/*
 * @brief HAL USB functions for the LPC18xx microcontrollers
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

 /** @ingroup Group_HAL_LPC
 *  @defgroup Group_HAL_LPC18xx Hardware Abstraction Layer LPC18XX
 *  @{
 */

#ifndef __HAL_LPC18XX_H__
#define __HAL_LPC18XX_H__

#include "chip.h"

#define  __INCLUDE_FROM_USB_DRIVER
#include "../../USBMode.h"

#define USBRAM_SECTION  RAM2

#if defined(__ICCARM__)
	#define __BSS(x)       @ ".ahb_sram1"
#elif defined(__CC_ARM)
	#define __BSS(x)
#endif
/* bit defines for DEVICEADDR register. */
#define USBDEV_ADDR_AD  (1 << 24)
#define USBDEV_ADDR(n)  (((n) & 0x7F) << 25)

/* Max USB Core specially for LPC18xx/43xx series. */
#define LPC18_43_MAX_USB_CORE	2

/* This macro is used to get proper USB Register base address
 * from specified USB core ID.
 */
#define USB_REG(CoreID)         USB_REG_BASE_ADDR[CoreID]

/* Terminated Link Mask of USB DMA. */
#define LINK_TERMINATE                          0x01

/* Constant table stores base addresses of USB Register Structures. */
extern IP_USBHS_001_T * const USB_REG_BASE_ADDR[];

/**
 * @brief	Interrupt Handler (Host side).
 * 			This handler is known as interrupt service routine of USB Host.
 *
 * @param	HostID		: Host ID
 * @return	Nothing.
 */
extern void HcdIrqHandler(uint8_t HostID);

/**
 * @brief	Interrupt Handler (Device side).
 * 			This handler is known as interrupt service routine of USB Device.
 *
 * @param	corenum		: ID Number of USB Core to be processed.
 * @return	Nothing.
 */
extern void DcdIrqHandler (uint8_t corenum);

void HAL_Reset (uint8_t corenum);

#endif	// __HAL_LPC18XX_H__

/** @} */
