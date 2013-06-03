/*
 * @brief Definition of functions exported by ROM based USB device stack
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

#ifndef __MW_USBD_ROM_API_H
#define __MW_USBD_ROM_API_H

#include "error.h"
#include "usbd.h"
#include "usbd_hw.h"
#include "usbd_core.h"
#include "usbd_mscuser.h"
#include "usbd_dfuuser.h"
#include "usbd_hiduser.h"
#include "usbd_cdcuser.h"

/** @brief Main USBD API functions structure.
 *  @ingroup Group_USBD
 *
 *  This structure contains pointer to various USB Device stack's sub-module
 *  function tables. This structure is used as main entry point to access
 *  various methods (grouped in sub-modules) exposed by ROM based USB device
 *  stack.
 *
 */
typedef struct USBD_API
{
  const USBD_HW_API_T* hw; /**< Pointer to function table which exposes functions
                           which interact directly with USB device stack's core
                           layer.*/
  const USBD_CORE_API_T* core; /**< Pointer to function table which exposes functions
                           which interact directly with USB device controller
                           hardware.*/
  const USBD_MSC_API_T* msc; /**< Pointer to function table which exposes functions
                           provided by MSC function driver module.
                           */
  const USBD_DFU_API_T* dfu; /**< Pointer to function table which exposes functions
                           provided by DFU function driver module.
                           */
  const USBD_HID_API_T* hid; /**< Pointer to function table which exposes functions
                           provided by HID function driver module.
                           */
  const USBD_CDC_API_T* cdc; /**< Pointer to function table which exposes functions 
                           provided by CDC-ACM function driver module.
                           */
  const uint32_t* reserved6; /**< Reserved for future function driver module.
                           */
  const uint32_t version; /**< Version identifier of USB ROM stack. The version is
                          defined as 0x0CHDMhCC where each nibble represnts version 
                          number of the corresponding component.
                          CC -  7:0  - 8bit core version number
                           h - 11:8  - 4bit hardware interface version number
                           M - 15:12 - 4bit MSC class module version number
                           D - 19:16 - 4bit DFU class module version number
                           H - 23:20 - 4bit HID class module version number
                           C - 27:24 - 4bit CDC class module version number
                           H - 31:28 - 4bit reserved 
                           */
} USBD_API_T;


#define USBD_API (((USBD_API_T*)(ROM_USBD_PTR)))

extern USBD_HANDLE_T UsbHandle;

/* USBD core functions */
void UsbdRom_Init(uint8_t corenum);
void UsbdRom_IrqHandler(void);
/* USBD MSC functions */
void UsbdMsc_Init(void);
/* USBD HID functions */
void UsbdHid_Init(void);
/* USBD CDC functions */
void UsbdCdc_Init(void);
#endif /*__MW_USBD_ROM_API_H*/

