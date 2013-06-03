/*
 * @brief Master include file for the library USB Printer Class driver, for both host and device modes
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * Copyright(C) Dean Camera, 2011, 2012
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

/** @ingroup Group_USBClassDrivers
 *  @defgroup Group_USBClassPrinter Printer Class Driver
 *
 *  @section Sec_Dependencies Module Source Dependencies
 *  The following files must be built with any user project that uses this module:
 *    - LPCUSBlib/Drivers/USB/Class/Host/Printer.c <i>(Makefile source module name: LPCUSBLIB_SRC_USBCLASS)</i>
 *
 *  @section Sec_ModDescription Module Description
 *  Printer Class Driver module. This module contains an internal implementation of the USB Printer Class, for the base
 *  USB Printer transport layer for USB Host mode only. Note that printers are free to implement whatever printer language
 *  they choose on top of this (e.g. Postscript), and so this driver exposes low level data transport functions only rather
 *  than high level raster or text functions. User applications can use this class driver instead of implementing the Printer
 *  class manually via the low-level nxpUSBlib APIs.
 *
 *  This module is designed to simplify the user code by exposing only the required interface needed to interface with
 *  Devices using the USB Printer Class.
 *
 *  @{
 */

#ifndef _PRINTER_CLASS_H_
#define _PRINTER_CLASS_H_

	/* Macros: */
		#define __INCLUDE_FROM_USB_DRIVER
		#define __INCLUDE_FROM_PRINTER_DRIVER

	/* Includes: */
		#include "../Core/USBMode.h"

		#if defined(USB_CAN_BE_HOST)
			#include "Host/PrinterClassHost.h"
		#endif

#endif

/** @} */

