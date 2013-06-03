/*
 * @brief USB mode and feature support definitions
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

/** @ingroup Group_USB
 *  @defgroup Group_USBMode USB Mode Tokens
 *  @brief USB mode and feature support definitions.
 *
 *  This file defines macros indicating the type of USB controller the library is being compiled for, and its
 *  capabilities. These macros may then be referenced in the user application to selectively enable or disable
 *  code sections depending on if they are defined or not.
 *
 *  After the inclusion of the master USB driver header, one or more of the following tokens may be defined, to
 *  allow the user code to conditionally enable or disable code based on the USB controller family and allowable
 *  USB modes. These tokens may be tested against to eliminate code relating to a USB mode which is not enabled for
 *  the given compilation.
 *
 *  @{
 */

#ifndef __USBMODE_H__
#define __USBMODE_H__

	/* Enable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			extern "C" {
		#endif

	/* Preprocessor Checks: */
		#if !defined(__INCLUDE_FROM_USB_DRIVER)
			#error Do not include this file directly. Include /software/LPCUSBLib/Drivers/USB/USB.h instead.
		#endif

		#include "../../../LPCUSBlibConfig.h"

	/* Public Interface - May be used in end-application: */
	#if defined(__DOXYGEN__)

		/** Indicates that the target microcontroller and compilation settings allow for the
		 *  target to be configured in USB Device mode when defined.
		 */
		#define USB_CAN_BE_DEVICE

		/** Indicates that the target microcontroller and compilation settings allow for the
		 *  target to be configured in USB Host mode when defined.
		 */
		#define USB_CAN_BE_HOST

		/** Indicates that the target microcontroller and compilation settings allow for the
		 *  target to be configured in either USB Device or Host mode when defined.
		 */
		#define USB_CAN_BE_BOTH
	#else
		/* Macros: */
			#if (defined(__LPC175X_6X__))||(defined(__LPC177X_8X__))||(defined(__LPC407X_8X__))
				#define USB_CAN_BE_HOST
				#define __LPC_OHCI__
				#define USB_CAN_BE_DEVICE

				#define MAX_USB_CORE					1

			#elif (defined (__LPC18XX__)||defined(__LPC43XX__))
				#define USB_CAN_BE_HOST
				#define __LPC_EHCI__
				#define USB_CAN_BE_DEVICE

				#if (USE_USB_ROM_STACK)
					#define USB_DEVICE_ROM_DRIVER
				#endif

				#define MAX_USB_CORE					2

			#elif (defined(__LPC11U1X__) || defined(__LPC11U2X_3X__) || defined(__LPC1347__))
				#define USB_CAN_BE_DEVICE

				#if ((USE_USB_ROM_STACK) && (defined(__LPC11U2X_3X__) || defined(__LPC1347__)))
					#define USB_DEVICE_ROM_DRIVER
				#endif

				#define MAX_USB_CORE					1

			#endif

			#if (defined(USB_CAN_BE_DEVICE) && defined(USB_CAN_BE_HOST))
				#define USB_CAN_BE_BOTH
			#endif

			#if defined(USB_HOST_ONLY)
				#if !defined(USB_CAN_BE_HOST)
					#error USB_HOST_ONLY is not available for the currently selected microcontroller model.
				#else
					#undef USB_CAN_BE_DEVICE
					#undef USB_CAN_BE_BOTH
				#endif
			#endif

			#if defined(USB_DEVICE_ONLY)
				#if !defined(USB_CAN_BE_DEVICE)
					#error USB_DEVICE_ONLY is not available for the currently selected microcontroller model.
				#else
					#undef USB_CAN_BE_HOST
					#undef USB_CAN_BE_BOTH
				#endif
			#endif
			
			#if (defined(USB_HOST_ONLY) && defined(USB_DEVICE_ONLY))
				#error USB_HOST_ONLY and USB_DEVICE_ONLY are mutually exclusive.
			#endif

			#if (!defined(USB_CAN_BE_DEVICE) && !defined(USB_CAN_BE_HOST))
				#error The currently selected device or architecture is not supported under the USB component of the library.
			#endif
	#endif

	/* Disable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			}
		#endif

#endif

/** @} */
