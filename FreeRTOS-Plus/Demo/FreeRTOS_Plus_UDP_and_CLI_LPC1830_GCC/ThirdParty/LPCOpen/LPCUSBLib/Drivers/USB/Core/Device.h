/*
 * @brief Common USB Device definitions for all architectures
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
 *  @defgroup Group_Device Device Management
 *  @brief USB Device management definitions for USB device mode.
 *
 *  USB Device mode related definitions common to all architectures. This module contains definitions which
 *  are used when the USB controller is initialized in device mode.
 *
 *  @{
 */

#ifndef __USBDEVICE_H__
#define __USBDEVICE_H__

	/* Includes: */
		#include "../../../Common/Common.h"
		#include "USBMode.h"		
		#include "StdDescriptors.h"
		#include "USBInterrupt.h"
		#include "Endpoint.h"
		
	/* Enable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			extern "C" {
		#endif

	/* Preprocessor Checks: */
		#if !defined(__INCLUDE_FROM_USB_DRIVER)
			#error Do not include this file directly. Include lpcroot/libraries/LPCUSBlib/Drivers/USB/USB.h instead.
		#endif

	/* Public Interface - May be used in end-application: */
		/* Enums: */
			/** Enum for the various states of the USB Device state machine. Only some states are
			 *  implemented in the nxpUSBlib library - other states are left to the user to implement.
			 *
			 *  For information on each possible USB device state, refer to the USB 2.0 specification.
			 *
			 *  \see @ref USB_DeviceState, which stores the current device state machine state.
			 */
			enum USB_Device_States_t
			{
				DEVICE_STATE_Unattached                   = 0, /**< Internally implemented by the library. This state indicates
				                                                *   that the device is not currently connected to a host.
				                                                */
				DEVICE_STATE_Powered                      = 1, /**< Internally implemented by the library. This state indicates
				                                                *   that the device is connected to a host, but enumeration has not
				                                                *   yet begun.
				                                                */
				DEVICE_STATE_Default                      = 2, /**< Internally implemented by the library. This state indicates
				                                                *   that the device's USB bus has been reset by the host and it is
				                                                *   now waiting for the host to begin the enumeration process.
				                                                */
				DEVICE_STATE_Addressed                    = 3, /**< Internally implemented by the library. This state indicates
				                                                *   that the device has been addressed by the USB Host, but is not
				                                                *   yet configured.
				                                                */
				DEVICE_STATE_Configured                   = 4, /**< May be implemented by the user project. This state indicates
				                                                *   that the device has been enumerated by the host and is ready
				                                                *   for USB communications to begin.
				                                                */
				DEVICE_STATE_Suspended                    = 5, /**< May be implemented by the user project. This state indicates
				                                                *   that the USB bus has been suspended by the host, and the device
				                                                *   should power down to a minimal power level until the bus is
				                                                *   resumed.
				                                                */
			};

		/* Function Prototypes: */
			/** @brief	Function to retrieve a given descriptor's size and memory location from the given descriptor type value,
			 *  		index and language ID. This function MUST be overridden in the user application (added with full, identical
			 *  		prototype and name so that the library can call it to retrieve descriptor data.
			 *  @param  corenum				 :  ID Number of USB Core to be processed.
			 *  @param 	wValue               :	The type of the descriptor to retrieve in the upper byte, and the index in the
			 *                                  lower byte (when more than one descriptor of the given type exists, such as the
			 *                                  case of string descriptors). The type may be one of the standard types defined
			 *                                  in the DescriptorTypes_t enum, or may be a class-specific descriptor type value.
			 *  @param 	wIndex               : 	The language ID of the string to return if the \c wValue type indicates
			 *                                  @ref DTYPE_String, otherwise zero for standard descriptors, or as defined in a
			 *                                  class-specific standards.
			 *  @param 	DescriptorAddress    :  Pointer to the descriptor in memory. This should be set by the routine to
			 *                                  the address of the descriptor.
			 *  @param 	MemoryAddressSpace   :	A value from the @ref USB_DescriptorMemorySpaces_t enum to indicate the memory
			 *                                  space in which the descriptor is stored. This parameter does not exist when one
			 *                                  of the \c USE_*_DESCRIPTORS compile time options is used, or on architectures which
			 *                                  use a unified address space.
			 *
			 *  @note By default, the library expects all descriptors to be located in flash memory via the \c PROGMEM attribute.
			 *        If descriptors should be located in RAM or EEPROM instead (to speed up access in the case of RAM, or to
			 *        allow the descriptors to be changed dynamically at runtime) either the \c USE_RAM_DESCRIPTORS or the
			 *        \c USE_EEPROM_DESCRIPTORS tokens may be defined in the project makefile and passed to the compiler by the -D
			 *        switch.
			 *
			 *  @return Size in bytes of the descriptor if it exists, zero or @ref NO_DESCRIPTOR otherwise.
			 */
			uint16_t CALLBACK_USB_GetDescriptor(uint8_t corenum, const uint16_t wValue,
			                                    const uint8_t wIndex,
			                                    const void** const DescriptorAddress
			#if (defined(ARCH_HAS_MULTI_ADDRESS_SPACE) || defined(__DOXYGEN__)) && \
			    !(defined(USE_FLASH_DESCRIPTORS) || defined(USE_EEPROM_DESCRIPTORS) || defined(USE_RAM_DESCRIPTORS))
			                                    , uint8_t* MemoryAddressSpace
			#endif
			                                    ) ATTR_WARN_UNUSED_RESULT ATTR_NON_NULL_PTR_ARG(4);

			#if defined(__LPC18XX__) || defined(__LPC43XX__)
				#include "DCD/LPC18XX/Device_LPC18xx.h"
			#elif defined(__LPC175X_6X__) || defined(__LPC177X_8X__) || defined(__LPC407X_8X__)
				#include "DCD/LPC17XX/Device_LPC17xx.h"
			#elif defined(__LPC11U1X__) || defined(__LPC11U2X_3X__) || defined(__LPC1347__)
				#include "DCD/LPC11UXX/Device_LPC11Uxx.h"
			#endif
			
	/* Disable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			}
		#endif

#endif

/** @} */

