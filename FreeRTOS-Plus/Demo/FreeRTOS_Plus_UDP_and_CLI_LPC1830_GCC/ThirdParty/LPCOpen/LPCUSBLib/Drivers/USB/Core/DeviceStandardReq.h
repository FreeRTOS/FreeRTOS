/*
 * @brief USB device standard request management
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


 
#ifndef __DEVICESTDREQ_H__
#define __DEVICESTDREQ_H__

	/* Includes: */
		#include "../../../Common/Common.h"
		#include "USBMode.h"		
		#include "StdDescriptors.h"
		#include "Events.h"
		#include "StdRequestType.h"
		#include "USBTask.h"
		#include "USBController.h"

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
			#if defined(ARCH_HAS_MULTI_ADDRESS_SPACE) || defined(__DOXYGEN__)
				/** Enum for the possible descriptor memory spaces, for the \c MemoryAddressSpace parameter of the
				 *  @ref CALLBACK_USB_GetDescriptor() function. This can be used when none of the \c USE_*_DESCRIPTORS
				 *  compile time options are used, to indicate in which memory space the descriptor is stored.
				 *
				 *  @ingroup Group_Device
				 */
				enum USB_DescriptorMemorySpaces_t
				{
					#if defined(ARCH_HAS_FLASH_ADDRESS_SPACE) || defined(__DOXYGEN__)
					MEMSPACE_FLASH    = 0, /**< Indicates the requested descriptor is located in FLASH memory. */
					#endif
					#if defined(ARCH_HAS_EEPROM_ADDRESS_SPACE) || defined(__DOXYGEN__)
					MEMSPACE_EEPROM   = 1, /**< Indicates the requested descriptor is located in EEPROM memory. */
					#endif
					MEMSPACE_RAM      = 2, /**< Indicates the requested descriptor is located in RAM memory. */
				};
			#endif

		/* Global Variables: */
			/** Indicates the currently set configuration number of the device. USB devices may have several
			 *  different configurations which the host can select between; this indicates the currently selected
			 *  value, or 0 if no configuration has been selected.
			 *
			 *  @note This variable should be treated as read-only in the user application, and never manually
			 *        changed in value.
			 *
			 *  @ingroup Group_Device
			 */
			extern uint8_t USB_Device_ConfigurationNumber;

			#if !defined(NO_DEVICE_REMOTE_WAKEUP)
				/** Indicates if the host is currently allowing the device to issue remote wakeup events. If this
				 *  flag is cleared, the device should not issue remote wakeup events to the host.
				 *
				 *  @note This variable should be treated as read-only in the user application, and never manually
				 *        changed in value.
				 *        \n\n
				 *
				 *  @note To reduce FLASH usage of the compiled applications where Remote Wakeup is not supported,
				 *        this global and the underlying management code can be disabled by defining the
				 *        \c NO_DEVICE_REMOTE_WAKEUP token in the project makefile and passing it to the compiler via
				 *        the -D switch.
				 *
				 *  @ingroup Group_Device
				 */
				extern bool USB_Device_RemoteWakeupEnabled;
			#endif

			#if !defined(NO_DEVICE_SELF_POWER)
				/** Indicates if the device is currently being powered by its own power supply, rather than being
				 *  powered by the host's USB supply. This flag should remain cleared if the device does not
				 *  support self powered mode, as indicated in the device descriptors.
				 *
				 *  @ingroup Group_Device
				 */
				extern bool USB_Device_CurrentlySelfPowered;
			#endif

	/* Private Interface - For use in library only: */
	#if !defined(__DOXYGEN__)
		#if defined(USE_RAM_DESCRIPTORS) && defined(USE_EEPROM_DESCRIPTORS)
			#error USE_RAM_DESCRIPTORS and USE_EEPROM_DESCRIPTORS are mutually exclusive.
		#elif defined(USE_RAM_DESCRIPTORS) && defined(USE_FLASH_DESCRIPTORS)
			#error USE_RAM_DESCRIPTORS and USE_FLASH_DESCRIPTORS are mutually exclusive.
		#elif defined(USE_FLASH_DESCRIPTORS) && defined(USE_EEPROM_DESCRIPTORS)
			#error USE_FLASH_DESCRIPTORS and USE_EEPROM_DESCRIPTORS are mutually exclusive.
		#elif defined(USE_FLASH_DESCRIPTORS) && defined(USE_EEPROM_DESCRIPTORS) && defined(USE_RAM_DESCRIPTORS)
			#error Only one of the USE_*_DESCRIPTORS modes should be selected.
		#endif

		/* Function Prototypes: */
			void USB_Device_ProcessControlRequest(uint8_t corenum);

			#if defined(__INCLUDE_FROM_DEVICESTDREQ_C)
				static void USB_Device_SetAddress(uint8_t corenum);
				static void USB_Device_SetConfiguration(uint8_t corenum);
				static void USB_Device_GetConfiguration(uint8_t corenum);
				static void USB_Device_GetDescriptor(uint8_t corenum);
				static void USB_Device_GetStatus(uint8_t corenum);
				static void USB_Device_ClearSetFeature(uint8_t corenum);

				#if !defined(NO_INTERNAL_SERIAL) && (USE_INTERNAL_SERIAL != NO_DESCRIPTOR)
					static void USB_Device_GetInternalSerialDescriptor(uint8_t corenum);
				#endif
			#endif
	#endif

	/* Disable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			}
		#endif

#endif

