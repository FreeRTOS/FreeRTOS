/*
 * @brief Common USB Controller definitions for all architectures
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
 *  @defgroup Group_USBManagement USB Interface Management
 *  @brief USB Controller definitions for general USB controller management.
 *
 *  Functions, macros, variables, enums and types related to the setup and management of the USB interface.
 *
 *  @{
 */

#ifndef __USBCONTROLLER_H__
#define __USBCONTROLLER_H__

	/* Includes: */
		#include "../../../Common/Common.h"
		#include "USBMode.h"		

	/* Enable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			extern "C" {
		#endif

	/* Preprocessor Checks and Defines: */
		#if !defined(__INCLUDE_FROM_USB_DRIVER)
			#error Do not include this file directly. Include lpcroot/libraries/LPCUSBlib/Drivers/USB/USB.h instead.
		#endif

	/* Defines: */
		/** \name Endpoint Direction Masks */
		//@{
		/** Endpoint direction mask, for masking against endpoint addresses to retrieve the endpoint's
		 *  direction for comparing with the \c ENDPOINT_DIR_* masks.
		 */
		#define ENDPOINT_DIR_MASK                       0x80

		/** Endpoint address direction mask for an OUT direction (Host to Device) endpoint. This may be ORed with
		 *  the index of the address within a device to obtain the full endpoint address.
		 */
		#define ENDPOINT_DIR_OUT                        0x00

		/** Endpoint address direction mask for an IN direction (Device to Host) endpoint. This may be ORed with
		 *  the index of the address within a device to obtain the full endpoint address.
		 */
		#define ENDPOINT_DIR_IN                         0x80
		//@}

		/** \name Endpoint/Pipe Type Masks */
		//@{
		/** Mask for determining the type of an endpoint from an endpoint descriptor. This should then be compared
		 *  with the \c EP_TYPE_* masks to determine the exact type of the endpoint.
		 */
		#define EP_TYPE_MASK                       0x03

		/** Mask for a CONTROL type endpoint or pipe.
		 *
		 *  @note See @ref Group_EndpointManagement and @ref Group_PipeManagement for endpoint/pipe functions.
		 */
		#define EP_TYPE_CONTROL                    0x00

		/** Mask for an ISOCHRONOUS type endpoint or pipe.
		 *
		 *  @note See @ref Group_EndpointManagement and @ref Group_PipeManagement for endpoint/pipe functions.
		 */
		#define EP_TYPE_ISOCHRONOUS                0x01

		/** Mask for a BULK type endpoint or pipe.
		 *
		 *  @note See @ref Group_EndpointManagement and @ref Group_PipeManagement for endpoint/pipe functions.
		 */
		#define EP_TYPE_BULK                       0x02

		/** Mask for an INTERRUPT type endpoint or pipe.
		 *
		 *  @note See @ref Group_EndpointManagement and @ref Group_PipeManagement for endpoint/pipe functions.
		 */
		#define EP_TYPE_INTERRUPT                  0x03
		//@}

		#include "Events.h"
		#include "USBTask.h"
		#include "USBInterrupt.h"
		
		#if defined(USB_CAN_BE_HOST) || defined(__DOXYGEN__)
			#include "Host.h"
			#include "OTG.h"
			#include "Pipe.h"
			#include "HostStandardReq.h"
			#include "PipeStream.h"
		#endif

		#if defined(USB_CAN_BE_DEVICE) || defined(__DOXYGEN__)
			#include "Device.h"
			#include "Endpoint.h"
			#include "DeviceStandardReq.h"
			#include "EndpointStream.h"
		#endif
		
		/* Public Interface - May be used in end-application: */
		/* Macros: */
		/** @name USB Controller Option Masks */
		//@{
		/** Regulator disable option mask for @ref USB_Init(). This indicates that the internal 3.3V USB data pad
		 *  regulator should be disabled and the LPC's VCC level used for the data pads.
		 *
		 *  @note See USB LPC data sheet for more information on the internal pad regulator.
		 */
					#define USB_OPT_REG_DISABLED               (1 << 1)

		/** Regulator enable option mask for @ref USB_Init(). This indicates that the internal 3.3V USB data pad
		 *  regulator should be enabled to regulate the data pin voltages from the VBUS level down to a level within
		 *  the range allowable by the USB standard.
		 *
		 *  @note See USB LPC data sheet for more information on the internal pad regulator.
		 */
					#define USB_OPT_REG_ENABLED                (0 << 1)

		/** Manual PLL control option mask for @ref USB_Init(). This indicates to the library that the user application
		 *  will take full responsibility for controlling the LPC's PLL (used to generate the high frequency clock
		 *  that the USB controller requires) and ensuring that it is locked at the correct frequency for USB operations.
		 */
					#define USB_OPT_MANUAL_PLL                 (1 << 2)

		/** Automatic PLL control option mask for @ref USB_Init(). This indicates to the library that the library should
		 *  take full responsibility for controlling the LPC's PLL (used to generate the high frequency clock
		 *  that the USB controller requires) and ensuring that it is locked at the correct frequency for USB operations.
		 */
					#define USB_OPT_AUTO_PLL                   (0 << 2)
					//@}
					
					#if !defined(USB_STREAM_TIMEOUT_MS) || defined(__DOXYGEN__)
		/** Constant for the maximum software timeout period of the USB data stream transfer functions
		 *  (both control and standard) when in either device or host mode. If the next packet of a stream
		 *  is not received or acknowledged within this time period, the stream function will fail.
		 *
		 *  This value may be overridden in the user project makefile as the value of the
		 *  @ref USB_STREAM_TIMEOUT_MS token, and passed to the compiler using the -D switch.
		 */
						#define USB_STREAM_TIMEOUT_MS       100
					#endif

		/* Inline Functions: */
					#if defined(USB_SERIES_4_AVR) || defined(USB_SERIES_6_AVR) || defined(USB_SERIES_7_AVR) || \
			defined(__DOXYGEN__)
		/**
		 * @brief  Determines if the VBUS line is currently high (i.e. the USB host is supplying power).
		 *
		 *  @note This function is not available on some AVR models which do not support hardware VBUS monitoring.
		 *
		 *  @return Boolean \c true if the VBUS line is currently detecting power from a host, \c false otherwise.
		 */
		PRAGMA_ALWAYS_INLINE
		static inline bool USB_VBUS_GetStatus(void) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

		static inline bool USB_VBUS_GetStatus(void)
		{
			return (USBSTA & (1 << VBUS)) ? true : false;
		}

					#endif

		/** Detaches the device from the USB bus. This has the effect of removing the device from any
		 *  attached host, ceasing USB communications. If no host is present, this prevents any host from
		 *  enumerating the device once attached until @ref USB_Attach() is called.
		 */
		PRAGMA_ALWAYS_INLINE
		static inline void USB_Detach(void) ATTR_ALWAYS_INLINE;

		static inline void USB_Detach(void)
		{}

		/** Attaches the device to the USB bus. This announces the device's presence to any attached
		 *  USB host, starting the enumeration process. If no host is present, attaching the device
		 *  will allow for enumeration once a host is connected to the device.
		 *
		 *  This is inexplicably also required for proper operation while in host mode, to enable the
		 *  attachment of a device to the host. This is despite the bit being located in the device-mode
		 *  register and despite the datasheet making no mention of its requirement in host mode.
		 */
		PRAGMA_ALWAYS_INLINE
		static inline void USB_Attach(void) ATTR_ALWAYS_INLINE;

		static inline void USB_Attach(void)
		{}

		/* Function Prototypes: */
		/** Main function to initialize and start the USB interface. Once active, the USB interface will
		 *  allow for device connection to a host when in device mode, or for device enumeration while in
		 *  host mode.
		 *
		 *  As the USB library relies on interrupts for the device and host mode enumeration processes,
		 *  the user must enable global interrupts before or shortly after this function is called. In
		 *  device mode, interrupts must be enabled within 500ms of this function being called to ensure
		 *  that the host does not time out whilst enumerating the device. In host mode, interrupts may be
		 *  enabled at the application's leisure however enumeration will not begin of an attached device
		 *  until after this has occurred.
		 *
		 *  Calling this function when the USB interface is already initialized will cause a complete USB
		 *  interface reset and re-enumeration.
		 *
		 *  \see @ref Group_Device for the \c USB_DEVICE_OPT_* masks.
		 */
		void USB_Init(uint8_t corenum, uint8_t mode);

		/** Shuts down the USB interface. This turns off the USB interface after deallocating all USB FIFO
		 *  memory, endpoints and pipes. When turned off, no USB functionality can be used until the interface
		 *  is restarted with the @ref USB_Init() function.
		 */
		void USB_Disable(uint8_t corenum, uint8_t mode);

		/** Resets the interface, when already initialized. This will re-enumerate the device if already connected
		 *  to a host, or re-enumerate an already attached device when in host mode.
		 */
		void USB_ResetInterface(uint8_t corenum, uint8_t mode);

		/* Global Variables: */
		extern volatile uint8_t USB_CurrentMode[];
		// 			#if (!defined(USB_HOST_ONLY) && !defined(USB_DEVICE_ONLY)) || defined(__DOXYGEN__)
		/** Indicates the mode that the USB interface is currently initialized to, a value from the
		 *  @ref USB_Modes_t enum.
		 *
		 *  @note This variable should be treated as read-only in the user application, and never manually
		 *        changed in value.
		 *
		 *  @note When the controller is initialized into UID auto-detection mode, this variable will hold the
		 *        currently selected USB mode (i.e. @ref USB_MODE_Device or @ref USB_MODE_Host). If the controller
		 *        is fixed into a specific mode (either through the \c USB_DEVICE_ONLY or \c USB_HOST_ONLY compile time
		 *        options, or a limitation of the USB controller in the chosen device model) this will evaluate to
		 *        a constant of the appropriate value and will never evaluate to @ref USB_MODE_None even when the
		 *        USB interface is not initialized.
		 */
		// extern volatile uint8_t USB_CurrentMode[];
		// 			#elif defined(USB_HOST_ONLY)
		// 				#define USB_CurrentMode[0] USB_MODE_Host
		// 			#elif defined(USB_DEVICE_ONLY)
		// 				#define USB_CurrentMode[0] USB_MODE_Device
		// 			#endif

					#if !defined(USE_STATIC_OPTIONS) || defined(__DOXYGEN__)
		/** Indicates the current USB options that the USB interface was initialized with when @ref USB_Init()
		 *  was called. This value will be one of the \c USB_MODE_* masks defined elsewhere in this module.
		 *
		 *  @note This variable should be treated as read-only in the user application, and never manually
		 *        changed in value.
		 */
		extern volatile uint8_t USB_Options;
					#elif defined(USE_STATIC_OPTIONS)
						#define USB_Options USE_STATIC_OPTIONS
					#endif

		/* Enums: */
		/** Enum for the possible USB controller modes, for initialization via @ref USB_Init() and indication back to the
		 *  user application via @ref USB_CurrentMode.
		 */
		enum USB_Modes_t {
			USB_MODE_None   = 0,			/**< Indicates that the controller is currently not initialized in any specific USB mode. */
			USB_MODE_Device = 1,			/**< Indicates that the controller is currently initialized in USB Device mode. */
			USB_MODE_Host   = 2,			/**< Indicates that the controller is currently initialized in USB Host mode. */
			USB_MODE_UID    = 3,			/**< Indicates that the controller should determine the USB mode from the UID pin of the
											 *   USB connector.
											 */
		};

		/* Private Interface - For use in library only: */
			#if !defined(__DOXYGEN__)
		/* Function Prototypes: */
					#if defined(__INCLUDE_FROM_USB_CONTROLLER_C)
						#if defined(USB_CAN_BE_DEVICE)
		static void USB_Init_Device(uint8_t corenum);

						#endif

						#if defined(USB_CAN_BE_HOST)
		static void USB_Init_Host(uint8_t corenum);

						#endif
					#endif

		/* Inline Functions: */
		PRAGMA_ALWAYS_INLINE
		static inline void USB_PLL_On(void) ATTR_ALWAYS_INLINE;

		static inline void USB_PLL_On(void)
		{}

		PRAGMA_ALWAYS_INLINE
		static inline void USB_PLL_Off(void) ATTR_ALWAYS_INLINE;

		static inline void USB_PLL_Off(void)
		{}

		PRAGMA_ALWAYS_INLINE
		static inline bool USB_PLL_IsReady(void) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

		static inline bool USB_PLL_IsReady(void)
		{
			return true;			// implement later if needed
		}

		PRAGMA_ALWAYS_INLINE
		static inline void USB_REG_On(void) ATTR_ALWAYS_INLINE;

		static inline void USB_REG_On(void)
		{}

		PRAGMA_ALWAYS_INLINE
		static inline void USB_REG_Off(void) ATTR_ALWAYS_INLINE;

		static inline void USB_REG_Off(void)
		{}

		PRAGMA_ALWAYS_INLINE
		static inline void USB_OTGPAD_On(void) ATTR_ALWAYS_INLINE;

		static inline void USB_OTGPAD_On(void)
		{}

		PRAGMA_ALWAYS_INLINE
		static inline void USB_OTGPAD_Off(void) ATTR_ALWAYS_INLINE;

		static inline void USB_OTGPAD_Off(void)
		{}

		PRAGMA_ALWAYS_INLINE
		static inline void USB_CLK_Freeze(void) ATTR_ALWAYS_INLINE;

		static inline void USB_CLK_Freeze(void)
		{}

		PRAGMA_ALWAYS_INLINE
		static inline void USB_CLK_Unfreeze(void) ATTR_ALWAYS_INLINE;

		static inline void USB_CLK_Unfreeze(void)
		{}

		PRAGMA_ALWAYS_INLINE
		static inline void USB_Controller_Enable(void) ATTR_ALWAYS_INLINE;

		static inline void USB_Controller_Enable(void)
		{}

		PRAGMA_ALWAYS_INLINE
		static inline void USB_Controller_Disable(void) ATTR_ALWAYS_INLINE;

		static inline void USB_Controller_Disable(void)
		{}

		PRAGMA_ALWAYS_INLINE
		static inline void USB_Controller_Reset(void) ATTR_ALWAYS_INLINE;

		static inline void USB_Controller_Reset(void)
		{}

					#if defined(USB_CAN_BE_BOTH)
		PRAGMA_ALWAYS_INLINE
		static inline uint8_t USB_GetUSBModeFromUID(void) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

		static inline uint8_t USB_GetUSBModeFromUID(void)
		{
			// if (USBSTA & (1 << ID))
			//  return USB_MODE_Device;
			// else
			//  return USB_MODE_Host;
			return 0;
		}

					#endif

			#endif


	/* Disable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			}
		#endif

#endif

/** @} */

