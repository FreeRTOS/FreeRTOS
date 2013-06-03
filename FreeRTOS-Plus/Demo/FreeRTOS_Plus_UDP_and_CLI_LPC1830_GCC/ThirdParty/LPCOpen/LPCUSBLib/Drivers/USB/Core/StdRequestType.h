/*
 * @brief USB control endpoint request definitions
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
 *  @defgroup Group_StdRequest Standard USB Requests
 *  @brief USB control endpoint request definitions.
 *
 *  This module contains definitions for the various control request parameters, so that the request
 *  details (such as data direction, request recipient, etc.) can be extracted via masking.
 *
 *  @{
 */

#ifndef __STDREQTYPE_H__
#define __STDREQTYPE_H__

	/* Includes: */
		#include "../../../Common/Common.h"
		#include "USBMode.h"		

	/* Enable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			extern "C" {
		#endif

	/* Preprocessor Checks: */
		#if !defined(__INCLUDE_FROM_USB_DRIVER)
			#error Do not include this file directly. Include lpcroot/libraries/LPCUSBlib/Drivers/USB/USB.h instead.
		#endif

	/* Public Interface - May be used in end-application: */
		/* Macros: */
			/** Mask for the request type parameter, to indicate the direction of the request data (Host to Device
			 *  or Device to Host). The result of this mask should then be compared to the request direction masks.
			 *
			 *  @see REQDIR_* macros for masks indicating the request data direction.
			 */
			#define CONTROL_REQTYPE_DIRECTION  0x80

			/** Mask for the request type parameter, to indicate the type of request (Device, Class or Vendor
			 *  Specific). The result of this mask should then be compared to the request type masks.
			 *
			 *  @see REQTYPE_* macros for masks indicating the request type.
			 */
			#define CONTROL_REQTYPE_TYPE       0x60

			/** Mask for the request type parameter, to indicate the recipient of the request (Device, Interface
			 *  Endpoint or Other). The result of this mask should then be compared to the request recipient
			 *  masks.
			 *
			 *  @see REQREC_* macros for masks indicating the request recipient.
			 */
			#define CONTROL_REQTYPE_RECIPIENT  0x1F

			/** \name Control Request Data Direction Masks */
			//@{
			/** Request data direction mask, indicating that the request data will flow from host to device.
			 *
			 *  @see @ref CONTROL_REQTYPE_DIRECTION macro.
			 */
			#define REQDIR_HOSTTODEVICE        (0 << 7)

			/** Request data direction mask, indicating that the request data will flow from device to host.
			 *
			 *  @see @ref CONTROL_REQTYPE_DIRECTION macro.
			 */
			#define REQDIR_DEVICETOHOST        (1 << 7)
			//@}

			/** \name Control Request Type Masks */
			//@{
			/** Request type mask, indicating that the request is a standard request.
			 *
			 *  @see @ref CONTROL_REQTYPE_TYPE macro.
			 */
			#define REQTYPE_STANDARD           (0 << 5)

			/** Request type mask, indicating that the request is a class-specific request.
			 *
			 *  @see @ref CONTROL_REQTYPE_TYPE macro.
			 */
			#define REQTYPE_CLASS              (1 << 5)

			/** Request type mask, indicating that the request is a vendor specific request.
			 *
			 *  @see @ref CONTROL_REQTYPE_TYPE macro.
			 */
			#define REQTYPE_VENDOR             (2 << 5)
			//@}

			/** \name Control Request Recipient Masks */
			//@{
			/** Request recipient mask, indicating that the request is to be issued to the device as a whole.
			 *
			 *  @see @ref CONTROL_REQTYPE_RECIPIENT macro.
			 */
			#define REQREC_DEVICE              (0 << 0)

			/** Request recipient mask, indicating that the request is to be issued to an interface in the
			 *  currently selected configuration.
			 *
			 *  @see @ref CONTROL_REQTYPE_RECIPIENT macro.
			 */
			#define REQREC_INTERFACE           (1 << 0)

			/** Request recipient mask, indicating that the request is to be issued to an endpoint in the
			 *  currently selected configuration.
			 *
			 *  @see @ref CONTROL_REQTYPE_RECIPIENT macro.
			 */
			#define REQREC_ENDPOINT            (2 << 0)

			/** Request recipient mask, indicating that the request is to be issued to an unspecified element
			 *  in the currently selected configuration.
			 *
			 *  @see @ref CONTROL_REQTYPE_RECIPIENT macro.
			 */
			#define REQREC_OTHER               (3 << 0)
			//@}

		/* Type Defines: */
			/** @brief Standard USB Control Request
			 *
			 *  Type define for a standard USB control request.
			 *
			 *  @see The USB 2.0 specification for more information on standard control requests.
			 */
			typedef ATTR_IAR_PACKED struct
			{
				uint8_t  bmRequestType; /**< Type of the request. */
				uint8_t  bRequest; /**< Request command code. */
				uint16_t wValue; /**< wValue parameter of the request. */
				uint16_t wIndex; /**< wIndex parameter of the request. */
				uint16_t wLength; /**< Length of the data to transfer in bytes. */
			} ATTR_PACKED USB_Request_Header_t;

		/* Enums: */
			/** Enumeration for the various standard request commands. These commands are applicable when the
			 *  request type is @ref REQTYPE_STANDARD (with the exception of @ref REQ_GetDescriptor, which is always
			 *  handled regardless of the request type value).
			 *
			 *  @see Chapter 9 of the USB 2.0 Specification.
			 */
			enum USB_Control_Request_t
			{
				REQ_GetStatus           = 0, /**< Implemented in the library for device and endpoint recipients. Passed
				                              *   to the user application for other recipients via the
				                              *   @ref EVENT_USB_Device_ControlRequest() event when received in
				                              *   device mode. */
				REQ_ClearFeature        = 1, /**< Implemented in the library for device and endpoint recipients. Passed
				                              *   to the user application for other recipients via the
				                              *   @ref EVENT_USB_Device_ControlRequest() event when received in
				                              *   device mode. */
				REQ_SetFeature          = 3, /**< Implemented in the library for device and endpoint recipients. Passed
				                              *   to the user application for other recipients via the
				                              *   @ref EVENT_USB_Device_ControlRequest() event when received in
				                              *   device mode. */
				REQ_SetAddress          = 5, /**< Implemented in the library for the device recipient. Passed
				                              *   to the user application for other recipients via the
				                              *   @ref EVENT_USB_Device_ControlRequest() event when received in
				                              *   device mode. */
				REQ_GetDescriptor       = 6, /**< Implemented in the library for device and interface recipients. Passed to the
				                              *   user application for other recipients via the
				                              *   @ref EVENT_USB_Device_ControlRequest() event when received in
				                              *   device mode. */
				REQ_SetDescriptor       = 7, /**< Not implemented in the library, passed to the user application
				                              *   via the @ref EVENT_USB_Device_ControlRequest() event when received in
				                              *   device mode. */
				REQ_GetConfiguration    = 8, /**< Implemented in the library for the device recipient. Passed
				                              *   to the user application for other recipients via the
				                              *   @ref EVENT_USB_Device_ControlRequest() event when received in
				                              *   device mode. */
				REQ_SetConfiguration    = 9, /**< Implemented in the library for the device recipient. Passed
				                              *   to the user application for other recipients via the
				                              *   @ref EVENT_USB_Device_ControlRequest() event when received in
				                              *   device mode. */
				REQ_GetInterface        = 10, /**< Not implemented in the library, passed to the user application
				                              *   via the @ref EVENT_USB_Device_ControlRequest() event when received in
				                              *   device mode. */
				REQ_SetInterface        = 11, /**< Not implemented in the library, passed to the user application
				                              *   via the @ref EVENT_USB_Device_ControlRequest() event when received in
				                              *   device mode. */
				REQ_SynchFrame          = 12, /**< Not implemented in the library, passed to the user application
				                              *   via the @ref EVENT_USB_Device_ControlRequest() event when received in
				                              *   device mode. */
			};
			
			/** Feature Selector values for Set Feature and Clear Feature standard control requests directed to the device, interface
			 *  and endpoint recipients.
			 */
			enum USB_Feature_Selectors_t
			{
				FEATURE_SEL_EndpointHalt       = 0x00, /**< Feature selector for Clear Feature or Set Feature commands. When
				                                        *   used in a Set Feature or Clear Feature request this indicates that an
				                                        *   endpoint (whose address is given elsewhere in the request) should have
				                                        *   its stall condition changed.
				                                        */
				FEATURE_SEL_DeviceRemoteWakeup = 0x01, /**< Feature selector for Device level Remote Wakeup enable set or clear.
			                                            *   This feature can be controlled by the host on devices which indicate
			                                            *   remote wakeup support in their descriptors to selectively disable or
			                                            *   enable remote wakeup.
			                                            */
				FEATURE_SEL_TestMode           = 0x02, /**< Feature selector for Test Mode features, used to test the USB controller
			                                            *   to check for incorrect operation.
			                                            */
			};

	/* Private Interface - For use in library only: */
		#if !defined(__DOXYGEN__)
			/* Macros: */
				#define FEATURE_SELFPOWERED_ENABLED     (1 << 0)
				#define FEATURE_REMOTE_WAKEUP_ENABLED   (1 << 1)
		#endif

	/* Disable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			}
		#endif

#endif

/** @} */

