/*
 * @brief Device mode driver for the library USB HID Class driver
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

/** @ingroup Group_USBClassHID
 *  @defgroup Group_USBClassHIDDevice HID Class Device Mode Driver
 *
 *  @section Sec_Dependencies Module Source Dependencies
 *  The following files must be built with any user project that uses this module:
 *    - nxpUSBlib/Drivers/USB/Class/Device/HID.c <i>(Makefile source module name: NXPUSBLIB_SRC_USBCLASS)</i>
 *
 *  @section Sec_ModDescription Module Description
 *  Device Mode USB Class driver framework interface, for the HID USB Class driver.
 *
 * @{
 */

#ifndef _HID_CLASS_DEVICE_H_
#define _HID_CLASS_DEVICE_H_

/* Includes: */
		#include "../../USB.h"
		#include "../Common/HIDClassCommon.h"

/* Enable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
extern "C" {
		#endif

/* Preprocessor Checks: */
		#if !defined(__INCLUDE_FROM_HID_DRIVER)
			#error Do not include this file directly. Include LPCUSBlib/Drivers/USB.h instead.
		#endif

/* Public Interface - May be used in end-application: */
/* Type Defines: */
/** @brief HID Class Device Mode Configuration and State Structure.
 *
 *  Class state structure. An instance of this structure should be made for each HID interface
 *  within the user application, and passed to each of the HID class driver functions as the
 *  \c HIDInterfaceInfo parameter. This stores each HID interface's configuration and state information.
 *
 * @note Due to technical limitations, the HID device class driver does not utilize a separate OUT
 *        endpoint for host->device communications. Instead, the host->device data (if any) is sent to
 *        the device via the control endpoint.
 */
typedef struct {
	const struct {
		uint8_t  InterfaceNumber;				/**< Interface number of the HID interface within the device. */

		uint8_t  ReportINEndpointNumber;			/**< Endpoint number of the HID interface's IN report endpoint. */
		uint16_t ReportINEndpointSize;				/**< Size in bytes of the HID interface's IN report endpoint. */
		bool     ReportINEndpointDoubleBank;			/**< Indicates if the HID interface's IN report endpoint should use double banking. */

		void *PrevReportINBuffer;				/**< Pointer to a buffer where the previously created HID input report can be
												 *  stored by the driver, for comparison purposes to detect report changes that
												 *  must be sent immediately to the host. This should point to a buffer big enough
												 *  to hold the largest HID input report sent from the HID interface. If this is set
												 *  to \c NULL, it is up to the user to force transfers when needed in the
												 *  @ref CALLBACK_HID_Device_CreateHIDReport() callback function.
												 *
												 * @note Due to the single buffer, the internal driver can only correctly compare
												 *        subsequent reports with identical report IDs. In multiple report devices,
												 *        this buffer should be set to \c NULL and the decision to send reports made
												 *        by the user application instead.
												 */
		uint8_t  PrevReportINBufferSize;			/**< Size in bytes of the given input report buffer. This is used to create a
													 *  second buffer of the same size within the driver so that subsequent reports
													 *  can be compared. If the user app is to determine when reports are to be sent
													 *  exclusively (i.e. @ref PrevReportINBuffer is \c NULL) this value must still be
													 *  set to the size of the largest report the device can issue to the host.
													 */
		uint8_t  PortNumber;				/**< Port number that this interface is running.*/
	} Config;				/**< Config data for the USB class interface within the device. All elements in this section
							 *   <b>must</b> be set or the interface will fail to enumerate and operate correctly.
							 */

	struct {
		bool     UsingReportProtocol;				/**< Indicates if the HID interface is set to Boot or Report protocol mode. */
		uint16_t IdleCount;				/**< Report idle period, in milliseconds, set by the host. */
		uint16_t IdleMSRemaining;				/**< Total number of milliseconds remaining before the idle period elapsed - this
												 *   should be decremented by the user application if non-zero each millisecond. */
	} State;			/**< State data for the USB class interface within the device. All elements in this section
						 *   are reset to their defaults when the interface is enumerated.
						 */

} USB_ClassInfo_HID_Device_t;

/* Function Prototypes: */
/**
 * @brief	 Configures the endpoints of a given HID interface, ready for use. This should be linked to the library
 *  @ref EVENT_USB_Device_ConfigurationChanged() event so that the endpoints are configured when the configuration
 *  containing the given HID interface is selected.
 *
 * @param	HIDInterfaceInfo	: Pointer to a structure containing a HID Class configuration and state.
 *
 * @return	Boolean \c true if the endpoints were successfully configured, \c false otherwise.
 */
bool HID_Device_ConfigureEndpoints(USB_ClassInfo_HID_Device_t *const HIDInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1);

/**
 * @brief	 Processes incoming control requests from the host, that are directed to the given HID class interface. This should be
 *  linked to the library @ref EVENT_USB_Device_ControlRequest() event.
 *
 * @param	HIDInterfaceInfo	: Pointer to a structure containing a HID Class configuration and state.
 * @return	Nothing
 */
void HID_Device_ProcessControlRequest(USB_ClassInfo_HID_Device_t *const HIDInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1);

/**
 * @brief	 General management task for a given HID class interface, required for the correct operation of the interface. This should
 *  be called frequently in the main program loop, before the master USB management task @ref USB_USBTask().
 *
 * @param	HIDInterfaceInfo	: Pointer to a structure containing a HID Class configuration and state.
 * @return	Nothing
 */
void HID_Device_USBTask(USB_ClassInfo_HID_Device_t *const HIDInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1);

/**
 * @brief	 HID class driver callback for the user creation of a HID IN report. This callback may fire in response to either
 *  HID class control requests from the host, or by the normal HID endpoint polling procedure. Inside this callback the
 *  user is responsible for the creation of the next HID input report to be sent to the host.
 *
 * @param	HIDInterfaceInfo	: Pointer to a structure containing a HID Class configuration and state.
 * @param	ReportID	: If preset to a non-zero value, this is the report ID being requested by the host. If zero,
 *                                   this should be set to the report ID of the generated HID input report (if any). If multiple
 *                                   reports are not sent via the given HID interface, this parameter should be ignored.
 * @param	ReportType	: Type of HID report to generate, either @ref HID_REPORT_ITEM_In or @ref HID_REPORT_ITEM_Feature.
 * @param	ReportData	: Pointer to a buffer where the generated HID report should be stored.
 * @param	ReportSize	: Number of bytes in the generated input report, or zero if no report is to be sent.
 *
 * @return	Boolean \c true to force the sending of the report even if it is identical to the previous report and still within
 *          the idle period (useful for devices which report relative movement), \c false otherwise.
 */
bool CALLBACK_HID_Device_CreateHIDReport(USB_ClassInfo_HID_Device_t *const HIDInterfaceInfo,
										 uint8_t *const ReportID,
										 const uint8_t ReportType,
										 void *ReportData,
										 uint16_t *const ReportSize) ATTR_NON_NULL_PTR_ARG(1)
ATTR_NON_NULL_PTR_ARG(2) ATTR_NON_NULL_PTR_ARG(4) ATTR_NON_NULL_PTR_ARG(5);

/**
 * @brief	 HID class driver callback for the user processing of a received HID OUT report. This callback may fire in response to
 *  either HID class control requests from the host, or by the normal HID endpoint polling procedure. Inside this callback
 *  the user is responsible for the processing of the received HID output report from the host.
 *
 * @param	HIDInterfaceInfo	: Pointer to a structure containing a HID Class configuration and state.
 * @param	ReportID	: Report ID of the received output report. If multiple reports are not received via the given HID
 *                                   interface, this parameter should be ignored.
 * @param	ReportType	: Type of received HID report, either @ref HID_REPORT_ITEM_Out or @ref HID_REPORT_ITEM_Feature.
 * @param	ReportData	: Pointer to a buffer where the received HID report is stored.
 * @param	ReportSize	: Size in bytes of the received report from the host.
 * @return	Nothing
 */
void CALLBACK_HID_Device_ProcessHIDReport(USB_ClassInfo_HID_Device_t *const HIDInterfaceInfo,
										  const uint8_t ReportID,
										  const uint8_t ReportType,
										  const void *ReportData,
										  const uint16_t ReportSize) ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(4);

/* Inline Functions: */
/**
 * @brief	 Indicates that a millisecond of idle time has elapsed on the given HID interface, and the interface's idle count should be
 *  decremented. This should be called once per millisecond so that hardware key-repeats function correctly. It is recommended
 *  that this be called by the @ref EVENT_USB_Device_StartOfFrame() event, once SOF events have been enabled via
 *  @ref USB_Device_EnableSOFEvents().
 *
 * @param	HIDInterfaceInfo	: Pointer to a structure containing a HID Class configuration and state.
 */
PRAGMA_ALWAYS_INLINE
static inline void HID_Device_MillisecondElapsed(USB_ClassInfo_HID_Device_t *const HIDInterfaceInfo) ATTR_ALWAYS_INLINE
ATTR_NON_NULL_PTR_ARG(1);
static inline void HID_Device_MillisecondElapsed(USB_ClassInfo_HID_Device_t *const HIDInterfaceInfo)
{
	if (HIDInterfaceInfo->State.IdleMSRemaining) {
		HIDInterfaceInfo->State.IdleMSRemaining--;
	}
}

/* Disable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
}
		#endif

#endif

/** @} */

