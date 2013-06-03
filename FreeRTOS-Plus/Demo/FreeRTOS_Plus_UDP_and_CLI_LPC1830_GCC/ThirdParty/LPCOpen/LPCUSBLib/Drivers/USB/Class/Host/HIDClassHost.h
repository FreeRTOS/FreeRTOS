/*
 * @brief Host mode driver for the library USB HID Class driver
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
 *  @defgroup Group_USBClassHIDHost HID Class Host Mode Driver
 *
 *  @section Sec_Dependencies Module Source Dependencies
 *  The following files must be built with any user project that uses this module:
 *    - LPCUSBlib/Drivers/USB/Class/Host/HID.c <i>(Makefile source module name: LPCUSBlib_SRC_USBCLASS)</i>
 *
 *  @section Sec_ModDescription Module Description
 *  Host Mode USB Class driver framework interface, for the HID USB Class driver.
 *
 *  @{
 */

#ifndef __HID_CLASS_HOST_H__
#define __HID_CLASS_HOST_H__

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
		/* Macros: */
			/** Error code for some HID Host functions, indicating a logical (and not hardware) error. */
			#define HID_ERROR_LOGICAL              0x80

		/* Type Defines: */
			/** @brief HID Class Host Mode Configuration and State Structure.
			 *
			 *  Class state structure. An instance of this structure should be made within the user application,
			 *  and passed to each of the HID class driver functions as the \c HIDInterfaceInfo parameter. This
			 *  stores each HID interface's configuration and state information.
			 */
			typedef struct
			{
				struct
				{
					uint8_t  DataINPipeNumber; /**< Pipe number of the HID interface's IN data pipe. */
					bool     DataINPipeDoubleBank; /**< Indicates if the HID interface's IN data pipe should use double banking. */

					uint8_t  DataOUTPipeNumber; /**< Pipe number of the HID interface's OUT data pipe. */
					bool     DataOUTPipeDoubleBank; /**< Indicates if the HID interface's OUT data pipe should use double banking. */

					uint8_t  HIDInterfaceProtocol; /**< HID interface protocol value to match against if a specific
					                                *   boot subclass protocol is required, a protocol value from the
					                                *   @ref HID_Descriptor_ClassSubclassProtocol_t enum.
					                                */
					#if !defined(HID_HOST_BOOT_PROTOCOL_ONLY)
					HID_ReportInfo_t* HIDParserData; /**< HID parser data to store the parsed HID report data, when boot protocol
					                                  *   is not used.
													  *
					                                  *  @note When the \c HID_HOST_BOOT_PROTOCOL_ONLY compile time token is defined,
					                                  *        this method is unavailable.
					                                  */
					#endif

					uint8_t  PortNumber;		/**< Port number that this interface is running.
												*/
				} Config; /**< Config data for the USB class interface within the device. All elements in this section
				           *   <b>must</b> be set or the interface will fail to enumerate and operate correctly.
				           */
				struct
				{
					bool IsActive; /**< Indicates if the current interface instance is connected to an attached device, valid
					                *   after @ref HID_Host_ConfigurePipes() is called and the Host state machine is in the
					                *   Configured state.
					                */
					uint8_t InterfaceNumber; /**< Interface index of the HID interface within the attached device. */

					uint16_t DataINPipeSize; /**< Size in bytes of the HID interface's IN data pipe. */
					uint16_t DataOUTPipeSize;  /**< Size in bytes of the HID interface's OUT data pipe. */

					bool SupportsBootProtocol; /**< Indicates if the current interface instance supports the HID Boot
					                            *   Protocol when enabled via @ref HID_Host_SetBootProtocol().
					                            */
					bool DeviceUsesOUTPipe; /**< Indicates if the current interface instance uses a separate OUT data pipe for
					                         *   OUT reports, or if OUT reports are sent via the control pipe instead.
					                         */
					bool UsingBootProtocol; /**< Indicates that the interface is currently initialized in Boot Protocol mode */
					uint16_t HIDReportSize; /**< Size in bytes of the HID report descriptor in the device. */

					uint8_t LargestReportSize; /**< Largest report the device will send, in bytes. */
				} State; /**< State data for the USB class interface within the device. All elements in this section
						  *   <b>may</b> be set to initial values, but may also be ignored to default to sane values when
						  *   the interface is enumerated.
						  */
			} USB_ClassInfo_HID_Host_t;

		/* Enums: */
			/** Enum for the possible error codes returned by the @ref HID_Host_ConfigurePipes() function. */
			enum HID_Host_EnumerationFailure_ErrorCodes_t
			{
				HID_ENUMERROR_NoError                    = 0, /**< Configuration Descriptor was processed successfully. */
				HID_ENUMERROR_InvalidConfigDescriptor    = 1, /**< The device returned an invalid Configuration Descriptor. */
				HID_ENUMERROR_NoCompatibleInterfaceFound = 2, /**< A compatible HID interface was not found in the device's Configuration Descriptor. */
				HID_ENUMERROR_PipeConfigurationFailed    = 3, /**< One or more pipes for the specified interface could not be configured correctly. */
			};

		/* Function Prototypes: */
			/** @brief Host interface configuration routine, to configure a given HID host interface instance using the Configuration
			 *  Descriptor read from an attached USB device. This function automatically updates the given HID Host instance's
			 *  state values and configures the pipes required to communicate with the interface if it is found within the
			 *  device. This should be called once after the stack has enumerated the attached device, while the host state
			 *  machine is in the Addressed state.
			 *
			 *  @note Once the device pipes are configured, the HID device's reporting protocol <b>must</b> be set via a call
			 *        to either the @ref HID_Host_SetBootProtocol() or @ref HID_Host_SetReportProtocol() function.
			 *
			 *  @param HIDInterfaceInfo       : Pointer to a structure containing a HID Class host configuration and state.
			 *  @param ConfigDescriptorSize   : Length of the attached device's Configuration Descriptor.
			 *  @param DeviceConfigDescriptor : Pointer to a buffer containing the attached device's Configuration Descriptor.
			 *
			 *  @return A value from the @ref HID_Host_EnumerationFailure_ErrorCodes_t enum.
			 */
			uint8_t HID_Host_ConfigurePipes(USB_ClassInfo_HID_Host_t* const HIDInterfaceInfo,
			                                uint16_t ConfigDescriptorSize,
			                                void* DeviceConfigDescriptor) ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(3);


			/** @brief Receives a HID IN report from the attached HID device, when a report has been received on the HID IN Data pipe.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @note The destination buffer should be large enough to accommodate the largest report that the attached device
			 *        can generate.
			 *
			 *  @param HIDInterfaceInfo : Pointer to a structure containing a HID Class host configuration and state.
			 *  @param Buffer           : Buffer to store the received report into.
			 *
			 *  @return An error code from the @ref Pipe_Stream_RW_ErrorCodes_t enum.
			 */
			uint8_t HID_Host_ReceiveReport(USB_ClassInfo_HID_Host_t* const HIDInterfaceInfo,
			                               void* Buffer) ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(2);

			#if !defined(HID_HOST_BOOT_PROTOCOL_ONLY)
			/** @brief Receives a HID IN report from the attached device, by the report ID.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @note When the \c HID_HOST_BOOT_PROTOCOL_ONLY compile time token is defined, this method is unavailable.
			 *
			 *  @param HIDInterfaceInfo : Pointer to a structure containing a HID Class host configuration and state.
			 *  @param ReportID         : Report ID of the received report if ControlRequest is false, set by the to the Report ID to fetch.
			 *  @param Buffer            Buffer to store the received report into.
			 *
			 *  @return A value from the @ref USB_Host_SendControlErrorCodes_t enum.
			 */
			uint8_t HID_Host_ReceiveReportByID(USB_ClassInfo_HID_Host_t* const HIDInterfaceInfo,
			                                   const uint8_t ReportID,
			                                   void* Buffer) ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(3);
			#endif

			/** @brief Sends an OUT or FEATURE report to the currently attached HID device, using the device's OUT pipe if available,
			 *  or the device's Control pipe if not.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @note When the \c HID_HOST_BOOT_PROTOCOL_ONLY compile time token is defined, the ReportID parameter is removed
			 *        from the parameter list of this function.
			 *
			 *  @param HIDInterfaceInfo : Pointer to a structure containing a HID Class host configuration and state.
			 *  @param ReportID         : Report ID of the report to send to the device, or 0 if the device does not use report IDs.
			 *  @param ReportType       : Type of report to issue to the device, either @ref HID_REPORT_ITEM_Out or @ref HID_REPORT_ITEM_Feature.
			 *  @param Buffer           : Buffer containing the report to send to the attached device.
			 *  @param ReportSize       : Report size in bytes to send to the attached device.
			 *
			 *  @return An error code from the @ref USB_Host_SendControlErrorCodes_t enum if the DeviceUsesOUTPipe flag is set in
			 *          the interface's state structure, a value from the @ref Pipe_Stream_RW_ErrorCodes_t enum otherwise.
			 */
			uint8_t HID_Host_SendReportByID(USB_ClassInfo_HID_Host_t* const HIDInterfaceInfo,
			#if !defined(HID_HOST_BOOT_PROTOCOL_ONLY)
			                                const uint8_t ReportID,
			#endif
			                                const uint8_t ReportType,
			                                void* Buffer,
			                                const uint16_t ReportSize) ATTR_NON_NULL_PTR_ARG(1)
			#if !defined(HID_HOST_BOOT_PROTOCOL_ONLY)
			                                ATTR_NON_NULL_PTR_ARG(4);
			#else
			                                ATTR_NON_NULL_PTR_ARG(3);
			#endif

			/** @brief Determines if a HID IN report has been received from the attached device on the data IN pipe.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @param HIDInterfaceInfo : Pointer to a structure containing a HID Class host configuration and state.
			 *
			 *  @return Boolean \c true if a report has been received, \c false otherwise.
			 */
			bool HID_Host_IsReportReceived(USB_ClassInfo_HID_Host_t* const HIDInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1);

			/** @brief Switches the attached HID device's reporting protocol over to the Boot Report protocol mode, on supported devices.
			 *
			 *  @note When the \c HID_HOST_BOOT_PROTOCOL_ONLY compile time token is defined, this method must still be called
			 *        to explicitly place the attached device into boot protocol mode before use.
			 *
			 *  @param HIDInterfaceInfo : Pointer to a structure containing a HID Class host configuration and state.
			 *
			 *  @return @ref HID_ERROR_LOGICAL if the device does not support Boot Protocol mode, a value from the
			 *          @ref USB_Host_SendControlErrorCodes_t enum otherwise.
			 */
			uint8_t HID_Host_SetBootProtocol(USB_ClassInfo_HID_Host_t* const HIDInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1);

			/** @brief Sets the idle period for the attached HID device to the specified interval. The HID idle period determines the rate
			 *  at which the device should send a report, when no state changes have ocurred; i.e. on HID keyboards, this sets the
			 *  hardware key repeat interval.
			 *
			 *  @param HIDInterfaceInfo : Pointer to a structure containing a HID Class host configuration and state.
			 *  @param MS               : Idle period as a multiple of four milliseconds, zero to disable hardware repeats
			 *
			 *  @return A value from the @ref USB_Host_SendControlErrorCodes_t enum.
			 */
			uint8_t HID_Host_SetIdlePeriod(USB_ClassInfo_HID_Host_t* const HIDInterfaceInfo,
			                               const uint16_t MS) ATTR_NON_NULL_PTR_ARG(1);

			#if !defined(HID_HOST_BOOT_PROTOCOL_ONLY)
			/** @brief Switches the attached HID device's reporting protocol over to the standard Report protocol mode. This also retrieves
			 *  and parses the device's HID report descriptor, so that the size of each report can be determined in advance.
			 *
			 *  @note Whether this function is used or not, the @ref CALLBACK_HIDParser_FilterHIDReportItem() callback from the HID
			 *        Report Parser this function references <b>must</b> be implemented in the user code.
			 *        \n\n
			 *
			 *  @note When the \c HID_HOST_BOOT_PROTOCOL_ONLY compile time token is defined, this method is unavailable.
			 *
			 *  @param HIDInterfaceInfo : Pointer to a structure containing a HID Class host configuration and state.
			 *
			 *  @return A value from the @ref USB_Host_SendControlErrorCodes_t enum if an error occurs while retrieving the HID
			 *          Report descriptor or the setting of the Report protocol, @ref HID_ERROR_LOGICAL if the HID interface does
			 *          not have a valid @ref HID_ReportInfo_t structure set in its configuration, a mask of @ref HID_ERROR_LOGICAL
			 *          and a value from the @ref HID_Parse_ErrorCodes_t otherwise.
			 */
			uint8_t HID_Host_SetReportProtocol(USB_ClassInfo_HID_Host_t* const HIDInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1);
			#endif

		/* Inline Functions: */
			/** @brief General management task for a given Human Interface Class host class interface, required for the correct operation of
			 *  the interface. This should be called frequently in the main program loop, before the master USB management task
			 *  @ref USB_USBTask().
			 *
			 *  @param HIDInterfaceInfo : Pointer to a structure containing a HID Class host configuration and state.
			 *	@return	Nothing
			 */
			static inline void HID_Host_USBTask(USB_ClassInfo_HID_Host_t* const HIDInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1);
			static inline void HID_Host_USBTask(USB_ClassInfo_HID_Host_t* const HIDInterfaceInfo)
			{
				(void)HIDInterfaceInfo;
			}

	/* Private Interface - For use in library only: */
	#if !defined(__DOXYGEN__)
		/* Function Prototypes: */
			#if defined(__INCLUDE_FROM_HID_HOST_C)
				static uint8_t DCOMP_HID_Host_NextHIDInterface(void* const CurrentDescriptor)
				                                               ATTR_WARN_UNUSED_RESULT ATTR_NON_NULL_PTR_ARG(1);
				static uint8_t DCOMP_HID_Host_NextHIDDescriptor(void* const CurrentDescriptor)
				                                                ATTR_WARN_UNUSED_RESULT ATTR_NON_NULL_PTR_ARG(1);
				static uint8_t DCOMP_HID_Host_NextHIDInterfaceEndpoint(void* const CurrentDescriptor)
				                                                       ATTR_WARN_UNUSED_RESULT ATTR_NON_NULL_PTR_ARG(1);
			#endif
	#endif

	/* Disable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			}
		#endif

#endif

/** @} */

