/*
 * @brief Host mode driver for the library USB Mass Storage Class driver
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

/** @ingroup Group_USBClassMS
 *  @defgroup Group_USBClassMassStorageHost Mass Storage Class Host Mode Driver
 *
 *  @section Sec_Dependencies Module Source Dependencies
 *  The following files must be built with any user project that uses this module:
 *    - LPCUSBlib/Drivers/USB/Class/Host/MassStorage.c <i>(Makefile source module name: LPCUSBlib_SRC_USBCLASS)</i>
 *
 *  @section Sec_ModDescription Module Description
 *  Host Mode USB Class driver framework interface, for the Mass Storage USB Class driver.
 *
 *  @{
 */

#ifndef __MS_CLASS_HOST_H__
#define __MS_CLASS_HOST_H__

	/* Includes: */
		#include "../../USB.h"
		#include "../Common/MassStorageClassCommon.h"

	/* Enable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			extern "C" {
		#endif

	/* Preprocessor Checks: */
		#if !defined(__INCLUDE_FROM_MS_DRIVER)
			#error Do not include this file directly. Include LPCUSBlib/Drivers/USB.h instead.
		#endif

	/* Public Interface - May be used in end-application: */
		/* Macros: */
			/** Error code for some Mass Storage Host functions, indicating a logical (and not hardware) error. */
			#define MS_ERROR_LOGICAL_CMD_FAILED              0x80

		/* Type Defines: */
			/** @brief Mass Storage Class Host Mode Configuration and State Structure.
			 *
			 *  Class state structure. An instance of this structure should be made within the user application,
			 *  and passed to each of the Mass Storage class driver functions as the \c MSInterfaceInfo parameter. This
			 *  stores each Mass Storage interface's configuration and state information.
			 */
			typedef struct
			{
				struct
				{
					uint8_t  DataINPipeNumber; /**< Pipe number of the Mass Storage interface's IN data pipe. */
					bool     DataINPipeDoubleBank; /**< Indicates if the Mass Storage interface's IN data pipe should use double banking. */

					uint8_t  DataOUTPipeNumber; /**< Pipe number of the Mass Storage interface's OUT data pipe. */
					bool     DataOUTPipeDoubleBank; /**< Indicates if the Mass Storage interface's OUT data pipe should use double banking. */
					uint8_t  PortNumber;		/**< Port number that this interface is running.
												*/
				} Config; /**< Config data for the USB class interface within the device. All elements in this section
				           *   <b>must</b> be set or the interface will fail to enumerate and operate correctly.
				           */
				struct
				{
					bool     IsActive; /**< Indicates if the current interface instance is connected to an attached device, valid
					                    *   after @ref MS_Host_ConfigurePipes() is called and the Host state machine is in the
					                    *   Configured state.
					                    */
					uint8_t  InterfaceNumber; /**< Interface index of the Mass Storage interface within the attached device. */

					uint16_t DataINPipeSize; /**< Size in bytes of the Mass Storage interface's IN data pipe. */
					uint16_t DataOUTPipeSize;  /**< Size in bytes of the Mass Storage interface's OUT data pipe. */

					uint32_t TransactionTag; /**< Current transaction tag for data synchronizing of packets. */
				} State; /**< State data for the USB class interface within the device. All elements in this section
						  *   <b>may</b> be set to initial values, but may also be ignored to default to sane values when
						  *   the interface is enumerated.
						  */
			} USB_ClassInfo_MS_Host_t;

			/** @brief SCSI Device LUN Capacity Structure.
			 *
			 *  SCSI capacity structure, to hold the total capacity of the device in both the number
			 *  of blocks in the current LUN, and the size of each block. This structure is filled by
			 *  the device when the @ref MS_Host_ReadDeviceCapacity() function is called.
			 */
			typedef struct
			{
				uint32_t Blocks; /**< Number of blocks in the addressed LUN of the device. */
				uint32_t BlockSize; /**< Number of bytes in each block in the addressed LUN. */
			} SCSI_Capacity_t;

		/* Enums: */
			enum MS_Host_EnumerationFailure_ErrorCodes_t
			{
				MS_ENUMERROR_NoError                    = 0, /**< Configuration Descriptor was processed successfully. */
				MS_ENUMERROR_InvalidConfigDescriptor    = 1, /**< The device returned an invalid Configuration Descriptor. */
				MS_ENUMERROR_NoCompatibleInterfaceFound = 2, /**< A compatible Mass Storage interface was not found in the device's Configuration Descriptor. */
				MS_ENUMERROR_PipeConfigurationFailed    = 3, /**< One or more pipes for the specified interface could not be configured correctly. */
			};

		/* Function Prototypes: */
			/** @brief Host interface configuration routine, to configure a given Mass Storage host interface instance using the
			 *  Configuration Descriptor read from an attached USB device. This function automatically updates the given Mass
			 *  Storage Host instance's state values and configures the pipes required to communicate with the interface if it
			 *  is found within the device. This should be called once after the stack has enumerated the attached device, while
			 *  the host state machine is in the Addressed state.
			 *
			 *  @param MSInterfaceInfo      : Pointer to a structure containing an MS Class host configuration and state.
			 *  @param ConfigDescriptorSize : Length of the attached device's Configuration Descriptor.
			 *  @param ConfigDescriptorData : Pointer to a buffer containing the attached device's Configuration Descriptor.
			 *
			 *  @return A value from the @ref MS_Host_EnumerationFailure_ErrorCodes_t enum.
			 */
			uint8_t MS_Host_ConfigurePipes(USB_ClassInfo_MS_Host_t* const MSInterfaceInfo,
			                               uint16_t ConfigDescriptorSize,
			                               void* ConfigDescriptorData) ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(3);

			/** @brief Sends a MASS STORAGE RESET control request to the attached device, resetting the Mass Storage Interface
			 *  and readying it for the next Mass Storage command. This should be called after a failed SCSI request to 
			 *  ensure the attached Mass Storage device is ready to receive the next command.
			 *
			 *  @param MSInterfaceInfo : Pointer to a structure containing a MS Class host configuration and state.
			 *
			 *  @return A value from the @ref USB_Host_SendControlErrorCodes_t enum.
			 */
			uint8_t MS_Host_ResetMSInterface(USB_ClassInfo_MS_Host_t* const MSInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1);

			/** @brief Sends a GET MAX LUN control request to the attached device, retrieving the index of the highest LUN (Logical
			 *  UNit, a logical drive) in the device. This value can then be used in the other functions of the Mass Storage
			 *  Host mode Class driver to address a specific LUN within the device.
			 *
			 *  @note Some devices do not support this request, and will STALL it when issued. To get around this,
			 *        on unsupported devices the max LUN index will be reported as zero and no error will be returned
			 *        if the device STALLs the request.
			 *
			 *  @param MSInterfaceInfo : Pointer to a structure containing a MS Class host configuration and state.
			 *  @param MaxLUNIndex     : Pointer to a location where the highest LUN index value should be stored.
			 *
			 *  @return A value from the @ref USB_Host_SendControlErrorCodes_t enum.
			 */
			uint8_t MS_Host_GetMaxLUN(USB_ClassInfo_MS_Host_t* const MSInterfaceInfo,
			                          uint8_t* const MaxLUNIndex) ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(2);

			/** @brief Retrieves the Mass Storage device's inquiry data for the specified LUN, indicating the device characteristics and
			 *  properties.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @param MSInterfaceInfo : Pointer to a structure containing a MS Class host configuration and state.
			 *  @param LUNIndex        : LUN index within the device the command is being issued to.
			 *  @param InquiryData     : Location where the read inquiry data should be stored.
			 *
			 *  @return A value from the @ref Pipe_Stream_RW_ErrorCodes_t enum or @ref MS_ERROR_LOGICAL_CMD_FAILED.
			 */
			uint8_t MS_Host_GetInquiryData(USB_ClassInfo_MS_Host_t* const MSInterfaceInfo,
			                               const uint8_t LUNIndex,
			                               SCSI_Inquiry_Response_t* const InquiryData) ATTR_NON_NULL_PTR_ARG(1)
			                               ATTR_NON_NULL_PTR_ARG(3);

			/** @brief Sends a TEST UNIT READY command to the device, to determine if it is ready to accept other SCSI commands.
			 *
			 *  @param MSInterfaceInfo : Pointer to a structure containing a MS Class host configuration and state.
			 *  @param LUNIndex        : LUN index within the device the command is being issued to.
			 *
			 *  @return A value from the @ref Pipe_Stream_RW_ErrorCodes_t enum or @ref MS_ERROR_LOGICAL_CMD_FAILED if not ready.
			 */
			uint8_t MS_Host_TestUnitReady(USB_ClassInfo_MS_Host_t* const MSInterfaceInfo,
			                              const uint8_t LUNIndex) ATTR_NON_NULL_PTR_ARG(1);

			/** @brief Retrieves the total capacity of the attached USB Mass Storage device, in blocks, and block size.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @param MSInterfaceInfo : Pointer to a structure containing a MS Class host configuration and state.
			 *  @param LUNIndex        : LUN index within the device the command is being issued to.
			 *  @param DeviceCapacity  : Pointer to the location where the capacity information should be stored.
			 *
			 *  @return A value from the @ref Pipe_Stream_RW_ErrorCodes_t enum or @ref MS_ERROR_LOGICAL_CMD_FAILED if not ready.
			 */
			uint8_t MS_Host_ReadDeviceCapacity(USB_ClassInfo_MS_Host_t* const MSInterfaceInfo,
			                                   const uint8_t LUNIndex,
			                                   SCSI_Capacity_t* const DeviceCapacity) ATTR_NON_NULL_PTR_ARG(1)
			                                   ATTR_NON_NULL_PTR_ARG(3);

			/** @brief Retrieves the device sense data, indicating the current device state and error codes for the previously
			 *  issued command.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @param MSInterfaceInfo : Pointer to a structure containing a MS Class host configuration and state.
			 *  @param LUNIndex        : LUN index within the device the command is being issued to.
			 *  @param SenseData       : Pointer to the location where the sense information should be stored.
			 *
			 *  @return A value from the @ref Pipe_Stream_RW_ErrorCodes_t enum or @ref MS_ERROR_LOGICAL_CMD_FAILED if not ready.
			 */
			uint8_t MS_Host_RequestSense(USB_ClassInfo_MS_Host_t* const MSInterfaceInfo,
			                             const uint8_t LUNIndex,
			                             SCSI_Request_Sense_Response_t* const SenseData) ATTR_NON_NULL_PTR_ARG(1)
			                             ATTR_NON_NULL_PTR_ARG(3);

			/** @brief Issues a PREVENT MEDIUM REMOVAL command, to logically (or, depending on the type of device, physically) lock
			 *  the device from removal so that blocks of data on the medium can be read or altered.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @param MSInterfaceInfo : Pointer to a structure containing a MS Class host configuration and state.
			 *  @param LUNIndex        : LUN index within the device the command is being issued to.
			 *  @param PreventRemoval  : Boolean \c true if the device should be locked from removal, \c false otherwise.
			 *
			 *  @return A value from the @ref Pipe_Stream_RW_ErrorCodes_t enum or @ref MS_ERROR_LOGICAL_CMD_FAILED if not ready.
			 */
			uint8_t MS_Host_PreventAllowMediumRemoval(USB_ClassInfo_MS_Host_t* const MSInterfaceInfo,
			                                          const uint8_t LUNIndex,
			                                          const bool PreventRemoval) ATTR_NON_NULL_PTR_ARG(1);

			/** @brief Reads blocks of data from the attached Mass Storage device's medium.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @param MSInterfaceInfo : Pointer to a structure containing a MS Class host configuration and state.
			 *  @param LUNIndex        : LUN index within the device the command is being issued to.
			 *  @param BlockAddress    : Starting block address within the device to read from.
			 *  @param Blocks          : Total number of blocks to read.
			 *  @param BlockSize       : Size in bytes of each block within the device.
			 *  @param BlockBuffer     : Pointer to where the read data from the device should be stored.
			 *
			 *  @return A value from the @ref Pipe_Stream_RW_ErrorCodes_t enum or @ref MS_ERROR_LOGICAL_CMD_FAILED if not ready.
			 */
			uint8_t MS_Host_ReadDeviceBlocks(USB_ClassInfo_MS_Host_t* const MSInterfaceInfo,
			                                 const uint8_t LUNIndex,
			                                 const uint32_t BlockAddress,
			                                 const uint8_t Blocks,
			                                 const uint16_t BlockSize,
			                                 void* BlockBuffer) ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(6);

			/** @brief Writes blocks of data to the attached Mass Storage device's medium.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @param MSInterfaceInfo : Pointer to a structure containing a MS Class host configuration and state.
			 *  @param LUNIndex        : LUN index within the device the command is being issued to.
			 *  @param BlockAddress    : Starting block address within the device to write to.
			 *  @param Blocks          : Total number of blocks to read.
			 *  @param BlockSize       : Size in bytes of each block within the device.
			 *  @param BlockBuffer     : Pointer to where the data to write should be sourced from.
			 *
			 *  @return A value from the @ref Pipe_Stream_RW_ErrorCodes_t enum or @ref MS_ERROR_LOGICAL_CMD_FAILED if not ready.
			 */
			uint8_t MS_Host_WriteDeviceBlocks(USB_ClassInfo_MS_Host_t* const MSInterfaceInfo,
			                                  const uint8_t LUNIndex,
			                                  const uint32_t BlockAddress,
			                                  const uint8_t Blocks,
			                                  const uint16_t BlockSize,
			                                  const void* BlockBuffer) ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(6);

		/* Inline Functions: */
			/** @brief General management task for a given Mass Storage host class interface, required for the correct operation of
			 *  the interface. This should be called frequently in the main program loop, before the master USB management task
			 *  @ref USB_USBTask().
			 *
			 *  @param MSInterfaceInfo : Pointer to a structure containing an Mass Storage Class host configuration and state.
			 *	@return	Nothing
			 */
			static inline void MS_Host_USBTask(USB_ClassInfo_MS_Host_t* const MSInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1) ATTR_ALWAYS_INLINE;
			static inline void MS_Host_USBTask(USB_ClassInfo_MS_Host_t* const MSInterfaceInfo)
			{
				(void)MSInterfaceInfo;
			}

	/* Private Interface - For use in library only: */
	#if !defined(__DOXYGEN__)
		/* Macros: */
			#define MS_COMMAND_DATA_TIMEOUT_MS        10000

		/* Function Prototypes: */
			#if defined(__INCLUDE_FROM_MASSSTORAGE_HOST_C)
				static uint8_t MS_Host_SendCommand(USB_ClassInfo_MS_Host_t* const MSInterfaceInfo,
				                                   MS_CommandBlockWrapper_t* const SCSICommandBlock,
				                                   const void* const BufferPtr) ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(2);
				static uint8_t MS_Host_WaitForDataReceived(USB_ClassInfo_MS_Host_t* const MSInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1);
				static uint8_t MS_Host_SendReceiveData(USB_ClassInfo_MS_Host_t* const MSInterfaceInfo,
				                                       MS_CommandBlockWrapper_t* const SCSICommandBlock,
				                                       void* BufferPtr) ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(2);
				static uint8_t MS_Host_GetReturnedStatus(USB_ClassInfo_MS_Host_t* const MSInterfaceInfo,
				                                         MS_CommandStatusWrapper_t* const SCSICommandStatus)
				                                         ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(2);

				static uint8_t DCOMP_MS_Host_NextMSInterface(void* const CurrentDescriptor)
				                                             ATTR_WARN_UNUSED_RESULT ATTR_NON_NULL_PTR_ARG(1);
				static uint8_t DCOMP_MS_Host_NextMSInterfaceEndpoint(void* const CurrentDescriptor)
				                                                     ATTR_WARN_UNUSED_RESULT ATTR_NON_NULL_PTR_ARG(1);
			#endif
	#endif

	/* Disable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			}
		#endif

#endif

/** @} */

