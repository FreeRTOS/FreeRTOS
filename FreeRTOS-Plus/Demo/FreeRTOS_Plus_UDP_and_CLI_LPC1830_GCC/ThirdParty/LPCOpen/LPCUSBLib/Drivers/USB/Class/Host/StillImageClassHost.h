/*
 * @brief Host mode driver for the library USB Still Image Class driver
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

/** @ingroup Group_USBClassSI
 *  @defgroup Group_USBClassStillImageHost Still Image Class Host Mode Driver
 *
 *  @section Sec_Dependencies Module Source Dependencies
 *  The following files must be built with any user project that uses this module:
 *    - LPCUSBlib/Drivers/USB/Class/Host/StillImage.c <i>(Makefile source module name: LPCUSBlib_SRC_USBCLASS)</i>
 *
 *  @section Sec_ModDescription Module Description
 *  Host Mode USB Class driver framework interface, for the Still Image USB Class driver.
 *
 *  @{
 */

#ifndef __SI_CLASS_HOST_H__
#define __SI_CLASS_HOST_H__

	/* Includes: */
		#include "../../USB.h"
		#include "../Common/StillImageClassCommon.h"

	/* Enable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			extern "C" {
		#endif

	/* Preprocessor Checks: */
		#if !defined(__INCLUDE_FROM_SI_DRIVER)
			#error Do not include this file directly. Include LPCUSBlib/Drivers/USB.h instead.
		#endif

	/* Public Interface - May be used in end-application: */
		/* Macros: */
			/** Error code for some Still Image Host functions, indicating a logical (and not hardware) error. */
			#define SI_ERROR_LOGICAL_CMD_FAILED              0x80

		/* Type Defines: */
			/** @brief Still Image Class Host Mode Configuration and State Structure.
			 *
			 *  Class state structure. An instance of this structure should be made within the user application,
			 *  and passed to each of the Still Image class driver functions as the \c SIInterfaceInfo parameter. This
			 *  stores each Still Image interface's configuration and state information.
			 */
			typedef struct
			{
				const struct
				{
					uint8_t  DataINPipeNumber; /**< Pipe number of the Still Image interface's IN data pipe. */
					bool     DataINPipeDoubleBank; /**< Indicates if the Still Image interface's IN data pipe should use double banking. */

					uint8_t  DataOUTPipeNumber; /**< Pipe number of the Still Image interface's OUT data pipe. */
					bool     DataOUTPipeDoubleBank; /**< Indicates if the Still Image interface's OUT data pipe should use double banking. */

					uint8_t  EventsPipeNumber; /**< Pipe number of the Still Image interface's IN events endpoint, if used. */
					bool     EventsPipeDoubleBank; /**< Indicates if the Still Image interface's events data pipe should use double banking. */
					uint8_t  PortNumber;		/**< Port number that this interface is running.
												*/
				} Config; /**< Config data for the USB class interface within the device. All elements in this section
				           *   <b>must</b> be set or the interface will fail to enumerate and operate correctly.
				           */
				struct
				{
					bool     IsActive; /**< Indicates if the current interface instance is connected to an attached device, valid
					                    *   after @ref SI_Host_ConfigurePipes() is called and the Host state machine is in the
					                    *   Configured state.
					                    */
					uint8_t  InterfaceNumber; /**< Interface index of the Still Image interface within the attached device. */

					uint16_t DataINPipeSize; /**< Size in bytes of the Still Image interface's IN data pipe. */
					uint16_t DataOUTPipeSize;  /**< Size in bytes of the Still Image interface's OUT data pipe. */
					uint16_t EventsPipeSize;  /**< Size in bytes of the Still Image interface's IN events pipe. */

					bool IsSessionOpen; /**< Indicates if a PIMA session is currently open with the attached device. */
					uint32_t TransactionID; /**< Transaction ID for the next transaction to send to the device. */
				} State; /**< State data for the USB class interface within the device. All elements in this section
						  *   <b>may</b> be set to initial values, but may also be ignored to default to sane values when
						  *   the interface is enumerated.
						  */
			} USB_ClassInfo_SI_Host_t;

		/* Enums: */
			/** Enum for the possible error codes returned by the @ref SI_Host_ConfigurePipes() function. */
			enum SI_Host_EnumerationFailure_ErrorCodes_t
			{
				SI_ENUMERROR_NoError                    = 0, /**< Configuration Descriptor was processed successfully. */
				SI_ENUMERROR_InvalidConfigDescriptor    = 1, /**< The device returned an invalid Configuration Descriptor. */
				SI_ENUMERROR_NoCompatibleInterfaceFound = 2, /**< A compatible Still Image interface was not found in the device's
				                                              *   Configuration Descriptor.
				                                              */
				SI_ENUMERROR_PipeConfigurationFailed    = 3, /**< One or more pipes for the specified interface could not be configured correctly. */
			};

		/* Function Prototypes: */
			/** @brief Host interface configuration routine, to configure a given Still Image host interface instance using the
			 *  Configuration Descriptor read from an attached USB device. This function automatically updates the given Still
			 *  Image Host instance's state values and configures the pipes required to communicate with the interface if it is
			 *  found within the device. This should be called once after the stack has enumerated the attached device, while
			 *  the host state machine is in the Addressed state.
			 *
			 *  @param SIInterfaceInfo      : Pointer to a structure containing a Still Image Class host configuration and state.
			 *  @param ConfigDescriptorSize : Length of the attached device's Configuration Descriptor.
			 *  @param ConfigDescriptorData : Pointer to a buffer containing the attached device's Configuration Descriptor.
			 *
			 *  @return A value from the @ref SI_Host_EnumerationFailure_ErrorCodes_t enum.
			 */
			uint8_t SI_Host_ConfigurePipes(USB_ClassInfo_SI_Host_t* const SIInterfaceInfo,
			                               uint16_t ConfigDescriptorSize,
			                               void* ConfigDescriptorData) ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(3);

			/** @brief Opens a new PIMA session with the attached device. This should be used before any session-orientated PIMA commands
			 *  are issued to the device. Only one session can be open at the one time.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @param SIInterfaceInfo : Pointer to a structure containing a Still Image Class host configuration and state.
			 *
			 *  @return A value from the @ref Pipe_Stream_RW_ErrorCodes_t enum, or @ref SI_ERROR_LOGICAL_CMD_FAILED if the device
			 *          returned a logical command failure.
			 */
			uint8_t SI_Host_OpenSession(USB_ClassInfo_SI_Host_t* const SIInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1);

			/** @brief Closes an already opened PIMA session with the attached device. This should be used after all session-orientated
			 *  PIMA commands have been issued to the device.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @param SIInterfaceInfo : Pointer to a structure containing a Still Image Class host configuration and state.
			 *
			 *  @return A value from the @ref Pipe_Stream_RW_ErrorCodes_t enum, or @ref SI_ERROR_LOGICAL_CMD_FAILED if the device
			 *          returned a logical command failure.
			 */
			uint8_t SI_Host_CloseSession(USB_ClassInfo_SI_Host_t* const SIInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1);

			/** @brief Sends a raw PIMA block header to the device, filling out the transaction ID automatically. This can be used to send
			 *  arbitrary PIMA blocks to the device with or without parameters.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @param SIInterfaceInfo : Pointer to a structure containing a Still Image Class host configuration and state.
			 *  @param PIMAHeader      : Pointer to a PIMA container structure that is to be sent.
			 *
			 *  @return A value from the @ref Pipe_Stream_RW_ErrorCodes_t enum.
			 */
			uint8_t SI_Host_SendBlockHeader(USB_ClassInfo_SI_Host_t* const SIInterfaceInfo,
			                                PIMA_Container_t* const PIMAHeader) ATTR_NON_NULL_PTR_ARG(1)
			                                ATTR_NON_NULL_PTR_ARG(2);

			/** @brief Receives a raw PIMA block header from the device. This can be used to receive arbitrary PIMA blocks from the device with
			 *  or without parameters.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @param SIInterfaceInfo : Pointer to a structure containing a Still Image Class host configuration and state.
			 *  @param PIMAHeader      : Pointer to a PIMA container structure where the received block is to be stored.
			 *
			 *  @return A value from the @ref Pipe_Stream_RW_ErrorCodes_t enum.
			 */
			uint8_t SI_Host_ReceiveBlockHeader(USB_ClassInfo_SI_Host_t* const SIInterfaceInfo,
			                                   PIMA_Container_t* const PIMAHeader) ATTR_NON_NULL_PTR_ARG(1)
			                                   ATTR_NON_NULL_PTR_ARG(2);

			/** @brief Sends a given PIMA command to the attached device, filling out the PIMA command header's Transaction ID automatically.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @param SIInterfaceInfo : Pointer to a structure containing a Still Image Class host configuration and state.
			 *  @param Operation       : PIMA operation code to issue to the device.
			 *  @param TotalParams     : Total number of 32-bit parameters to send to the device in the issued command block.
			 *  @param Params          : Pointer to an array of 32-bit values containing the parameters to send in the command block.
			 *
			 *  @return A value from the @ref Pipe_Stream_RW_ErrorCodes_t enum, or @ref SI_ERROR_LOGICAL_CMD_FAILED if the device
			 *          returned a logical command failure.
			 */
			uint8_t SI_Host_SendCommand(USB_ClassInfo_SI_Host_t* const SIInterfaceInfo,
			                            const uint16_t Operation,
			                            const uint8_t TotalParams,
			                            uint32_t* const Params) ATTR_NON_NULL_PTR_ARG(1);

			/** @brief Receives and checks a response block from the attached Still Image device, once a command has been issued and all data
			 *  associated with the command has been transferred.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @param SIInterfaceInfo : Pointer to a structure containing a Still Image Class host configuration and state.
			 *
			 *  @return A value from the @ref Pipe_Stream_RW_ErrorCodes_t enum, or @ref SI_ERROR_LOGICAL_CMD_FAILED if the device
			 *          returned a logical command failure.
			 */
			uint8_t SI_Host_ReceiveResponse(USB_ClassInfo_SI_Host_t* const SIInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1);

			/** @brief Indicates if the device has issued a PIMA event block to the host via the asynchronous events pipe.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @param SIInterfaceInfo : Pointer to a structure containing a Still Image Class host configuration and state.
			 *
			 *  @return Boolean \c true if an event is waiting to be read, \c false otherwise.
			 */
			bool SI_Host_IsEventReceived(USB_ClassInfo_SI_Host_t* const SIInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1);

			/** @brief Receives an asynchronous event block from the device via the asynchronous events pipe.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @param SIInterfaceInfo : Pointer to a structure containing a Still Image Class host configuration and state.
			 *  @param PIMAHeader      : Pointer to a PIMA container structure where the event should be stored.
			 *
			 *  @return A value from the @ref Pipe_Stream_RW_ErrorCodes_t enum, or @ref SI_ERROR_LOGICAL_CMD_FAILED if the device
			 *          returned a logical command failure.
			 */
			uint8_t SI_Host_ReceiveEventHeader(USB_ClassInfo_SI_Host_t* const SIInterfaceInfo,
			                                   PIMA_Container_t* const PIMAHeader) ATTR_NON_NULL_PTR_ARG(1)
			                                   ATTR_NON_NULL_PTR_ARG(2);

			/** @brief Sends arbitrary data to the attached device, for use in the data phase of PIMA commands which require data
			 *  transfer beyond the regular PIMA command block parameters.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @param SIInterfaceInfo : Pointer to a structure containing a Still Image Class host configuration and state.
			 *  @param Buffer          : Pointer to a buffer where the data to send has been stored.
			 *  @param Bytes           : Length in bytes of the data in the buffer to send to the attached device.
			 *
			 *  @return A value from the @ref Pipe_Stream_RW_ErrorCodes_t enum.
			 */
			uint8_t SI_Host_SendData(USB_ClassInfo_SI_Host_t* const SIInterfaceInfo,
			                         void* Buffer,
			                         const uint16_t Bytes) ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(2);

			/** @brief Receives arbitrary data from the attached device, for use in the data phase of PIMA commands which require data
			 *  transfer beyond the regular PIMA command block parameters.
			 *
			 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
			 *       call will fail.
			 *
			 *  @param SIInterfaceInfo : Pointer to a structure containing a Still Image Class host configuration and state.
			 *  @param Buffer          : Pointer to a buffer where the received data is to be stored.
			 *  @param Bytes           : Length in bytes of the data to read.
			 *
			 *  @return A value from the @ref Pipe_Stream_RW_ErrorCodes_t enum.
			 */
			uint8_t SI_Host_ReadData(USB_ClassInfo_SI_Host_t* const SIInterfaceInfo,
			                         void* Buffer,
			                         const uint16_t Bytes) ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(2);

		/* Inline Functions: */
			/** @brief General management task for a given Still Image host class interface, required for the correct operation of the
			 *  interface. This should be called frequently in the main program loop, before the master USB management task
			 *  @ref USB_USBTask().
			 *
			 *  @param SIInterfaceInfo : Pointer to a structure containing a Still Image Class host configuration and state.
			 *	@return	Nothing
			 */
			static inline void SI_Host_USBTask(USB_ClassInfo_SI_Host_t* const SIInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1) ATTR_ALWAYS_INLINE;
			static inline void SI_Host_USBTask(USB_ClassInfo_SI_Host_t* const SIInterfaceInfo)
			{
				(void)SIInterfaceInfo;
			}

	/* Private Interface - For use in library only: */
	#if !defined(__DOXYGEN__)
		/* Macros: */
			#define SI_COMMAND_DATA_TIMEOUT_MS        10000

		/* Function Prototypes: */
			#if defined(__INCLUDE_FROM_STILLIMAGE_HOST_C)
				static uint8_t DCOMP_SI_Host_NextSIInterface(void* const CurrentDescriptor)
				                                             ATTR_WARN_UNUSED_RESULT ATTR_NON_NULL_PTR_ARG(1);
				static uint8_t DCOMP_SI_Host_NextSIInterfaceEndpoint(void* const CurrentDescriptor)
				                                                     ATTR_WARN_UNUSED_RESULT ATTR_NON_NULL_PTR_ARG(1);
			#endif
	#endif

	/* Disable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			}
		#endif

#endif

/** @} */

