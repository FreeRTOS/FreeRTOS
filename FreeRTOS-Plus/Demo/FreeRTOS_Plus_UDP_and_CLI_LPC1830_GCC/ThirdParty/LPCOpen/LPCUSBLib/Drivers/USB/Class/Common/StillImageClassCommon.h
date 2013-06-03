/*
 * @brief Common definitions and declarations for the library USB Still Image Class driver
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
 *  @defgroup Group_USBClassSICommon  Common Class Definitions
 *
 *  @section Sec_ModDescription Module Description
 *  Constants, Types and Enum definitions that are common to both Device and Host modes for the USB
 *  Still Image Class.
 *
 *  @{
 */

#ifndef _SI_CLASS_COMMON_H_
#define _SI_CLASS_COMMON_H_

	/* Includes: */
		#include "../../Core/StdDescriptors.h"

	/* Enable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			extern "C" {
		#endif

	/* Preprocessor Checks: */
		#if !defined(__INCLUDE_FROM_SI_DRIVER)
			#error Do not include this file directly. Include LPCUSBlib/Drivers/USB.h instead.
		#endif

	/* Macros: */
		/** Length in bytes of a given Unicode string's character length.
		 *
		 *  @param Chars  Total number of Unicode characters in the string.
		 *
		 *  @return Number of bytes of the given unicode string.
		 */
		#define UNICODE_STRING_LENGTH(Chars)  ((Chars) << 1)

		/** Used in the DataLength field of a PIMA container, to give the total container size in bytes for
		 *  a command container.
		 *
		 *  @param Params  Number of parameters which are to be sent in the \c Param field of the container.
		 */
		#define PIMA_COMMAND_SIZE(Params)     ((sizeof(PIMA_Container_t) - 12) + ((Params) * sizeof(uint32_t)))

		/** Used in the DataLength field of a PIMA container, to give the total container size in bytes for
		 *  a data container.
		 *
		 *  @param DataLen  Length in bytes of the data in the container.
		 */
		#define PIMA_DATA_SIZE(DataLen)       ((sizeof(PIMA_Container_t) - 12) + (DataLen))

	/* Enums: */
		/** Enum for the possible PIMA contains types. */
		enum PIMA_Container_Types_t
		{
			PIMA_CONTAINER_Undefined     = 0, /**< Undefined container type. */
			PIMA_CONTAINER_CommandBlock  = 1, /**< Command Block container type. */
			PIMA_CONTAINER_DataBlock     = 2, /**< Data Block container type. */
			PIMA_CONTAINER_ResponseBlock = 3, /**< Response container type. */
			PIMA_CONTAINER_EventBlock    = 4, /**< Event Block container type. */
		};

	/* Enums: */
		/** Enum for possible Class, Subclass and Protocol values of device and interface descriptors relating to the
		 *  Still Image device class.
		 */
		enum SI_Descriptor_ClassSubclassProtocol_t
		{
			SI_CSCP_StillImageClass             = 0x06, /**< Descriptor Class value indicating that the device or interface
			                                             *   belongs to the Still Image class.
			                                             */
			SI_CSCP_StillImageSubclass          = 0x01, /**< Descriptor Subclass value indicating that the device or interface
			                                             *   belongs to the Still Image subclass.
			                                             */
			SI_CSCP_BulkOnlyProtocol            = 0x01, /**< Descriptor Protocol value indicating that the device or interface
			                                             *   belongs to the Bulk Only Transport protocol of the Still Image class.
			                                             */
		};

		/** Enums for the possible status codes of a returned Response Block from an attached PIMA compliant Still Image device. */
		enum PIMA_ResponseCodes_t
		{
			PIMA_RESPONSE_OK                    = 1, /**< Response code indicating no error in the issued command. */
			PIMA_RESPONSE_GeneralError          = 2, /**< Response code indicating a general error while processing the
			                                             *  issued command.
			                                             */
			PIMA_RESPONSE_SessionNotOpen        = 3, /**< Response code indicating that the sent command requires an open
			                                             *   session before being issued.
			                                             */
			PIMA_RESPONSE_InvalidTransaction    = 4, /**< Response code indicating an invalid transaction occurred. */
			PIMA_RESPONSE_OperationNotSupported = 5, /**< Response code indicating that the issued command is not supported
			                                             *   by the attached device.
			                                             */
			PIMA_RESPONSE_ParameterNotSupported = 6, /**< Response code indicating that one or more of the issued command's
			                                             *   parameters are not supported by the device.
			                                             */
		};

	/* Type Defines: */
		/** @brief PIMA Still Image Device Command/Response Container.
		 *
		 *  Type define for a PIMA container, use to send commands and receive responses to and from an
		 *  attached Still Image device.
		 *
		 *  @note Regardless of CPU architecture, these values should be stored as little endian.
		 */
		typedef struct
		{
			uint32_t DataLength; /**< Length of the container and data, in bytes. */
			uint16_t Type; /**< Container type, a value from the @ref PIMA_Container_Types_t enum. */
			uint16_t Code; /**< Command, event or response code of the container. */
			uint32_t TransactionID; /**< Unique container ID to link blocks together. */
			uint32_t Params[3]; /**< Block parameters to be issued along with the block code (command blocks only). */
		} ATTR_PACKED PIMA_Container_t;

	/* Disable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			}
		#endif

#endif

/** @} */

