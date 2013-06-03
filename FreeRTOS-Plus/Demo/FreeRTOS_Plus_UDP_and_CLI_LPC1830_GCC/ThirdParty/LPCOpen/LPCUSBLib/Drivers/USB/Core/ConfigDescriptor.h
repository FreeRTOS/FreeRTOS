/*
 * @brief USB Configuration Descriptor definitions
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
 *  @defgroup Group_ConfigDescriptorParser Configuration Descriptor Parser
 *  @brief USB Configuration Descriptor definitions.
 *
 *  This section of the library gives a friendly API which can be used in host applications to easily
 *  parse an attached device's configuration descriptor so that endpoint, interface and other descriptor
 *  data can be extracted and used as needed.
 *
 *  @{
 */

#ifndef __CONFIGDESCRIPTOR_H__
#define __CONFIGDESCRIPTOR_H__

	/* Includes: */
		#include "../../../Common/Common.h"
		#include "USBMode.h"		
		#include "HostStandardReq.h"
		#include "StdDescriptors.h"

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
			/** Casts a pointer to a descriptor inside the configuration descriptor into a pointer to the given
			 *  descriptor type.
			 *
			 *  Usage Example:
			 *  \code
			 *  uint8_t* CurrDescriptor = &ConfigDescriptor[0]; // Pointing to the configuration header
			 *  USB_Descriptor_Configuration_Header_t* ConfigHeaderPtr = DESCRIPTOR_PCAST(CurrDescriptor,
			 *                                                           USB_Descriptor_Configuration_Header_t);
			 *
			 *  // Can now access elements of the configuration header struct using the -> indirection operator
			 *  \endcode
			 */
			#define DESCRIPTOR_PCAST(DescriptorPtr, Type) ((Type*)(DescriptorPtr))

			/** Casts a pointer to a descriptor inside the configuration descriptor into the given descriptor
			 *  type (as an actual struct instance rather than a pointer to a struct).
			 *
			 *  Usage Example:
			 *  \code
			 *  uint8_t* CurrDescriptor = &ConfigDescriptor[0]; // Pointing to the configuration header
			 *  USB_Descriptor_Configuration_Header_t ConfigHeader = DESCRIPTOR_CAST(CurrDescriptor,
			 *                                                       USB_Descriptor_Configuration_Header_t);
			 *
			 *  // Can now access elements of the configuration header struct using the . operator
			 *  \endcode
			 */
			#define DESCRIPTOR_CAST(DescriptorPtr, Type)  (*DESCRIPTOR_PCAST(DescriptorPtr, Type))

			/** Returns the descriptor's type, expressed as the 8-bit type value in the header of the descriptor.
			 *  This value's meaning depends on the descriptor's placement in the descriptor, but standard type
			 *  values can be accessed in the @ref USB_DescriptorTypes_t enum.
			 */
			#define DESCRIPTOR_TYPE(DescriptorPtr)    DESCRIPTOR_PCAST(DescriptorPtr, USB_Descriptor_Header_t)->Type

			/** Returns the descriptor's size, expressed as the 8-bit value indicating the number of bytes. */
			#define DESCRIPTOR_SIZE(DescriptorPtr)    DESCRIPTOR_PCAST(DescriptorPtr, USB_Descriptor_Header_t)->Size

		/* Type Defines: */
			/** Type define for a Configuration Descriptor comparator function (function taking a pointer to an array
			 *  of type void, returning a uint8_t value).
			 *
			 *  \see @ref USB_GetNextDescriptorComp function for more details.
			 */
			typedef uint8_t (* ConfigComparatorPtr_t)(void*);

		/* Enums: */
			/** Enum for the possible return codes of the @ref USB_Host_GetDeviceConfigDescriptor() function. */
			enum USB_Host_GetConfigDescriptor_ErrorCodes_t
			{
				HOST_GETCONFIG_Successful       = 0, /**< No error occurred while retrieving the configuration descriptor. */
				HOST_GETCONFIG_DeviceDisconnect = 1, /**< The attached device was disconnected while retrieving the configuration
				                                        * descriptor.
				                                        */
				HOST_GETCONFIG_PipeError        = 2, /**< An error occurred in the pipe while sending the request. */
				HOST_GETCONFIG_SetupStalled     = 3, /**< The attached device stalled the request to retrieve the configuration
				                                        * descriptor.
				                                        */
				HOST_GETCONFIG_SoftwareTimeOut  = 4, /**< The request or data transfer timed out. */
				HOST_GETCONFIG_BuffOverflow     = 5, /**< The device's configuration descriptor is too large to fit into the allocated
				                                        * buffer.
				                                        */
				HOST_GETCONFIG_InvalidData      = 6, /**< The device returned invalid configuration descriptor data. */
			};

			/** Enum for return values of a descriptor comparator function. */
			enum DSearch_Return_ErrorCodes_t
			{
				DESCRIPTOR_SEARCH_Found                = 0, /**< Current descriptor matches comparator criteria. */
				DESCRIPTOR_SEARCH_Fail                 = 1, /**< No further descriptor could possibly match criteria, fail the search. */
				DESCRIPTOR_SEARCH_NotFound             = 2, /**< Current descriptor does not match comparator criteria. */
			};

			/** Enum for return values of @ref USB_GetNextDescriptorComp(). */
			enum DSearch_Comp_Return_ErrorCodes_t
			{
				DESCRIPTOR_SEARCH_COMP_Found           = 0, /**< Configuration descriptor now points to descriptor which matches
				                                             *   search criteria of the given comparator function. */
				DESCRIPTOR_SEARCH_COMP_Fail            = 1, /**< Comparator function returned @ref DESCRIPTOR_SEARCH_Fail. */
				DESCRIPTOR_SEARCH_COMP_EndOfDescriptor = 2, /**< End of configuration descriptor reached before match found. */
			};

		/* Function Prototypes: */
			/** @brief	Retrieves the configuration descriptor data from an attached device via a standard request into a buffer,
			 *  		including validity and size checking to prevent a buffer overflow.
			 *
			 *  @param  	corenum		: USB port number
			 *  @param  ConfigNumber	: Device configuration descriptor number to fetch from the device (usually set to 1 for
			 *                                single configuration devices).
			 *  @param 	ConfigSizePtr  	: Pointer to a location for storing the retrieved configuration descriptor size.
			 *  @param  BufferPtr      	: Pointer to the buffer for storing the configuration descriptor data.
			 *  @param  BufferSize     	: Size of the allocated buffer where the configuration descriptor is to be stored.
			 *
			 *  @return A value from the @ref USB_Host_GetConfigDescriptor_ErrorCodes_t enum.
			 */
			uint8_t USB_Host_GetDeviceConfigDescriptor(const uint8_t corenum,
													   const uint8_t ConfigNumber,
			                                           uint16_t* const ConfigSizePtr,
			                                           void* const BufferPtr,
			                                           const uint16_t BufferSize) ATTR_NON_NULL_PTR_ARG(3) ATTR_NON_NULL_PTR_ARG(4);

			/** @brief	Skips to the next sub-descriptor inside the configuration descriptor of the specified type value.
			 *  		The bytes remaining value is automatically decremented.
			 *
			 * 	@param	BytesRem		: Pointer to the number of bytes remaining of the configuration descriptor.
			 *  @param	CurrConfigLoc  	: Pointer to the current descriptor inside the configuration descriptor.
			 * 	@param	Type           	: Descriptor type value to search for.
			 *	@return	Nothing
			 */
			void USB_GetNextDescriptorOfType(uint16_t* const BytesRem,
			                                 void** const CurrConfigLoc,
			                                 const uint8_t Type)
			                                 ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(2);

			/** @brief	Skips to the next sub-descriptor inside the configuration descriptor of the specified type value,
			 *  		which must come before a descriptor of the second given type value. If the BeforeType type
			 *  		descriptor is reached first, the number of bytes remaining to process is set to zero and the
			 *  		function exits. The bytes remaining value is automatically decremented.
			 *
			 * @param	BytesRem		: Pointer to the number of bytes remaining of the configuration descriptor.
			 * @param	CurrConfigLoc  	: Pointer to the current descriptor inside the configuration descriptor.
			 * @param	Type           	: Descriptor type value to search for.
			 * @param	BeforeType     	: Descriptor type value which must not be reached before the given Type descriptor.
			 * @return	Nothing
			 */
			void USB_GetNextDescriptorOfTypeBefore(uint16_t* const BytesRem,
			                                       void** const CurrConfigLoc,
			                                       const uint8_t Type,
			                                       const uint8_t BeforeType)
			                                       ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(2);

			/** @brief	Skips to the next sub-descriptor inside the configuration descriptor of the specified type value,
			 *  		which must come after a descriptor of the second given type value. The bytes remaining value is
			 *  		automatically decremented.
			 *
			 * @param	BytesRem		: Pointer to the number of bytes remaining of the configuration descriptor.
			 * @param	CurrConfigLoc  	: Pointer to the current descriptor inside the configuration descriptor.
			 * @param	Type           	: Descriptor type value to search for.
			 * @param	AfterType      	: Descriptor type value which must be reached before the given Type descriptor.
			 * @return 	Nothing
			 */
			void USB_GetNextDescriptorOfTypeAfter(uint16_t* const BytesRem,
			                                      void** const CurrConfigLoc,
			                                      const uint8_t Type,
			                                      const uint8_t AfterType)
			                                      ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(2);

			/** @brief	Searches for the next descriptor in the given configuration descriptor using a pre-made comparator
			 *  		function. The routine updates the position and remaining configuration descriptor bytes values
			 *  		automatically. If a comparator routine fails a search, the descriptor pointer is retreated back
			 *  		so that the next descriptor search invocation will start from the descriptor which first caused the
			 *  		original search to fail. This behaviour allows for one comparator to be used immediately after another
			 *  		has failed, starting the second search from the descriptor which failed the first.
			 *
			 *  		Comparator functions should be standard functions which accept a pointer to the header of the current
			 *  		descriptor inside the configuration descriptor which is being compared, and should return a value from
			 *  		the @ref DSearch_Return_ErrorCodes_t enum as a uint8_t value.
			 *
			 *  @note This function is available in USB Host mode only.
			 *
			 *  @param	BytesRem			: Pointer to an int storing the remaining bytes in the configuration descriptor.
			 *  @param	CurrConfigLoc		: Pointer to the current position in the configuration descriptor.
			 *  @param	ComparatorRoutine  	: Name of the comparator search function to use on the configuration descriptor.
			 *
			 *  @return Value of one of the members of the @ref DSearch_Comp_Return_ErrorCodes_t enum.
			 *
			 *  Usage Example:
			 *  \code
			 *  uint8_t EndpointSearcher(void* CurrentDescriptor); // Comparator Prototype
			 *
			 *  uint8_t EndpointSearcher(void* CurrentDescriptor)
			 *  {
			 *     if (DESCRIPTOR_TYPE(CurrentDescriptor) == DTYPE_Endpoint)
			 *         return DESCRIPTOR_SEARCH_Found;
			 *     else
			 *         return DESCRIPTOR_SEARCH_NotFound;
			 *  }
			 *
			 *  //...
			 *  // After retrieving configuration descriptor:
			 *  if (USB_Host_GetNextDescriptorComp(&BytesRemaining, &CurrentConfigLoc, EndpointSearcher) ==
			 *      Descriptor_Search_Comp_Found)
			 *  {
			 *      // Do something with the endpoint descriptor
			 *  }
			 *  \endcode
			 */
			uint8_t USB_GetNextDescriptorComp(uint16_t* const BytesRem,
			                                  void** const CurrConfigLoc,
			                                  ConfigComparatorPtr_t const ComparatorRoutine);

		/* Inline Functions: */
			/** @brief	Skips over the current sub-descriptor inside the configuration descriptor, so that the pointer then
						points to the next sub-descriptor. The bytes remaining value is automatically decremented.
			 *
			 * @param	BytesRem		: Pointer to the number of bytes remaining of the configuration descriptor.
			 * @param	CurrConfigLoc  	: Pointer to the current descriptor inside the configuration descriptor.
			 */
			static inline void USB_GetNextDescriptor(uint16_t* const BytesRem,
			                                         void** CurrConfigLoc) ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(2);
			static inline void USB_GetNextDescriptor(uint16_t* const BytesRem,
			                                         void** CurrConfigLoc)
			{
				uint16_t CurrDescriptorSize = DESCRIPTOR_CAST(*CurrConfigLoc, USB_Descriptor_Header_t).Size;
				
				if (*BytesRem < CurrDescriptorSize)
				  CurrDescriptorSize = *BytesRem;

				*CurrConfigLoc  = (void*)((uintptr_t)*CurrConfigLoc + CurrDescriptorSize);
				*BytesRem      -= CurrDescriptorSize;
			}

	/* Disable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			}
		#endif

#endif

/** @} */

