/*
 * @brief Common definitions and declarations for the library USB MIDI Class driver
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

/** @ingroup Group_USBClassMIDI
 *  @defgroup Group_USBClassMIDICommon  Common Class Definitions
 *
 *  @section Sec_ModDescription Module Description
 *  Constants, Types and Enum definitions that are common to both Device and Host modes for the USB
 *  MIDI Class.
 *
 *  @{
 */

#ifndef _MIDI_CLASS_COMMON_H_
#define _MIDI_CLASS_COMMON_H_

	/* Macros: */
		#define __INCLUDE_FROM_AUDIO_DRIVER

	/* Includes: */
		#include "../../Core/StdDescriptors.h"
		#include "AudioClassCommon.h"

	/* Enable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			extern "C" {
		#endif

	/* Preprocessor Checks: */
		#if !defined(__INCLUDE_FROM_MIDI_DRIVER)
			#error Do not include this file directly. Include LPCUSBlib/Drivers/USB.h instead.
		#endif

	/* Macros: */
		/** @name MIDI Command Values */
		//@{
		/** MIDI command for a note on (activation) event. */
		#define MIDI_COMMAND_NOTE_ON        0x90

		/** MIDI command for a note off (deactivation) event. */
		#define MIDI_COMMAND_NOTE_OFF       0x80
		//@}

		/** Standard key press velocity value used for all note events. */
		#define MIDI_STANDARD_VELOCITY      64

		/** Convenience macro. MIDI channels are numbered from 1-10 (natural numbers) however the logical channel
		 *  addresses are zero-indexed. This converts a natural MIDI channel number into the logical channel address.
		 *
		 *  @param channel  MIDI channel number to address.
		 */
		#define MIDI_CHANNEL(channel)        ((channel) - 1)

	/* Enums: */
		/** Enum for the possible MIDI jack types in a MIDI device jack descriptor. */
		enum MIDI_JackTypes_t
		{
			MIDI_JACKTYPE_Embedded = 0x01, /**< MIDI class descriptor jack type value for an embedded (logical) MIDI input or output jack. */
			MIDI_JACKTYPE_External = 0x02, /**< MIDI class descriptor jack type value for an external (physical) MIDI input or output jack. */
		};

	/* Type Defines: */
		/** @brief MIDI class-specific Streaming Interface Descriptor (nxpUSBlib naming conventions).
		 *
		 *  Type define for an Audio class-specific MIDI streaming interface descriptor. This indicates to the host
		 *  how MIDI the specification compliance of the device and the total length of the Audio class-specific descriptors.
		 *  See the USB Audio specification for more details.
		 *
		 *  @see @ref USB_MIDI_StdDescriptor_AudioInterface_AS_t for the version of this type with standard element names.
		 *
		 *  @note Regardless of CPU architecture, these values should be stored as little endian.
		 */
		typedef ATTR_IAR_PACKED struct
		{
			USB_Descriptor_Header_t Header; /**< Regular descriptor header containing the descriptor's type and length. */
			uint8_t                 Subtype; /**< Sub type value used to distinguish between audio class-specific descriptors. */

			uint16_t                AudioSpecification; /**< Binary coded decimal value, indicating the supported Audio Class
			                                             *   specification version.
			                                             */
			uint16_t                TotalLength; /**< Total length of the Audio class-specific descriptors, including this descriptor. */
		} ATTR_PACKED USB_MIDI_Descriptor_AudioInterface_AS_t;

		/** @brief MIDI class-specific Streaming Interface Descriptor (USB-IF naming conventions).
		 *
		 *  Type define for an Audio class-specific MIDI streaming interface descriptor. This indicates to the host
		 *  how MIDI the specification compliance of the device and the total length of the Audio class-specific descriptors.
		 *  See the USB Audio specification for more details.
		 *
		 *  @see @ref USB_MIDI_Descriptor_AudioInterface_AS_t for the version of this type with non-standard nxpUSBlib specific
		 *       element names.
		 *
		 *  @note Regardless of CPU architecture, these values should be stored as little endian.
		 */
		typedef ATTR_IAR_PACKED struct
		{
			uint8_t  bLength; /**< Size of the descriptor, in bytes. */
			uint8_t  bDescriptorType; /**< Type of the descriptor, either a value in @ref USB_DescriptorTypes_t or a value
			                           *   given by the specific class.
			                           */

			uint8_t  bDescriptorSubtype; /**< Sub type value used to distinguish between audio class-specific descriptors. */

			uint16_t bcdMSC; /**< Binary coded decimal value, indicating the supported MIDI Class specification version. */
			uint16_t wTotalLength; /**< Total length of the Audio class-specific descriptors, including this descriptor. */
		} ATTR_PACKED USB_MIDI_StdDescriptor_AudioInterface_AS_t;

		/** @brief MIDI class-specific Input Jack Descriptor (nxpUSBlib naming conventions).
		 *
		 *  Type define for an Audio class-specific MIDI IN jack. This gives information to the host on a MIDI input, either
		 *  a physical input jack, or a logical jack (receiving input data internally, or from the host via an endpoint).
		 *
		 *  @see @ref USB_MIDI_StdDescriptor_InputJack_t for the version of this type with standard element names.
		 *
		 *  @note Regardless of CPU architecture, these values should be stored as little endian.
		 */
		typedef ATTR_IAR_PACKED struct
		{
			USB_Descriptor_Header_t Header; /**< Regular descriptor header containing the descriptor's type and length. */
			uint8_t                 Subtype; /**< Sub type value used to distinguish between audio class-specific descriptors. */

			uint8_t                 JackType; /**< Type of jack, one of the \c JACKTYPE_* mask values. */
			uint8_t                 JackID; /**< ID value of this jack - must be a unique value within the device. */

			uint8_t                 JackStrIndex; /**< Index of a string descriptor describing this descriptor within the device. */
		} ATTR_PACKED USB_MIDI_Descriptor_InputJack_t;

		/** @brief MIDI class-specific Input Jack Descriptor (USB-IF naming conventions).
		 *
		 *  Type define for an Audio class-specific MIDI IN jack. This gives information to the host on a MIDI input, either
		 *  a physical input jack, or a logical jack (receiving input data internally, or from the host via an endpoint).
		 *
		 *  @see @ref USB_MIDI_Descriptor_InputJack_t for the version of this type with non-standard nxpUSBlib specific
		 *       element names.
		 *
		 *  @note Regardless of CPU architecture, these values should be stored as little endian.
		 */
		typedef ATTR_IAR_PACKED struct
		{
			uint8_t  bLength; /**< Size of the descriptor, in bytes. */
			uint8_t  bDescriptorType; /**< Type of the descriptor, either a value in @ref USB_DescriptorTypes_t or a value
			                           *   given by the specific class.
			                           */

			uint8_t  bDescriptorSubtype; /**< Sub type value used to distinguish between audio class-specific descriptors. */

			uint8_t  bJackType; /**< Type of jack, one of the \c JACKTYPE_* mask values. */
			uint8_t  bJackID; /**< ID value of this jack - must be a unique value within the device. */

			uint8_t  iJack; /**< Index of a string descriptor describing this descriptor within the device. */
		} ATTR_PACKED USB_MIDI_StdDescriptor_InputJack_t;

		/** @brief MIDI class-specific Output Jack Descriptor (nxpUSBlib naming conventions).
		 *
		 *  Type define for an Audio class-specific MIDI OUT jack. This gives information to the host on a MIDI output, either
		 *  a physical output jack, or a logical jack (sending output data internally, or to the host via an endpoint).
		 *
		 *  @see @ref USB_MIDI_StdDescriptor_OutputJack_t for the version of this type with standard element names.
		 *
		 *  @note Regardless of CPU architecture, these values should be stored as little endian.
		 */
		typedef ATTR_IAR_PACKED struct
		{
			USB_Descriptor_Header_t   Header; /**< Regular descriptor header containing the descriptor's type and length. */
			uint8_t                   Subtype; /**< Sub type value used to distinguish between audio class-specific descriptors. */

			uint8_t                   JackType; /**< Type of jack, one of the \c JACKTYPE_* mask values. */
			uint8_t                   JackID; /**< ID value of this jack - must be a unique value within the device. */

			uint8_t                   NumberOfPins; /**< Number of output channels within the jack, either physical or logical. */
			uint8_t                   SourceJackID[1]; /**< ID of each output pin's source data jack. */
			uint8_t                   SourcePinID[1]; /**< Pin number in the input jack of each output pin's source data. */

			uint8_t                   JackStrIndex; /**< Index of a string descriptor describing this descriptor within the device. */
		} ATTR_PACKED USB_MIDI_Descriptor_OutputJack_t;

		/** @brief MIDI class-specific Output Jack Descriptor (USB-IF naming conventions).
		 *
		 *  Type define for an Audio class-specific MIDI OUT jack. This gives information to the host on a MIDI output, either
		 *  a physical output jack, or a logical jack (sending output data internally, or to the host via an endpoint).
		 *
		 *  @see @ref USB_MIDI_Descriptor_OutputJack_t for the version of this type with non-standard nxpUSBlib specific
		 *       element names.
		 *
		 *  @note Regardless of CPU architecture, these values should be stored as little endian.
		 */
		typedef ATTR_IAR_PACKED struct
		{
			uint8_t  bLength; /**< Size of the descriptor, in bytes. */
			uint8_t  bDescriptorType; /**< Type of the descriptor, either a value in @ref USB_DescriptorTypes_t or a value
			                           *   given by the specific class.
			                           */

			uint8_t  bDescriptorSubtype; /**< Sub type value used to distinguish between audio class-specific descriptors. */

			uint8_t  bJackType; /**< Type of jack, one of the \c JACKTYPE_* mask values. */
			uint8_t  bJackID; /**< ID value of this jack - must be a unique value within the device. */

			uint8_t  bNrInputPins; /**< Number of output channels within the jack, either physical or logical. */
			uint8_t  baSourceID[1]; /**< ID of each output pin's source data jack. */
			uint8_t  baSourcePin[1]; /**< Pin number in the input jack of each output pin's source data. */

			uint8_t  iJack; /**< Index of a string descriptor describing this descriptor within the device. */
		} ATTR_PACKED USB_MIDI_StdDescriptor_OutputJack_t;

		/** @brief Audio class-specific Jack Endpoint Descriptor (nxpUSBlib naming conventions).
		 *
		 *  Type define for an Audio class-specific extended MIDI jack endpoint descriptor. This contains extra information
		 *  on the usage of MIDI endpoints used to stream MIDI events in and out of the USB Audio device, and follows an Audio
		 *  class-specific extended MIDI endpoint descriptor. See the USB Audio specification for more details.
		 *
		 *  @see @ref USB_MIDI_StdDescriptor_Jack_Endpoint_t for the version of this type with standard element names.
		 *
		 *  @note Regardless of CPU architecture, these values should be stored as little endian.
		 */
		typedef ATTR_IAR_PACKED struct
		{
			USB_Descriptor_Header_t   Header; /**< Regular descriptor header containing the descriptor's type and length. */
			uint8_t                   Subtype; /**< Sub type value used to distinguish between audio class-specific descriptors. */

			uint8_t                   TotalEmbeddedJacks; /**< Total number of jacks inside this endpoint. */
			uint8_t                   AssociatedJackID[1]; /**< IDs of each jack inside the endpoint. */
		} ATTR_PACKED USB_MIDI_Descriptor_Jack_Endpoint_t;

		/** @brief Audio class-specific Jack Endpoint Descriptor (USB-IF naming conventions).
		 *
		 *  Type define for an Audio class-specific extended MIDI jack endpoint descriptor. This contains extra information
		 *  on the usage of MIDI endpoints used to stream MIDI events in and out of the USB Audio device, and follows an Audio
		 *  class-specific extended MIDI endpoint descriptor. See the USB Audio specification for more details.
		 *
		 *  @see @ref USB_MIDI_Descriptor_Jack_Endpoint_t for the version of this type with non-standard nxpUSBlib specific
		 *       element names.
		 *
		 *  @note Regardless of CPU architecture, these values should be stored as little endian.
		 */
		typedef ATTR_IAR_PACKED struct
		{
			uint8_t  bLength; /**< Size of the descriptor, in bytes. */
			uint8_t  bDescriptorType; /**< Type of the descriptor, either a value in @ref USB_DescriptorTypes_t or a value
			                           *   given by the specific class.
			                           */

			uint8_t  bDescriptorSubtype; /**< Sub type value used to distinguish between audio class-specific descriptors. */

			uint8_t  bNumEmbMIDIJack; /**< Total number of jacks inside this endpoint. */
			uint8_t  bAssocJackID[1]; /**< IDs of each jack inside the endpoint. */
		} ATTR_PACKED USB_MIDI_StdDescriptor_Jack_Endpoint_t;

		/** @brief MIDI Class Driver Event Packet.
		 *
		 *  Type define for a USB MIDI event packet, used to encapsulate sent and received MIDI messages from a USB MIDI interface.
		 *
		 *  @note Regardless of CPU architecture, these values should be stored as little endian.
		 */
		typedef ATTR_IAR_PACKED struct
		{
			unsigned Command     : 4; /**< Upper nibble of the MIDI command being sent or received in the event packet. */
			unsigned CableNumber : 4; /**< Virtual cable number of the event being sent or received in the given MIDI interface. */

			uint8_t  Data1; /**< First byte of data in the MIDI event. */
			uint8_t  Data2; /**< Second byte of data in the MIDI event. */
			uint8_t  Data3; /**< Third byte of data in the MIDI event. */
		} ATTR_PACKED MIDI_EventPacket_t;

	/* Disable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			}
		#endif

#endif

/** @} */

