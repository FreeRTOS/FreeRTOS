/*
 * @brief Device mode driver for the library USB MIDI Class driver
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
 *  @defgroup Group_USBClassMIDIDevice MIDI Class Device Mode Driver
 *
 *  @section Sec_Dependencies Module Source Dependencies
 *  The following files must be built with any user project that uses this module:
 *    - nxpUSBlib/Drivers/USB/Class/Device/MIDI.c <i>(Makefile source module name: NXPUSBLIB_SRC_USBCLASS)</i>
 *
 *  @section Sec_ModDescription Module Description
 *  Device Mode USB Class driver framework interface, for the MIDI USB Class driver.
 *
 * @{
 */

#ifndef _MIDI_CLASS_DEVICE_H_
#define _MIDI_CLASS_DEVICE_H_

/* Includes: */
		#include "../../USB.h"
		#include "../Common/MIDIClassCommon.h"

/* Enable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
extern "C" {
		#endif

/* Preprocessor Checks: */
		#if !defined(__INCLUDE_FROM_MIDI_DRIVER)
			#error Do not include this file directly. Include LPCUSBlib/Drivers/USB.h instead.
		#endif

/* Public Interface - May be used in end-application: */
/* Type Define: */
/**
 * @brief MIDI Class Device Mode Configuration and State Structure.
 *
 *  Class state structure. An instance of this structure should be made for each MIDI interface
 *  within the user application, and passed to each of the MIDI class driver functions as the
 *  \c MIDIInterfaceInfo parameter. This stores each MIDI interface's configuration and state information.
 */
typedef struct {
	const struct {
		uint8_t  StreamingInterfaceNumber;				/**< Index of the Audio Streaming interface within the device this structure controls. */

		uint8_t  DataINEndpointNumber;				/**< Endpoint number of the incoming MIDI IN data, if available (zero if unused). */
		uint16_t DataINEndpointSize;			/**< Size in bytes of the incoming MIDI IN data endpoint, if available (zero if unused). */
		bool     DataINEndpointDoubleBank;				/**< Indicates if the MIDI interface's IN data endpoint should use double banking. */

		uint8_t  DataOUTEndpointNumber;				/**< Endpoint number of the outgoing MIDI OUT data, if available (zero if unused). */
		uint16_t DataOUTEndpointSize;				/**< Size in bytes of the outgoing MIDI OUT data endpoint, if available (zero if unused). */
		bool     DataOUTEndpointDoubleBank;				/**< Indicates if the MIDI interface's OUT data endpoint should use double banking. */
		uint8_t  PortNumber;				/**< Port number that this interface is running.*/
	} Config;				/**< Config data for the USB class interface within the device. All elements in this section
							 *   <b>must</b> be set or the interface will fail to enumerate and operate correctly.
							 */

#if 0
	struct {
		// No state information for this class
	} State;			/**< State data for the USB class interface within the device. All elements in this section
						 *   are reset to their defaults when the interface is enumerated.
						 */

#endif
} USB_ClassInfo_MIDI_Device_t;

/* Function Prototypes: */
/**
 * @brief	Configures the endpoints of a given MIDI interface, ready for use. This should be linked to the library
 *  @ref EVENT_USB_Device_ConfigurationChanged() event so that the endpoints are configured when the configuration
 *  containing the given MIDI interface is selected.
 *
 * @param	MIDIInterfaceInfo	: Pointer to a structure containing a MIDI Class configuration and state.
 *
 * @return	Boolean \c true if the endpoints were successfully configured, \c false otherwise.
 */
bool MIDI_Device_ConfigureEndpoints(USB_ClassInfo_MIDI_Device_t *const MIDIInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1);

/**
 * @brief	General management task for a given MIDI class interface, required for the correct operation of the interface. This should
 *  be called frequently in the main program loop, before the master USB management task @ref USB_USBTask().
 *
 * @param	MIDIInterfaceInfo	: Pointer to a structure containing a MIDI Class configuration and state.
  * @return	Nothing
 */
void MIDI_Device_USBTask(USB_ClassInfo_MIDI_Device_t *const MIDIInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1);

/**
 * @brief	Sends a MIDI event packet to the host. If no host is connected, the event packet is discarded. Events are queued into the
 *  endpoint bank until either the endpoint bank is full, or @ref MIDI_Device_Flush() is called. This allows for multiple
 *  MIDI events to be packed into a single endpoint packet, increasing data throughput.
 *
 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
 *       call will fail.
 *
 * @param	MIDIInterfaceInfo	: Pointer to a structure containing a MIDI Class configuration and state.
 * @param	Event	: Pointer to a populated @ref MIDI_EventPacket_t structure containing the MIDI event to send.
 *
 * @return	A value from the @ref Endpoint_Stream_RW_ErrorCodes_t enum.
 */
uint8_t MIDI_Device_SendEventPacket(USB_ClassInfo_MIDI_Device_t *const MIDIInterfaceInfo,
									const MIDI_EventPacket_t *const Event) ATTR_NON_NULL_PTR_ARG(1)
ATTR_NON_NULL_PTR_ARG(2);

/**
 * @brief	Flushes the MIDI send buffer, sending any queued MIDI events to the host. This should be called to override the
 *  @ref MIDI_Device_SendEventPacket() function's packing behaviour, to flush queued events.
 *
 * @param	MIDIInterfaceInfo	: Pointer to a structure containing a MIDI Class configuration and state.
 *
 * @return	A value from the @ref Endpoint_WaitUntilReady_ErrorCodes_t enum.
 */
uint8_t MIDI_Device_Flush(USB_ClassInfo_MIDI_Device_t *const MIDIInterfaceInfo) ATTR_NON_NULL_PTR_ARG(1);

/**
 * @brief	Receives a MIDI event packet from the host. Events are unpacked from the endpoint, thus if the endpoint bank contains
 *  multiple MIDI events from the host in the one packet, multiple calls to this function will return each individual event.
 *
 *  @pre This function must only be called when the Host state machine is in the @ref HOST_STATE_Configured state or the
 *       call will fail.
 *
 * @param	MIDIInterfaceInfo	: Pointer to a structure containing a MIDI Class configuration and state.
 * @param	Event	: Pointer to a USB_MIDI_EventPacket_t structure where the received MIDI event is to be placed.
 *
 * @return	Boolean \c true if a MIDI event packet was received, \c false otherwise.
 */
bool MIDI_Device_ReceiveEventPacket(USB_ClassInfo_MIDI_Device_t *const MIDIInterfaceInfo,
									MIDI_EventPacket_t *const Event) ATTR_NON_NULL_PTR_ARG(1) ATTR_NON_NULL_PTR_ARG(2);

/* Inline Functions: */
/**
 * @brief	Processes incoming control requests from the host, that are directed to the given MIDI class interface. This should be
 *  linked to the library @ref EVENT_USB_Device_ControlRequest() event.
 *
 * @param	MIDIInterfaceInfo	: Pointer to a structure containing a MIDI Class configuration and state.
 */
static inline void MIDI_Device_ProcessControlRequest(USB_ClassInfo_MIDI_Device_t *const MIDIInterfaceInfo)
ATTR_NON_NULL_PTR_ARG(1);

static inline void MIDI_Device_ProcessControlRequest(USB_ClassInfo_MIDI_Device_t *const MIDIInterfaceInfo)
{
	(void) MIDIInterfaceInfo;
}

/* Disable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
}
		#endif

#endif

/** @} */

