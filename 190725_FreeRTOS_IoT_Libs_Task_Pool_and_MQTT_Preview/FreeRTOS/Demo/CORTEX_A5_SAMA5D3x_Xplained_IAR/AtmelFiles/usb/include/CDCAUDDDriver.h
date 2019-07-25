/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2010, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 * \file
 *
 * \section Purpose
 *
 *   Definitions and methods for USB composite device implement.
 * 
 */

#ifndef CDCAUDDDRIVER_H
#define CDCAUDDDRIVER_H
/** \addtogroup usbd_composite_cdcaud
 *@{
 */

/*---------------------------------------------------------------------------
 *         Headers
 *---------------------------------------------------------------------------*/

#include <USBRequests.h>
#include <CDCDescriptors.h>
#include <AUDDescriptors.h>
#include "USBD.h"
#include <USBDDriver.h>

/*---------------------------------------------------------------------------
 *         Definitions
 *---------------------------------------------------------------------------*/

/** \addtogroup usbd_cdc_aud_desc USB CDC(Serial) + AUD(Speaker) Definitions
 *      @{
 */
/** Number of interfaces of the device (5, can be 4 if no mic support */
#define CDCAUDDDriverDescriptors_MaxNumInterfaces   5
/** Number of the CDC interface. */
#define CDCAUDDDriverDescriptors_CDC_INTERFACE      0
/** Number of the Audio interface. */
#define CDCAUDDDriverDescriptors_AUD_INTERFACE      2
/** Number of Audio function channels (M,L,R) */
#define AUDD_NumChannels                            3
/**     @}*/

/*---------------------------------------------------------------------------
 *         Types
 *---------------------------------------------------------------------------*/
#pragma pack(1)
#if defined   ( __CC_ARM   ) /* Keil ¦ÌVision 4 */
#elif defined ( __ICCARM__ ) /* IAR Ewarm */
#define __attribute__(...)
#define __packed__  packed
#elif defined (  __GNUC__  ) /* GCC CS3 */
#define __packed__  aligned(1)
#endif

/** Audio header descriptor with 1 interface */
typedef struct _AUDHeaderDescriptor1{

    /** Header descriptor.*/
    AUDHeaderDescriptor header;
    /** Id of the first grouped interface.*/
    uint8_t bInterface0;

} __attribute__ ((__packed__)) AUDHeaderDescriptor1;

/** Audio header descriptor with 2 interface */
typedef struct _AUDHeaderDescriptor2 {

    /** Header descriptor. */
    AUDHeaderDescriptor header;
    /** Id of the first grouped interface - Speaker. */
    uint8_t bInterface0;
    /** Id of the second grouped interface - Speakerphone. */
    uint8_t bInterface1;

} __attribute__ ((__packed__)) AUDHeaderDescriptor2; /* GCC */

/**
 * Feature unit descriptor with 3 channel controls (master, right, left).
 */
typedef struct _AUDFeatureUnitDescriptor3{

    /** Feature unit descriptor.*/
    AUDFeatureUnitDescriptor feature;
    /** Available controls for each channel.*/
    uint8_t bmaControls[AUDD_NumChannels];
    /** Index of a string descriptor for the feature unit.*/
    uint8_t iFeature;

} __attribute__ ((__packed__)) AUDFeatureUnitDescriptor3;

/**
 * List of descriptors for detailling the audio control interface of a
 * device using a USB audio speaker function.
 */
typedef struct _AUDDSpeakerAcDescriptors{

    /** Header descriptor (with one slave interface).*/
    AUDHeaderDescriptor1 header;
    /** Input terminal descriptor.*/
    AUDInputTerminalDescriptor input;
    /** Output terminal descriptor.*/
    AUDOutputTerminalDescriptor output;
    /** Feature unit descriptor.*/
    AUDFeatureUnitDescriptor3 feature;

} __attribute__ ((__packed__)) AUDDSpeakerAcDescriptors;

/**
 * List of descriptors for detailling the audio control interface of a
 * device using a USB Audio Speakerphoneer function.
 */
typedef struct _AUDDSpeakerPhoneAcDescriptors {

    /** Header descriptor (with one slave interface). */
    AUDHeaderDescriptor2 header;
    /** Input terminal descriptor. */
    AUDInputTerminalDescriptor inputSpeakerPhone;
    /** Output terminal descriptor. */
    AUDOutputTerminalDescriptor outputSpeakerPhone;
    /** Feature unit descriptor - SpeakerPhone. */
    AUDFeatureUnitDescriptor3 featureSpeakerPhone;
    /** Input terminal descriptor. */
    AUDInputTerminalDescriptor inputRec;
    /** Output terminal descriptor. */
    AUDOutputTerminalDescriptor outputRec;
    /** Feature unit descriptor - SpeakerPhonephone. */
    AUDFeatureUnitDescriptor3 featureRec;

} __attribute__ ((__packed__)) AUDDSpeakerPhoneAcDescriptors;

/**
 * Format type I descriptor with one discrete sampling frequency.
 */
typedef struct _AUDFormatTypeOneDescriptor1{

    /** Format type I descriptor.*/
    AUDFormatTypeOneDescriptor formatType;
    /** Sampling frequency in Hz.*/
    uint8_t tSamFreq[3];

} __attribute__ ((__packed__)) AUDFormatTypeOneDescriptor1;

/**
 * Configuration descriptor list for a device implementing
 * CDC(Serial) + Audio(Speaker) composite driver.
 */
typedef struct _CdcAudspkdDriverConfigurationDescriptors {

    /** Standard configuration descriptor. */
    USBConfigurationDescriptor configuration;

    /* --- CDC 0 */
    /** IAD 0 */
    USBInterfaceAssociationDescriptor cdcIAD0;
    /** Communication interface descriptor */
    USBInterfaceDescriptor cdcCommunication0;
    /** CDC header functional descriptor. */
    CDCHeaderDescriptor cdcHeader0;
    /** CDC call management functional descriptor. */
    CDCCallManagementDescriptor cdcCallManagement0;
    /** CDC abstract control management functional descriptor. */
    CDCAbstractControlManagementDescriptor cdcAbstractControlManagement0;
    /** CDC union functional descriptor (with one slave interface). */
    CDCUnionDescriptor cdcUnion0;
    /** Notification endpoint descriptor. */
    USBEndpointDescriptor cdcNotification0;
    /** Data interface descriptor. */
    USBInterfaceDescriptor cdcData0;
    /** Data OUT endpoint descriptor. */
    USBEndpointDescriptor cdcDataOut0;
    /** Data IN endpoint descriptor. */
    USBEndpointDescriptor cdcDataIn0;

    /* --- AUDIO (AC) */
    /** IAD 1*/
    USBInterfaceAssociationDescriptor audIAD;
    /** Audio control interface.*/
    USBInterfaceDescriptor audInterface;
    /** Descriptors for the audio control interface.*/
    AUDDSpeakerAcDescriptors audControl;
    /* -- AUDIO out (AS) */
    /** Streaming out interface descriptor (with no endpoint, required).*/
    USBInterfaceDescriptor audStreamingOutNoIsochronous;
    /** Streaming out interface descriptor.*/
    USBInterfaceDescriptor audStreamingOut;
    /** Audio class descriptor for the streaming out interface.*/
    AUDStreamingInterfaceDescriptor audStreamingOutClass;
    /** Stream format descriptor.*/
    AUDFormatTypeOneDescriptor1 audStreamingOutFormatType;
    /** Streaming out endpoint descriptor.*/
    AUDEndpointDescriptor audStreamingOutEndpoint;
    /** Audio class descriptor for the streaming out endpoint.*/
    AUDDataEndpointDescriptor audStreamingOutDataEndpoint;

} __attribute__ ((__packed__)) CdcAudspkdDriverConfigurationDescriptors;

/**
 * Configuration descriptor list for a device implementing
 * CDC(Serial) + Audio(SpeakerPhone) composite driver.
 */
typedef struct _CdcAuddDriverConfigurationDescriptors {

    /** Standard configuration descriptor. */
    USBConfigurationDescriptor configuration;

    /* --- CDC 0 */
    /** IAD 0 */
    USBInterfaceAssociationDescriptor cdcIAD0;
    /** Communication interface descriptor */
    USBInterfaceDescriptor cdcCommunication0;
    /** CDC header functional descriptor. */
    CDCHeaderDescriptor cdcHeader0;
    /** CDC call management functional descriptor. */
    CDCCallManagementDescriptor cdcCallManagement0;
    /** CDC abstract control management functional descriptor. */
    CDCAbstractControlManagementDescriptor cdcAbstractControlManagement0;
    /** CDC union functional descriptor (with one slave interface). */
    CDCUnionDescriptor cdcUnion0;
    /** Notification endpoint descriptor. */
    USBEndpointDescriptor cdcNotification0;
    /** Data interface descriptor. */
    USBInterfaceDescriptor cdcData0;
    /** Data OUT endpoint descriptor. */
    USBEndpointDescriptor cdcDataOut0;
    /** Data IN endpoint descriptor. */
    USBEndpointDescriptor cdcDataIn0;

    /* --- AUDIO (AC) */
    /** IAD 1*/
    USBInterfaceAssociationDescriptor audIAD;
    /** Audio control interface.*/
    USBInterfaceDescriptor audInterface;
    /** Descriptors for the audio control interface.*/
    AUDDSpeakerPhoneAcDescriptors audControl;
    /* -- AUDIO out (AS) */
    /** Streaming out interface descriptor (with no endpoint, required).*/
    USBInterfaceDescriptor audStreamingOutNoIsochronous;
    /** Streaming out interface descriptor.*/
    USBInterfaceDescriptor audStreamingOut;
    /** Audio class descriptor for the streaming out interface.*/
    AUDStreamingInterfaceDescriptor audStreamingOutClass;
    /** Stream format descriptor.*/
    AUDFormatTypeOneDescriptor1 audStreamingOutFormatType;
    /** Streaming out endpoint descriptor.*/
    AUDEndpointDescriptor audStreamingOutEndpoint;
    /** Audio class descriptor for the streaming out endpoint.*/
    AUDDataEndpointDescriptor audStreamingOutDataEndpoint;
    /*- AUDIO IN */
    /** Streaming in interface descriptor (with no endpoint, required). */
    USBInterfaceDescriptor streamingInNoIsochronous;
    /** Streaming in interface descriptor. */
    USBInterfaceDescriptor streamingIn;
    /** Audio class descriptor for the streaming in interface. */
    AUDStreamingInterfaceDescriptor streamingInClass;
    /** Stream format descriptor. */
    AUDFormatTypeOneDescriptor1 streamingInFormatType;
    /** Streaming in endpoint descriptor. */
    AUDEndpointDescriptor streamingInEndpoint;
    /** Audio class descriptor for the streaming in endpoint. */
    AUDDataEndpointDescriptor streamingInDataEndpoint;

} __attribute__ ((__packed__)) CdcAuddDriverConfigurationDescriptors;

#pragma pack()

/*---------------------------------------------------------------------------
 *         Exported functions
 *---------------------------------------------------------------------------*/

extern void CDCAUDDDriver_Initialize(const USBDDriverDescriptors * pDescriptors);
extern void CDCAUDDDriver_ConfigurationChangedHandler(uint8_t cfgnum);
extern void CDCAUDDDriver_InterfaceSettingChangedHandler(
    uint8_t interface, uint8_t setting);
extern void CDCAUDDDriver_RequestHandler(const USBGenericRequest *request);

/**@}*/
#endif //#ifndef CDCHIDDDRIVER_H

