/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
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
 *    USB Device Driver class definition.
 *
 * \section Usage
 *
 *    -# Instanciate a USBDDriver object and initialize it using
 *       USBDDriver_Initialize.
 *    -# When a USB SETUP request is received, forward it to the standard
 *       driver using USBDDriver_RequestHandler.
 *    -# Check the Remote Wakeup setting via USBDDriver_IsRemoteWakeUpEnabled.
 */

#ifndef USBDDRIVER_H
#define USBDDRIVER_H

/** \addtogroup usbd_interface
 *@{
 */

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

/* These headers were introduced in C99 by working group
 * ISO/IEC JTC1/SC22/WG14.
 */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

#include <USBRequests.h>
#include <USBDescriptors.h>
#include <USBLib_Types.h>

/*------------------------------------------------------------------------------
 *         Types
 *------------------------------------------------------------------------------*/

/**
 * \typedef USBDDriverDescriptors
 * \brief List of all descriptors used by a USB device driver. Each descriptor
 *        can be provided in two versions: full-speed and high-speed. Devices
 *        which are not high-speed capable do not need to provided high-speed
 *        descriptors and the full-speed qualifier & other speed descriptors.
 */
typedef struct _USBDDriverDescriptors {

    /** Pointer to the full-speed device descriptor */
    const USBDeviceDescriptor *pFsDevice;
    /** Pointer to the full-speed configuration descriptor */
    const USBConfigurationDescriptor *pFsConfiguration;
    /** Pointer to the full-speed qualifier descriptor */
    const USBDeviceQualifierDescriptor *pFsQualifier;
    /** Pointer to the full-speed other speed configuration descriptor */
    const USBConfigurationDescriptor *pFsOtherSpeed;
    /** Pointer to the high-speed device descriptor */
    const USBDeviceDescriptor *pHsDevice;
    /** Pointer to the high-speed configuration descriptor */
    const USBConfigurationDescriptor *pHsConfiguration;
    /** Pointer to the high-speed qualifier descriptor */
    const USBDeviceQualifierDescriptor *pHsQualifier;
    /** Pointer to the high-speed other speed configuration descriptor */
    const USBConfigurationDescriptor *pHsOtherSpeed;
    /** Pointer to the list of string descriptors */
    const uint8_t **pStrings;
    /** Number of string descriptors in list */
    uint8_t numStrings;

} USBDDriverDescriptors;

/**
 * \typedef USBDDriver
 * \brief USB device driver structure, holding a list of descriptors identifying
 *        the device as well as the driver current state.
 */
typedef struct _USBDDriver {

    /** List of descriptors used by the device. */
    const USBDDriverDescriptors *pDescriptors;
    /** Current setting for each interface. */
    uint8_t *pInterfaces;
    /** Current configuration number (0 -> device is not configured). */
    uint8_t cfgnum;
    /** Indicates if remote wake up has been enabled by the host. */
    uint8_t isRemoteWakeUpEnabled;
    /** Features supported by OTG */
    uint8_t otg_features_supported;
} USBDDriver;

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

extern USBDDriver *USBD_GetDriver(void);
extern void USBDDriver_Initialize(
    USBDDriver *pDriver,
    const USBDDriverDescriptors *pDescriptors,
    uint8_t *pInterfaces);
extern USBConfigurationDescriptor* USBDDriver_GetCfgDescriptors(
    USBDDriver * pDriver,
    uint8_t cfgNum);
extern void USBDDriver_RequestHandler(
    USBDDriver *pDriver,
    const USBGenericRequest *pRequest);
extern uint8_t USBDDriver_IsRemoteWakeUpEnabled(const USBDDriver *pDriver);
extern uint8_t USBDDriver_returnOTGFeatures(const USBDDriver *pDriver);
extern void USBDDriver_clearOTGFeatures(USBDDriver *pDriver);

extern void USBDDriverCallbacks_ConfigurationChanged(uint8_t cfgnum);
extern void USBDDriverCallbacks_InterfaceSettingChanged(uint8_t interface,
                                                             uint8_t setting);

/**@}*/

#endif /*#ifndef USBDDRIVER_H*/

