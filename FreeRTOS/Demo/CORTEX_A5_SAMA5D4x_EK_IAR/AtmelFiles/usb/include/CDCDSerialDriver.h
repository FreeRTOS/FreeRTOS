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
 * Definition of a class for implementing a USB device CDC serial driver.
 *
 * \section Usage
 *
 * -# Re-implement the USBDCallbacks_RequestReceived method to pass
 *    received requests to CDCDSerialDriver_RequestHandler. *This is
 *    automatically done unless the NOAUTOCALLBACK symbol is defined*.
 * -# Initialize the CDC serial and USB drivers using
 *    CDCDSerialDriver_Initialize.
 * -# Logically connect the device to the host using USBD_Connect.
 * -# Send serial data to the USB host using CDCDSerialDriver_Write.
 * -# Receive serial data from the USB host using CDCDSerialDriver_Read.
 */

#ifndef CDCDSERIALDRIVER_H
#define CDCDSERIALDRIVER_H

/** \addtogroup usbd_cdc
 *@{
 */

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

/* These headers were introduced in C99
   by working group ISO/IEC JTC1/SC22/WG14. */
#include <stdint.h>

#include <USBRequests.h>
#include <CDCRequests.h>
#include <CDCDescriptors.h>
#include <CDCNotifications.h>

#include <CDCDSerial.h>

/*------------------------------------------------------------------------------
 *         Definitions
 *------------------------------------------------------------------------------*/

/** \addtogroup usbd_cdc_if USB Device CDC Serial Interface IDs
 *      @{
 */
/** Communication Class Interface ID */
#define CDCDSerialDriver_CC_INTERFACE           0
/** Data Class Interface ID */
#define CDCDSerialDriver_DC_INTERFACE           1
/**     @}*/

/*------------------------------------------------------------------------------
 *         Types
 *------------------------------------------------------------------------------*/
#pragma pack(1)
#if defined   ( __CC_ARM   ) /* Keil ¦ÌVision 4 */
#elif defined ( __ICCARM__ ) /* IAR Ewarm */
#define __attribute__(...)
#define __packed__  packed
#elif defined (  __GNUC__  ) /* GCC CS3 */
#define __packed__  aligned(1)
#endif

/**
 * \typedef CDCDSerialDriverConfigurationDescriptors
 * \brief Configuration descriptor list for a device implementing a
 *        CDC serial driver.
 */
typedef struct _CDCDSerialDriverConfigurationDescriptors {

    /** Standard configuration descriptor. */
    USBConfigurationDescriptor configuration;
    /** Communication interface descriptor. */
    USBInterfaceDescriptor  communication;
    /** CDC header functional descriptor. */
    CDCHeaderDescriptor header;
    /** CDC call management functional descriptor. */
    CDCCallManagementDescriptor callManagement;
    /** CDC abstract control management functional descriptor. */
    CDCAbstractControlManagementDescriptor abstractControlManagement;
    /** CDC union functional descriptor (with one slave interface). */
    CDCUnionDescriptor union1;
    /** Notification endpoint descriptor. */
    USBEndpointDescriptor notification;
    /** Data interface descriptor. */
    USBInterfaceDescriptor data;
    /** Data OUT endpoint descriptor. */
    USBEndpointDescriptor dataOut;
    /** Data IN endpoint descriptor. */
    USBEndpointDescriptor dataIn;

} __attribute__ ((__packed__)) CDCDSerialDriverConfigurationDescriptors;

/**
 * \typedef CDCDSerialDriverConfigurationDescriptorsOTG
 * \brief Configuration descriptor list for a device implementing a
 *        CDC serial OTG driver.
 */
typedef struct _CDCDSerialDriverConfigurationDescriptorsOTG {

    /** Standard configuration descriptor. */
    USBConfigurationDescriptor configuration;
    /* OTG descriptor */
    USBOtgDescriptor otgDescriptor;
    /** Communication interface descriptor. */
    USBInterfaceDescriptor  communication;
    /** CDC header functional descriptor. */
    CDCHeaderDescriptor header;
    /** CDC call management functional descriptor. */
    CDCCallManagementDescriptor callManagement;
    /** CDC abstract control management functional descriptor. */
    CDCAbstractControlManagementDescriptor abstractControlManagement;
    /** CDC union functional descriptor (with one slave interface). */
    CDCUnionDescriptor union1;
    /** Notification endpoint descriptor. */
    USBEndpointDescriptor notification;
    /** Data interface descriptor. */
    USBInterfaceDescriptor data;
    /** Data OUT endpoint descriptor. */
    USBEndpointDescriptor dataOut;
    /** Data IN endpoint descriptor. */
    USBEndpointDescriptor dataIn;

} __attribute__ ((__packed__)) CDCDSerialDriverConfigurationDescriptorsOTG;

#pragma pack()

/*------------------------------------------------------------------------------
 *      Exported functions
 *------------------------------------------------------------------------------*/

extern void CDCDSerialDriver_Initialize(
    const USBDDriverDescriptors *pDescriptors);

extern void CDCDSerialDriver_ConfigurationChangedHandler(uint8_t cfgnum);

extern void CDCDSerialDriver_RequestHandler(
    const USBGenericRequest *request);

/**
 * Sends a data buffer through the virtual COM port created by the CDC
 * device serial driver. This function behaves exactly like USBD_Write.
 * \param data Pointer to the data buffer to send.
 * \param size Size of the data buffer in bytes.
 * \param callback Optional callback function to invoke when the transfer
 *                 finishes.
 * \param argument Optional argument to the callback function.
 * \return USBD_STATUS_SUCCESS if the read operation has been started normally;
 *         otherwise, the corresponding error code.
 */
static inline uint32_t CDCDSerialDriver_Write(
    void *data,
    uint32_t size,
    TransferCallback callback,
    void *argument)
{
    return CDCDSerial_Write(data, size, callback, argument);
}

/**
 * Receives data from the host through the virtual COM port created by
 * the CDC device serial driver. This function behaves like USBD_Read.
 * \param data Pointer to the data buffer to put received data.
 * \param size Size of the data buffer in bytes.
 * \param callback Optional callback function to invoke when the transfer
 *                 finishes.
 * \param argument Optional argument to the callback function.
 * \return USBD_STATUS_SUCCESS if the read operation has been started normally;
 *         otherwise, the corresponding error code.
 */
static inline uint32_t CDCDSerialDriver_Read(
    void *data,
    uint32_t size,
    TransferCallback callback,
    void *argument)
{
    return CDCDSerial_Read(data, size, callback, argument);
}

/**
 * Copy current line coding settings to pointered space.
 * \param pLineCoding Pointer to CDCLineCoding instance.
 */
static inline void CDCDSerialDriver_GetLineCoding(CDCLineCoding * pLineCoding)
{
    CDCDSerial_GetLineCoding(pLineCoding);
}

/**
 * Returns the current control line state of the RS-232 line.
 */
static inline uint8_t CDCDSerialDriver_GetControlLineState(void)
{
    return CDCDSerial_GetControlLineState();
}

/**
 * Returns the current status of the RS-232 line.
 */
static inline uint16_t CDCDSerialDriver_GetSerialState(void)
{
    return CDCDSerial_GetSerialState();
}

/**
 * Sets the current serial state of the device to the given value.
 * \param serialState  New device state.
 */
static inline void CDCDSerialDriver_SetSerialState(uint16_t serialState)
{
    CDCDSerial_SetSerialState(serialState);
}

/**@}*/

#endif /*#ifndef CDCSERIALDRIVER_H*/

