/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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


/** \file
 * \addtogroup usbd_cdc
 *@{
 */

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "board.h"
#include "include/USBD_Config.h"
#include "CDCDSerialDriver.h"

/*------------------------------------------------------------------------------
 *         Definitions
 *------------------------------------------------------------------------------*/

/** \addtogroup usbd_cdc_serial_device_ids CDC Serial Device IDs
 *      @{
 * This page lists the IDs used in the CDC Serial Device Descriptor.
 *
 * \section IDs
 * - CDCDSerialDriverDescriptors_PRODUCTID
 * - CDCDSerialDriverDescriptors_VENDORID
 * - CDCDSerialDriverDescriptors_RELEASE
 */

/** Device product ID. */
#define CDCDSerialDriverDescriptors_PRODUCTID       0x6119
/** Device vendor ID (Atmel). */
#define CDCDSerialDriverDescriptors_VENDORID        0x03EB
/** Device release number. */
#define CDCDSerialDriverDescriptors_RELEASE         0x0100
/**      @}*/

/*------------------------------------------------------------------------------
 *         Macros
 *------------------------------------------------------------------------------*/

/** Returns the minimum between two values. */
#define MIN(a, b)       ((a < b) ? a : b)

/*------------------------------------------------------------------------------
 *         Exported variables
 *------------------------------------------------------------------------------*/

/** Standard USB device descriptor for the CDC serial driver */
const USBDeviceDescriptor deviceDescriptor = {

    sizeof(USBDeviceDescriptor),
    USBGenericDescriptor_DEVICE,
    USBDeviceDescriptor_USB2_00,
    CDCDeviceDescriptor_CLASS,
    CDCDeviceDescriptor_SUBCLASS,
    CDCDeviceDescriptor_PROTOCOL,
    CHIP_USB_ENDPOINTS_MAXPACKETSIZE(0),
    CDCDSerialDriverDescriptors_VENDORID,
    CDCDSerialDriverDescriptors_PRODUCTID,
    CDCDSerialDriverDescriptors_RELEASE,
    0, /* No string descriptor for manufacturer */
    1, /* Index of product string descriptor is #1 */
    0, /* No string descriptor for serial number */
    1 /* Device has 1 possible configuration */
};

/** Standard USB configuration descriptor for the CDC serial driver */
const CDCDSerialDriverConfigurationDescriptors configurationDescriptorsFS = {

    /* Standard configuration descriptor */
    {
        sizeof(USBConfigurationDescriptor),
        USBGenericDescriptor_CONFIGURATION,
        sizeof(CDCDSerialDriverConfigurationDescriptors),
        2, /* There are two interfaces in this configuration */
        1, /* This is configuration #1 */
        0, /* No string descriptor for this configuration */
        USBD_BMATTRIBUTES,
        USBConfigurationDescriptor_POWER(100)
    },
    /* Communication class interface standard descriptor */
    {
        sizeof(USBInterfaceDescriptor),
        USBGenericDescriptor_INTERFACE,
        0, /* This is interface #0 */
        0, /* This is alternate setting #0 for this interface */
        1, /* This interface uses 1 endpoint */
        CDCCommunicationInterfaceDescriptor_CLASS,
        CDCCommunicationInterfaceDescriptor_ABSTRACTCONTROLMODEL,
        CDCCommunicationInterfaceDescriptor_NOPROTOCOL,
        0  /* No string descriptor for this interface */
    },
    /* Class-specific header functional descriptor */
    {
        sizeof(CDCHeaderDescriptor),
        CDCGenericDescriptor_INTERFACE,
        CDCGenericDescriptor_HEADER,
        CDCGenericDescriptor_CDC1_10
    },
    /* Class-specific call management functional descriptor */
    {
        sizeof(CDCCallManagementDescriptor),
        CDCGenericDescriptor_INTERFACE,
        CDCGenericDescriptor_CALLMANAGEMENT,
        CDCCallManagementDescriptor_SELFCALLMANAGEMENT,
        0 /* No associated data interface */
    },
    /* Class-specific abstract control management functional descriptor */
    {
        sizeof(CDCAbstractControlManagementDescriptor),
        CDCGenericDescriptor_INTERFACE,
        CDCGenericDescriptor_ABSTRACTCONTROLMANAGEMENT,
        CDCAbstractControlManagementDescriptor_LINE
    },
    /* Class-specific union functional descriptor with one slave interface */
    {
        sizeof(CDCUnionDescriptor),
        CDCGenericDescriptor_INTERFACE,
        CDCGenericDescriptor_UNION,
        0, /* Number of master interface is #0 */
        1 /* First slave interface is #1 */
    },
    /* Notification endpoint standard descriptor */
    {
        sizeof(USBEndpointDescriptor),
        USBGenericDescriptor_ENDPOINT,
        USBEndpointDescriptor_ADDRESS(USBEndpointDescriptor_IN,
                                      CDCDSerialDriverDescriptors_NOTIFICATION),
        USBEndpointDescriptor_INTERRUPT,
        MIN(CHIP_USB_ENDPOINTS_MAXPACKETSIZE(CDCDSerialDriverDescriptors_NOTIFICATION),
            USBEndpointDescriptor_MAXINTERRUPTSIZE_FS),
        10 /* Endpoint is polled every 10ms */
    },
    /* Data class interface standard descriptor */
    {
        sizeof(USBInterfaceDescriptor),
        USBGenericDescriptor_INTERFACE,
        1, /* This is interface #1 */
        0, /* This is alternate setting #0 for this interface */
        2, /* This interface uses 2 endpoints */
        CDCDataInterfaceDescriptor_CLASS,
        CDCDataInterfaceDescriptor_SUBCLASS,
        CDCDataInterfaceDescriptor_NOPROTOCOL,
        0  /* No string descriptor for this interface */
    },
    /* Bulk-OUT endpoint standard descriptor */
    {
        sizeof(USBEndpointDescriptor),
        USBGenericDescriptor_ENDPOINT,
        USBEndpointDescriptor_ADDRESS(USBEndpointDescriptor_OUT,
                                      CDCDSerialDriverDescriptors_DATAOUT),
        USBEndpointDescriptor_BULK,
        MIN(CHIP_USB_ENDPOINTS_MAXPACKETSIZE(CDCDSerialDriverDescriptors_DATAOUT),
            USBEndpointDescriptor_MAXBULKSIZE_FS),
        0 /* Must be 0 for full-speed bulk endpoints */
    },
    /* Bulk-IN endpoint descriptor */
    {
        sizeof(USBEndpointDescriptor),
        USBGenericDescriptor_ENDPOINT,
        USBEndpointDescriptor_ADDRESS(USBEndpointDescriptor_IN,
                                      CDCDSerialDriverDescriptors_DATAIN),
        USBEndpointDescriptor_BULK,
        MIN(CHIP_USB_ENDPOINTS_MAXPACKETSIZE(CDCDSerialDriverDescriptors_DATAIN),
            USBEndpointDescriptor_MAXBULKSIZE_FS),
        0 /* Must be 0 for full-speed bulk endpoints */
    }
};

/** Other-speed configuration descriptor (when in full-speed). */
const CDCDSerialDriverConfigurationDescriptors otherSpeedDescriptorsFS = {

    /* Standard configuration descriptor */
    {
        sizeof(USBConfigurationDescriptor),
        USBGenericDescriptor_OTHERSPEEDCONFIGURATION,
        sizeof(CDCDSerialDriverConfigurationDescriptors),
        2, /* There are two interfaces in this configuration */
        1, /* This is configuration #1 */
        0, /* No string descriptor for this configuration */
        BOARD_USB_BMATTRIBUTES,
        USBConfigurationDescriptor_POWER(100)
    },
    /* Communication class interface standard descriptor */
    {
        sizeof(USBInterfaceDescriptor),
        USBGenericDescriptor_INTERFACE,
        0, /* This is interface #0 */
        0, /* This is alternate setting #0 for this interface */
        1, /* This interface uses 1 endpoint */
        CDCCommunicationInterfaceDescriptor_CLASS,
        CDCCommunicationInterfaceDescriptor_ABSTRACTCONTROLMODEL,
        CDCCommunicationInterfaceDescriptor_NOPROTOCOL,
        0  /* No string descriptor for this interface */
    },
    /* Class-specific header functional descriptor */
    {
        sizeof(CDCHeaderDescriptor),
        CDCGenericDescriptor_INTERFACE,
        CDCGenericDescriptor_HEADER,
        CDCGenericDescriptor_CDC1_10
    },
    /* Class-specific call management functional descriptor */
    {
        sizeof(CDCCallManagementDescriptor),
        CDCGenericDescriptor_INTERFACE,
        CDCGenericDescriptor_CALLMANAGEMENT,
        CDCCallManagementDescriptor_SELFCALLMANAGEMENT,
        0 /* No associated data interface */
    },
    /* Class-specific abstract control management functional descriptor */
    {
        sizeof(CDCAbstractControlManagementDescriptor),
        CDCGenericDescriptor_INTERFACE,
        CDCGenericDescriptor_ABSTRACTCONTROLMANAGEMENT,
        CDCAbstractControlManagementDescriptor_LINE
    },
    /* Class-specific union functional descriptor with one slave interface */
    {
        sizeof(CDCUnionDescriptor),
        CDCGenericDescriptor_INTERFACE,
        CDCGenericDescriptor_UNION,
        0, /* Number of master interface is #0 */
        1 /* First slave interface is #1 */
    },
    /* Notification endpoint standard descriptor */
    {
        sizeof(USBEndpointDescriptor), 
        USBGenericDescriptor_ENDPOINT,
        USBEndpointDescriptor_ADDRESS(USBEndpointDescriptor_IN,
                                      CDCDSerialDriverDescriptors_NOTIFICATION),
        USBEndpointDescriptor_INTERRUPT,
        MIN(CHIP_USB_ENDPOINTS_MAXPACKETSIZE(CDCDSerialDriverDescriptors_NOTIFICATION),
            USBEndpointDescriptor_MAXINTERRUPTSIZE_FS),
        8 /* Endpoint is polled every 16ms */
    },
    /* Data class interface standard descriptor */
    {
        sizeof(USBInterfaceDescriptor),
        USBGenericDescriptor_INTERFACE,
        1, /* This is interface #1 */
        0, /* This is alternate setting #0 for this interface */
        2, /* This interface uses 2 endpoints */
        CDCDataInterfaceDescriptor_CLASS,
        CDCDataInterfaceDescriptor_SUBCLASS,
        CDCDataInterfaceDescriptor_NOPROTOCOL,
        0  /* No string descriptor for this interface */
    },
    /* Bulk-OUT endpoint standard descriptor */
    {
        sizeof(USBEndpointDescriptor), 
        USBGenericDescriptor_ENDPOINT,
        USBEndpointDescriptor_ADDRESS(USBEndpointDescriptor_OUT,
                                      CDCDSerialDriverDescriptors_DATAOUT),
        USBEndpointDescriptor_BULK,
        MIN(CHIP_USB_ENDPOINTS_MAXPACKETSIZE(CDCDSerialDriverDescriptors_DATAOUT),
            USBEndpointDescriptor_MAXBULKSIZE_HS),
        0 /* Must be 0 for full-speed bulk endpoints */
    },
    /* Bulk-IN endpoint descriptor */
    {
        sizeof(USBEndpointDescriptor),
        USBGenericDescriptor_ENDPOINT,
        USBEndpointDescriptor_ADDRESS(USBEndpointDescriptor_IN,
                                      CDCDSerialDriverDescriptors_DATAIN),
        USBEndpointDescriptor_BULK,
        MIN(CHIP_USB_ENDPOINTS_MAXPACKETSIZE(CDCDSerialDriverDescriptors_DATAIN),
            USBEndpointDescriptor_MAXBULKSIZE_HS),
        0 /* Must be 0 for full-speed bulk endpoints */
    }
};

/** Configuration descriptor (when in high-speed). */
const CDCDSerialDriverConfigurationDescriptors configurationDescriptorsHS = {

    /* Standard configuration descriptor */
    {
        sizeof(USBConfigurationDescriptor),
        USBGenericDescriptor_CONFIGURATION,
        sizeof(CDCDSerialDriverConfigurationDescriptors),
        2, /* There are two interfaces in this configuration */
        1, /* This is configuration #1 */
        0, /* No string descriptor for this configuration */
        BOARD_USB_BMATTRIBUTES,
        USBConfigurationDescriptor_POWER(100)
    },
    /* Communication class interface standard descriptor */
    {
        sizeof(USBInterfaceDescriptor),
        USBGenericDescriptor_INTERFACE,
        0, /* This is interface #0 */
        0, /* This is alternate setting #0 for this interface */
        1, /* This interface uses 1 endpoint */
        CDCCommunicationInterfaceDescriptor_CLASS,
        CDCCommunicationInterfaceDescriptor_ABSTRACTCONTROLMODEL,
        CDCCommunicationInterfaceDescriptor_NOPROTOCOL,
        0  /* No string descriptor for this interface */
    },
    /* Class-specific header functional descriptor */
    {
        sizeof(CDCHeaderDescriptor),
        CDCGenericDescriptor_INTERFACE,
        CDCGenericDescriptor_HEADER,
        CDCGenericDescriptor_CDC1_10
    },
    /* Class-specific call management functional descriptor */
    {
        sizeof(CDCCallManagementDescriptor),
        CDCGenericDescriptor_INTERFACE,
        CDCGenericDescriptor_CALLMANAGEMENT,
        CDCCallManagementDescriptor_SELFCALLMANAGEMENT,
        0 /* No associated data interface */
    },
    /* Class-specific abstract control management functional descriptor */
    {
        sizeof(CDCAbstractControlManagementDescriptor),
        CDCGenericDescriptor_INTERFACE,
        CDCGenericDescriptor_ABSTRACTCONTROLMANAGEMENT,
        CDCAbstractControlManagementDescriptor_LINE
    },
    /* Class-specific union functional descriptor with one slave interface */
    {
        sizeof(CDCUnionDescriptor),
        CDCGenericDescriptor_INTERFACE,
        CDCGenericDescriptor_UNION,
        0, /* Number of master interface is #0 */
        1 /* First slave interface is #1 */
    },
    /* Notification endpoint standard descriptor */
    {
        sizeof(USBEndpointDescriptor), 
        USBGenericDescriptor_ENDPOINT,
        USBEndpointDescriptor_ADDRESS(USBEndpointDescriptor_IN,
                                      CDCDSerialDriverDescriptors_NOTIFICATION),
        USBEndpointDescriptor_INTERRUPT,
        MIN(CHIP_USB_ENDPOINTS_MAXPACKETSIZE(CDCDSerialDriverDescriptors_NOTIFICATION),
            USBEndpointDescriptor_MAXINTERRUPTSIZE_FS),
        8  /* Endpoint is polled every 16ms */
    },
    /* Data class interface standard descriptor */
    {
        sizeof(USBInterfaceDescriptor),
        USBGenericDescriptor_INTERFACE,
        1, /* This is interface #1 */
        0, /* This is alternate setting #0 for this interface */
        2, /* This interface uses 2 endpoints */
        CDCDataInterfaceDescriptor_CLASS,
        CDCDataInterfaceDescriptor_SUBCLASS,
        CDCDataInterfaceDescriptor_NOPROTOCOL,
        0  /* No string descriptor for this interface */
    },
    /* Bulk-OUT endpoint standard descriptor */
    {
        sizeof(USBEndpointDescriptor), 
        USBGenericDescriptor_ENDPOINT,
        USBEndpointDescriptor_ADDRESS(USBEndpointDescriptor_OUT,
                                      CDCDSerialDriverDescriptors_DATAOUT),
        USBEndpointDescriptor_BULK,
        MIN(CHIP_USB_ENDPOINTS_MAXPACKETSIZE(CDCDSerialDriverDescriptors_DATAOUT),
            USBEndpointDescriptor_MAXBULKSIZE_HS),
        0 /* Must be 0 for full-speed bulk endpoints */
    },
    /* Bulk-IN endpoint descriptor */
    {
        sizeof(USBEndpointDescriptor),
        USBGenericDescriptor_ENDPOINT,
        USBEndpointDescriptor_ADDRESS(USBEndpointDescriptor_IN,
                                      CDCDSerialDriverDescriptors_DATAIN),
        USBEndpointDescriptor_BULK,
        MIN(CHIP_USB_ENDPOINTS_MAXPACKETSIZE(CDCDSerialDriverDescriptors_DATAIN),
            USBEndpointDescriptor_MAXBULKSIZE_HS),
        0 /* Must be 0 for full-speed bulk endpoints */
    }
};

/** Other-speed configuration descriptor (when in high-speed). */
const CDCDSerialDriverConfigurationDescriptors otherSpeedDescriptorsHS = {

    /* Standard configuration descriptor */
    {
        sizeof(USBConfigurationDescriptor),
        USBGenericDescriptor_OTHERSPEEDCONFIGURATION,
        sizeof(CDCDSerialDriverConfigurationDescriptors),
        2, /* There are two interfaces in this configuration */
        1, /* This is configuration #1 */
        0, /* No string descriptor for this configuration */
        BOARD_USB_BMATTRIBUTES,
        USBConfigurationDescriptor_POWER(100)
    },
    /* Communication class interface standard descriptor */
    {
        sizeof(USBInterfaceDescriptor),
        USBGenericDescriptor_INTERFACE,
        0, /* This is interface #0 */
        0, /* This is alternate setting #0 for this interface */
        1, /* This interface uses 1 endpoint */
        CDCCommunicationInterfaceDescriptor_CLASS,
        CDCCommunicationInterfaceDescriptor_ABSTRACTCONTROLMODEL,
        CDCCommunicationInterfaceDescriptor_NOPROTOCOL,
        0  /* No string descriptor for this interface */
    },
    /* Class-specific header functional descriptor */
    {
        sizeof(CDCHeaderDescriptor),
        CDCGenericDescriptor_INTERFACE,
        CDCGenericDescriptor_HEADER,
        CDCGenericDescriptor_CDC1_10
    },
    /* Class-specific call management functional descriptor */
    {
        sizeof(CDCCallManagementDescriptor),
        CDCGenericDescriptor_INTERFACE,
        CDCGenericDescriptor_CALLMANAGEMENT,
        CDCCallManagementDescriptor_SELFCALLMANAGEMENT,
        0 /* No associated data interface */
    },
    /* Class-specific abstract control management functional descriptor */
    {
        sizeof(CDCAbstractControlManagementDescriptor),
        CDCGenericDescriptor_INTERFACE,
        CDCGenericDescriptor_ABSTRACTCONTROLMANAGEMENT,
        CDCAbstractControlManagementDescriptor_LINE
    },
    /* Class-specific union functional descriptor with one slave interface */
    {
        sizeof(CDCUnionDescriptor),
        CDCGenericDescriptor_INTERFACE,
        CDCGenericDescriptor_UNION,
        0, /* Number of master interface is #0 */
        1 /* First slave interface is #1 */
    },
    /* Notification endpoint standard descriptor */
    {
        sizeof(USBEndpointDescriptor), 
        USBGenericDescriptor_ENDPOINT,
        USBEndpointDescriptor_ADDRESS(USBEndpointDescriptor_IN,
                                      CDCDSerialDriverDescriptors_NOTIFICATION),
        USBEndpointDescriptor_INTERRUPT,
        MIN(CHIP_USB_ENDPOINTS_MAXPACKETSIZE(CDCDSerialDriverDescriptors_NOTIFICATION),
            USBEndpointDescriptor_MAXINTERRUPTSIZE_FS),
        10 /* Endpoint is polled every 10ms */
    },
    /* Data class interface standard descriptor */
    {
        sizeof(USBInterfaceDescriptor),
        USBGenericDescriptor_INTERFACE,
        1, /* This is interface #1 */
        0, /* This is alternate setting #0 for this interface */
        2, /* This interface uses 2 endpoints */
        CDCDataInterfaceDescriptor_CLASS,
        CDCDataInterfaceDescriptor_SUBCLASS,
        CDCDataInterfaceDescriptor_NOPROTOCOL,
        0  /* No string descriptor for this interface */
    },
    /* Bulk-OUT endpoint standard descriptor */
    {
        sizeof(USBEndpointDescriptor), 
        USBGenericDescriptor_ENDPOINT,
        USBEndpointDescriptor_ADDRESS(USBEndpointDescriptor_OUT,
                                      CDCDSerialDriverDescriptors_DATAOUT),
        USBEndpointDescriptor_BULK,
        MIN(CHIP_USB_ENDPOINTS_MAXPACKETSIZE(CDCDSerialDriverDescriptors_DATAOUT),
            USBEndpointDescriptor_MAXBULKSIZE_FS),
        0 /* Must be 0 for full-speed bulk endpoints */
    },
    /* Bulk-IN endpoint descriptor */
    {
        sizeof(USBEndpointDescriptor),
        USBGenericDescriptor_ENDPOINT,
        USBEndpointDescriptor_ADDRESS(USBEndpointDescriptor_IN,
                                      CDCDSerialDriverDescriptors_DATAIN),
        USBEndpointDescriptor_BULK,
        MIN(CHIP_USB_ENDPOINTS_MAXPACKETSIZE(CDCDSerialDriverDescriptors_DATAIN),
            USBEndpointDescriptor_MAXBULKSIZE_FS),
        0 /* Must be 0 for full-speed bulk endpoints */
    }
};

/** Language ID string descriptor */
const unsigned char languageIdStringDescriptor[] = {

    USBStringDescriptor_LENGTH(1),
    USBGenericDescriptor_STRING,
    USBStringDescriptor_ENGLISH_US
};

/** Product string descriptor */
const unsigned char productStringDescriptor[] = {

    USBStringDescriptor_LENGTH(13),
    USBGenericDescriptor_STRING,
    USBStringDescriptor_UNICODE('A'),
    USBStringDescriptor_UNICODE('T'),
    USBStringDescriptor_UNICODE('9'),
    USBStringDescriptor_UNICODE('1'),
    USBStringDescriptor_UNICODE('U'),
    USBStringDescriptor_UNICODE('S'),
    USBStringDescriptor_UNICODE('B'),
    USBStringDescriptor_UNICODE('S'),
    USBStringDescriptor_UNICODE('e'),
    USBStringDescriptor_UNICODE('r'),
    USBStringDescriptor_UNICODE('i'),
    USBStringDescriptor_UNICODE('a'),
    USBStringDescriptor_UNICODE('l')
};

/** List of string descriptors used by the device */
const unsigned char *stringDescriptors[] = {

    languageIdStringDescriptor,
    productStringDescriptor,
};

/** List of standard descriptors for the serial driver. */
WEAK const USBDDriverDescriptors cdcdSerialDriverDescriptors = {

    &deviceDescriptor,
    (USBConfigurationDescriptor *) &(configurationDescriptorsFS),
    0, /* No full-speed device qualifier descriptor */
    (USBConfigurationDescriptor *) &(otherSpeedDescriptorsFS),
    0, /* No high-speed device descriptor (uses FS one) */
    (USBConfigurationDescriptor *) &(configurationDescriptorsHS),
    0, /* No high-speed device qualifier descriptor */
    (USBConfigurationDescriptor *) &(otherSpeedDescriptorsHS),
    stringDescriptors,
    2 /* 2 string descriptors in list */
};

/**@}*/
