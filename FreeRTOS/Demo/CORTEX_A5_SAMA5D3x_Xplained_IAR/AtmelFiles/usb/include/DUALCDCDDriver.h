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
 *   Definitions and methods for USB composite device implement.
 * 
 */

#ifndef DUALCDCDDRIVER_H
#define DUALCDCDDRIVER_H
/** \addtogroup usbd_composite_cdccdc
 *@{
 */

/*---------------------------------------------------------------------------
 *         Headers
 *---------------------------------------------------------------------------*/

#include <USBRequests.h>
#include <CDCDescriptors.h>

#include "USBD.h"
#include <CDCDSerialPort.h>


/*---------------------------------------------------------------------------
 *         Defines
 *---------------------------------------------------------------------------*/

/** \addtogroup usbd_composite_cdccdc_desc
 *  The driver uses these interface numbers in configuration descriptor.
 *      @{
 */
/** Number of interfaces of the device */
#define DUALCDCDDriverDescriptors_NUMINTERFACE      4
/** Number of the CDC0 interface. */
#define DUALCDCDDriverDescriptors_INTERFACENUM0     0
/** Number of the CDC1 interface. */
#define DUALCDCDDriverDescriptors_INTERFACENUM1     2
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
/**
 * \typedef DualCdcDriverConfigurationDescriptors
 * \brief Configuration descriptor list for a device implementing a
 *        dual CDC serial composite driver.
 */
typedef struct _DualCdcDriverConfigurationDescriptors {

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

    /* --- CDC 1 */
    /** IAD 1 */
    USBInterfaceAssociationDescriptor cdcIAD1;
    /** Communication interface descriptor */
    USBInterfaceDescriptor cdcCommunication1;
    /** CDC header functional descriptor. */
    CDCHeaderDescriptor cdcHeader1;
    /** CDC call management functional descriptor. */
    CDCCallManagementDescriptor cdcCallManagement1;
    /** CDC abstract control management functional descriptor. */
    CDCAbstractControlManagementDescriptor cdcAbstractControlManagement1;
    /** CDC union functional descriptor (with one slave interface). */
    CDCUnionDescriptor cdcUnion1;
    /** Notification endpoint descriptor. */
    USBEndpointDescriptor cdcNotification1;
    /** Data interface descriptor. */
    USBInterfaceDescriptor cdcData1;
    /** Data OUT endpoint descriptor. */
    USBEndpointDescriptor cdcDataOut1;
    /** Data IN endpoint descriptor. */
    USBEndpointDescriptor cdcDataIn1;

} __attribute__ ((__packed__)) DualCdcDriverConfigurationDescriptors;

#pragma pack()

/*---------------------------------------------------------------------------
 *         Exported functions
 *---------------------------------------------------------------------------*/

/* -DUALCDC */
extern void DUALCDCDDriver_Initialize(
    const USBDDriverDescriptors* pDescriptors);

extern void DUALCDCDDriver_ConfigurationChangeHandler(uint8_t cfgnum);

extern void DUALCDCDDriver_RequestHandler(const USBGenericRequest *request);

extern CDCDSerialPort* DUALCDCDDriver_GetSerialPort(uint32_t port);

/**@}*/
#endif /* #ifndef DUALCDCDDRIVER_H */

