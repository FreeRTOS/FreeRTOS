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

/**\file
 *   Title: CDCDSerialDriver implementation
 *
 *   About: Purpose
 *       Implementation of the CDCDSerialDriver class methods.
 */

/** \addtogroup usbd_cdc
 *@{
 */

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "CDCDSerialDriver.h"

#include <USBLib_Trace.h>
#include <USBDDriver.h>
#include <USBD_HAL.h>

/*------------------------------------------------------------------------------
 *         Types
 *------------------------------------------------------------------------------*/

/*------------------------------------------------------------------------------
 *         Internal variables
 *------------------------------------------------------------------------------*/

/*------------------------------------------------------------------------------
 *         Internal functions
 *------------------------------------------------------------------------------*/

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

/**
 *  Initializes the USB Device CDC serial driver & USBD Driver.
 *  \param  pDescriptors Pointer to Descriptors list for CDC Serial Device.
 */
void CDCDSerialDriver_Initialize(const USBDDriverDescriptors *pDescriptors)
{
    USBDDriver *pUsbd = USBD_GetDriver();

    /* Initialize the standard driver */
    USBDDriver_Initialize(pUsbd,
                          pDescriptors,
                          0); /* Multiple settings for interfaces not supported */

    CDCDSerial_Initialize(pUsbd, CDCDSerialDriver_CC_INTERFACE);

    /* Initialize the USB driver */
    USBD_Init();
}

/**
 * Invoked whenever the active configuration of device is changed by the
 * host.
 * \param cfgnum Configuration number.
 */
void CDCDSerialDriver_ConfigurationChangedHandler(uint8_t cfgnum)
{
    USBDDriver *pUsbd = USBD_GetDriver();
    USBConfigurationDescriptor *pDesc;
    if (cfgnum) {
        pDesc = USBDDriver_GetCfgDescriptors(pUsbd, cfgnum);
        CDCDSerial_ConfigureFunction((USBGenericDescriptor *)pDesc,
                                      pDesc->wTotalLength);
    }
}

/**
 * Handles CDC-specific SETUP requests. Should be called from a
 * re-implementation of USBDCallbacks_RequestReceived() method.
 * \param request Pointer to a USBGenericRequest instance.
 */
void CDCDSerialDriver_RequestHandler(const USBGenericRequest *request)
{
    USBDDriver *pUsbd = USBD_GetDriver();
    TRACE_INFO_WP("NewReq ");
    if (CDCDSerial_RequestHandler(request))
        USBDDriver_RequestHandler(pUsbd, request);
}

/**@}*/

