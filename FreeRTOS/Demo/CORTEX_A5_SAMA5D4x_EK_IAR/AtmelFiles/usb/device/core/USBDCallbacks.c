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

/** \file
 *    Definitions of callbacks used by the USBD API to notify the user
 *    application of incoming events. These functions are declared as 'weak',
 *    so they can be re-implemented elsewhere in the application in a
 *    transparent way.
 *
 * \addtogroup usbd_interface 
 *@{
 */

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "USBD.h"
#include "USBDDriver.h"

/*------------------------------------------------------------------------------
 *         Exported function
 *------------------------------------------------------------------------------*/

/**
 * Invoked after the USB driver has been initialized. By default, do nothing.
 */
WEAK void USBDCallbacks_Initialized(void)
{
    /* Does nothing */
}

/**
 * Invoked when the USB driver is reset. Does nothing by default.
 */
WEAK void USBDCallbacks_Reset(void)
{
    /* Does nothing*/
}

/**
 * Invoked when the USB device gets suspended. By default, do nothing.
 */
WEAK void USBDCallbacks_Suspended(void) {}

/**
 * Invoked when the USB device leaves the Suspended state. By default,
 * Do nothing.
 */
WEAK void USBDCallbacks_Resumed(void) {}

/**
 * USBDCallbacks_RequestReceived - Invoked when a new SETUP request is
 * received. Does nothing by default.
 * \param request Pointer to the request to handle.
 */
WEAK void USBDCallbacks_RequestReceived(const USBGenericRequest *request)
{
    /* Does basic enumeration */
    USBDDriver_RequestHandler(USBD_GetDriver(), request);
}

/**@}*/
