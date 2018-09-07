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
 *
 * Implementation of the CDCSetControlLineStateRequest class.
 */

/** \addtogroup usb_cdc
 *@{
 */

/*----------------------------------------------------------------------------
 *         Headers
 *----------------------------------------------------------------------------*/

#include <CDCRequests.h>

/*----------------------------------------------------------------------------
 *         Exported functions
 *----------------------------------------------------------------------------*/

/**
 *  Notifies if the given request indicates that the DTE signal is present.
 *  \param request Pointer to a USBGenericRequest instance.
 *  \return 1 if the DTE signal is present, otherwise 0.
 */
uint8_t CDCSetControlLineStateRequest_IsDtePresent(
    const USBGenericRequest *request)
{
    if ((USBGenericRequest_GetValue(request) & 0x0001) != 0) {

        return 1;
    }
    else {

        return 0;
    }
}

/**
 *  Notifies if the given request indicates that the device carrier should
 *  be activated.
 *  \param request Pointer to a USBGenericRequest instance.
 *  \return 1 is the device should activate its carrier, 0 otherwise.
 */
uint8_t CDCSetControlLineStateRequest_ActivateCarrier(
    const USBGenericRequest *request)
{
    if ((USBGenericRequest_GetValue(request) & 0x0002) != 0) {

        return 1;
    }
    else {

        return 0;
    }
}

/**@}*/

