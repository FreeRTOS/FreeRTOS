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

/** \file
 *  \section Purpose
 * 
 *    Implements for USB requests described by the USB specification.
 */

/** \addtogroup usb_request
 * @{
 */

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/
     
#include <USBRequests.h>

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

/**
 * Returns the type of the given request.
 * \param request Pointer to a USBGenericRequest instance.
 * \return "USB Request Types"
 */
extern uint8_t USBGenericRequest_GetType(const USBGenericRequest *request)
{
    return ((request->bmRequestType >> 5) & 0x3);
}

/**
 * Returns the request code of the given request.
 * \param request Pointer to a USBGenericRequest instance.
 * \return Request code.
 * \sa "USB Request Codes"
 */
uint8_t USBGenericRequest_GetRequest(const USBGenericRequest *request)
{
    return request->bRequest;
}

/**
 * Returns the wValue field of the given request.
 * \param request - Pointer to a USBGenericRequest instance.
 * \return Request value.
 */
uint16_t USBGenericRequest_GetValue(const USBGenericRequest *request)
{
    return request->wValue;
}

/**
 * Returns the wIndex field of the given request.
 * \param request Pointer to a USBGenericRequest instance.
 * \return Request index;
 */
uint16_t USBGenericRequest_GetIndex(const USBGenericRequest *request)
{
    return request->wIndex;
}

/**
 * Returns the expected length of the data phase following a request.
 * \param request Pointer to a USBGenericRequest instance.
 * \return Length of data phase.
 */
uint16_t USBGenericRequest_GetLength(const USBGenericRequest *request)
{
    return request->wLength;
}

/**
 * Returns the endpoint number targetted by a given request.
 * \param request Pointer to a USBGenericRequest instance.
 * \return Endpoint number.
 */
uint8_t USBGenericRequest_GetEndpointNumber(
    const USBGenericRequest *request)
{
    return USBGenericRequest_GetIndex(request) & 0xF;
}

/**
 * Returns the intended recipient of a given request.
 * \param request Pointer to a USBGenericRequest instance.
 * \return Request recipient.
 * \sa "USB Request Recipients"
 */
uint8_t USBGenericRequest_GetRecipient(const USBGenericRequest *request)
{
    /* Recipient is in bits [0..4] of the bmRequestType field */
    return request->bmRequestType & 0xF;
}

/**
 * Returns the direction of the data transfer following the given request.
 * \param request Pointer to a USBGenericRequest instance.
 * \return Transfer direction.
 * \sa "USB Request Directions"
 */
uint8_t USBGenericRequest_GetDirection(const USBGenericRequest *request)
{
    /* Transfer direction is located in bit D7 of the bmRequestType field */
    if ((request->bmRequestType & 0x80) != 0) {

        return USBGenericRequest_IN;
    }
    else {

        return USBGenericRequest_OUT;
    }
}


/**
 * Returns the type of the descriptor requested by the host given the
 * corresponding GET_DESCRIPTOR request.
 * \param request Pointer to a USBGenericDescriptor instance.
 * \return Type of the requested descriptor.
 */
uint8_t USBGetDescriptorRequest_GetDescriptorType(
    const USBGenericRequest *request)
{
    /* Requested descriptor type is in the high-byte of the wValue field */
    return (USBGenericRequest_GetValue(request) >> 8) & 0xFF;
}

/**
 * Returns the index of the requested descriptor, given the corresponding
 * GET_DESCRIPTOR request.
 * \param request Pointer to a USBGenericDescriptor instance.
 * \return Index of the requested descriptor.
 */
uint8_t USBGetDescriptorRequest_GetDescriptorIndex(
    const USBGenericRequest *request)
{
    /* Requested descriptor index if in the low byte of the wValue field */
    return USBGenericRequest_GetValue(request) & 0xFF;
}


/**
 * Returns the address that the device must take in response to a
 * SET_ADDRESS request.
 * \param request Pointer to a USBGenericRequest instance.
 * \return New device address.
 */
uint8_t USBSetAddressRequest_GetAddress(const USBGenericRequest *request)
{
    return USBGenericRequest_GetValue(request) & 0x7F;
}


/**
 * Returns the number of the configuration that should be set in response
 * to the given SET_CONFIGURATION request.
 * \param request Pointer to a USBGenericRequest instance.
 * \return Number of the requested configuration.
 */
uint8_t USBSetConfigurationRequest_GetConfiguration(
    const USBGenericRequest *request)
{
    return USBGenericRequest_GetValue(request);
}


/**
 * Indicates which interface is targetted by a GET_INTERFACE or
 * SET_INTERFACE request.
 * \param request Pointer to a USBGenericRequest instance.
 * \return Interface number.
 */
uint8_t USBInterfaceRequest_GetInterface(const USBGenericRequest *request)
{
    return (USBGenericRequest_GetIndex(request) & 0xFF);
}

/**
 * Indicates the new alternate setting that the interface targetted by a
 * SET_INTERFACE request should use.
 * \param request Pointer to a USBGenericRequest instance.
 * \return New active setting for the interface.
 */
uint8_t USBInterfaceRequest_GetAlternateSetting(
    const USBGenericRequest *request)
{
    return (USBGenericRequest_GetValue(request) & 0xFF);
}


/**
 *  Returns the feature selector of a given CLEAR_FEATURE or SET_FEATURE
 *  request.
 *  \param request Pointer to a USBGenericRequest instance.
 *  \return Feature selector.
 */
uint8_t USBFeatureRequest_GetFeatureSelector(
    const USBGenericRequest *request)
{
    return USBGenericRequest_GetValue(request);
}

/**
 *  Indicates the test that the device must undertake following a
 *  SET_FEATURE request.
 *  \param request Pointer to a USBGenericRequest instance.
 *  \return Test selector.
 */
uint8_t USBFeatureRequest_GetTestSelector(
    const USBGenericRequest *request)
{
    return (USBGenericRequest_GetIndex(request) >> 8) & 0xFF;
}

/**@}*/
