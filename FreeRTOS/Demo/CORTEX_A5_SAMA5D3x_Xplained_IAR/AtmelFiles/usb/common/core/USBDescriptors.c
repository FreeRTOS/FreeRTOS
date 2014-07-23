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
 *
 *    Implements for USB descriptor methods described by the USB specification.
 */

/** \addtogroup usb_descriptor
 *@{
 */

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "USBDescriptors.h"

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

/**
 * Returns the length of a descriptor.
 * \param descriptor Pointer to a USBGenericDescriptor instance.
 * \return Length of descriptor in bytes.
 */
uint32_t USBGenericDescriptor_GetLength(
    const USBGenericDescriptor *descriptor)
{
    return descriptor->bLength;
}

/**
 * Returns the type of a descriptor.
 * \param descriptor Pointer to a USBGenericDescriptor instance.
 * \return Type of descriptor.
 */
uint8_t USBGenericDescriptor_GetType(
    const USBGenericDescriptor *descriptor)
{
    return descriptor->bDescriptorType;
}

/**
 * Returns a pointer to the descriptor right after the given one, when
 * parsing a Configuration descriptor.
 * \param descriptor - Pointer to a USBGenericDescriptor instance.
 * \return Pointer to the next descriptor.
 */
USBGenericDescriptor *USBGenericDescriptor_GetNextDescriptor(
    const USBGenericDescriptor *descriptor)
{
    return (USBGenericDescriptor *)
        (((char *) descriptor) + USBGenericDescriptor_GetLength(descriptor));
}

/** Parses the given descriptor list via costomized function.
 *  \param descriptor    Pointer to the start of the whole descriptors list.
 *  \param totalLength   Total size of descriptors in bytes.
 *  \param parseFunction Function to parse each descriptor scanned.
 *                       Return 0 to continue parsing.
 *  \param parseArg      Argument passed to parse function.
 *  \return Pointer to USBGenericDescriptor instance for next descriptor.
 */
USBGenericDescriptor *USBGenericDescriptor_Parse(
    const USBGenericDescriptor *descriptor,
    uint32_t totalLength,
    USBDescriptorParseFunction parseFunction,
    void *parseArg)
{
    int32_t size = totalLength;

    if (size == 0)
        return 0;

    /* Start parsing descriptors */
    while (1) {

        uint32_t parseRC = 0;

        /* Parse current descriptor */
        if (parseFunction) {

            parseRC = parseFunction((void*)descriptor, parseArg);
        }

        /* Get next descriptor */
        size -= USBGenericDescriptor_GetLength(descriptor);
        descriptor = USBGenericDescriptor_GetNextDescriptor(descriptor);

        if (size) {
            if (parseRC != 0) {

                return (USBGenericDescriptor *)descriptor;
            }
        }
        else
            break;
    }
    /* No descriptors remaining */
    return 0;
}


/**
 *  Returns the number of an endpoint given its descriptor.
 *  \param endpoint Pointer to a USBEndpointDescriptor instance.
 *  \return Endpoint number.
 */
uint8_t USBEndpointDescriptor_GetNumber(
    const USBEndpointDescriptor *endpoint)
{
    return endpoint->bEndpointAddress & 0xF;
}

/**
 *  Returns the direction of an endpoint given its descriptor.
 *  \param endpoint Pointer to a USBEndpointDescriptor instance.
 *  \return Endpoint direction (see \ref usb_ep_dir).
 */
uint8_t USBEndpointDescriptor_GetDirection(
    const USBEndpointDescriptor *endpoint)
{
    if ((endpoint->bEndpointAddress & 0x80) != 0) {

        return USBEndpointDescriptor_IN;
    }
    else {

        return USBEndpointDescriptor_OUT;
    }
}

/**
 *  Returns the type of an endpoint given its descriptor.
 *  \param endpoint Pointer to a USBEndpointDescriptor instance.
 *  \return Endpoint type (see \ref usb_ep_type).
 */
uint8_t USBEndpointDescriptor_GetType(
    const USBEndpointDescriptor *endpoint)
{
    return endpoint->bmAttributes & 0x3;
}

/**
 *  Returns the maximum size of a packet (in bytes) on an endpoint given
 *  its descriptor.
 *  \param endpoint - Pointer to a USBEndpointDescriptor instance.
 *  \return Maximum packet size of endpoint.
 */
uint16_t USBEndpointDescriptor_GetMaxPacketSize(
    const USBEndpointDescriptor *endpoint)
{
uint16_t usTemp;
uint8_t *pc1, *pc2;

	pc1 = ( uint8_t * ) &( endpoint->wMaxPacketSize );
	pc2 = pc1 + 1;
	usTemp = ( ( *pc2 ) << 8 ) | *pc1;

	return usTemp;
#warning The original code below crashes when build for A5 as endpoint can be misaligned.
    //_RB_return endpoint->wMaxPacketSize;
}

/**
 *  Returns the polling interval on an endpoint given its descriptor.
 *  \param endpoint - Pointer to a USBEndpointDescriptor instance.
 *  \return Polling interval of endpoint.
 */
uint8_t USBEndpointDescriptor_GetInterval(
    const USBEndpointDescriptor *endpoint)
{
    return endpoint->bInterval;
}



/** Returns the total length of a configuration, i.e. including the
 *  descriptors following it.
 *  \param configuration Pointer to a USBConfigurationDescriptor instance.
 *  \return Total length (in bytes) of the configuration.
 */
volatile unsigned long ulCount = 0;
uint32_t USBConfigurationDescriptor_GetTotalLength(
    const USBConfigurationDescriptor *configuration)
{
ulCount++;
if( ulCount == 5 )
{
	__asm volatile( "NOP" );
}
    return configuration->wTotalLength;
}

/** Returns the number of interfaces in a configuration.
 *  \param configuration Pointer to a USBConfigurationDescriptor instance.
 *  \return Number of interfaces in configuration.
 */
unsigned char USBConfigurationDescriptor_GetNumInterfaces(
    const USBConfigurationDescriptor *configuration)
{
    return configuration->bNumInterfaces;
}

/** Indicates if the device is self-powered when in a given configuration.
 *  \param configuration Pointer to a USBConfigurationDescriptor instance.
 *  \return 1 if the device is self-powered when in the given configuration;
 *          otherwise 0.
 */
unsigned char USBConfigurationDescriptor_IsSelfPowered(
    const USBConfigurationDescriptor *configuration)
{
    if ((configuration->bmAttributes & (1 << 6)) != 0) {

        return 1;
    }
    else {

        return 0;
    }
}

/** Parses the given Configuration descriptor (followed by relevant
 *  interface, endpoint and class-specific descriptors) into three arrays.
 *  *Each array must have its size equal or greater to the number of
 *  descriptors it stores plus one*. A null-value is inserted after the last
 *  descriptor of each type to indicate the array end.
 *
 *  Note that if the pointer to an array is null (0), nothing is stored in
 *  it.
 *  \param configuration Pointer to the start of the whole Configuration
 *                       descriptor.
 *  \param interfaces    Pointer to the Interface descriptor array.
 *  \param endpoints     Pointer to the Endpoint descriptor array.
 *  \param others        Pointer to the class-specific descriptor array.
 */
void USBConfigurationDescriptor_Parse(
    const USBConfigurationDescriptor *configuration,
    USBInterfaceDescriptor **interfaces,
    USBEndpointDescriptor **endpoints,
    USBGenericDescriptor **others)
{
    /* Get size of configuration to parse */
    int size = USBConfigurationDescriptor_GetTotalLength(configuration);
    size -= sizeof(USBConfigurationDescriptor);

    /* Start parsing descriptors */
    USBGenericDescriptor *descriptor = (USBGenericDescriptor *) configuration;
    while (size > 0) {

        /* Get next descriptor */
        descriptor = USBGenericDescriptor_GetNextDescriptor(descriptor);
        size -= USBGenericDescriptor_GetLength(descriptor);

        /* Store descriptor in correponding array */
        if (USBGenericDescriptor_GetType(descriptor)
             == USBGenericDescriptor_INTERFACE) {

            if (interfaces) {

                *interfaces = (USBInterfaceDescriptor *) descriptor;
                interfaces++;
            }
        }
        else if (USBGenericDescriptor_GetType(descriptor)
                  == USBGenericDescriptor_ENDPOINT) {

            if (endpoints) {

                *endpoints = (USBEndpointDescriptor *) descriptor;
                endpoints++;
            }
        }
        else if (others) {

            *others = descriptor;
            others++;
        }
    }

    /* Null-terminate arrays */
    if (interfaces) {

        *interfaces = 0;
    }
    if (endpoints) {

        *endpoints = 0;
    }
    if (others) {

        *others = 0;
    }
}

/**@}*/

