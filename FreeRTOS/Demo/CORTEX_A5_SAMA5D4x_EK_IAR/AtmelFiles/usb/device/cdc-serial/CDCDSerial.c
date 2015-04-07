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
 * Implementation of a single CDC serial port function for USB device.
 */

/** \addtogroup usbd_cdc
 *@{
 */

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "CDCDSerial.h"

#include <USBLib_Trace.h>
#include <USBDDriver.h>
#include <USBD_HAL.h>

/*------------------------------------------------------------------------------
 *         Types
 *------------------------------------------------------------------------------*/

/*------------------------------------------------------------------------------
 *         Internal variables
 *------------------------------------------------------------------------------*/

/** Serial Port instance list */
static CDCDSerialPort cdcdSerial;

/*------------------------------------------------------------------------------
 *         Internal functions
 *------------------------------------------------------------------------------*/

/**
 * USB CDC Serial Port Event Handler.
 * \param event Event code.
 * \param param Event parameter.
 */
static uint32_t CDCDSerial_EventHandler(uint32_t event,
                                        uint32_t param)
{
    switch (event) {
    case CDCDSerialPortEvent_SETCONTROLLINESTATE:
        {
            if (CDCDSerial_ControlLineStateChanged != NULL) {
                CDCDSerial_ControlLineStateChanged(
                    (param & CDCControlLineState_DTR) > 0,
                    (param & CDCControlLineState_RTS) > 0);
            }
        }
        break;
    case CDCDSerialPortEvent_SETLINECODING:
        {
            if (NULL != CDCDSerial_LineCodingIsToChange) {
                event = CDCDSerial_LineCodingIsToChange(
                                        (CDCLineCoding*)param);
                if (event != USBRC_SUCCESS)
                    return event;
            }
        }
        break;
    default:
        return USBRC_SUCCESS;
    }

    return USBRC_SUCCESS;
}

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

/**
 *  Initializes the USB Device CDC serial driver & USBD Driver.
 * \param pUsbd         Pointer to USBDDriver instance.
 * \param bInterfaceNb  Interface number for the function.
 */
void CDCDSerial_Initialize(
    USBDDriver *pUsbd, uint8_t bInterfaceNb)
{
    CDCDSerialPort *pCdcd = &cdcdSerial;

    TRACE_INFO("CDCDSerial_Initialize\n\r");

    /* Initialize serial port function */
    CDCDSerialPort_Initialize(
                      pCdcd, pUsbd,
                      (CDCDSerialPortEventHandler)CDCDSerial_EventHandler,
                      0,
                      bInterfaceNb, 2);
}

/**
 * Invoked whenever the device is changed by the
 * host.
 * \pDescriptors Pointer to the descriptors for function configure.
 * \wLength      Length of descriptors in number of bytes.
 */
void CDCDSerial_ConfigureFunction(USBGenericDescriptor *pDescriptors,
                                  uint16_t wLength)
{
    CDCDSerialPort *pCdcd = &cdcdSerial;
    CDCDSerialPort_ParseInterfaces(pCdcd,
                                   (USBGenericDescriptor*)pDescriptors,
                                   wLength);
}

/**
 * Handles CDC-specific SETUP requests. Should be called from a
 * re-implementation of USBDCallbacks_RequestReceived() method.
 * \param request Pointer to a USBGenericRequest instance.
 */
uint32_t CDCDSerial_RequestHandler(const USBGenericRequest *request)
{
    CDCDSerialPort * pCdcd = &cdcdSerial;

    TRACE_INFO_WP("Cdcf ");
    return CDCDSerialPort_RequestHandler(pCdcd, request);
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
uint32_t CDCDSerial_Read(void *data,
                         uint32_t size,
                         TransferCallback callback,
                         void *argument)
{
    CDCDSerialPort * pCdcd = &cdcdSerial;
    return CDCDSerialPort_Read(pCdcd, data, size, callback, argument);
}

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
uint32_t CDCDSerial_Write(void *data,
                          uint32_t size,
                          TransferCallback callback,
                          void *argument)
{
    CDCDSerialPort * pCdcd = &cdcdSerial;
    return CDCDSerialPort_Write(pCdcd, data, size, callback, argument);
}

/**
 * Returns the current control line state of the RS-232 line.
 */
uint8_t CDCDSerial_GetControlLineState(void)
{
    CDCDSerialPort * pCdcd = &cdcdSerial;
    return CDCDSerialPort_GetControlLineState(pCdcd);
}

/**
 * Copy current line coding settings to pointered space.
 * \param pLineCoding Pointer to CDCLineCoding instance.
 */
void CDCDSerial_GetLineCoding(CDCLineCoding* pLineCoding)
{
    CDCDSerialPort * pCdcd = &cdcdSerial;
    CDCDSerialPort_GetLineCoding(pCdcd, pLineCoding);
}

/**
 * Returns the current status of the RS-232 line.
 */
uint16_t CDCDSerial_GetSerialState(void)
{
    CDCDSerialPort * pCdcd = &cdcdSerial;
    return CDCDSerialPort_GetSerialState(pCdcd);
}

/**
 * Sets the current serial state of the device to the given value.
 * \param serialState  New device state.
 */
void CDCDSerial_SetSerialState(uint16_t serialState)
{
    CDCDSerialPort * pCdcd = &cdcdSerial;
    CDCDSerialPort_SetSerialState(pCdcd, serialState);
}

/**@}*/
