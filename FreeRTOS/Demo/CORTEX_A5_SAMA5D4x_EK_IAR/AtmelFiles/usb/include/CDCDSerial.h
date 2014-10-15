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
 * Single CDC Serial Port Function for USB device & composite driver.
 */

#ifndef CDCDSERIAL_H
#define CDCDSERIAL_H

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

#include <USBDDriver.h>
#include <CDCDSerialPort.h>

/*------------------------------------------------------------------------------
 *         Definitions
 *------------------------------------------------------------------------------*/

/*------------------------------------------------------------------------------
 *         Types
 *------------------------------------------------------------------------------*/

/*------------------------------------------------------------------------------
 *      Exported functions
 *------------------------------------------------------------------------------*/

extern void CDCDSerial_Initialize(
    USBDDriver * pUsbd, uint8_t bInterfaceNb);

extern uint32_t CDCDSerial_RequestHandler(
    const USBGenericRequest *request);

extern void CDCDSerial_ConfigureFunction(
    USBGenericDescriptor * pDescriptors, uint16_t wLength);

extern uint32_t CDCDSerial_Write(
    void *data,
    uint32_t size,
    TransferCallback callback,
    void *argument);

extern uint32_t CDCDSerial_Read(
    void *data,
    uint32_t size,
    TransferCallback callback,
    void *argument);

extern void CDCDSerial_GetLineCoding(CDCLineCoding * pLineCoding);

extern uint8_t CDCDSerial_GetControlLineState(void);

extern uint16_t CDCDSerial_GetSerialState(void);

extern void CDCDSerial_SetSerialState(uint16_t serialState);

extern uint8_t CDCDSerial_LineCodingIsToChange(
    CDCLineCoding * pLineCoding);

extern void CDCDSerial_ControlLineStateChanged(
    uint8_t DTR,uint8_t RTS);

/**@}*/

#endif /*#ifndef CDCSERIAL_H*/

