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
 *  Definitions and classes for USB CDC class requests
 *  (mostly for ACM).
 *
 * \section CDCLineCoding
 *
 * -# Initialize a CDCLineCoding instance using CDCLineCoding_Initialize.
 * -# Send a CDCLineCoding object to the host in response to a GetLineCoding
 *    request.
 * -# Receive a CDCLineCoding object from the host after a SetLineCoding
 *    request.
 *  
 */

#ifndef _CDCREQUESTS_H_
#define _CDCREQUESTS_H_
/** \addtogroup usb_cdc
 *@{
 */

/*----------------------------------------------------------------------------
 *         Includes
 *----------------------------------------------------------------------------*/

#include <stdint.h>

#include <USBRequests.h>

/*----------------------------------------------------------------------------
 *         Definitions
 *----------------------------------------------------------------------------*/

/** \addtogroup usb_cdc_request USB CDC Request Codes
 *      @{
 * This section lists USB CDC Request Codes.
 * - \ref CDCGenericRequest_SETLINECODING
 * - \ref CDCGenericRequest_GETLINECODING
 * - \ref CDCGenericRequest_SETCONTROLLINESTATE
 */

/** SetLineCoding request code. */
#define CDCGenericRequest_SETLINECODING             0x20
/** GetLineCoding request code. */
#define CDCGenericRequest_GETLINECODING             0x21
/** SetControlLineState request code. */
#define CDCGenericRequest_SETCONTROLLINESTATE       0x22
/**     @}*/

/** \addtogroup usb_cdc_ctrl_line_state USB CDC ControlLineState bitmap
 *      @{
 * This section lists CDC ControlLineState bitmap.
 * - \ref CDCControlLineState_DTR, CDCControlLineState_DTE_PRESENT
 * - \ref CDCControlLineState_RTS, CDCControlLineState_CARRIER_ON
 */
/** Indicates to DCE if DTE is present or not. */
#define CDCControlLineState_DTE_PRESENT                     (1 << 0)
/** RS232 signal DTR: Data Terminal Ready. */
#define CDCControlLineState_DTR                             (1 << 0)
/** Carrier control for half duplex modems. */
#define CDCControlLineState_CARRIER_ON                      (1 << 1)
/** RS232 signal RTS: Request to send. */
#define CDCControlLineState_RTS                             (1 << 1)
/**     @}*/

/** \addtogroup usb_cdc_stop USB CDC LineCoding StopBits
 *      @{
 * This section lists Stop Bits for CDC Line Coding.
 * - \ref CDCLineCoding_ONESTOPBIT
 * - \ref CDCLineCoding_ONE5STOPBIT
 * - \ref CDCLineCoding_TWOSTOPBITS
 */
/** The transmission protocol uses one stop bit. */
#define CDCLineCoding_ONESTOPBIT            0
/** The transmission protocol uses 1.5 stop bit. */
#define CDCLineCoding_ONE5STOPBIT           1
/** The transmissin protocol uses two stop bits. */
#define CDCLineCoding_TWOSTOPBITS           2
/**     @}*/

/** \addtogroup usb_cdc_parity USB CDC LineCoding ParityCheckings
 *      @{
 * This section lists Parity checkings for CDC Line Coding.
 * - \ref CDCLineCoding_NOPARITY
 * - \ref CDCLineCoding_ODDPARITY
 * - \ref CDCLineCoding_EVENPARITY
 * - \ref CDCLineCoding_MARKPARITY
 * - \ref CDCLineCoding_SPACEPARITY
 */
/** No parity checking. */
#define CDCLineCoding_NOPARITY              0
/** Odd parity checking. */
#define CDCLineCoding_ODDPARITY             1
/** Even parity checking. */
#define CDCLineCoding_EVENPARITY            2
/** Mark parity checking. */
#define CDCLineCoding_MARKPARITY            3
/** Space parity checking. */
#define CDCLineCoding_SPACEPARITY           4
/**     @}*/

/*----------------------------------------------------------------------------
 *         Types
 *----------------------------------------------------------------------------*/
#pragma pack(1)
#if defined   ( __CC_ARM   ) /* Keil ¦ÌVision 4 */
#elif defined ( __ICCARM__ ) /* IAR Ewarm */
#define __attribute__(...)
#define __packed__  packed
#elif defined (  __GNUC__  ) /* GCC CS3 */
#define __packed__  aligned(1)
#endif

/**
 * \typedef CDCLineCoding
 * \brief Format of the data returned when a GetLineCoding request is received.
 */
typedef struct _CDCLineCoding {

    /** Data terminal rate in bits per second. */
    uint32_t dwDTERate;
    /** Number of stop bits.
        \sa usb_cdc_stop CDC LineCoding StopBits. */
    uint8_t bCharFormat;
    /** Type of parity checking used.
        \sa usb_cdc_parity CDC LineCoding ParityCheckings. */
    uint8_t bParityType;
    /** Number of data bits (5, 6, 7, 8 or 16). */
    uint8_t bDataBits;

} __attribute__ ((__packed__)) CDCLineCoding; /* GCC */

#pragma pack()

/*----------------------------------------------------------------------------
 *         Functions
 *----------------------------------------------------------------------------*/

extern uint8_t CDCSetControlLineStateRequest_IsDtePresent(
    const USBGenericRequest *request);

extern uint8_t CDCSetControlLineStateRequest_ActivateCarrier(
    const USBGenericRequest *request);

extern void CDCLineCoding_Initialize(CDCLineCoding *lineCoding,
                                     uint32_t bitrate,
                                     uint8_t stopbits,
                                     uint8_t parity,
                                     uint8_t databits);


/**@}*/
#endif /* #define _CDCREQUESTS_H_ */

