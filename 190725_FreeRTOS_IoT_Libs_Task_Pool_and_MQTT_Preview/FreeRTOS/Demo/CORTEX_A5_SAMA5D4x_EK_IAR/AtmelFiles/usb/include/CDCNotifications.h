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
 *  Definitions and methods for USB CDC Notifications.
 */

#ifndef _CDCNOTIFICATIONS_H_
#define _CDCNOTIFICATIONS_H_
/** \addtogroup usb_cdc
 *@{
 */

/*----------------------------------------------------------------------------
 *         Includes
 *----------------------------------------------------------------------------*/

#include <stdint.h>

/*----------------------------------------------------------------------------
 *         Definitions
 *----------------------------------------------------------------------------*/

/** \addtogroup cdc_serial_states CDC SerialState bits
 *      @{
 * This page lists the bit map for CDC Serial States.
 *
 * - \ref CDCSerialState_RXDRIVER
 * - \ref CDCSerialState_TXCARRIER
 * - \ref CDCSerialState_BREAK
 * - \ref CDCSerialState_RINGSIGNAL
 * - \ref CDCSerialState_FRAMING
 * - \ref CDCSerialState_PARITY
 * - \ref CDCSerialState_OVERRUN
 */

/** Indicates the receiver carrier signal is present */
#define CDCSerialState_RXDRIVER         (1 << 0)
/** Indicates the transmission carrier signal is present */
#define CDCSerialState_TXCARRIER        (1 << 1)
/** Indicates a break has been detected */
#define CDCSerialState_BREAK            (1 << 2)
/** Indicates a ring signal has been detected */
#define CDCSerialState_RINGSIGNAL       (1 << 3)
/** Indicates a framing error has occured */
#define CDCSerialState_FRAMING          (1 << 4)
/** Indicates a parity error has occured */
#define CDCSerialState_PARITY           (1 << 5)
/** Indicates a data overrun error has occured */
#define CDCSerialState_OVERRUN          (1 << 6)
/**      @}*/

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
/** USB CDC SerialState struct (bitmap) */
typedef struct _CDCSerialState {
    uint16_t bRxCarrier:1,  /**< State of receive carrier detection (V2.4 signal
                                 109 and RS-232 signal DCD) */
             bTxCarrier:1,  /**< State of transmission carrier */
             bBreak:1,      /**< State of break detection */
             bRingSignal:1, /**< State of ring signal */
             bFraming:1,    /**< Framing error */
             bParity:1,     /**< Parity error */
             bOverRun:1,    /**< Received data discarded due to overrun error */
             reserved:9;    /**< Reserved */
} __attribute__ ((__packed__)) CDCSerialState;

#pragma pack()

/*----------------------------------------------------------------------------
 *         Functions
 *----------------------------------------------------------------------------*/

/**@}*/
#endif /* #ifndef _CDCNOTIFICATIONS_H_ */

