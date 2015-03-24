/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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

#ifndef _TWID_
#define _TWID_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include <stdint.h>

/*----------------------------------------------------------------------------
 *        Definition
 *----------------------------------------------------------------------------*/

/** TWI driver is currently busy. */
#define TWID_ERROR_BUSY              1

   /** Transfer is still pending.*/
#define ASYNC_STATUS_PENDING        0xFF
#ifdef __cplusplus
 extern "C" {
#endif

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

   /*----------------------------------------------------------------------------
 *        Type
 *----------------------------------------------------------------------------*/
/** \brief Asynchronous transfer descriptor. */
typedef struct _Async
{
    /** Asynchronous transfer status.*/
    volatile uint32_t status ;
    /** Callback function to invoke when transfer completes or fails.*/
    void *callback ;
    /** Driver storage area; do not use.*/
    uint8_t pStorage[9] ;
} Async ;

/** \brief TWI driver structure. Holds the internal state of the driver.*/
typedef struct _Twid
{
    /** Pointer to the underlying TWI peripheral.*/
    Twihs *pTwi ;
    /** Current asynchronous transfer being processed.*/
    Async *pTransfer ;
} Twid;

/*----------------------------------------------------------------------------
 *        Export functions
 *----------------------------------------------------------------------------*/
extern void TWID_Initialize( Twid *pTwid, Twihs *pTwi ) ;
extern void TWID_DmaInitialize(Twid *pTwid, Twihs *pTwi);

extern void TWID_Handler( Twid *pTwid ) ;

extern uint32_t ASYNC_IsFinished( Async* pAsync ) ;

extern uint8_t TWID_Read(
    Twid *pTwid,
    uint8_t address,
    uint32_t iaddress,
    uint8_t isize,
    uint8_t *pData,
    uint32_t num,
    Async *pAsync);

extern uint8_t TWID_Write(
    Twid *pTwid,
    uint8_t address,
    uint32_t iaddress,
    uint8_t isize,
    uint8_t *pData,
    uint32_t num,
    Async *pAsync);

extern uint8_t TWID_DmaRead(
    Twid *pTwid,
    uint8_t address,
    uint32_t iaddress,
    uint8_t isize,
    uint8_t *pData,
    uint32_t num,
    Async *pAsync,
    uint8_t TWI_ID);

extern uint8_t TWID_DmaWrite(
    Twid *pTwid,
    uint8_t address,
    uint32_t iaddress,
    uint8_t isize,
    uint8_t *pData,
    uint32_t num,
    Async *pAsync,
    uint8_t TWI_ID);

#ifdef __cplusplus
}
#endif

#endif //#ifndef TWID_H

