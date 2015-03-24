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

/**
 * \file
 *
 * Interface for configuration the Two Wire Interface (TWI) peripheral.
 *
 */

#ifndef _TWI_
#define _TWI_

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "chip.h"

#include <stdint.h>

/*----------------------------------------------------------------------------
 *        Macros
 *----------------------------------------------------------------------------*/
/* Returns 1 if the TXRDY bit (ready to transmit data) is set in the given status register value.*/
#define TWI_STATUS_TXRDY(status) ((status & TWIHS_SR_TXRDY) == TWIHS_SR_TXRDY)

/* Returns 1 if the RXRDY bit (ready to receive data) is set in the given status register value.*/
#define TWI_STATUS_RXRDY(status) ((status & TWIHS_SR_RXRDY) == TWIHS_SR_RXRDY)

/* Returns 1 if the TXCOMP bit (transfer complete) is set in the given status register value.*/
#define TWI_STATUS_TXCOMP(status) ((status & TWIHS_SR_TXCOMP) == TWIHS_SR_TXCOMP)

#ifdef __cplusplus
 extern "C" {
#endif

/*----------------------------------------------------------------------------
 *        External function
 *----------------------------------------------------------------------------*/

extern void TWI_ConfigureMaster(Twihs *pTwi, uint32_t twck, uint32_t mck);

extern void TWI_ConfigureSlave(Twihs *pTwi, uint8_t slaveAddress);

extern void TWI_Stop(Twihs *pTwi);

extern void TWI_StartRead(
    Twihs *pTwi,
    uint8_t address,
    uint32_t iaddress,
    uint8_t isize);

extern uint8_t TWI_ReadByte(Twihs *pTwi);

extern void TWI_WriteByte(Twihs *pTwi, uint8_t byte);

extern void TWI_StartWrite(
    Twihs *pTwi,
    uint8_t address,
    uint32_t iaddress,
    uint8_t isize,
    uint8_t byte);

extern uint8_t TWI_ByteReceived(Twihs *pTwi);

extern uint8_t TWI_ByteSent(Twihs *pTwi);

extern uint8_t TWI_TransferComplete(Twihs *pTwi);

extern void TWI_EnableIt(Twihs *pTwi, uint32_t sources);

extern void TWI_DisableIt(Twihs *pTwi, uint32_t sources);

extern uint32_t TWI_GetStatus(Twihs *pTwi);

extern uint32_t TWI_GetMaskedStatus(Twihs *pTwi);

extern void TWI_SendSTOPCondition(Twihs *pTwi);

#ifdef __cplusplus
}
#endif

#endif /* #ifndef _TWI_ */
