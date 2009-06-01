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

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include "aes.h"
#include <board.h>
#include <utility/trace.h>
#include <utility/assert.h>

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Configures the AES peripheral to encrypt/decrypt, start mode (manual, auto,
/// PDC) and operating mode (ECB, CBC, OFB, CFB, CTR).
/// \param cipher  Indicates if the peripheral should encrypt or decrypt data.
/// \param smode  Start mode.
/// \param opmode  Operating mode.
//------------------------------------------------------------------------------
void AES_Configure(
    unsigned char cipher,
    unsigned int smode,
    unsigned int opmode)
{
    TRACE_DEBUG("AES_Configure()\n\r");
    SANITY_CHECK((cipher & 0xFFFFFFFE) == 0);
    SANITY_CHECK((smode & 0xFFFFFCFF) == 0);
    SANITY_CHECK((opmode & 0xFFFF8FFF) == 0);

    // Reset the peripheral first
    AT91C_BASE_AES->AES_CR = AT91C_AES_SWRST;

    // Configure mode register
    AT91C_BASE_AES->AES_MR = cipher | smode | opmode;
}

//------------------------------------------------------------------------------
/// Sets the key used by the AES algorithm to cipher the plain text or
/// decipher the encrypted text.
/// \param pKey  Pointer to a 16-bytes cipher key.
//------------------------------------------------------------------------------
void AES_SetKey(const unsigned int *pKey)
{
    TRACE_DEBUG("AES_SetKey()\n\r");
    SANITY_CHECK(pKey);

    AT91C_BASE_AES->AES_KEYWxR[0] = pKey[0];
    AT91C_BASE_AES->AES_KEYWxR[1] = pKey[1];
    AT91C_BASE_AES->AES_KEYWxR[2] = pKey[2];
    AT91C_BASE_AES->AES_KEYWxR[3] = pKey[3];
}

//------------------------------------------------------------------------------
/// Sets the initialization vector that is used to encrypt the plain text or
/// decrypt the cipher text in chained block modes (CBC, CFB, OFB & CTR).
/// \param pVector  Pointer to a 16-bytes initialization vector.
//------------------------------------------------------------------------------
void AES_SetVector(const unsigned int *pVector)
{
    TRACE_DEBUG("AES_SetVector()\n\r");
    SANITY_CHECK(pVector);

    AT91C_BASE_AES->AES_IVxR[0] = pVector[0];
    AT91C_BASE_AES->AES_IVxR[1] = pVector[1];
    AT91C_BASE_AES->AES_IVxR[2] = pVector[2];
    AT91C_BASE_AES->AES_IVxR[3] = pVector[3];
}

//------------------------------------------------------------------------------
/// Sets the input data of the AES algorithm (i.e. plain text in cipher mode,
/// ciphered text in decipher mode). If auto mode is active, the encryption is
/// started automatically after writing the last word.
/// \param pData  Pointer to the 16-bytes data to cipher/decipher.
//------------------------------------------------------------------------------
void AES_SetInputData(const unsigned int *pData)
{
    TRACE_DEBUG("AES_SetInputData()\n\r");
    SANITY_CHECK(pData);

    AT91C_BASE_AES->AES_IDATAxR[0] = pData[0];
    AT91C_BASE_AES->AES_IDATAxR[1] = pData[1];
    AT91C_BASE_AES->AES_IDATAxR[2] = pData[2];
    AT91C_BASE_AES->AES_IDATAxR[3] = pData[3];
}

//------------------------------------------------------------------------------
/// Stores the result of the last AES operation (encrypt/decrypt) in the
/// provided buffer.
/// \param pData  Pointer to a 16-bytes buffer.
//------------------------------------------------------------------------------
void AES_GetOutputData(unsigned int *pData)
{
    TRACE_DEBUG("AES_GetOutputData()\n\r");
    SANITY_CHECK(pData);

    pData[0] = AT91C_BASE_AES->AES_ODATAxR[0];
    pData[1] = AT91C_BASE_AES->AES_ODATAxR[1];
    pData[2] = AT91C_BASE_AES->AES_ODATAxR[2];
    pData[3] = AT91C_BASE_AES->AES_ODATAxR[3];
}

//------------------------------------------------------------------------------
/// Sets the input buffer to use when in PDC mode.
/// \param pInput  Pointer to the input buffer.
//------------------------------------------------------------------------------
void AES_SetInputBuffer(const unsigned int *pInput)
{
    TRACE_DEBUG("AES_SetInputBuffer()\n\r");
    SANITY_CHECK(pInput);

    AT91C_BASE_AES->AES_TPR = (unsigned int) pInput;
    AT91C_BASE_AES->AES_TCR = 4;
}

//------------------------------------------------------------------------------
/// Sets the output buffer to use when in PDC mode.
/// \param pOutput  Pointer to the output buffer.
//------------------------------------------------------------------------------
void AES_SetOutputBuffer(unsigned int *pOutput)
{
    TRACE_DEBUG("AES_SetOutputBuffer()\n\r");
    SANITY_CHECK(pOutput);

    AT91C_BASE_AES->AES_RPR = (unsigned int) pOutput;
    AT91C_BASE_AES->AES_RCR = 4;
}

//------------------------------------------------------------------------------
/// Starts the encryption/decryption process when in manual or PDC mode. In
/// manual mode, the key and input data must have been entered using
/// AES_SetKey() and AES_SetInputData(). In PDC mode, the key, input & output
/// buffer must have been set using AES_SetKey(), AES_SetInputBuffer() and
/// AES_SetOutputBuffer().
//------------------------------------------------------------------------------
void AES_Start(void)
{
    TRACE_DEBUG("AES_Start()\n\r");
    SANITY_CHECK(((AT91C_BASE_AES->AES_MR & AT91C_AES_SMOD) == AT91C_AES_SMOD_MANUAL)
                 || ((AT91C_BASE_AES->AES_MR & AT91C_AES_SMOD) == AT91C_AES_SMOD_PDC));

    // Manual mode
    if ((AT91C_BASE_AES->AES_MR & AT91C_AES_SMOD) == AT91C_AES_SMOD_MANUAL) {

        AT91C_BASE_AES->AES_CR = AT91C_AES_START;
    }
    // PDC
    else {

        AT91C_BASE_AES->AES_PTCR = AT91C_PDC_RXTEN | AT91C_PDC_TXTEN;
    }
}

//------------------------------------------------------------------------------
/// Returns the current value of the AES interrupt status register.
//------------------------------------------------------------------------------
unsigned int AES_GetStatus(void)
{
    TRACE_DEBUG("AES_GetStatus()\n\r");

    return AT91C_BASE_AES->AES_ISR;
}

