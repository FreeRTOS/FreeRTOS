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

#ifndef trace_LEVEL
    #define trace_LEVEL     1
#endif

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include "tdes.h"
#include <board.h>
#include <utility/assert.h>
#include <utility/trace.h>

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Configures the triple-DES peripheral to cipher/decipher, use single-DES or
/// triple-DES, use two or three keys (when in triple-DES mode), start manually,
/// automatically or via the PDC and use the given operating mode (ECB, CBC,
/// CFB or OFB).
/// \param cipher  Encrypts if 1, decrypts if 0.
/// \param tdesmod  Single- or triple-DES mode.
/// \param keymod  Use two or three keys (must be 0 in single-DES mode).
/// \param smod  Start mode.
/// \param opmod  Encryption/decryption mode.
//------------------------------------------------------------------------------
void TDES_Configure(
    unsigned char cipher,
    unsigned int tdesmod,
    unsigned int keymod,
    unsigned int smod,
    unsigned int opmod)
{
    trace_LOG(trace_DEBUG, "-D- TDES_Configure()\n\r");
    SANITY_CHECK((cipher & 0xFFFFFFFE) == 0);
    SANITY_CHECK((tdesmod & 0xFFFFFFFD) == 0);
    SANITY_CHECK((keymod & 0xFFFFFFEF) == 0);
    SANITY_CHECK((smod & 0xFFFFFCFF) == 0);
    SANITY_CHECK((opmod & 0xFFFFCFFF) == 0);

    // Reset peripheral
    AT91C_BASE_TDES->TDES_CR = AT91C_TDES_SWRST;

    // Configure mode register
    AT91C_BASE_TDES->TDES_MR = cipher | tdesmod | keymod | smod | opmod;
}

//------------------------------------------------------------------------------
/// Starts the encryption or decryption process if the TDES peripheral is
/// configured in manual or PDC mode.
//------------------------------------------------------------------------------
void TDES_Start(void)
{
    trace_LOG(trace_DEBUG, "-D- TDES_Start()\n\r");
    SANITY_CHECK(((AT91C_BASE_TDES->TDES_MR & AT91C_TDES_SMOD) == AT91C_TDES_SMOD_MANUAL)
                 || ((AT91C_BASE_TDES->TDES_MR & AT91C_TDES_SMOD) == AT91C_TDES_SMOD_PDC));

    // Manual mode
    if ((AT91C_BASE_TDES->TDES_MR & AT91C_TDES_SMOD) == AT91C_TDES_SMOD_MANUAL) {

        AT91C_BASE_TDES->TDES_CR = AT91C_TDES_START;
    }
    // PDC mode
    else {

        AT91C_BASE_TDES->TDES_PTCR = AT91C_PDC_RXTEN | AT91C_PDC_TXTEN;
    }
}

//------------------------------------------------------------------------------
/// Returns the current status register value of the TDES peripheral.
//------------------------------------------------------------------------------
unsigned int TDES_GetStatus(void)
{
    trace_LOG(trace_DEBUG, "-D- TDES_GetStatus()\n\r");

    return AT91C_BASE_TDES->TDES_ISR;
}

//------------------------------------------------------------------------------
/// Sets the 64-bits keys (one, two or three depending on the configuration)
/// that shall be used by the TDES algorithm.
/// \param pKey1  Pointer to key #1.
/// \param pKey2  Pointer to key #2 (shall be 0 in single-DES mode).
/// \param pKey3  Pointer to key #3 (shall be 0 when using two keys).
//------------------------------------------------------------------------------
void TDES_SetKeys(
    const unsigned int *pKey1,
    const unsigned int *pKey2,
    const unsigned int *pKey3)
{
    trace_LOG(trace_DEBUG, "-D- TDES_SetKeys()\n\r");
    SANITY_CHECK(pKey1);
    SANITY_CHECK((pKey2 && ((AT91C_BASE_TDES->TDES_MR & AT91C_TDES_TDESMOD) == AT91C_TDES_TDESMOD))
                 || (!pKey2 && ((AT91C_BASE_TDES->TDES_MR & AT91C_TDES_TDESMOD) == 0)));
    SANITY_CHECK((pKey3
                  && ((AT91C_BASE_TDES->TDES_MR & AT91C_TDES_TDESMOD) == AT91C_TDES_TDESMOD)
                  && ((AT91C_BASE_TDES->TDES_MR & AT91C_TDES_KEYMOD) == 0))
                 ||
                 (!pKey3
                  && ((AT91C_BASE_TDES->TDES_MR & AT91C_TDES_TDESMOD) == AT91C_TDES_TDESMOD)
                  && ((AT91C_BASE_TDES->TDES_MR & AT91C_TDES_KEYMOD) == AT91C_TDES_KEYMOD))
                 ||
                 (!pKey3
                  && ((AT91C_BASE_TDES->TDES_MR & AT91C_TDES_TDESMOD) == 0)
                  && ((AT91C_BASE_TDES->TDES_MR & AT91C_TDES_KEYMOD) == 0)));

    // Write key #1
    if (pKey1) {

        AT91C_BASE_TDES->TDES_KEY1WxR[0] = pKey1[0];
        AT91C_BASE_TDES->TDES_KEY1WxR[1] = pKey1[1];
    }

    // Write key #2
    if (pKey1) {

        AT91C_BASE_TDES->TDES_KEY2WxR[0] = pKey2[0];
        AT91C_BASE_TDES->TDES_KEY2WxR[1] = pKey2[1];
    }

    // Write key #2
    if (pKey1) {

        AT91C_BASE_TDES->TDES_KEY3WxR[0] = pKey3[0];
        AT91C_BASE_TDES->TDES_KEY3WxR[1] = pKey3[1];
    }
}

//------------------------------------------------------------------------------
/// Sets the input data to encrypt/decrypt using TDES.
/// \param pInput  Pointer to the 64-bits input data.
//------------------------------------------------------------------------------
void TDES_SetInputData(const unsigned int *pInput)
{
    trace_LOG(trace_DEBUG, "-D- TDES_SetInputData()\n\r");
    SANITY_CHECK(pInput);

    AT91C_BASE_TDES->TDES_IDATAxR[0] = pInput[0];
    AT91C_BASE_TDES->TDES_IDATAxR[1] = pInput[1];
}

//------------------------------------------------------------------------------
/// Sets the input data buffer to encrypt/decrypt when in PDC mode.
/// \param pInput  Pointer to the input data.
/// \param size  Size of buffer in bytes.
//------------------------------------------------------------------------------
void TDES_SetInputBuffer(const unsigned int *pInput, unsigned int size)
{
    trace_LOG(trace_DEBUG, "-D- TDES_SetInputBuffer()\n\r");
    SANITY_CHECK(pInput);
    SANITY_CHECK((size > 0) && ((size % 8) == 0));

    AT91C_BASE_TDES->TDES_TPR = (unsigned int) pInput;
    AT91C_BASE_TDES->TDES_TCR = size / 4;
}

//------------------------------------------------------------------------------
/// Stores the output data from the last TDES operation into the given 64-bits
/// buffers.
/// \param pOutput  Pointer to a 64-bits output buffer.
//------------------------------------------------------------------------------
void TDES_GetOutputData(unsigned int *pOutput)
{
    trace_LOG(trace_DEBUG, "-D- TDES_GetOutputData()\n\r");
    SANITY_CHECK(pOutput);

    pOutput[0] = AT91C_BASE_TDES->TDES_ODATAxR[0];
    pOutput[1] = AT91C_BASE_TDES->TDES_ODATAxR[1];
}

//------------------------------------------------------------------------------
/// Sets the output buffer which will receive the encrypted/decrypted data when
/// using the PDC.
/// \param pOutput  Pointer to the output data.
/// \param size  Size of buffer in bytes.
//------------------------------------------------------------------------------
void TDES_SetOutputBuffer(unsigned int *pOutput, unsigned int size)
{
    trace_LOG(trace_DEBUG, "-D- TDES_SetOutputBuffer()\n\r");
    SANITY_CHECK(pOutput);
    SANITY_CHECK((size > 0) && ((size % 8) == 0));

    AT91C_BASE_TDES->TDES_RPR = (unsigned int) pOutput;
    AT91C_BASE_TDES->TDES_RCR = size / 4;
}

//------------------------------------------------------------------------------
/// Sets the initialization vector to use when the TDES algorithm is configured
/// in a chained block mode (CBC, CFB or OFB).
/// \param pVector  Pointer to the 64-bits vector.
//------------------------------------------------------------------------------
void TDES_SetVector(const unsigned int *pVector)
{
    trace_LOG(trace_DEBUG, "-D- TDES_SetVector()\n\r");
    SANITY_CHECK(pVector);

    AT91C_BASE_TDES->TDES_IVxR[0] = pVector[0];
    AT91C_BASE_TDES->TDES_IVxR[1] = pVector[1];
}

