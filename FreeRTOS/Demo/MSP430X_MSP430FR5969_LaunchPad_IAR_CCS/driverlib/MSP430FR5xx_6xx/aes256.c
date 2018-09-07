/* --COPYRIGHT--,BSD
 * Copyright (c) 2014, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * --/COPYRIGHT--*/
//*****************************************************************************
//
// aes256.c - Driver for the aes256 Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup aes256_api aes256
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_AES256__
#include "aes256.h"

#include <assert.h>

uint8_t AES256_setCipherKey(uint16_t baseAddress,
                            const uint8_t * cipherKey,
                            uint16_t keyLength)
{
    uint8_t i;
    uint16_t sCipherKey;

    HWREG16(baseAddress + OFS_AESACTL0) &= (~(AESKL_1 + AESKL_2));

    switch(keyLength)
    {
    case AES256_KEYLENGTH_128BIT:
        HWREG16(baseAddress + OFS_AESACTL0) |= AESKL__128;
        break;

    case AES256_KEYLENGTH_192BIT:
        HWREG16(baseAddress + OFS_AESACTL0) |= AESKL__192;
        break;

    case AES256_KEYLENGTH_256BIT:
        HWREG16(baseAddress + OFS_AESACTL0) |= AESKL__256;
        break;

    default:
        return(STATUS_FAIL);
    }

    keyLength = keyLength / 8;

    for(i = 0; i < keyLength; i = i + 2)
    {
        sCipherKey = (uint16_t)(cipherKey[i]);
        sCipherKey = sCipherKey | ((uint16_t)(cipherKey[i + 1]) << 8);
        HWREG16(baseAddress + OFS_AESAKEY) = sCipherKey;
    }

    // Wait until key is written
    while(0x00 == (HWREG16(baseAddress + OFS_AESASTAT) & AESKEYWR))
    {
        ;
    }
    return(STATUS_SUCCESS);
}

void AES256_encryptData(uint16_t baseAddress,
                        const uint8_t * data,
                        uint8_t * encryptedData)
{
    uint8_t i;
    uint16_t tempData = 0;
    uint16_t tempVariable = 0;

    // Set module to encrypt mode
    HWREG16(baseAddress + OFS_AESACTL0) &= ~AESOP_3;

    // Write data to encrypt to module
    for(i = 0; i < 16; i = i + 2)
    {
        tempVariable = (uint16_t)(data[i]);
        tempVariable = tempVariable | ((uint16_t)(data[i + 1]) << 8);
        HWREG16(baseAddress + OFS_AESADIN) = tempVariable;
    }

    // Key that is already written shall be used
    // Encryption is initialized by setting AESKEYWR to 1
    HWREG16(baseAddress + OFS_AESASTAT) |= AESKEYWR;

    // Wait unit finished ~167 MCLK
    while(AESBUSY == (HWREG16(baseAddress + OFS_AESASTAT) & AESBUSY))
    {
        ;
    }

    // Write encrypted data back to variable
    for(i = 0; i < 16; i = i + 2)
    {
        tempData = HWREG16(baseAddress + OFS_AESADOUT);
        *(encryptedData + i) = (uint8_t)tempData;
        *(encryptedData + i + 1) = (uint8_t)(tempData >> 8);
    }
}

void AES256_decryptData(uint16_t baseAddress,
                        const uint8_t * data,
                        uint8_t * decryptedData)
{
    uint8_t i;
    uint16_t tempData = 0;
    uint16_t tempVariable = 0;

    // Set module to decrypt mode
    HWREG16(baseAddress + OFS_AESACTL0) |= (AESOP_3);

    // Write data to decrypt to module
    for(i = 0; i < 16; i = i + 2)
    {
        tempVariable = (uint16_t)(data[i + 1] << 8);
        tempVariable = tempVariable | ((uint16_t)(data[i]));
        HWREG16(baseAddress + OFS_AESADIN) = tempVariable;
    }

    // Key that is already written shall be used
    // Now decryption starts
    HWREG16(baseAddress + OFS_AESASTAT) |= AESKEYWR;

    // Wait unit finished ~167 MCLK
    while(AESBUSY == (HWREG16(baseAddress + OFS_AESASTAT) & AESBUSY))
    {
        ;
    }

    // Write encrypted data back to variable
    for(i = 0; i < 16; i = i + 2)
    {
        tempData = HWREG16(baseAddress + OFS_AESADOUT);
        *(decryptedData + i) = (uint8_t)tempData;
        *(decryptedData + i + 1) = (uint8_t)(tempData >> 8);
    }
}

uint8_t AES256_setDecipherKey(uint16_t baseAddress,
                              const uint8_t * cipherKey,
                              uint16_t keyLength)
{
    uint8_t i;
    uint16_t tempVariable = 0;

    // Set module to decrypt mode
    HWREG16(baseAddress + OFS_AESACTL0) &= ~(AESOP0);
    HWREG16(baseAddress + OFS_AESACTL0) |= AESOP1;

    switch(keyLength)
    {
    case AES256_KEYLENGTH_128BIT:
        HWREG16(baseAddress + OFS_AESACTL0) |= AESKL__128;
        break;

    case AES256_KEYLENGTH_192BIT:
        HWREG16(baseAddress + OFS_AESACTL0) |= AESKL__192;
        break;

    case AES256_KEYLENGTH_256BIT:
        HWREG16(baseAddress + OFS_AESACTL0) |= AESKL__256;
        break;

    default:
        return(STATUS_FAIL);
    }

    keyLength = keyLength / 8;

    // Write cipher key to key register
    for(i = 0; i < keyLength; i = i + 2)
    {
        tempVariable = (uint16_t)(cipherKey[i]);
        tempVariable = tempVariable | ((uint16_t)(cipherKey[i + 1]) << 8);
        HWREG16(baseAddress + OFS_AESAKEY) = tempVariable;
    }

    // Wait until key is processed ~52 MCLK
    while((HWREG16(baseAddress + OFS_AESASTAT) & AESBUSY) == AESBUSY)
    {
        ;
    }

    return(STATUS_SUCCESS);
}

void AES256_clearInterrupt(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_AESACTL0) &= ~AESRDYIFG;
}

uint32_t AES256_getInterruptStatus(uint16_t baseAddress)
{
    return ((HWREG16(baseAddress + OFS_AESACTL0) & AESRDYIFG) << 0x04);
}

void AES256_enableInterrupt(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_AESACTL0) |= AESRDYIE;
}

void AES256_disableInterrupt(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_AESACTL0) &= ~AESRDYIE;
}

void AES256_reset(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_AESACTL0) |= AESSWRST;
}

void AES256_startEncryptData(uint16_t baseAddress,
                             const uint8_t * data)
{
    uint8_t i;
    uint16_t tempVariable = 0;

    // Set module to encrypt mode
    HWREG16(baseAddress + OFS_AESACTL0) &= ~AESOP_3;

    // Write data to encrypt to module
    for(i = 0; i < 16; i = i + 2)
    {
        tempVariable = (uint16_t)(data[i]);
        tempVariable = tempVariable | ((uint16_t)(data[i + 1 ]) << 8);
        HWREG16(baseAddress + OFS_AESADIN) = tempVariable;
    }

    // Key that is already written shall be used
    // Encryption is initialized by setting AESKEYWR to 1
    HWREG16(baseAddress + OFS_AESASTAT) |= AESKEYWR;
}

void AES256_startDecryptData(uint16_t baseAddress,
                             const uint8_t * data)
{
    uint8_t i;
    uint16_t tempVariable = 0;

    // Set module to decrypt mode
    HWREG16(baseAddress + OFS_AESACTL0) |= (AESOP_3);

    // Write data to decrypt to module
    for(i = 0; i < 16; i = i + 2)
    {
        tempVariable = (uint16_t)(data[i + 1] << 8);
        tempVariable = tempVariable | ((uint16_t)(data[i]));
        HWREG16(baseAddress + OFS_AESADIN) = tempVariable;
    }

    // Key that is already written shall be used
    // Now decryption starts
    HWREG16(baseAddress + OFS_AESASTAT) |= AESKEYWR;
}

uint8_t AES256_startSetDecipherKey(uint16_t baseAddress,
                                   const uint8_t * cipherKey,
                                   uint16_t keyLength)
{
    uint8_t i;
    uint16_t tempVariable = 0;

    HWREG16(baseAddress + OFS_AESACTL0) &= ~(AESOP0);
    HWREG16(baseAddress + OFS_AESACTL0) |= AESOP1;

    switch(keyLength)
    {
    case AES256_KEYLENGTH_128BIT:
        HWREG16(baseAddress + OFS_AESACTL0) |= AESKL__128;
        break;

    case AES256_KEYLENGTH_192BIT:
        HWREG16(baseAddress + OFS_AESACTL0) |= AESKL__192;
        break;

    case AES256_KEYLENGTH_256BIT:
        HWREG16(baseAddress + OFS_AESACTL0) |= AESKL__256;
        break;

    default:
        return(STATUS_FAIL);
    }

    keyLength = keyLength / 8;

    // Write cipher key to key register
    for(i = 0; i < keyLength; i = i + 2)
    {
        tempVariable = (uint16_t)(cipherKey[i]);
        tempVariable = tempVariable | ((uint16_t)(cipherKey[i + 1]) << 8);
        HWREG16(baseAddress + OFS_AESAKEY) = tempVariable;
    }

    return(STATUS_SUCCESS);
}

uint8_t AES256_getDataOut(uint16_t baseAddress,
                          uint8_t *outputData)
{
    uint8_t i;
    uint16_t tempData = 0;

    // If module is busy, exit and return failure
    if(AESBUSY == (HWREG16(baseAddress + OFS_AESASTAT) & AESBUSY))
    {
        return(STATUS_FAIL);
    }

    // Write encrypted data back to variable
    for(i = 0; i < 16; i = i + 2)
    {
        tempData = HWREG16(baseAddress + OFS_AESADOUT);
        *(outputData + i) = (uint8_t)tempData;
        *(outputData + i + 1) = (uint8_t)(tempData >> 8);
    }

    return(STATUS_SUCCESS);
}

uint16_t AES256_isBusy(uint16_t baseAddress)
{
    return (HWREG16(baseAddress + OFS_AESASTAT) & AESBUSY);
}

void AES256_clearErrorFlag(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_AESACTL0) &= ~AESERRFG;
}

uint32_t AES256_getErrorFlagStatus(uint16_t baseAddress)
{
    return (HWREG16(baseAddress + OFS_AESACTL0) & AESERRFG);
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for aes256_api
//! @}
//
//*****************************************************************************
