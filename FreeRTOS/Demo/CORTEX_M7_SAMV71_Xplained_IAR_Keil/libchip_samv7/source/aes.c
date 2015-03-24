/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2013, Atmel Corporation
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

/** \addtogroup aes_module Working with AES
 * \ingroup peripherals_module
 * The AES driver provides the interface to configure and use the AES peripheral.
 * \n
 *
 * The Advanced Encryption Standard (AES) specifies a FIPS-approved cryptographic algorithm
 * that can be used to protect electronic data. The AES algorithm is a symmetric block 
 * cipher that can encrypt (encipher) and decrypt (decipher) information.
 * Encryption converts data to an unintelligible form called ciphertext. 
 * Decrypting the ciphertext converts the data back into its original form, 
 * called plaintext. The CIPHER bit in the AES Mode Register (AES_MR) allows selection 
 * between the encryption and the decryption processes. The AES is capable of using cryptographic 
 * keys of 128/192/256 bits to encrypt and decrypt data in blocks of 128 bits. 
 * This 128-bit/192-bit/256-bit key is defined in the Key Registers (AES_KEYWRx) and set by 
 * AES_WriteKey(). The input to the encryption processes of the CBC, CFB, and OFB modes includes,
 * in addition to the plaintext, a 128-bit data block called the initialization vector (IV), 
 * which must be set with AES_SetVector(). 
 * The initialization vector is used in an initial step in the encryption of a message and 
 * in the corresponding decryption of the message. The Initialization Vector Registers are 
 * also used by the CTR mode to set the counter value.
 *
 * To Enable a AES encryption and decryption,the user has to follow these few steps:
 * <ul>
 * <li> A software triggered hardware reset of the AES interface is performed by AES_SoftReset().</li>
 * <li> Configure AES algorithm mode, key mode, start mode and operation mode by AES_Configure(). </li>
 * <li> Input AES data for encryption and decryption with function AES_SetInput() </li>
 * <li> Set AES key with fucntion AES_WriteKey(). </li>
 * <li> To start the encryption or the decryption process with AES_Start()</li>
 * <li> To get the encryption or decryption reslut by AES_GetOutput() </li>
 * </ul>
 *
 *
 * For more accurate information, please look at the AES section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref aes.c\n
 * \ref aes.h\n
 */
/*@{*/
/*@}*/


/**
 * \file
 *
 * Implementation of Advanced Encryption Standard (AES)
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Starts Manual encryption/decryption process.
 */
void AES_Start(void)
{
    AES->AES_CR = AES_CR_START;
}

/**
 * \brief Resets the AES. A software triggered hardware reset of the AES interface is performed.
 */
void AES_SoftReset(void)
{
    AES->AES_CR = AES_CR_SWRST;
}


/**
 * \brief Configures an AES peripheral with the specified parameters.
 *  \param mode  Desired value for the AES mode register (see the datasheet).
 */
void AES_Configure(uint32_t mode)
{
    AES->AES_MR = mode; 
}

/**
 * \brief Enables the selected interrupts sources on a AES peripheral.
 * \param sources  Bitwise OR of selected interrupt sources.
 */
void AES_EnableIt(uint32_t sources)
{
    AES->AES_IER = sources;
}

/**
 * \brief Disables the selected interrupts sources on a AES peripheral.
 * \param sources  Bitwise OR of selected interrupt sources.
 */
void AES_DisableIt(uint32_t sources)
{
    AES->AES_IDR = sources;
}

/**
 * \brief Get the current status register of the given AES peripheral.
 * \return  AES status register.
 */
uint32_t AES_GetStatus(void)
{
    return AES->AES_ISR;
}

/**
 * \brief Set the 128-bit/192-bit/256-bit cryptographic key used for encryption/decryption.
 * \param pKey Pointer to a 16/24/32 bytes cipher key.
 * \param keyLength length of key
 */
void AES_WriteKey(const uint32_t *pKey, uint32_t keyLength)
{
    AES->AES_KEYWR[0] = pKey[0];
    AES->AES_KEYWR[1] = pKey[1];
    AES->AES_KEYWR[2] = pKey[2];
    AES->AES_KEYWR[3] = pKey[3];

    if( keyLength >= 24 ) {
        AES->AES_KEYWR[4] = pKey[4];
        AES->AES_KEYWR[5] = pKey[5];
    }
    if( keyLength == 32 ) {
        AES->AES_KEYWR[6] = pKey[6];
        AES->AES_KEYWR[7] = pKey[7];
    }
}

/**
 * \brief Set the for 32-bit input Data allow to set the 128-bit data block used for encryption/decryption.
 * \param data Pointer to the 16-bytes data to cipher/decipher.
 */
void AES_SetInput(uint32_t *data)
{
    uint8_t i;
    for (i = 0; i< 4; i++)
        AES->AES_IDATAR[i] = data[i];
}

/**
 * \brief Get the four 32-bit data contain the 128-bit data block which has been encrypted/decrypted.
 * \param data pointer to the word that has been encrypted/decrypted..
 */
void AES_GetOutput(uint32_t *data)
{
    uint8_t i;
    for (i = 0; i< 4; i++) 
        data[i] = AES->AES_ODATAR[i];
}

/**
 * \brief Set four 64-bit initialization vector data block, which is used by some
 * modes of operation as an additional initial input.
 * \param pVector point to the word of the initialization vector.
 */
void AES_SetVector(const uint32_t *pVector)
{
    AES->AES_IVR[0] = pVector[0];
    AES->AES_IVR[1] = pVector[1];
    AES->AES_IVR[2] = pVector[2];
    AES->AES_IVR[3] = pVector[3];
}


/**
 * \brief Set Length in bytes of the AAD data that is to be processed.
 * \param len Length.
 */
void AES_SetAadLen(uint32_t len)
{
    AES->AES_AADLENR = len;
}

/**
 * \brief Set Length in bytes of the Length in bytes of the 
 * plaintext/ciphertext (C) data that is to be processed..
 * \param len Length.
 */
void AES_SetDataLen(uint32_t len)
{
    AES->AES_CLENR = len;
}

/**
 * \brief Set The four 32-bit Hash Word registers expose the intermediate GHASH value. 
 * May be read to save the current GHASH value so processing can later be resumed, 
 * presumably on a later message fragment. modes of operation as an additional initial input.
 * \param hash point to the word of the hash.
 */
void AES_SetGcmHash(uint32_t * hash)
{
    uint8_t i;
    for (i = 0; i< 4; i++) 
        AES->AES_GHASHR[i] = hash[i];
}


/**
 * \brief Get The four 32-bit Tag which contain the final 128-bit GCM Authentication tag 
 * ¡°T¡± when GCM processing is complete.
 * \param tag point to the word of the tag.
 */
void AES_GetGcmTag(uint32_t * tag)
{
    uint8_t i;
    for (i = 0; i< 4; i++) 
        tag[i] = AES->AES_TAGR[i] ;
}

/**
 * \brief Reports the current value of the 32-bit GCM counter
 * \param counter Point to value of GCM counter.
 */
void AES_GetGcmCounter(uint32_t * counter)
{
    *counter = AES->AES_CTRR;
}


/**
 * \brief Get the four 32-bit data contain the 128-bit H value computed from the KEYW value
 * \param data point to the word that has been encrypted/decrypted..
 */
void AES_GetGcmH(uint32_t *h)
{
    uint8_t i;
    for (i = 0; i< 4; i++) 
        h[i] = AES->AES_GCMHR[i];
}


