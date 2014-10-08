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

/** \addtogroup aesb_module Working with AESB
 * The TWI driver provides the interface to True Random Number Generator (AESB) passes the American NIST Special Publication 800-22 and Diehard
Random Tests Suites.
The AESB may be used as an entropy source for seeding an NIST approved DRNG (Deterministic RNG) as required by
FIPS PUB 140-2 and 140-3. use the TWI
 * peripheral.
 *
 * \section Usage
 * <ul>
 * <li> Configures a TWI peripheral to operate in master mode, at the given
 * frequency (in Hz) using TWI_Configure(). </li>
 * <li> Sends a STOP condition on the TWI using TWI_Stop().</li>
 * <li> Starts a read operation on the TWI bus with the specified slave using
 * TWI_StartRead(). Data must then be read using TWI_ReadByte() whenever
 * a byte is available (poll using TWI_ByteReceived()).</li>
 * <li> Starts a write operation on the TWI to access the selected slave using
 * TWI_StartWrite(). A byte of data must be provided to start the write;
 * other bytes are written next.</li>
 * <li> Sends a byte of data to one of the TWI slaves on the bus using TWI_WriteByte().
 * This function must be called once before TWI_StartWrite() with the first byte of data
 * to send, then it shall be called repeatedly after that to send the remaining bytes.</li>
 * <li> Check if a byte has been received and can be read on the given TWI
 * peripheral using TWI_ByteReceived().<
 * Check if a byte has been sent using TWI_ByteSent().</li>
 * <li> Check if the current transmission is complete (the STOP has been sent)
 * using TWI_TransferComplete().</li>
 * <li> Enables & disable the selected interrupts sources on a TWI peripheral
 * using TWI_EnableIt() and TWI_DisableIt().</li>
 * <li> Get current status register of the given TWI peripheral using
 * TWI_GetStatus(). Get current status register of the given TWI peripheral, but
 * masking interrupt sources which are not currently enabled using
 * TWI_GetMaskedStatus().</li>
 * </ul>
 * For more accurate information, please look at the TWI section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref twi.c\n
 * \ref twi.h.\n
*/
/*@{*/
/*@}*/

/**
 * \file
 *
 * Implementation of True Random Number Generator (AESB)
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
void AESB_Start(void)
{
    AESB->AESB_CR = AESB_CR_START;
}

/**
 * \brief Resets the AESB. A software triggered hardware reset of the AESB interface is performed.
 */
void AESB_SoftReset(void)
{
    AESB->AESB_CR = AESB_CR_SWRST;
}

/**
 * \brief Restarts the countermeasures generator to an internal pre-defined value.
 */
void AESB_Recount(void)
{
    AESB->AESB_CR = AESB_CR_LOADSEED;
}

/**
 * \brief Configures an AESB peripheral with the specified parameters.
 *  \param mode  Desired value for the AESB mode register (see the datasheet).
 */
void AESB_Configure(uint32_t mode)
{
    AESB->AESB_MR = mode; 
}

/**
 * \brief Enables the selected interrupts sources on a AESB peripheral.
 * \param sources  Bitwise OR of selected interrupt sources.
 */
void AESB_EnableIt(uint32_t sources)
{
    AESB->AESB_IER = sources;
}

/**
 * \brief Disables the selected interrupts sources on a AESB peripheral.
 * \param sources  Bitwise OR of selected interrupt sources.
 */
void AESB_DisableIt(uint32_t sources)
{
    AESB->AESB_IDR = sources;
}

/**
 * \brief Get the current status register of the given AESB peripheral.
 * \return  AESB status register.
 */
uint32_t AESB_GetStatus(void)
{
    return AESB->AESB_ISR;
}

/**
 * \brief Set the 128-bit cryptographic key used for encryption/decryption.
 * \param pKey Pointer to a 16 bytes cipher key.
 * \param keyLength length of key
 */
void AESB_WriteKey(const uint32_t *pKey)
{
    AESB->AESB_KEYWR[0] = pKey[0];
    AESB->AESB_KEYWR[1] = pKey[1];
    AESB->AESB_KEYWR[2] = pKey[2];
    AESB->AESB_KEYWR[3] = pKey[3];
}

/**
 * \brief Set the for 32-bit input Data allow to set the 128-bit data block used for encryption/decryption.
 * \param data Pointer to the 16-bytes data to cipher/decipher.
 */
void AESB_SetInput(uint32_t *data)
{
    uint8_t i;
    for (i = 0; i < 4; i++)
        AESB->AESB_IDATAR[i] = data[i];
}

/**
 * \brief Get the four 32-bit data contain the 128-bit data block which has been encrypted/decrypted.
 * \param data pointer to the word that has been encrypted/decrypted..
 */
void AESB_GetOutput(uint32_t *data)
{
    uint8_t i;
    for (i = 0; i < 4; i++) 
        data[i] = AESB->AESB_ODATAR[i];
}

/**
 * \brief Set four 64-bit initialization vector data block, which is used by some
 * modes of operation as an additional initial input.
 * \param pVector point to the word of the initialization vector.
 */
void AESB_SetVector(const uint32_t *pVector)
{
    AESB->AESB_IVR[0] = pVector[0];
    AESB->AESB_IVR[1] = pVector[1];
    AESB->AESB_IVR[2] = pVector[2];
    AESB->AESB_IVR[3] = pVector[3];
}

