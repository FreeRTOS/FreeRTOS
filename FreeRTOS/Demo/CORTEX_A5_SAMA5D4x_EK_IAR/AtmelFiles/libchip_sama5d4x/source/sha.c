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

/** \addtogroup sha_module Working with SHA
 * \ingroup peripherals_module
 * The SHA driver provides the interface to configure and use the SHA peripheral.
 * \n
 *
 * The Secure Hash Algorithm (SHA) module requires a padded message according to FIPS180-2
 * specification. The first block of the message must be indicated to the module by a specific 
 * command. The SHA module produces a N-bit message digest each time a block is written and
 * processing period ends. N is 160 for SHA1, 224 for SHA224, 256 for SHA256, 384 for SHA384,
 * 512 for SHA512.
 *
 * To Enable a SHA encryption and decrypt,the user has to follow these few steps:
 * <ul>
 * <li> Configure SHA algorithm mode, key mode, start mode and operation mode by SHA_Configure(). </li>
 * <li> Set SHA_FirstBlock() to indicates that the next block to process is the first one of a message.</li>
 * <li> Input data for encryption by SHA_SetInput(). </li>
 * <li> To start the encryption process with SHA_Start()</li>
 * <li> To get the encryption reslut by SHA_GetOutput() </li>
 * </ul>
 *
 * For more accurate information, please look at the SHA section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref sha.c\n
 * \ref sha.h\n
 */
/*@{*/
/*@}*/


/**
 * \file
 *
 * Implementation of Secure Hash Algorithm (SHA)
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"


/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/
 
/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Starts Manual hash algorithm process.
 */
void SHA_Start(void)
{
    SHA->SHA_CR = SHA_CR_START;
}

/**
 * \brief Resets the SHA. A software triggered hardware reset of the SHA interface is performed.
 */
void SHA_SoftReset(void)
{
    SHA->SHA_CR = SHA_CR_SWRST;
}

/**
 * \brief Indicates that the next block to process is the first one of a message.
 */
void SHA_FirstBlock(void)
{
    SHA->SHA_CR = SHA_CR_FIRST;
}

/**
 * \brief Configures an SHA peripheral with the specified parameters.
 *  \param mode  Desired value for the SHA mode register (see the datasheet).
 */
void SHA_Configure(uint32_t mode)
{
    SHA->SHA_MR = mode; 
}

/**
 * \brief Enables the selected interrupts sources on a SHA peripheral.
 * \param sources  Bitwise OR of selected interrupt sources.
 */
void SHA_EnableIt(uint32_t sources)
{
    SHA->SHA_IER = sources;
}

/**
 * \brief Disables the selected interrupts sources on a SHA peripheral.
 * \param sources  Bitwise OR of selected interrupt sources.
 */
void SHA_DisableIt(uint32_t sources)
{
    SHA->SHA_IDR = sources;
}

/**
 * \brief Get the current status register of the given SHA peripheral.
 * \return  SHA status register.
 */
uint32_t SHA_GetStatus(void)
{
    return SHA->SHA_ISR;
}

/**
 * \brief Set the 32-bit Input Data registers allow to load the data block used for hash processing.
 * \param data Pointer data block.
 * \param len 512/1024-bits block size
 */
void SHA_SetInput(uint32_t *data, uint8_t len)
{
    uint8_t i;
    uint8_t num;
    num = len <= 16 ? len: 16;
    for (i = 0; i < num ; i++)
        SHA->SHA_IDATAR[i] = (data[i]);
    num = len > 16 ? len - 16: 0;
    for (i = 0; i < num; i++)
        SHA->SHA_IODATAR[i] = (data[i+16]);
}

/**
 * \brief Getread the resulting message digest and to write the second part of the message block when the
* SHA algorithm is SHA-384 or SHA-512.
 * \param data pointer to the word that has been encrypted/decrypted..
 */
void SHA_GetOutput(uint32_t *data)
{
    uint8_t i;
    for (i = 0; i < 16; i++) 
        data[i] = SHA->SHA_IODATAR[i];
}
