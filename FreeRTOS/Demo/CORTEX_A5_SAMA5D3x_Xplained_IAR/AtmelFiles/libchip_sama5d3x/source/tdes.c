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

/** \addtogroup tdes_module Working with TDES
 * \ingroup peripherals_module
 * The TDES driver provides the interface to configure and use the TDES peripheral.
 * \n
 *
 * The Data Encryption Standard (DES) and the Triple Data Encryption Algorithm (TDES) specify
 * FIPS-approved cryptographic algorithms that can be used to protect electronic data. The TDES
 * bit in the TDES Mode Register (TDES_MR) is used to select either the single DES or the Triple
 * DES mode by function TDES_Configure().
 * A DES is capable of using cryptographic keys of 64 bits to encrypt and decrypt data in blocks of
 * 64 bits, Date input can be set with TDES_SetInput(). This 64-bit key is defined in the Key 1 Word 
 * Registers (TDES_KEY1WRx) and set by TDES_WriteKey1. A TDES key consists of three DES keys, 
 * which is also referred to as a key bundle. These three 64-bit keys are defined, respectively, 
 * in the Key 1, 2 and 3 Word Registers (TDES_KEY1WRx, TDES_KEY2WRx and TDES_KEY3WRx). 
 * In Triple DES mode (TDESMOD set to 1), the KEYMOD bit in the TDES Mode Register is used to choose between a two- and a three-key
 * algorithm:
 *
 * To Enable a TDES encryption and decryption,the user has to follow these few steps:
 * <ul>
 * <li> A software triggered hardware reset of the TDES interface is performed by TDES_SoftReset().</li>
 * <li> Configure TDES algorithm mode, key mode, start mode and operation mode by TDES_Configure(). </li>
 * <li> Set DES key with fucntion TDES_WriteKey1(), TDES_WriteKey2(), or TDES_WriteKey3(). </li>
 * <li> Input TDES data for encryption and decryption with function TDES_SetInput() </li>
 * <li> To start the encryption or the decryption process with TDES_Start()</li>
 * <li> To get the encryption or decryption reslut by TDES_GetOutput() </li>
 * </ul>
 *
 * For more accurate information, please look at the TDES section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref tdes.c\n
 * \ref tdes.h\n
 */
/*@{*/
/*@}*/
/**
 * \file
 *
 * Implementation of Triple Data Encryption Standard (TDES).
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
void TDES_Start(void)
{
    TDES->TDES_CR = TDES_CR_START;
}

/**
 * \brief Resets the TDES. A software triggered hardware reset of the TDES interface is performed.
 */
void TDES_SoftReset(void)
{
    TDES->TDES_CR = TDES_CR_SWRST;
}

/**
 * \brief Restarts the countermeasures generator to an internal pre-defined value.
 */
void TDES_Recount(void)
{
    TDES->TDES_CR = TDES_CR_LOADSEED;
}

/**
 * \brief Configures an TDES peripheral with the specified parameters.
 *  \param mode  Desired value for the TDES mode register (see the datasheet).
 */
void TDES_Configure(uint32_t mode)
{
    TDES->TDES_MR = mode; 
}

/**
 * \brief Enables the selected interrupts sources on a TDES peripheral.
 * \param sources  Bitwise OR of selected interrupt sources.
 */
void TDES_EnableIt(uint32_t sources)
{
    TDES->TDES_IER = sources;
}

/**
 * \brief Disables the selected interrupts sources on a TDES peripheral.
 * \param sources  Bitwise OR of selected interrupt sources.
 */
void TDES_DisableIt(uint32_t sources)
{
    TDES->TDES_IDR = sources;
}

/**
 * \brief Get the current status register of the given TDES peripheral.
 * \return  TDES status register.
 */
uint32_t TDES_GetStatus(void)
{
    return TDES->TDES_ISR;
}

/**
 * \brief Set KEY1.
 * \param keyword0 key word 0
 * \param keyword0 key word 1
 */
void TDES_WriteKey1(uint32_t keyword0, uint32_t keyword1)
{
    TDES->TDES_KEY1WR[0] = keyword0;
    TDES->TDES_KEY1WR[1] = keyword1;
}

/**
 * \brief Set KEY2.
 * \param keyword0 key word 0
 * \param keyword0 key word 1
 */
void TDES_WriteKey2(uint32_t keyword0, uint32_t keyword1)
{
    TDES->TDES_KEY2WR[0] = keyword0;
    TDES->TDES_KEY2WR[1] = keyword1;
}

/**
 * \brief Set KEY3.
 * \param keyword0 key word 0
 * \param keyword0 key word 1
 */
void TDES_WriteKey3(uint32_t keyword0, uint32_t keyword1)
{
    TDES->TDES_KEY3WR[0] = keyword0;
    TDES->TDES_KEY3WR[1] = keyword1;
}

/**
 * \brief Set the two 32-bit input Data allow to set the 64-bit data block used for encryption/decryption.
 * \param data0 corresponds to the first word of the data to be encrypted/decrypted
 * \param data1 corresponds to the last word of the data to be encrypted/decrypted
 */
void TDES_SetInput(uint32_t data0, uint32_t data1)
{
    TDES->TDES_IDATAR[0] = data0;
    TDES->TDES_IDATAR[1] = data1;
}

/**
 * \brief Get the two 32-bit data contain the 64-bit data block which has been encrypted/decrypted.
 * \param data0 point to the first word.
 * \param data1 point to the last word.
 */
void TDES_GetOutput(uint32_t *data0, uint32_t *data1)
{
    *data0 = TDES->TDES_ODATAR[0];
    *data1 = TDES->TDES_ODATAR[1];
}

/**
 * \brief Set the 64-bit initialization vector data block, which is used by some
 * modes of operation as an additional initial input.
 * \param v0 corresponds to the first word of the initialization vector.
 * \param v1 corresponds to the last word  of the initialization vector.
 */
void TDES_SetVector(uint32_t v0, uint32_t v1)
{
    TDES->TDES_IVR[0] = v0;
    TDES->TDES_IVR[1] = v1;
}

/**
 * \brief Set the 6-bit complete rounds.
 * \param rounds corresponds to rounds+1 complete round.
 */
void TDES_SetXteaRounds(uint32_t rounds)
{
    TDES->TDES_XTEARNDR = rounds;
}

