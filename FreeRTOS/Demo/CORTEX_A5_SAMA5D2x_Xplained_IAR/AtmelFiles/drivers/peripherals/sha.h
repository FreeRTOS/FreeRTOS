/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
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

#ifndef _SHA_
#define _SHA_

/*------------------------------------------------------------------------------
 *         Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

/*----------------------------------------------------------------------------*/
/*         Exported functions                                                 */
/*----------------------------------------------------------------------------*/

/**
 * \brief Starts Manual hash algorithm process.
 */
extern void sha_start(void);

/**
 * \brief Resets the SHA. A software triggered hardware reset of the
 * SHA interface is performed.
 */
extern void sha_soft_reset(void);

/**
 * \brief Indicates that the next block to process is the first one of
 * a message.
 */
extern void sha_first_block(void);

/**
 * \brief Configures an SHA peripheral with the specified parameters.
 *  \param mode  Desired value for the SHA mode register (see the datasheet).
 */
extern void sha_configure(uint32_t mode);

/**
 * \brief Enables the selected interrupts sources on a SHA peripheral.
 * \param sources  Bitwise OR of selected interrupt sources.
 */
extern void sha_enable_it(uint32_t sources);

/**
 * \brief Disables the selected interrupts sources on a SHA peripheral.
 * \param sources  Bitwise OR of selected interrupt sources.
 */
extern void sha_disable_it(uint32_t sources);

/**
 * \brief Get the current status register of the given SHA peripheral.
 * \return  SHA status register.
 */
extern uint32_t sha_get_status(void);

/**
 * \brief Set the 32-bit Input Data registers allow to load the data block used for hash processing.
 * \param data Pointer data block.
 * \param len 512/1024-bits block size
 */
extern void sha_set_input(uint32_t * data, uint8_t len);

/**
 * \brief Getread the resulting message digest and to write the second part of the message block when the
* SHA algorithm is SHA-384 or SHA-512.
 * \param data pointer to the word that has been encrypted/decrypted..
 */
extern void sha_get_output(uint32_t * data);

#endif				/* #ifndef _SHA_ */
