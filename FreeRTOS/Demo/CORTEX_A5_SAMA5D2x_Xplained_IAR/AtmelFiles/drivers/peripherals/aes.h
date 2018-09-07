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

#ifndef _AES_
#define _AES_

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "chip.h"

/*------------------------------------------------------------------------------*/
/*         Definition                                                           */
/*------------------------------------------------------------------------------*/
#define AES_MR_CIPHER_ENCRYPT 1
#define AES_MR_CIPHER_DECRYPT 0
/*------------------------------------------------------------------------------*/
/*         Exported functions                                                   */
/*------------------------------------------------------------------------------*/

/**
 * \brief Starts Manual encryption/decryption process.
 */
void aes_start(void);

/**
 * \brief Resets the AES.
 * A software triggered hardware reset of the AES interface is performed.
 */
void aes_soft_reset(void);

/**
 * \brief Configures an AES peripheral with the specified parameters.
 *  \param mode  Desired value for the AES mode register (see the datasheet).
 */
void aes_configure(uint32_t mode);

/**
 * \brief Enables the selected interrupts sources on a AES peripheral.
 * \param sources  Bitwise OR of selected interrupt sources.
 */
void aes_enable_it(uint32_t sources);

/**
 * \brief Disables the selected interrupts sources on a AES peripheral.
 * \param sources  Bitwise OR of selected interrupt sources.
 */
void aes_disable_it(uint32_t sources);

/**
 * \brief Get the current status register of the given AES peripheral.
 * \return  AES status register.
 */
extern uint32_t aes_get_status(void);

/**
 * \brief Set the 128-bit/192-bit/256-bit cryptographic key used for
 * encryption/decryption.
 * \param key  Pointer to a 16/24/32 bytes cipher key.
 * \param len  Length of the key, in bytes.
 */
void aes_write_key(const uint32_t * key, uint32_t len);

/**
 * \brief Set the for 32-bit input Data allow to set the 128-bit data block used
 * for encryption/decryption.
 * \param data  Pointer to the 16-bytes data to cipher/decipher.
 */
void aes_set_input(uint32_t * data);

/**
 * \brief Get the four 32-bit data contain the 128-bit data block which has
 * been encrypted/decrypted.
 * \param data  Pointer to the word that has been encrypted/decrypted..
 */
void aes_get_output(uint32_t * data);

/**
 * \brief Set four 64-bit initialization vector data block, which is used by
 * some modes of operation as an additional initial input.
 * \param vector  Pointer to the word of the initialization vector.
 */
void aes_set_vector(const uint32_t * vector);

/**
 * \brief Set Length in bytes of the Additional Authenticated Data that are to
 * be processed.
 * \param len  Length.
 */
void aes_set_aad_len(uint32_t len);

/**
 * \brief Set Length in bytes of the plaintext/ciphertext data (that is, the C
 * portion of the message) that are to be processed.
 * \param len  Length.
 */
void aes_set_data_len(uint32_t len);

/**
 * \brief Set The four 32-bit Hash Word registers expose the intermediate GHASH
 * value. May be read to save the current GHASH value so processing can later be
 * resumed, presumably on a later message fragment.
 * Modes of operation as an additional initial input.
 * \param hash  Pointer to the word of the hash.
 */
void aes_set_gcm_hash(uint32_t * hash);

/**
 * \brief Get The four 32-bit Tag which contain the final 128-bit GCM
 * Authentication tag 'T' when GCM processing is complete.
 * \param tag  Pointer to the word of the tag.
 */
void aes_get_gcm_tag(uint32_t * tag);

/**
 * \brief Reports the current value of the 32-bit GCM counter.
 * \param counter  Pointer to value of GCM counter.
 */
void aes_get_gcm_counter(uint32_t * counter);

/**
 * \brief Get the four 32-bit data containing the 128-bit H value computed from
 * the KEYW value.
 * \param h  Pointer to the word that has been encrypted/decrypted.
 */
void aes_get_gcm_hash_subkey(uint32_t * h);

#endif				/* #ifndef _AES_ */
