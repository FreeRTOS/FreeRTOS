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

/** \addtogroup aes_module Working with AES
 * \ingroup peripherals_module
 * The AES driver provides the interface to configure and use the AES
 * peripheral.
 * \n
 *
 * The Advanced Encryption Standard (AES) specifies a FIPS-approved
 * cryptographic algorithm that can be used to protect electronic data. The AES
 * algorithm is a symmetric block cipher that can encrypt (encipher) and decrypt
 * (decipher) information.
 * Encryption converts data to an unintelligible form called ciphertext.
 * Decrypting the ciphertext converts the data back into its original form,
 * called plaintext. The CIPHER bit in the AES Mode Register (AES_MR) allows
 * selection between the encryption and the decryption processes. The AES is
 * capable of using cryptographic keys of 128/192/256 bits to encrypt and
 * decrypt data in blocks of 128 bits.
 * This 128-bit/192-bit/256-bit key is defined in the Key Registers (AES_KEYWRx)
 * and set by aes_write_key(). The input to the encryption processes of the CBC,
 * CFB, and OFB modes includes, in addition to the plaintext, a 128-bit data
 * block called the initialization vector (IV), which must be set using
 * aes_set_vector(). The initialization vector is used in an initial step in the
 * encryption of a message and in the corresponding decryption of the message.
 * The Initialization Vector Registers are also used by the CTR mode to set the
 * counter value.
 *
 * To enable AES encryption and decryption, the user has to follow these few
 * steps:
 * <ul>
 * <li> A software triggered hardware reset of the AES interface is performed by
 * aes_soft_reset().</li>
 * <li> Configure AES algorithm mode, key mode, start mode and operation mode
 * with aes_configure().</li>
 * <li> Input AES data for encryption and decryption with function
 * aes_set_input().</li>
 * <li> Set AES key with fucntion aes_write_key().</li>
 * <li> To start the encryption or the decryption process with aes_start().</li>
 * <li> To get the encryption or decryption result by aes_get_output().</li>
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
#include "peripherals/aes.h"

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

void aes_start(void)
{
	AES->AES_CR = AES_CR_START;
}

void aes_soft_reset(void)
{
	AES->AES_CR = AES_CR_SWRST;
}

void aes_configure(uint32_t mode)
{
	AES->AES_MR = mode;
}

void aes_enable_it(uint32_t sources)
{
	AES->AES_IER = sources;
}

void aes_disable_it(uint32_t sources)
{
	AES->AES_IDR = sources;
}

uint32_t aes_get_status(void)
{
	return AES->AES_ISR;
}

void aes_write_key(const uint32_t * key, uint32_t len)
{
	AES->AES_KEYWR[0] = key[0];
	AES->AES_KEYWR[1] = key[1];
	AES->AES_KEYWR[2] = key[2];
	AES->AES_KEYWR[3] = key[3];

	if (len >= 24) {
		AES->AES_KEYWR[4] = key[4];
		AES->AES_KEYWR[5] = key[5];
	}
	if (len == 32) {
		AES->AES_KEYWR[6] = key[6];
		AES->AES_KEYWR[7] = key[7];
	}
}

void aes_set_input(uint32_t * data)
{
	uint8_t i;
	for (i = 0; i < 4; i++)
		AES->AES_IDATAR[i] = data[i];
}

void aes_get_output(uint32_t * data)
{
	uint8_t i;
	for (i = 0; i < 4; i++)
		data[i] = AES->AES_ODATAR[i];
}

void aes_set_vector(const uint32_t * vector)
{
	AES->AES_IVR[0] = vector[0];
	AES->AES_IVR[1] = vector[1];
	AES->AES_IVR[2] = vector[2];
	AES->AES_IVR[3] = vector[3];
}

void aes_set_aad_len(uint32_t len)
{
	AES->AES_AADLENR = len;
}

void aes_set_data_len(uint32_t len)
{
	AES->AES_CLENR = len;
}

void aes_set_gcm_hash(uint32_t * hash)
{
	uint8_t i;
	for (i = 0; i < 4; i++)
		AES->AES_GHASHR[i] = hash[i];
}

void aes_get_gcm_tag(uint32_t * tag)
{
	uint8_t i;
	for (i = 0; i < 4; i++)
		tag[i] = AES->AES_TAGR[i];
}

void aes_get_gcm_counter(uint32_t * counter)
{
	*counter = AES->AES_CTRR;
}

void aes_get_gcm_hash_subkey(uint32_t * h)
{
	uint8_t i;
	for (i = 0; i < 4; i++)
		h[i] = AES->AES_GCMHR[i];
}
