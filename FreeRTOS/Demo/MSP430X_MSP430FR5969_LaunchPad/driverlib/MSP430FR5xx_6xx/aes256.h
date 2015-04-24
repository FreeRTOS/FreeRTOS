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
// aes256.h - Driver for the AES256 Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_AES256_H__
#define __MSP430WARE_AES256_H__

#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_AES256__

//*****************************************************************************
//
// If building with a C++ compiler, make all of the definitions in this header
// have a C binding.
//
//*****************************************************************************
#ifdef __cplusplus
extern "C"
{
#endif

//*****************************************************************************
//
// The following are values that can be passed to the keyLength parameter for
// functions: AES256_setCipherKey(), AES256_setDecipherKey(), and
// AES256_startSetDecipherKey().
//
//*****************************************************************************
#define AES256_KEYLENGTH_128BIT                                             128
#define AES256_KEYLENGTH_192BIT                                             192
#define AES256_KEYLENGTH_256BIT                                             256

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the AES256_getErrorFlagStatus() function.
//
//*****************************************************************************
#define AES256_ERROR_OCCURRED                                          AESERRFG
#define AES256_NO_ERROR                                                    0x00

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the AES256_isBusy() function.
//
//*****************************************************************************
#define AES256_BUSY                                                     AESBUSY
#define AES256_NOT_BUSY                                                    0x00

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the AES256_getInterruptStatus() function.
//
//*****************************************************************************
#define AES256_READY_INTERRUPT                                         AESRDYIE
#define AES256_NOTREADY_INTERRUPT                                          0x00

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Loads a 128, 192 or 256 bit cipher key to AES256 module.
//!
//! This function loads a 128, 192 or 256 bit cipher key to AES256 module.
//! Requires both a key as well as the length of the key provided. Acceptable
//! key lengths are AES256_KEYLENGTH_128BIT, AES256_KEYLENGTH_192BIT, or
//! AES256_KEYLENGTH_256BIT
//!
//! \param baseAddress is the base address of the AES256 module.
//! \param cipherKey is a pointer to an uint8_t array with a length of 16 bytes
//!        that contains a 128 bit cipher key.
//! \param keyLength is the length of the key.
//!        Valid values are:
//!        - \b AES256_KEYLENGTH_128BIT
//!        - \b AES256_KEYLENGTH_192BIT
//!        - \b AES256_KEYLENGTH_256BIT
//!
//! \return STATUS_SUCCESS or STATUS_FAIL of key loading
//
//*****************************************************************************
extern uint8_t AES256_setCipherKey(uint16_t baseAddress,
                                   const uint8_t *cipherKey,
                                   uint16_t keyLength);

//*****************************************************************************
//
//! \brief Encrypts a block of data using the AES256 module.
//!
//! The cipher key that is used for encryption should be loaded in advance by
//! using function AES256_setCipherKey()
//!
//! \param baseAddress is the base address of the AES256 module.
//! \param data is a pointer to an uint8_t array with a length of 16 bytes that
//!        contains data to be encrypted.
//! \param encryptedData is a pointer to an uint8_t array with a length of 16
//!        bytes in that the encrypted data will be written.
//!
//! \return None
//
//*****************************************************************************
extern void AES256_encryptData(uint16_t baseAddress,
                               const uint8_t *data,
                               uint8_t *encryptedData);

//*****************************************************************************
//
//! \brief Decrypts a block of data using the AES256 module.
//!
//! This function requires a pregenerated decryption key. A key can be loaded
//! and pregenerated by using function AES256_setDecipherKey() or
//! AES256_startSetDecipherKey(). The decryption takes 167 MCLK.
//!
//! \param baseAddress is the base address of the AES256 module.
//! \param data is a pointer to an uint8_t array with a length of 16 bytes that
//!        contains encrypted data to be decrypted.
//! \param decryptedData is a pointer to an uint8_t array with a length of 16
//!        bytes in that the decrypted data will be written.
//!
//! \return None
//
//*****************************************************************************
extern void AES256_decryptData(uint16_t baseAddress,
                               const uint8_t *data,
                               uint8_t *decryptedData);

//*****************************************************************************
//
//! \brief Sets the decipher key.
//!
//! The API AES256_startSetDecipherKey or AES256_setDecipherKey must be invoked
//! before invoking AES256_startDecryptData.
//!
//! \param baseAddress is the base address of the AES256 module.
//! \param cipherKey is a pointer to an uint8_t array with a length of 16 bytes
//!        that contains a 128 bit cipher key.
//! \param keyLength is the length of the key.
//!        Valid values are:
//!        - \b AES256_KEYLENGTH_128BIT
//!        - \b AES256_KEYLENGTH_192BIT
//!        - \b AES256_KEYLENGTH_256BIT
//!
//! \return STATUS_SUCCESS or STATUS_FAIL of key loading
//
//*****************************************************************************
extern uint8_t AES256_setDecipherKey(uint16_t baseAddress,
                                     const uint8_t *cipherKey,
                                     uint16_t keyLength);

//*****************************************************************************
//
//! \brief Clears the AES256 ready interrupt flag.
//!
//! This function clears the AES256 ready interrupt flag. This flag is
//! automatically cleared when AES256ADOUT is read, or when AES256AKEY or
//! AES256ADIN is written. This function should be used when the flag needs to
//! be reset and it has not been automatically cleared by one of the previous
//! actions.
//!
//! \param baseAddress is the base address of the AES256 module.
//!
//! Modified bits are \b AESRDYIFG of \b AESACTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void AES256_clearInterrupt(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Gets the AES256 ready interrupt flag status.
//!
//! This function checks the AES256 ready interrupt flag. This flag is
//! automatically cleared when AES256ADOUT is read, or when AES256AKEY or
//! AES256ADIN is written. This function can be used to confirm that this has
//! been done.
//!
//! \param baseAddress is the base address of the AES256 module.
//!
//! \return One of the following:
//!         - \b AES256_READY_INTERRUPT
//!         - \b AES256_NOTREADY_INTERRUPT
//!         \n indicating the status of the AES256 ready status
//
//*****************************************************************************
extern uint32_t AES256_getInterruptStatus(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Enables AES256 ready interrupt.
//!
//! Enables AES256 ready interrupt. This interrupt is reset by a PUC, but not
//! reset by AES256_reset.
//!
//! \param baseAddress is the base address of the AES256 module.
//!
//! Modified bits are \b AESRDYIE of \b AESACTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void AES256_enableInterrupt(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Disables AES256 ready interrupt.
//!
//! Disables AES256 ready interrupt. This interrupt is reset by a PUC, but not
//! reset by AES256_reset.
//!
//! \param baseAddress is the base address of the AES256 module.
//!
//! Modified bits are \b AESRDYIE of \b AESACTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void AES256_disableInterrupt(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Resets AES256 Module immediately.
//!
//! This function performs a software reset on the AES256 Module, note that
//! this does not affect the AES256 ready interrupt.
//!
//! \param baseAddress is the base address of the AES256 module.
//!
//! Modified bits are \b AESSWRST of \b AESACTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void AES256_reset(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Starts an encryption process on the AES256 module.
//!
//! The cipher key that is used for decryption should be loaded in advance by
//! using function AES256_setCipherKey(). This is a non-blocking equivalent of
//! AES256_encryptData(). It is recommended to use the interrupt functionality
//! to check for procedure completion then use the AES256_getDataOut() API to
//! retrieve the encrypted data.
//!
//! \param baseAddress is the base address of the AES256 module.
//! \param data is a pointer to an uint8_t array with a length of 16 bytes that
//!        contains data to be encrypted.
//!
//! \return None
//
//*****************************************************************************
extern void AES256_startEncryptData(uint16_t baseAddress,
                                    const uint8_t *data);

//*****************************************************************************
//
//! \brief Decrypts a block of data using the AES256 module.
//!
//! This is the non-blocking equivalent of AES256_decryptData(). This function
//! requires a pregenerated decryption key. A key can be loaded and
//! pregenerated by using function AES256_setDecipherKey() or
//! AES256_startSetDecipherKey(). The decryption takes 167 MCLK. It is
//! recommended to use interrupt to check for procedure completion then use the
//! AES256_getDataOut() API to retrieve the decrypted data.
//!
//! \param baseAddress is the base address of the AES256 module.
//! \param data is a pointer to an uint8_t array with a length of 16 bytes that
//!        contains encrypted data to be decrypted.
//!
//! \return None
//
//*****************************************************************************
extern void AES256_startDecryptData(uint16_t baseAddress,
                                    const uint8_t *data);

//*****************************************************************************
//
//! \brief Sets the decipher key
//!
//! The API AES256_startSetDecipherKey() or AES256_setDecipherKey() must be
//! invoked before invoking AES256_startDecryptData.
//!
//! \param baseAddress is the base address of the AES256 module.
//! \param cipherKey is a pointer to an uint8_t array with a length of 16 bytes
//!        that contains a 128 bit cipher key.
//! \param keyLength is the length of the key.
//!        Valid values are:
//!        - \b AES256_KEYLENGTH_128BIT
//!        - \b AES256_KEYLENGTH_192BIT
//!        - \b AES256_KEYLENGTH_256BIT
//!
//! \return STATUS_SUCCESS or STATUS_FAIL of key loading
//
//*****************************************************************************
extern uint8_t AES256_startSetDecipherKey(uint16_t baseAddress,
                                          const uint8_t *cipherKey,
                                          uint16_t keyLength);

//*****************************************************************************
//
//! \brief Reads back the output data from AES256 module.
//!
//! This function is meant to use after an encryption or decryption process
//! that was started and finished by initiating an interrupt by use of
//! AES256_startEncryptData or AES256_startDecryptData functions.
//!
//! \param baseAddress is the base address of the AES256 module.
//! \param outputData is a pointer to an uint8_t array with a length of 16
//!        bytes in that the data will be written.
//!
//! \return STATUS_SUCCESS if data is valid, otherwise STATUS_FAIL
//
//*****************************************************************************
extern uint8_t AES256_getDataOut(uint16_t baseAddress,
                                 uint8_t *outputData);

//*****************************************************************************
//
//! \brief Gets the AES256 module busy status.
//!
//! Gets the AES256 module busy status. If a key or data are written while the
//! AES256 module is busy, an error flag will be thrown.
//!
//! \param baseAddress is the base address of the AES256 module.
//!
//! \return One of the following:
//!         - \b AES256_BUSY
//!         - \b AES256_NOT_BUSY
//!         \n indicating if the AES256 module is busy
//
//*****************************************************************************
extern uint16_t AES256_isBusy(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Clears the AES256 error flag.
//!
//! Clears the AES256 error flag that results from a key or data being written
//! while the AES256 module is busy.
//!
//! \param baseAddress is the base address of the AES256 module.
//!
//! Modified bits are \b AESERRFG of \b AESACTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void AES256_clearErrorFlag(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Gets the AES256 error flag status.
//!
//! Checks the AES256 error flag that results from a key or data being written
//! while the AES256 module is busy. If the flag is set, it needs to be cleared
//! using AES256_clearErrorFlag.
//!
//! \param baseAddress is the base address of the AES256 module.
//!
//! \return One of the following:
//!         - \b AES256_ERROR_OCCURRED
//!         - \b AES256_NO_ERROR
//!         \n indicating the error flag status
//
//*****************************************************************************
extern uint32_t AES256_getErrorFlagStatus(uint16_t baseAddress);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_AES256_H__
