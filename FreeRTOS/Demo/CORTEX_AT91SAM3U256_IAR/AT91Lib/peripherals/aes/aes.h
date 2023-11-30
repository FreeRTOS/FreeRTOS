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

#ifndef AES_H
#define AES_H

//------------------------------------------------------------------------------
/// \unit
///
/// !Purpose
/// 
/// Methods to manage the Advanced Encryption Standard (AES)
/// 
/// !Usage
///
/// -# Configure AES
/// -# Sets the key used by the AES algorithm
/// -# Sets the input data of the AES algorithm
/// -# Starts the encryption/decryption process
/// -# Stores the result of the last AES operation
///
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

extern void AES_Configure(
    unsigned char cipher,
    unsigned int smode,
    unsigned int opmode);

extern void AES_SetKey(const unsigned int *pKey);

extern void AES_SetVector(const unsigned int *pVector);

extern void AES_SetInputData(const unsigned int *pData);

extern void AES_GetOutputData(unsigned int *pData);

extern void AES_SetInputBuffer(const unsigned int *pInput);

extern void AES_SetOutputBuffer(unsigned int *pOutput);

extern void AES_Start(void);

extern unsigned int AES_GetStatus(void);

#endif //#ifndef AES_H

