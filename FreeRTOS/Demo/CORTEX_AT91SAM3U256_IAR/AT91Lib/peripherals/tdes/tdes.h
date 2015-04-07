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

#ifndef TDES_H
#define TDES_H

//------------------------------------------------------------------------------
/// \unit
///
/// !Purpose
/// 
/// Methods to manage the Triple DES (3DES)
/// 
/// !Usage
///
/// -# Configure TDES
/// -# Sets the key used by the TDES algorithm
/// -# Sets the input data of the TDES algorithm
/// -# Starts the encryption/decryption process
/// -# Stores the result of the last TDES operation
///
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

extern void TDES_Configure(
    unsigned char cipher,
    unsigned int tdesmod,
    unsigned int keymod,
    unsigned int smod,
    unsigned int opmod);

extern void TDES_Start(void);

extern unsigned int TDES_GetStatus(void);

extern void TDES_SetKeys(
    const unsigned int *pKey1,
    const unsigned int *pKey2,
    const unsigned int *pKey3);

extern void TDES_SetInputData(const unsigned int *pInput);

extern void TDES_SetInputBuffer(const unsigned int *pInput, unsigned int size);

extern void TDES_GetOutputData(unsigned int *pOutput);

extern void TDES_SetOutputBuffer(unsigned int *pOutput, unsigned int size);

extern void TDES_SetVector(const unsigned int *pVector);

#endif //#ifndef TDES_H
