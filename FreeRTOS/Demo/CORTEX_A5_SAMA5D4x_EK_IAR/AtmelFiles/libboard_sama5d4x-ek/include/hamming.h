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

#ifndef _HAMMING_
#define _HAMMING_

/*------------------------------------------------------------------------------
 *         Defines
 *------------------------------------------------------------------------------*/

/**
 *  These are the possible errors when trying to verify a block of data encoded
 *  using a Hamming code:
 *
 *  \section Errors
 *   - Hamming_ERROR_SINGLEBIT
 *   - Hamming_ERROR_ECC
 *   - Hamming_ERROR_MULTIPLEBITS
 */

/**  A single bit was incorrect but has been recovered. */
#define Hamming_ERROR_SINGLEBIT         1

/** The original code has been corrupted. */
#define Hamming_ERROR_ECC               2

/** Multiple bits are incorrect in the data and they cannot be corrected. */
#define Hamming_ERROR_MULTIPLEBITS      3

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

extern void Hamming_Compute256x( const uint8_t* pucData, uint32_t dwSize, uint8_t* pucCode ) ;

extern uint8_t Hamming_Verify256x( uint8_t* pucData, uint32_t dwSize, const uint8_t* pucCode ) ;

#endif /* _HAMMING_ */
