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

extern void AES_Start(void);
extern void AES_SoftReset(void);
extern void AES_Recount(void);
extern void AES_Configure(uint32_t mode);
extern void AES_EnableIt(uint32_t sources);
extern void AES_DisableIt(uint32_t sources);
extern uint32_t AES_GetStatus(void);
extern void AES_WriteKey(const uint32_t *pKey, uint32_t keyLength);
extern void AES_SetInput(uint32_t *data);
extern void AES_GetOutput(uint32_t *data);
extern void AES_SetVector(const uint32_t *pVector);
extern void AES_SetAadLen(uint32_t len);
extern void AES_SetDataLen(uint32_t len);
extern void AES_SetGcmHash(uint32_t * hash);
extern void AES_GetGcmTag(uint32_t * tag);
extern void AES_GetGcmCounter(uint32_t * counter);
extern void AES_GetGcmH(uint32_t *h);


#endif /* #ifndef _AES_ */
