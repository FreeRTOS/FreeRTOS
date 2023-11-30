/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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

#ifndef _RSTC_H
#define _RSTC_H

/*---------------------------------------------------------------------------
 *         Includes
 *---------------------------------------------------------------------------*/

#include <stdint.h>

/*---------------------------------------------------------------------------
 *         Exported functions
 *---------------------------------------------------------------------------*/

void RSTC_ConfigureMode(uint32_t rmr);

void RSTC_SetUserResetEnable(uint8_t enable);

void RSTC_SetUserResetInterruptEnable(uint8_t enable);

void RSTC_SetExtResetLength(uint8_t powl);

void RSTC_ProcessorReset(void);

void RSTC_ExtReset(void);

uint8_t RSTC_GetNrstLevel(void);

uint8_t RSTC_IsUserResetDetected(void);

uint8_t RSTC_IsBusy(void);

uint32_t RSTC_GetStatus(void);

#endif /* #ifndef _RSTC_H */

