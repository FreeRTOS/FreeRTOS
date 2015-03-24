/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2010, Atmel Corporation
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

/**
 * \file
 *
 * Interface for the AT25 Serialflash driver.
 *
 */

#ifndef AT25D_H
#define AT25D_H

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "at25_spi.h"

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
extern void AT25D_WaitReady(At25 *pAt25);

extern unsigned int AT25D_ReadJedecId(At25 *pAt25);

extern void AT25D_EnableWrite(At25 *pAt25);

extern void AT25D_DisableWrite(At25 *pAt25);
extern unsigned char AT25D_Unprotect(At25 *pAt25);

extern unsigned char AT25D_EraseChip(At25 *pAt25);

extern unsigned char AT25D_EraseBlock(At25 *pAt25, unsigned int address);
extern unsigned char AT25D_Erase64KBlock(At25 *pAt25, unsigned int address);

extern unsigned char AT25D_Write(
    At25 *pAt25,
    unsigned char *pData,
    unsigned int size,
    unsigned int address);

extern unsigned char AT25D_Read(
    At25 *pAt25,
    unsigned char *pData,
    unsigned int size,
    unsigned int address);

#endif // #ifndef AT25D_H

