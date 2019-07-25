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

#ifndef EFC_H
#define EFC_H

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include <board.h>

#ifdef BOARD_FLASH_EFC

//------------------------------------------------------------------------------
//         Constants
//------------------------------------------------------------------------------

/// Number of GPNVMs available on each chip.
#if defined(at91sam7s16) || defined(at91sam7s161) || defined(at91sam7s32) \
    || defined(at91sam7s321) || defined(at91sam7s64) || defined(at91sam7s128) \
    || defined(at91sam7s256) || defined(at91sam7s512)

    #define EFC_NUM_GPNVMS          2

#elif defined(at91sam7se32) || defined(at91sam7se256) || defined(at91sam7se512) \
      || defined(at91sam7x128) || defined(at91sam7x256) || defined(at91sam7x512) \
      || defined(at91sam7xc128) || defined(at91sam7xc256) || defined(at91sam7xc512) \

    #define EFC_NUM_GPNVMS          3

#elif defined(at91sam7a3)

    #define EFC_NUM_GPNVMS          0
#endif

// Missing FRDY bit for SAM7A3
#if defined(at91sam7a3)
    #define AT91C_MC_FRDY       (AT91C_MC_EOP | AT91C_MC_EOL)
#endif

// No security bit on SAM7A3
#if defined(at91sam7a3)
    #define EFC_NO_SECURITY_BIT
#endif

//------------------------------------------------------------------------------
//         Types
//------------------------------------------------------------------------------

// For chips which do not define AT91S_EFC
#if !defined(AT91C_BASE_EFC) && !defined(AT91C_BASE_EFC0)
typedef struct _AT91S_EFC {

    AT91_REG EFC_FMR;
    AT91_REG EFC_FCR;
    AT91_REG EFC_FSR;

} AT91S_EFC, *AT91PS_EFC;
	#define AT91C_BASE_EFC       (AT91_CAST(AT91PS_EFC)	0xFFFFFF60) 
#endif	

//------------------------------------------------------------------------------
//         Functions
//------------------------------------------------------------------------------

extern void EFC_SetMasterClock(unsigned int mck);

extern void EFC_EnableIt(AT91S_EFC *pEfc, unsigned int sources);

extern void EFC_DisableIt(AT91S_EFC *pEfc, unsigned int sources);

extern void EFC_SetEraseBeforeProgramming(AT91S_EFC *pEfc, unsigned char enable);

extern void EFC_TranslateAddress(
    unsigned int address,
    AT91S_EFC **ppEfc,
    unsigned short *pPage,
    unsigned short *pOffset);

extern void EFC_ComputeAddress(
    AT91S_EFC *pEfc,
    unsigned short page,
    unsigned short offset,
    unsigned int *pAddress);

extern void EFC_StartCommand(
    AT91S_EFC *pEfc,
    unsigned char command,
    unsigned short argument);

extern unsigned char EFC_PerformCommand(
    AT91S_EFC *pEfc,
    unsigned char command,
    unsigned short argument);

extern unsigned int EFC_GetStatus(AT91S_EFC *pEfc);

#endif //#ifdef BOARD_FLASH_EFC
#endif //#ifndef EFC_H

