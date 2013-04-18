/* random.h
 *
 * Copyright (C) 2006-2012 Sawtooth Consulting Ltd.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */


#ifndef CTAO_CRYPT_RANDOM_H
#define CTAO_CRYPT_RANDOM_H

#include <cyassl/ctaocrypt/arc4.h>

#ifdef __cplusplus
    extern "C" {
#endif


#if defined(USE_WINDOWS_API)
    #if defined(_WIN64)
        typedef unsigned __int64 ProviderHandle;
        /* type HCRYPTPROV, avoid #include <windows.h> */
    #else
        typedef unsigned long ProviderHandle;
    #endif
#endif


/* OS specific seeder */
typedef struct OS_Seed {
    #if defined(USE_WINDOWS_API)
        ProviderHandle handle;
    #else
        int fd;
    #endif
} OS_Seed;

CYASSL_LOCAL
int GenerateSeed(OS_Seed* os, byte* seed, word32 sz);


/* secure Random Nnumber Generator */
typedef struct RNG {
    OS_Seed seed;
    Arc4    cipher;
} RNG;


CYASSL_API int  InitRng(RNG*);
CYASSL_API void RNG_GenerateBlock(RNG*, byte*, word32 sz);
CYASSL_API byte RNG_GenerateByte(RNG*);


#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* CTAO_CRYPT_RANDOM_H */

