/* random.h
 *
 * Copyright (C) 2006-2014 wolfSSL Inc.
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */


#ifndef CTAO_CRYPT_RANDOM_H
#define CTAO_CRYPT_RANDOM_H

#include <cyassl/ctaocrypt/types.h>

#if defined(HAVE_HASHDRBG) || defined(NO_RC4)
    #ifdef NO_SHA256
        #error "Hash DRBG requires SHA-256."
    #endif /* NO_SHA256 */

    #include <cyassl/ctaocrypt/sha256.h>
#else /* HAVE_HASHDRBG || NO_RC4 */
    #include <cyassl/ctaocrypt/arc4.h>
#endif /* HAVE_HASHDRBG || NO_RC4 */

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

#if defined(CYASSL_MDK_ARM)
#undef RNG
#define RNG CyaSSL_RNG   /* for avoiding name conflict in "stm32f2xx.h" */
#endif


#if defined(HAVE_HASHDRBG) || defined(NO_RC4)


#define DRBG_SEED_LEN (440/8)


/* Hash-based Deterministic Random Bit Generator */
typedef struct RNG {
    OS_Seed seed;

    Sha256 sha;
    byte digest[SHA256_DIGEST_SIZE];
    byte V[DRBG_SEED_LEN];
    byte C[DRBG_SEED_LEN];
    word32 reseedCtr;
    byte status;
} RNG;


#else /* HAVE_HASHDRBG || NO_RC4 */


#define CYASSL_RNG_CAVIUM_MAGIC 0xBEEF0004

/* secure Random Number Generator */


typedef struct RNG {
    OS_Seed seed;
    Arc4    cipher;
#ifdef HAVE_CAVIUM
    int    devId;           /* nitrox device id */
    word32 magic;           /* using cavium magic */
#endif
} RNG;


#ifdef HAVE_CAVIUM
    CYASSL_API int  InitRngCavium(RNG*, int);
#endif


#endif /* HAVE_HASH_DRBG || NO_RC4 */


CYASSL_API int  InitRng(RNG*);
CYASSL_API int  RNG_GenerateBlock(RNG*, byte*, word32 sz);
CYASSL_API int  RNG_GenerateByte(RNG*, byte*);


#if defined(HAVE_HASHDRBG) || defined(NO_RC4)
    CYASSL_API int FreeRng(RNG*);
    CYASSL_API int RNG_HealthTest(int reseed,
                                        const byte* entropyA, word32 entropyASz,
                                        const byte* entropyB, word32 entropyBSz,
                                        const byte* output, word32 outputSz);
#endif /* HAVE_HASHDRBG || NO_RC4 */


#ifdef HAVE_FIPS
    /* fips wrapper calls, user can call direct */
    CYASSL_API int InitRng_fips(RNG* rng);
    CYASSL_API int FreeRng_fips(RNG* rng);
    CYASSL_API int RNG_GenerateBlock_fips(RNG* rng, byte* buf, word32 bufSz);
    CYASSL_API int RNG_HealthTest_fips(int reseed,
                                        const byte* entropyA, word32 entropyASz,
                                        const byte* entropyB, word32 entropyBSz,
                                        const byte* output, word32 outputSz);
    #ifndef FIPS_NO_WRAPPERS
        /* if not impl or fips.c impl wrapper force fips calls if fips build */
        #define InitRng              InitRng_fips
        #define FreeRng              FreeRng_fips
        #define RNG_GenerateBlock    RNG_GenerateBlock_fips
        #define RNG_HealthTest       RNG_HealthTest_fips
    #endif /* FIPS_NO_WRAPPERS */
#endif /* HAVE_FIPS */


#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* CTAO_CRYPT_RANDOM_H */

