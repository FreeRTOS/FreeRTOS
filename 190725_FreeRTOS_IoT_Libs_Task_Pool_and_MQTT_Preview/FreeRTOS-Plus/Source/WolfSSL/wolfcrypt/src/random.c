/* random.c
 *
 * Copyright (C) 2006-2015 wolfSSL Inc.
 *
 * This file is part of wolfSSL. (formerly known as CyaSSL)
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif
 
#include <wolfssl/wolfcrypt/settings.h>

/* on HPUX 11 you may need to install /dev/random see
   http://h20293.www2.hp.com/portal/swdepot/displayProductInfo.do?productNumber=KRNG11I

*/

#include <wolfssl/wolfcrypt/random.h>

#ifdef HAVE_FIPS
int wc_GenerateSeed(OS_Seed* os, byte* seed, word32 sz)
{
    return GenerateSeed(os, seed, sz);
}

#ifdef HAVE_CAVIUM
    int  wc_InitRngCavium(RNG* rng, int i)
    {
        return InitRngCavium(rng, i);
    }
#endif


int  wc_InitRng(RNG* rng)
{
    return InitRng_fips(rng);
}


int  wc_RNG_GenerateBlock(RNG* rng, byte* b, word32 sz)
{
    return RNG_GenerateBlock_fips(rng, b, sz);
}


int  wc_RNG_GenerateByte(RNG* rng, byte* b)
{
    return RNG_GenerateByte(rng, b);
}

#if defined(HAVE_HASHDRBG) || defined(NO_RC4)

    int wc_FreeRng(RNG* rng)
    {
        return FreeRng_fips(rng);
    }


    int wc_RNG_HealthTest(int reseed,
                                        const byte* entropyA, word32 entropyASz,
                                        const byte* entropyB, word32 entropyBSz,
                                        byte* output, word32 outputSz)
    {
        return RNG_HealthTest_fips(reseed, entropyA, entropyASz,
                              entropyB, entropyBSz, output, outputSz);
    }
#endif /* HAVE_HASHDRBG || NO_RC4 */
#else /* else build without fips */
#include <wolfssl/wolfcrypt/error-crypt.h>

#if defined(HAVE_HASHDRBG) || defined(NO_RC4)

    #include <wolfssl/wolfcrypt/sha256.h>

    #ifdef NO_INLINE
        #include <wolfssl/wolfcrypt/misc.h>
    #else
        #include <wolfcrypt/src/misc.c>
    #endif
#endif /* HAVE_HASHDRBG || NO_RC4 */

#if defined(USE_WINDOWS_API)
    #ifndef _WIN32_WINNT
        #define _WIN32_WINNT 0x0400
    #endif
    #include <windows.h>
    #include <wincrypt.h>
#else
    #if !defined(NO_DEV_RANDOM) && !defined(CUSTOM_RAND_GENERATE) && \
                          !defined(WOLFSSL_MDK_ARM) && !defined(WOLFSSL_IAR_ARM)
            #include <fcntl.h>
        #ifndef EBSNET
            #include <unistd.h>
        #endif
    #else
        /* include headers that may be needed to get good seed */
    #endif
#endif /* USE_WINDOWS_API */
    
#ifdef HAVE_INTEL_RDGEN
    static int wc_InitRng_IntelRD(void) ;
    #if defined(HAVE_HASHDRBG) || defined(NO_RC4)
	static int wc_GenerateSeed_IntelRD(OS_Seed* os, byte* output, word32 sz) ;
    #else
    static int wc_GenerateRand_IntelRD(OS_Seed* os, byte* output, word32 sz) ;
    #endif
    static word32 cpuid_check = 0 ;
    static word32 cpuid_flags = 0 ;
    #define CPUID_RDRAND 0x4
    #define CPUID_RDSEED 0x8
    #define IS_INTEL_RDRAND     (cpuid_flags&CPUID_RDRAND)
    #define IS_INTEL_RDSEED     (cpuid_flags&CPUID_RDSEED)
#endif

#if defined(HAVE_HASHDRBG) || defined(NO_RC4)

/* Start NIST DRBG code */

#define OUTPUT_BLOCK_LEN  (SHA256_DIGEST_SIZE)
#define MAX_REQUEST_LEN   (0x10000)
#define RESEED_INTERVAL   (1000000)
#define SECURITY_STRENGTH (256)
#define ENTROPY_SZ        (SECURITY_STRENGTH/8)
#define NONCE_SZ          (ENTROPY_SZ/2)
#define ENTROPY_NONCE_SZ  (ENTROPY_SZ+NONCE_SZ)

/* Internal return codes */
#define DRBG_SUCCESS      0
#define DRBG_ERROR        1
#define DRBG_FAILURE      2
#define DRBG_NEED_RESEED  3
#define DRBG_CONT_FAILURE 4

/* RNG health states */
#define DRBG_NOT_INIT     0
#define DRBG_OK           1
#define DRBG_FAILED       2
#define DRBG_CONT_FAILED  3


enum {
    drbgInitC     = 0,
    drbgReseed    = 1,
    drbgGenerateW = 2,
    drbgGenerateH = 3,
    drbgInitV
};


typedef struct DRBG {
    word32 reseedCtr;
    word32 lastBlock;
    byte V[DRBG_SEED_LEN];
    byte C[DRBG_SEED_LEN];
    byte   matchCount;
} DRBG;


static int wc_RNG_HealthTestLocal(int reseed);

/* Hash Derivation Function */
/* Returns: DRBG_SUCCESS or DRBG_FAILURE */
static int Hash_df(DRBG* drbg, byte* out, word32 outSz, byte type,
                                                  const byte* inA, word32 inASz,
                                                  const byte* inB, word32 inBSz)
{
    byte ctr;
    int i;
    int len;
    word32 bits = (outSz * 8); /* reverse byte order */
    Sha256 sha;
    byte digest[SHA256_DIGEST_SIZE];

    (void)drbg;
    #ifdef LITTLE_ENDIAN_ORDER
        bits = ByteReverseWord32(bits);
    #endif
    len = (outSz / OUTPUT_BLOCK_LEN)
        + ((outSz % OUTPUT_BLOCK_LEN) ? 1 : 0);

    for (i = 0, ctr = 1; i < len; i++, ctr++)
    {
        if (wc_InitSha256(&sha) != 0)
            return DRBG_FAILURE;

        if (wc_Sha256Update(&sha, &ctr, sizeof(ctr)) != 0)
            return DRBG_FAILURE;

        if (wc_Sha256Update(&sha, (byte*)&bits, sizeof(bits)) != 0)
            return DRBG_FAILURE;

        /* churning V is the only string that doesn't have the type added */
        if (type != drbgInitV)
            if (wc_Sha256Update(&sha, &type, sizeof(type)) != 0)
                return DRBG_FAILURE;

        if (wc_Sha256Update(&sha, inA, inASz) != 0)
            return DRBG_FAILURE;

        if (inB != NULL && inBSz > 0)
            if (wc_Sha256Update(&sha, inB, inBSz) != 0)
                return DRBG_FAILURE;

        if (wc_Sha256Final(&sha, digest) != 0)
            return DRBG_FAILURE;

        if (outSz > OUTPUT_BLOCK_LEN) {
            XMEMCPY(out, digest, OUTPUT_BLOCK_LEN);
            outSz -= OUTPUT_BLOCK_LEN;
            out += OUTPUT_BLOCK_LEN;
        }
        else {
            XMEMCPY(out, digest, outSz);
        }
    }
    ForceZero(digest, sizeof(digest));

    return DRBG_SUCCESS;
}


/* Returns: DRBG_SUCCESS or DRBG_FAILURE */
static int Hash_DRBG_Reseed(DRBG* drbg, const byte* entropy, word32 entropySz)
{
    byte seed[DRBG_SEED_LEN];

    if (Hash_df(drbg, seed, sizeof(seed), drbgReseed, drbg->V, sizeof(drbg->V),
                                          entropy, entropySz) != DRBG_SUCCESS) {
        return DRBG_FAILURE;
    }

    XMEMCPY(drbg->V, seed, sizeof(drbg->V));
    ForceZero(seed, sizeof(seed));

    if (Hash_df(drbg, drbg->C, sizeof(drbg->C), drbgInitC, drbg->V,
                                    sizeof(drbg->V), NULL, 0) != DRBG_SUCCESS) {
        return DRBG_FAILURE;
    }

    drbg->reseedCtr = 1;
    drbg->lastBlock = 0;
    drbg->matchCount = 0;
    return DRBG_SUCCESS;
}

static INLINE void array_add_one(byte* data, word32 dataSz)
{
    int i;

    for (i = dataSz - 1; i >= 0; i--)
    {
        data[i]++;
        if (data[i] != 0) break;
    }
}


/* Returns: DRBG_SUCCESS or DRBG_FAILURE */
static int Hash_gen(DRBG* drbg, byte* out, word32 outSz, const byte* V)
{
    byte data[DRBG_SEED_LEN];
    int i;
    int len;
    word32 checkBlock;
    Sha256 sha;
    byte digest[SHA256_DIGEST_SIZE];

    /* Special case: outSz is 0 and out is NULL. wc_Generate a block to save for
     * the continuous test. */

    if (outSz == 0) outSz = 1;

    len = (outSz / OUTPUT_BLOCK_LEN) + ((outSz % OUTPUT_BLOCK_LEN) ? 1 : 0);

    XMEMCPY(data, V, sizeof(data));
    for (i = 0; i < len; i++) {
        if (wc_InitSha256(&sha) != 0 ||
            wc_Sha256Update(&sha, data, sizeof(data)) != 0 ||
            wc_Sha256Final(&sha, digest) != 0) {

            return DRBG_FAILURE;
        }

        XMEMCPY(&checkBlock, digest, sizeof(word32));
        if (drbg->reseedCtr > 1 && checkBlock == drbg->lastBlock) {
            if (drbg->matchCount == 1) {
                return DRBG_CONT_FAILURE;
            }
            else {
                if (i == len) {
                    len++;
                }
                drbg->matchCount = 1;
            }
        }
        else {
            drbg->matchCount = 0;
            drbg->lastBlock = checkBlock;
        }

        if (outSz >= OUTPUT_BLOCK_LEN) {
            XMEMCPY(out, digest, OUTPUT_BLOCK_LEN);
            outSz -= OUTPUT_BLOCK_LEN;
            out += OUTPUT_BLOCK_LEN;
            array_add_one(data, DRBG_SEED_LEN);
        }
        else if (out != NULL && outSz != 0) {
            XMEMCPY(out, digest, outSz);
            outSz = 0;
        }
    }
    ForceZero(data, sizeof(data));

    return DRBG_SUCCESS;
}


static INLINE void array_add(byte* d, word32 dLen, const byte* s, word32 sLen)
{
    word16 carry = 0;

    if (dLen > 0 && sLen > 0 && dLen >= sLen) {
        int sIdx, dIdx;

        for (sIdx = sLen - 1, dIdx = dLen - 1; sIdx >= 0; dIdx--, sIdx--)
        {
            carry += d[dIdx] + s[sIdx];
            d[dIdx] = (byte)carry;
            carry >>= 8;
        }

        for (; carry != 0 && dIdx >= 0; dIdx--) {
            carry += d[dIdx];
            d[dIdx] = (byte)carry;
            carry >>= 8;
        }
    }
}


/* Returns: DRBG_SUCCESS, DRBG_NEED_RESEED, or DRBG_FAILURE */
static int Hash_DRBG_Generate(DRBG* drbg, byte* out, word32 outSz)
{
    int ret = DRBG_NEED_RESEED;
    Sha256 sha;
    byte digest[SHA256_DIGEST_SIZE];

    if (drbg->reseedCtr != RESEED_INTERVAL) {
        byte type = drbgGenerateH;
        word32 reseedCtr = drbg->reseedCtr;

        ret = Hash_gen(drbg, out, outSz, drbg->V);
        if (ret == DRBG_SUCCESS) {
            if (wc_InitSha256(&sha) != 0 ||
                wc_Sha256Update(&sha, &type, sizeof(type)) != 0 ||
                wc_Sha256Update(&sha, drbg->V, sizeof(drbg->V)) != 0 ||
                wc_Sha256Final(&sha, digest) != 0) {

                ret = DRBG_FAILURE;
            }
            else {
                array_add(drbg->V, sizeof(drbg->V), digest, sizeof(digest));
                array_add(drbg->V, sizeof(drbg->V), drbg->C, sizeof(drbg->C));
                #ifdef LITTLE_ENDIAN_ORDER
                    reseedCtr = ByteReverseWord32(reseedCtr);
                #endif
                array_add(drbg->V, sizeof(drbg->V),
                                          (byte*)&reseedCtr, sizeof(reseedCtr));
                ret = DRBG_SUCCESS;
            }
            drbg->reseedCtr++;
        }
    }
    ForceZero(digest, sizeof(digest));

    return ret;
}


/* Returns: DRBG_SUCCESS or DRBG_FAILURE */
static int Hash_DRBG_Instantiate(DRBG* drbg, const byte* seed, word32 seedSz,
                                             const byte* nonce, word32 nonceSz)
{
    int ret = DRBG_FAILURE;

    XMEMSET(drbg, 0, sizeof(DRBG));

    if (Hash_df(drbg, drbg->V, sizeof(drbg->V), drbgInitV, seed, seedSz,
                                              nonce, nonceSz) == DRBG_SUCCESS &&
        Hash_df(drbg, drbg->C, sizeof(drbg->C), drbgInitC, drbg->V,
                                    sizeof(drbg->V), NULL, 0) == DRBG_SUCCESS) {

        drbg->reseedCtr = 1;
        drbg->lastBlock = 0;
        drbg->matchCount = 0;
        ret = DRBG_SUCCESS;
    }

    return ret;
}


/* Returns: DRBG_SUCCESS or DRBG_FAILURE */
static int Hash_DRBG_Uninstantiate(DRBG* drbg)
{
    word32 i;
    int    compareSum = 0;
    byte*  compareDrbg = (byte*)drbg;

    ForceZero(drbg, sizeof(DRBG));

    for (i = 0; i < sizeof(DRBG); i++)
        compareSum |= compareDrbg[i] ^ 0;

    return (compareSum == 0) ? DRBG_SUCCESS : DRBG_FAILURE;
}

/* End NIST DRBG Code */


/* Get seed and key cipher */
int wc_InitRng(RNG* rng)
{
    int ret = BAD_FUNC_ARG;

    if (rng != NULL) {
        if (wc_RNG_HealthTestLocal(0) == 0) {
            byte entropy[ENTROPY_NONCE_SZ];

            rng->drbg =
                    (struct DRBG*)XMALLOC(sizeof(DRBG), NULL, DYNAMIC_TYPE_RNG);
            if (rng->drbg == NULL) {
                ret = MEMORY_E;
            }
            /* This doesn't use a separate nonce. The entropy input will be
             * the default size plus the size of the nonce making the seed
             * size. */
            else if (wc_GenerateSeed(&rng->seed,
                                              entropy, ENTROPY_NONCE_SZ) == 0 &&
                     Hash_DRBG_Instantiate(rng->drbg,
                          entropy, ENTROPY_NONCE_SZ, NULL, 0) == DRBG_SUCCESS) {

                ret = Hash_DRBG_Generate(rng->drbg, NULL, 0);
            }
            else
                ret = DRBG_FAILURE;

            ForceZero(entropy, ENTROPY_NONCE_SZ);
        }
        else
            ret = DRBG_CONT_FAILURE;

        if (ret == DRBG_SUCCESS) {
            rng->status = DRBG_OK;
            ret = 0;
        }
        else if (ret == DRBG_CONT_FAILURE) {
            rng->status = DRBG_CONT_FAILED;
            ret = DRBG_CONT_FIPS_E;
        }
        else if (ret == DRBG_FAILURE) {
            rng->status = DRBG_FAILED;
            ret = RNG_FAILURE_E;
        }
        else {
            rng->status = DRBG_FAILED;
        }
    }

    return ret;
}


/* place a generated block in output */
int wc_RNG_GenerateBlock(RNG* rng, byte* output, word32 sz)
{
    int ret;

    if (rng == NULL || output == NULL || sz > MAX_REQUEST_LEN)
        return BAD_FUNC_ARG;

    if (rng->status != DRBG_OK)
        return RNG_FAILURE_E;

    ret = Hash_DRBG_Generate(rng->drbg, output, sz);

    if (ret == DRBG_NEED_RESEED) {
        if (wc_RNG_HealthTestLocal(1) == 0) {
            byte entropy[ENTROPY_SZ];

            if (wc_GenerateSeed(&rng->seed, entropy, ENTROPY_SZ) == 0 &&
                Hash_DRBG_Reseed(rng->drbg, entropy, ENTROPY_SZ)
                                                              == DRBG_SUCCESS) {

                ret = Hash_DRBG_Generate(rng->drbg, NULL, 0);
                if (ret == DRBG_SUCCESS)
                    ret = Hash_DRBG_Generate(rng->drbg, output, sz);
            }
            else
                ret = DRBG_FAILURE;

            ForceZero(entropy, ENTROPY_SZ);
        }
        else
            ret = DRBG_CONT_FAILURE;
    }

    if (ret == DRBG_SUCCESS) {
        ret = 0;
    }
    else if (ret == DRBG_CONT_FAILURE) {
        ret = DRBG_CONT_FIPS_E;
        rng->status = DRBG_CONT_FAILED;
    }
    else {
        ret = RNG_FAILURE_E;
        rng->status = DRBG_FAILED;
    }

    return ret;
}


int wc_RNG_GenerateByte(RNG* rng, byte* b)
{
    return wc_RNG_GenerateBlock(rng, b, 1);
}


int wc_FreeRng(RNG* rng)
{
    int ret = BAD_FUNC_ARG;

    if (rng != NULL) {
        if (rng->drbg != NULL) {
            if (Hash_DRBG_Uninstantiate(rng->drbg) == DRBG_SUCCESS)
                ret = 0;
            else
                ret = RNG_FAILURE_E;

            XFREE(rng->drbg, NULL, DYNAMIC_TYPE_RNG);
            rng->drbg = NULL;
        }

        rng->status = DRBG_NOT_INIT;
    }

    return ret;
}


int wc_RNG_HealthTest(int reseed, const byte* entropyA, word32 entropyASz,
                                  const byte* entropyB, word32 entropyBSz,
                                  byte* output, word32 outputSz)
{
    DRBG drbg;

    if (entropyA == NULL || output == NULL)
        return BAD_FUNC_ARG;

    if (reseed != 0 && entropyB == NULL)
        return BAD_FUNC_ARG;

    if (outputSz != (SHA256_DIGEST_SIZE * 4))
        return -1;

    if (Hash_DRBG_Instantiate(&drbg, entropyA, entropyASz, NULL, 0) != 0)
        return -1;

    if (reseed) {
        if (Hash_DRBG_Reseed(&drbg, entropyB, entropyBSz) != 0) {
            Hash_DRBG_Uninstantiate(&drbg);
            return -1;
        }
    }

    if (Hash_DRBG_Generate(&drbg, output, outputSz) != 0) {
        Hash_DRBG_Uninstantiate(&drbg);
        return -1;
    }

    if (Hash_DRBG_Generate(&drbg, output, outputSz) != 0) {
        Hash_DRBG_Uninstantiate(&drbg);
        return -1;
    }

    if (Hash_DRBG_Uninstantiate(&drbg) != 0) {
        return -1;
    }

    return 0;
}


const byte entropyA[] = {
    0x63, 0x36, 0x33, 0x77, 0xe4, 0x1e, 0x86, 0x46, 0x8d, 0xeb, 0x0a, 0xb4,
    0xa8, 0xed, 0x68, 0x3f, 0x6a, 0x13, 0x4e, 0x47, 0xe0, 0x14, 0xc7, 0x00,
    0x45, 0x4e, 0x81, 0xe9, 0x53, 0x58, 0xa5, 0x69, 0x80, 0x8a, 0xa3, 0x8f,
    0x2a, 0x72, 0xa6, 0x23, 0x59, 0x91, 0x5a, 0x9f, 0x8a, 0x04, 0xca, 0x68
};

const byte reseedEntropyA[] = {
    0xe6, 0x2b, 0x8a, 0x8e, 0xe8, 0xf1, 0x41, 0xb6, 0x98, 0x05, 0x66, 0xe3,
    0xbf, 0xe3, 0xc0, 0x49, 0x03, 0xda, 0xd4, 0xac, 0x2c, 0xdf, 0x9f, 0x22,
    0x80, 0x01, 0x0a, 0x67, 0x39, 0xbc, 0x83, 0xd3
};

const byte outputA[] = {
    0x04, 0xee, 0xc6, 0x3b, 0xb2, 0x31, 0xdf, 0x2c, 0x63, 0x0a, 0x1a, 0xfb,
    0xe7, 0x24, 0x94, 0x9d, 0x00, 0x5a, 0x58, 0x78, 0x51, 0xe1, 0xaa, 0x79,
    0x5e, 0x47, 0x73, 0x47, 0xc8, 0xb0, 0x56, 0x62, 0x1c, 0x18, 0xbd, 0xdc,
    0xdd, 0x8d, 0x99, 0xfc, 0x5f, 0xc2, 0xb9, 0x20, 0x53, 0xd8, 0xcf, 0xac,
    0xfb, 0x0b, 0xb8, 0x83, 0x12, 0x05, 0xfa, 0xd1, 0xdd, 0xd6, 0xc0, 0x71,
    0x31, 0x8a, 0x60, 0x18, 0xf0, 0x3b, 0x73, 0xf5, 0xed, 0xe4, 0xd4, 0xd0,
    0x71, 0xf9, 0xde, 0x03, 0xfd, 0x7a, 0xea, 0x10, 0x5d, 0x92, 0x99, 0xb8,
    0xaf, 0x99, 0xaa, 0x07, 0x5b, 0xdb, 0x4d, 0xb9, 0xaa, 0x28, 0xc1, 0x8d,
    0x17, 0x4b, 0x56, 0xee, 0x2a, 0x01, 0x4d, 0x09, 0x88, 0x96, 0xff, 0x22,
    0x82, 0xc9, 0x55, 0xa8, 0x19, 0x69, 0xe0, 0x69, 0xfa, 0x8c, 0xe0, 0x07,
    0xa1, 0x80, 0x18, 0x3a, 0x07, 0xdf, 0xae, 0x17
};

const byte entropyB[] = {
    0xa6, 0x5a, 0xd0, 0xf3, 0x45, 0xdb, 0x4e, 0x0e, 0xff, 0xe8, 0x75, 0xc3,
    0xa2, 0xe7, 0x1f, 0x42, 0xc7, 0x12, 0x9d, 0x62, 0x0f, 0xf5, 0xc1, 0x19,
    0xa9, 0xef, 0x55, 0xf0, 0x51, 0x85, 0xe0, 0xfb, 0x85, 0x81, 0xf9, 0x31,
    0x75, 0x17, 0x27, 0x6e, 0x06, 0xe9, 0x60, 0x7d, 0xdb, 0xcb, 0xcc, 0x2e
};

const byte outputB[] = {
    0xd3, 0xe1, 0x60, 0xc3, 0x5b, 0x99, 0xf3, 0x40, 0xb2, 0x62, 0x82, 0x64,
    0xd1, 0x75, 0x10, 0x60, 0xe0, 0x04, 0x5d, 0xa3, 0x83, 0xff, 0x57, 0xa5,
    0x7d, 0x73, 0xa6, 0x73, 0xd2, 0xb8, 0xd8, 0x0d, 0xaa, 0xf6, 0xa6, 0xc3,
    0x5a, 0x91, 0xbb, 0x45, 0x79, 0xd7, 0x3f, 0xd0, 0xc8, 0xfe, 0xd1, 0x11,
    0xb0, 0x39, 0x13, 0x06, 0x82, 0x8a, 0xdf, 0xed, 0x52, 0x8f, 0x01, 0x81,
    0x21, 0xb3, 0xfe, 0xbd, 0xc3, 0x43, 0xe7, 0x97, 0xb8, 0x7d, 0xbb, 0x63,
    0xdb, 0x13, 0x33, 0xde, 0xd9, 0xd1, 0xec, 0xe1, 0x77, 0xcf, 0xa6, 0xb7,
    0x1f, 0xe8, 0xab, 0x1d, 0xa4, 0x66, 0x24, 0xed, 0x64, 0x15, 0xe5, 0x1c,
    0xcd, 0xe2, 0xc7, 0xca, 0x86, 0xe2, 0x83, 0x99, 0x0e, 0xea, 0xeb, 0x91,
    0x12, 0x04, 0x15, 0x52, 0x8b, 0x22, 0x95, 0x91, 0x02, 0x81, 0xb0, 0x2d,
    0xd4, 0x31, 0xf4, 0xc9, 0xf7, 0x04, 0x27, 0xdf
};


static int wc_RNG_HealthTestLocal(int reseed)
{
    int ret = 0;
    byte check[SHA256_DIGEST_SIZE * 4];

    if (reseed) {
        ret = wc_RNG_HealthTest(1, entropyA, sizeof(entropyA),
                                reseedEntropyA, sizeof(reseedEntropyA),
                                check, sizeof(check));
        if (ret == 0) {
            if (ConstantCompare(check, outputA, sizeof(check)) != 0)
                ret = -1;
        }
    }
    else {
        ret = wc_RNG_HealthTest(0, entropyB, sizeof(entropyB),
                                NULL, 0,
                                check, sizeof(check));
        if (ret == 0) {
            if (ConstantCompare(check, outputB, sizeof(check)) != 0)
                ret = -1;
        }
    }

    return ret;
}


#else /* HAVE_HASHDRBG || NO_RC4 */

/* Get seed and key cipher */
int wc_InitRng(RNG* rng)
{
    int  ret;
#ifdef WOLFSSL_SMALL_STACK
    byte* key;
    byte* junk;
#else
    byte key[32];
    byte junk[256];
#endif

#ifdef HAVE_INTEL_RDGEN
    wc_InitRng_IntelRD() ;
    if(IS_INTEL_RDRAND)return 0 ;
#endif
#ifdef HAVE_CAVIUM
    if (rng->magic == WOLFSSL_RNG_CAVIUM_MAGIC)
        return 0;
#endif

#ifdef WOLFSSL_SMALL_STACK
    key = (byte*)XMALLOC(32, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (key == NULL)
        return MEMORY_E;

    junk = (byte*)XMALLOC(256, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (junk == NULL) {
        XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
#endif

    ret = wc_GenerateSeed(&rng->seed, key, 32);

    if (ret == 0) {
        wc_Arc4SetKey(&rng->cipher, key, sizeof(key));

        ret = wc_RNG_GenerateBlock(rng, junk, 256); /*rid initial state*/
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(junk, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#ifdef HAVE_CAVIUM
    static void CaviumRNG_GenerateBlock(RNG* rng, byte* output, word32 sz);
#endif

/* place a generated block in output */
int wc_RNG_GenerateBlock(RNG* rng, byte* output, word32 sz)
{
#ifdef HAVE_INTEL_RDGEN
    if(IS_INTEL_RDRAND)
        return wc_GenerateRand_IntelRD(NULL, output, sz) ;
#endif
#ifdef HAVE_CAVIUM
    if (rng->magic == WOLFSSL_RNG_CAVIUM_MAGIC)
        return CaviumRNG_GenerateBlock(rng, output, sz);
#endif
    XMEMSET(output, 0, sz);
    wc_Arc4Process(&rng->cipher, output, output, sz);

    return 0;
}


int wc_RNG_GenerateByte(RNG* rng, byte* b)
{
    return wc_RNG_GenerateBlock(rng, b, 1);
}


int wc_FreeRng(RNG* rng)
{
    (void)rng;
    return 0;
}


#ifdef HAVE_CAVIUM

#include <wolfssl/ctaocrypt/logging.h>
#include "cavium_common.h"

/* Initiliaze RNG for use with Nitrox device */
int wc_InitRngCavium(RNG* rng, int devId)
{
    if (rng == NULL)
        return -1;

    rng->devId = devId;
    rng->magic = WOLFSSL_RNG_CAVIUM_MAGIC;

    return 0;
}


static void CaviumRNG_GenerateBlock(RNG* rng, byte* output, word32 sz)
{
    wolfssl_word offset = 0;
    word32      requestId;

    while (sz > WOLFSSL_MAX_16BIT) {
        word16 slen = (word16)WOLFSSL_MAX_16BIT;
        if (CspRandom(CAVIUM_BLOCKING, slen, output + offset, &requestId,
                      rng->devId) != 0) {
            WOLFSSL_MSG("Cavium RNG failed");
        }
        sz     -= WOLFSSL_MAX_16BIT;
        offset += WOLFSSL_MAX_16BIT;
    }
    if (sz) {
        word16 slen = (word16)sz;
        if (CspRandom(CAVIUM_BLOCKING, slen, output + offset, &requestId,
                      rng->devId) != 0) {
            WOLFSSL_MSG("Cavium RNG failed");
        }
    }
}

#endif /* HAVE_CAVIUM */

#endif /* HAVE_HASHDRBG || NO_RC4 */


#if defined(HAVE_INTEL_RDGEN)

#ifndef _MSC_VER
    #define cpuid(reg, leaf, sub)\
            __asm__ __volatile__ ("cpuid":\
             "=a" (reg[0]), "=b" (reg[1]), "=c" (reg[2]), "=d" (reg[3]) :\
             "a" (leaf), "c"(sub));

    #define XASM_LINK(f) asm(f)
#else

    #include <intrin.h>
    #define cpuid(a,b) __cpuid((int*)a,b)

    #define XASM_LINK(f)

#endif /* _MSC_VER */

#define EAX 0
#define EBX 1
#define ECX 2 
#define EDX 3

static word32 cpuid_flag(word32 leaf, word32 sub, word32 num, word32 bit) {
    int got_intel_cpu=0;
    unsigned int reg[5]; 
    
    reg[4] = '\0' ;
    cpuid(reg, 0, 0);  
    if(memcmp((char *)&(reg[EBX]), "Genu", 4) == 0 &&  
                memcmp((char *)&(reg[EDX]), "ineI", 4) == 0 &&  
                memcmp((char *)&(reg[ECX]), "ntel", 4) == 0) {  
        got_intel_cpu = 1;  
    }    
    if (got_intel_cpu) {
        cpuid(reg, leaf, sub);
        return((reg[num]>>bit)&0x1) ;
    }
    return 0 ;
}

static int wc_InitRng_IntelRD()
{
    if(cpuid_check==0) {
        if(cpuid_flag(1, 0, ECX, 30)){ cpuid_flags |= CPUID_RDRAND ;} 
        if(cpuid_flag(7, 0, EBX, 18)){ cpuid_flags |= CPUID_RDSEED ;}
        cpuid_check = 1 ;
    }
    return 1 ;
}

#define INTELRD_RETRY 10

#if defined(HAVE_HASHDRBG) || defined(NO_RC4)

/* return 0 on success */
static inline int IntelRDseed32(unsigned int *seed)  
{  
    int rdseed;  unsigned char ok ;

    __asm__ volatile("rdseed %0; setc %1":"=r"(rdseed), "=qm"(ok));  
    if(ok){
        *seed = rdseed ;
        return 0 ;
    } else
        return 1;
}

/* return 0 on success */
static inline int IntelRDseed32_r(unsigned int *rnd)  
{  
    int i ;
    for(i=0; i<INTELRD_RETRY;i++) {
       if(IntelRDseed32(rnd) == 0) return 0 ;
    }
    return 1 ;
}

/* return 0 on success */
static int wc_GenerateSeed_IntelRD(OS_Seed* os, byte* output, word32 sz)
{
    (void) os ;
    int ret ;
    unsigned int rndTmp ;

    for(  ; sz/4 > 0; sz-=4, output+=4) {
        if(IS_INTEL_RDSEED)ret = IntelRDseed32_r((word32 *)output) ;
        else return 1 ;
        if(ret)
             return 1 ;
    }
    if(sz == 0)return 0 ;

    if(IS_INTEL_RDSEED)ret = IntelRDseed32_r(&rndTmp) ;
    else return 1 ;
    if(ret)
         return 1 ;
    XMEMCPY(output, &rndTmp, sz) ;
    return 0;
}

#else

/* return 0 on success */
static inline int IntelRDrand32(unsigned int *rnd)  
{  
    int rdrand; unsigned char ok ;  
    __asm__ volatile("rdrand %0; setc %1":"=r"(rdrand), "=qm"(ok));  
    if(ok){
        *rnd = rdrand;
        return 0 ;
    } else
        return 1;
}

/* return 0 on success */
static inline int IntelRDrand32_r(unsigned int *rnd)  
{  
    int i ;
    for(i=0; i<INTELRD_RETRY;i++) {
       if(IntelRDrand32(rnd) == 0) return 0 ;
    }
    return 1 ;
}

/* return 0 on success */
static int wc_GenerateRand_IntelRD(OS_Seed* os, byte* output, word32 sz)
{
    (void) os ;
    int ret ;
    unsigned int rndTmp;

    for(  ; sz/4 > 0; sz-=4, output+=4) {
        if(IS_INTEL_RDRAND)ret = IntelRDrand32_r((word32 *)output);
        else return 1 ;
        if(ret)
             return 1 ;
    }
    if(sz == 0)return 0 ;

    if(IS_INTEL_RDRAND)ret = IntelRDrand32_r(&rndTmp);
    else return 1 ;
    if(ret)
         return 1 ;
    XMEMCPY(output, &rndTmp, sz) ;
    return 0;
}
#endif /* defined(HAVE_HASHDRBG) || defined(NO_RC4) */

#endif /* HAVE_INTEL_RDGEN */


#if defined(USE_WINDOWS_API)


int wc_GenerateSeed(OS_Seed* os, byte* output, word32 sz)
{
    if(!CryptAcquireContext(&os->handle, 0, 0, PROV_RSA_FULL,
                            CRYPT_VERIFYCONTEXT))
        return WINCRYPT_E;

    if (!CryptGenRandom(os->handle, sz, output))
        return CRYPTGEN_E;

    CryptReleaseContext(os->handle, 0);

    return 0;
}


#elif defined(HAVE_RTP_SYS) || defined(EBSNET)

#include "rtprand.h"   /* rtp_rand () */
#include "rtptime.h"   /* rtp_get_system_msec() */


int wc_GenerateSeed(OS_Seed* os, byte* output, word32 sz)
{
    int i;
    rtp_srand(rtp_get_system_msec());

    for (i = 0; i < sz; i++ ) {
        output[i] = rtp_rand() % 256;
        if ( (i % 8) == 7)
            rtp_srand(rtp_get_system_msec());
    }

    return 0;
}


#elif defined(MICRIUM)

int wc_GenerateSeed(OS_Seed* os, byte* output, word32 sz)
{
    #if (NET_SECURE_MGR_CFG_EN == DEF_ENABLED)
        NetSecure_InitSeed(output, sz);
    #endif
    return 0;
}

#elif defined(MBED)

/* write a real one !!!, just for testing board */
int wc_GenerateSeed(OS_Seed* os, byte* output, word32 sz)
{
    int i;
    for (i = 0; i < sz; i++ )
        output[i] = i;

    return 0;
}

#elif defined(MICROCHIP_PIC32)

#ifdef MICROCHIP_MPLAB_HARMONY
    #define PIC32_SEED_COUNT _CP0_GET_COUNT
#else
    #if !defined(WOLFSSL_MICROCHIP_PIC32MZ)
        #include <peripheral/timer.h>
    #endif
    #define PIC32_SEED_COUNT ReadCoreTimer
#endif
    #ifdef WOLFSSL_MIC32MZ_RNG
        #include "xc.h"
        int wc_GenerateSeed(OS_Seed* os, byte* output, word32 sz)
        {
            int i ;
            byte rnd[8] ;
            word32 *rnd32 = (word32 *)rnd ;
            word32 size = sz ;
            byte* op = output ;

            /* This part has to be replaced with better random seed */
            RNGNUMGEN1 = ReadCoreTimer();
            RNGPOLY1 = ReadCoreTimer();
            RNGPOLY2 = ReadCoreTimer();
            RNGNUMGEN2 = ReadCoreTimer();
#ifdef DEBUG_WOLFSSL
            printf("GenerateSeed::Seed=%08x, %08x\n", RNGNUMGEN1, RNGNUMGEN2) ;
#endif
            RNGCONbits.PLEN = 0x40;
            RNGCONbits.PRNGEN = 1;
            for(i=0; i<5; i++) { /* wait for RNGNUMGEN ready */
                volatile int x ;
                x = RNGNUMGEN1 ;
                x = RNGNUMGEN2 ;
            }
            do {
                rnd32[0] = RNGNUMGEN1;
                rnd32[1] = RNGNUMGEN2;

                for(i=0; i<8; i++, op++) {
                    *op = rnd[i] ;
                    size -- ;
                    if(size==0)break ;
                }
            } while(size) ;
            return 0;
        }
    #else  /* WOLFSSL_MIC32MZ_RNG */
        /* uses the core timer, in nanoseconds to seed srand */
        int wc_GenerateSeed(OS_Seed* os, byte* output, word32 sz)
        {
            int i;
            srand(PIC32_SEED_COUNT() * 25);

            for (i = 0; i < sz; i++ ) {
                output[i] = rand() % 256;
                if ( (i % 8) == 7)
                    srand(PIC32_SEED_COUNT() * 25);
            }
            return 0;
        }
    #endif /* WOLFSSL_MIC32MZ_RNG */

#elif defined(FREESCALE_MQX)

    #ifdef FREESCALE_K70_RNGA
        /*
         * wc_Generates a RNG seed using the Random Number Generator Accelerator
         * on the Kinetis K70. Documentation located in Chapter 37 of
         * K70 Sub-Family Reference Manual (see Note 3 in the README for link).
         */
        int wc_GenerateSeed(OS_Seed* os, byte* output, word32 sz)
        {
            int i;

            /* turn on RNGA module */
            SIM_SCGC3 |= SIM_SCGC3_RNGA_MASK;

            /* set SLP bit to 0 - "RNGA is not in sleep mode" */
            RNG_CR &= ~RNG_CR_SLP_MASK;

            /* set HA bit to 1 - "security violations masked" */
            RNG_CR |= RNG_CR_HA_MASK;

            /* set GO bit to 1 - "output register loaded with data" */
            RNG_CR |= RNG_CR_GO_MASK;

            for (i = 0; i < sz; i++) {

                /* wait for RNG FIFO to be full */
                while((RNG_SR & RNG_SR_OREG_LVL(0xF)) == 0) {}

                /* get value */
                output[i] = RNG_OR;
            }

            return 0;
        }

    #elif defined(FREESCALE_K53_RNGB)
        /*
         * wc_Generates a RNG seed using the Random Number Generator (RNGB)
         * on the Kinetis K53. Documentation located in Chapter 33 of
         * K53 Sub-Family Reference Manual (see note in the README for link).
         */
        int wc_GenerateSeed(OS_Seed* os, byte* output, word32 sz)
        {
            int i;

            /* turn on RNGB module */
            SIM_SCGC3 |= SIM_SCGC3_RNGB_MASK;

            /* reset RNGB */
            RNG_CMD |= RNG_CMD_SR_MASK;

            /* FIFO generate interrupt, return all zeros on underflow,
             * set auto reseed */
            RNG_CR |= (RNG_CR_FUFMOD_MASK | RNG_CR_AR_MASK);

            /* gen seed, clear interrupts, clear errors */
            RNG_CMD |= (RNG_CMD_GS_MASK | RNG_CMD_CI_MASK | RNG_CMD_CE_MASK);

            /* wait for seeding to complete */
            while ((RNG_SR & RNG_SR_SDN_MASK) == 0) {}

            for (i = 0; i < sz; i++) {

                /* wait for a word to be available from FIFO */
                while((RNG_SR & RNG_SR_FIFO_LVL_MASK) == 0) {}

                /* get value */
                output[i] = RNG_OUT;
            }

            return 0;
        }

    #else
        #warning "write a real random seed!!!!, just for testing now"

        int wc_GenerateSeed(OS_Seed* os, byte* output, word32 sz)
        {
            int i;
            for (i = 0; i < sz; i++ )
                output[i] = i;

            return 0;
        }
    #endif /* FREESCALE_K70_RNGA */

#elif defined(WOLFSSL_SAFERTOS) || defined(WOLFSSL_LEANPSK) \
   || defined(WOLFSSL_IAR_ARM)  || defined(WOLFSSL_MDK_ARM) \
   || defined(WOLFSSL_uITRON4)  || defined(WOLFSSL_uTKERNEL2)

#warning "write a real random seed!!!!, just for testing now"

int wc_GenerateSeed(OS_Seed* os, byte* output, word32 sz)
{
    word32 i;
    for (i = 0; i < sz; i++ )
        output[i] = i;

    (void)os;

    return 0;
}

#elif defined(STM32F2_RNG)
    #undef RNG
    #include "stm32f2xx_rng.h"
    #include "stm32f2xx_rcc.h"
    /*
     * wc_Generate a RNG seed using the hardware random number generator
     * on the STM32F2. Documentation located in STM32F2xx Standard Peripheral
     * Library document (See note in README).
     */
    int wc_GenerateSeed(OS_Seed* os, byte* output, word32 sz)
    {
        int i;

        /* enable RNG clock source */
        RCC_AHB2PeriphClockCmd(RCC_AHB2Periph_RNG, ENABLE);

        /* enable RNG peripheral */
        RNG_Cmd(ENABLE);

        for (i = 0; i < sz; i++) {
            /* wait until RNG number is ready */
            while(RNG_GetFlagStatus(RNG_FLAG_DRDY)== RESET) { }

            /* get value */
            output[i] = RNG_GetRandomNumber();
        }

        return 0;
    }
#elif defined(WOLFSSL_LPC43xx) || defined(WOLFSSL_STM32F2xx)

    #warning "write a real random seed!!!!, just for testing now"

    int wc_GenerateSeed(OS_Seed* os, byte* output, word32 sz)
    {
        int i;

        for (i = 0; i < sz; i++ )
            output[i] = i;

        return 0;
    }

#elif defined(WOLFSSL_TIRTOS)

    #include <xdc/runtime/Timestamp.h>
    #include <stdlib.h>
    int wc_GenerateSeed(OS_Seed* os, byte* output, word32 sz)
    {
        int i;
        srand(xdc_runtime_Timestamp_get32());

        for (i = 0; i < sz; i++ ) {
            output[i] = rand() % 256;
            if ((i % 8) == 7) {
                srand(xdc_runtime_Timestamp_get32());
            }
        }

        return 0;
    }

#elif defined(CUSTOM_RAND_GENERATE)

   /* Implement your own random generation function
    * word32 rand_gen(void);
    * #define CUSTOM_RAND_GENERATE  rand_gen  */

    int wc_GenerateSeed(OS_Seed* os, byte* output, word32 sz)
    {
        word32 i;

        (void)os;

        for (i = 0; i < sz; i++ )
            output[i] = CUSTOM_RAND_GENERATE();

        return 0;
    }

#elif defined(NO_DEV_RANDOM)

#error "you need to write an os specific wc_GenerateSeed() here"

/*
int wc_GenerateSeed(OS_Seed* os, byte* output, word32 sz)
{
    return 0;
}
*/


#else /* !USE_WINDOWS_API && !HAVE_RPT_SYS && !MICRIUM && !NO_DEV_RANDOM */

/* may block */
int wc_GenerateSeed(OS_Seed* os, byte* output, word32 sz)
{
    int ret = 0;


#if defined(HAVE_INTEL_RDGEN) && (defined(HAVE_HASHDRBG) || defined(NO_RC4))
    wc_InitRng_IntelRD() ; /* set cpuid_flags if not yet */
    if(IS_INTEL_RDSEED)
         return wc_GenerateSeed_IntelRD(NULL, output, sz) ;
#endif

    os->fd = open("/dev/urandom",O_RDONLY);
    if (os->fd == -1) {
        /* may still have /dev/random */
        os->fd = open("/dev/random",O_RDONLY);
        if (os->fd == -1)
            return OPEN_RAN_E;
    }

    while (sz) {
        int len = (int)read(os->fd, output, sz);
        if (len == -1) {
            ret = READ_RAN_E;
            break;
        }

        sz     -= len;
        output += len;

        if (sz) {
#ifdef BLOCKING
            sleep(0);             /* context switch */
#else
            ret = RAN_BLOCK_E;
            break;
#endif
        }
    }
    close(os->fd);

    return ret;
}

#endif /* USE_WINDOWS_API */
#endif /* HAVE_FIPS */

