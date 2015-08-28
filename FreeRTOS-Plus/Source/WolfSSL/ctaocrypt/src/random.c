/* random.c
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

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <cyassl/ctaocrypt/settings.h>

/* on HPUX 11 you may need to install /dev/random see
   http://h20293.www2.hp.com/portal/swdepot/displayProductInfo.do?productNumber=KRNG11I

*/

#ifdef HAVE_FIPS
    /* set NO_WRAPPERS before headers, use direct internal f()s not wrappers */
    #define FIPS_NO_WRAPPERS
#endif

#include <cyassl/ctaocrypt/random.h>
#include <cyassl/ctaocrypt/error-crypt.h>

#if defined(HAVE_HASHDRBG) || defined(NO_RC4)

    #include <cyassl/ctaocrypt/sha256.h>

    #ifdef NO_INLINE
        #include <cyassl/ctaocrypt/misc.h>
    #else
        #include <ctaocrypt/src/misc.c>
    #endif
#endif /* HAVE_HASHDRBG || NO_RC4 */

#if defined(USE_WINDOWS_API)
    #ifndef _WIN32_WINNT
        #define _WIN32_WINNT 0x0400
    #endif
    #include <windows.h>
    #include <wincrypt.h>
#else
    #if !defined(NO_DEV_RANDOM) && !defined(CYASSL_MDK_ARM) \
                                && !defined(CYASSL_IAR_ARM)
            #include <fcntl.h>
        #ifndef EBSNET
            #include <unistd.h>
        #endif
    #else
        /* include headers that may be needed to get good seed */
    #endif
#endif /* USE_WINDOWS_API */


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

/* RNG health states */
#define DRBG_NOT_INIT     0
#define DRBG_OK           1
#define DRBG_FAILED       2


enum {
    drbgInitC     = 0,
    drbgReseed    = 1,
    drbgGenerateW = 2,
    drbgGenerateH = 3,
    drbgInitV
};


/* Hash Derivation Function */
/* Returns: DRBG_SUCCESS or DRBG_FAILURE */
static int Hash_df(RNG* rng, byte* out, word32 outSz, byte type,
                                                  const byte* inA, word32 inASz,
                                                  const byte* inB, word32 inBSz)
{
    byte ctr;
    int i;
    int len;
    word32 bits = (outSz * 8); /* reverse byte order */

    #ifdef LITTLE_ENDIAN_ORDER
        bits = ByteReverseWord32(bits);
    #endif
    len = (outSz / OUTPUT_BLOCK_LEN)
        + ((outSz % OUTPUT_BLOCK_LEN) ? 1 : 0);

    for (i = 0, ctr = 1; i < len; i++, ctr++)
    {
        if (InitSha256(&rng->sha) != 0)
            return DRBG_FAILURE;

        if (Sha256Update(&rng->sha, &ctr, sizeof(ctr)) != 0)
            return DRBG_FAILURE;

        if (Sha256Update(&rng->sha, (byte*)&bits, sizeof(bits)) != 0)
            return DRBG_FAILURE;

        /* churning V is the only string that doesn't have 
         * the type added */
        if (type != drbgInitV)
            if (Sha256Update(&rng->sha, &type, sizeof(type)) != 0)
                return DRBG_FAILURE;

        if (Sha256Update(&rng->sha, inA, inASz) != 0)
            return DRBG_FAILURE;

        if (inB != NULL && inBSz > 0)
            if (Sha256Update(&rng->sha, inB, inBSz) != 0)
                return DRBG_FAILURE;

        if (Sha256Final(&rng->sha, rng->digest) != 0)
            return DRBG_FAILURE;

        if (outSz > OUTPUT_BLOCK_LEN) {
            XMEMCPY(out, rng->digest, OUTPUT_BLOCK_LEN);
            outSz -= OUTPUT_BLOCK_LEN;
            out += OUTPUT_BLOCK_LEN;
        }
        else {
            XMEMCPY(out, rng->digest, outSz);
        }
    }

    return DRBG_SUCCESS;
}


/* Returns: DRBG_SUCCESS or DRBG_FAILURE */
static int Hash_DRBG_Reseed(RNG* rng, const byte* entropy, word32 entropySz)
{
    byte seed[DRBG_SEED_LEN];

    if (Hash_df(rng, seed, sizeof(seed), drbgReseed, rng->V, sizeof(rng->V),
                                          entropy, entropySz) != DRBG_SUCCESS) {
        return DRBG_FAILURE;
    }

    XMEMCPY(rng->V, seed, sizeof(rng->V));
    XMEMSET(seed, 0, sizeof(seed));

    if (Hash_df(rng, rng->C, sizeof(rng->C), drbgInitC, rng->V,
                                     sizeof(rng->V), NULL, 0) != DRBG_SUCCESS) {
        return DRBG_FAILURE;
    }

    rng->reseedCtr = 1;
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
static int Hash_gen(RNG* rng, byte* out, word32 outSz, const byte* V)
{
    byte data[DRBG_SEED_LEN];
    int i;
    int len = (outSz / OUTPUT_BLOCK_LEN)
        + ((outSz % OUTPUT_BLOCK_LEN) ? 1 : 0);

    XMEMCPY(data, V, sizeof(data));
    for (i = 0; i < len; i++) {
        if (InitSha256(&rng->sha) != 0 ||
            Sha256Update(&rng->sha, data, sizeof(data)) != 0 ||
            Sha256Final(&rng->sha, rng->digest) != 0) {

            return DRBG_FAILURE;
        }

        if (outSz > OUTPUT_BLOCK_LEN) {
            XMEMCPY(out, rng->digest, OUTPUT_BLOCK_LEN);
            outSz -= OUTPUT_BLOCK_LEN;
            out += OUTPUT_BLOCK_LEN;
            array_add_one(data, DRBG_SEED_LEN);
        }
        else {
            XMEMCPY(out, rng->digest, outSz);
        }
    }
    XMEMSET(data, 0, sizeof(data));

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
            d[dIdx] = carry;
            carry >>= 8;
        }
        if (dIdx > 0)
            d[dIdx] += carry;
    }
}


/* Returns: DRBG_SUCCESS, DRBG_NEED_RESEED, or DRBG_FAILURE */
static int Hash_DRBG_Generate(RNG* rng, byte* out, word32 outSz)
{
    int ret = DRBG_NEED_RESEED;

    if (rng->reseedCtr != RESEED_INTERVAL) {
        byte type = drbgGenerateH;
        word32 reseedCtr = rng->reseedCtr;

        rng->reseedCtr++;
        if (Hash_gen(rng, out, outSz, rng->V) != 0 ||
            InitSha256(&rng->sha) != 0 ||
            Sha256Update(&rng->sha, &type, sizeof(type)) != 0 ||
            Sha256Update(&rng->sha, rng->V, sizeof(rng->V)) != 0 ||
            Sha256Final(&rng->sha, rng->digest) != 0) {

            ret = DRBG_FAILURE;
        }
        else {
            array_add(rng->V, sizeof(rng->V), rng->digest, sizeof(rng->digest));
            array_add(rng->V, sizeof(rng->V), rng->C, sizeof(rng->C));
            #ifdef LITTLE_ENDIAN_ORDER
                reseedCtr = ByteReverseWord32(reseedCtr);
            #endif
            array_add(rng->V, sizeof(rng->V),
                                          (byte*)&reseedCtr, sizeof(reseedCtr));
            ret = DRBG_SUCCESS;
        }
    }

    return ret;
}


/* Returns: DRBG_SUCCESS or DRBG_FAILURE */
static int Hash_DRBG_Instantiate(RNG* rng, const byte* seed, word32 seedSz,
                                           const byte* nonce, word32 nonceSz)
{
    int ret = DRBG_FAILURE;

    XMEMSET(rng, 0, sizeof(*rng));

    if (Hash_df(rng, rng->V, sizeof(rng->V), drbgInitV, seed, seedSz,
                                              nonce, nonceSz) == DRBG_SUCCESS &&
        Hash_df(rng, rng->C, sizeof(rng->C), drbgInitC, rng->V,
                                     sizeof(rng->V), NULL, 0) == DRBG_SUCCESS) {

        rng->reseedCtr = 1;
        ret = DRBG_SUCCESS;
    }

    return ret;
}


/* Returns: DRBG_SUCCESS */
static int Hash_DRBG_Uninstantiate(RNG* rng)
{
    XMEMSET(rng, 0, sizeof(*rng));

    return DRBG_SUCCESS;
}

/* End NIST DRBG Code */


/* Get seed and key cipher */
int InitRng(RNG* rng)
{
    int ret = BAD_FUNC_ARG;

    if (rng != NULL) {
        byte entropy[ENTROPY_NONCE_SZ];

        /* This doesn't use a separate nonce. The entropy input will be
         * the default size plus the size of the nonce making the seed
         * size. */
        if (GenerateSeed(&rng->seed, entropy, ENTROPY_NONCE_SZ) == 0 &&
            Hash_DRBG_Instantiate(rng, entropy, ENTROPY_NONCE_SZ,
                                                     NULL, 0) == DRBG_SUCCESS) {
            rng->status = DRBG_OK;
            ret = 0;
        }
        else {
            rng->status = DRBG_FAILED;
            ret = RNG_FAILURE_E;
        }

        XMEMSET(entropy, 0, ENTROPY_NONCE_SZ);
    }

    return ret;
}


/* place a generated block in output */
int RNG_GenerateBlock(RNG* rng, byte* output, word32 sz)
{
    int ret;

    if (rng == NULL || output == NULL || sz > MAX_REQUEST_LEN)
        return BAD_FUNC_ARG;

    if (rng->status != DRBG_OK)
        return RNG_FAILURE_E;

    ret = Hash_DRBG_Generate(rng, output, sz);
    if (ret == DRBG_SUCCESS) {
        ret = 0;
    }
    else if (ret == DRBG_NEED_RESEED) {
        byte entropy[ENTROPY_SZ];

        if (GenerateSeed(&rng->seed, entropy, ENTROPY_SZ) == 0 &&
                Hash_DRBG_Reseed(rng, entropy, ENTROPY_SZ) == DRBG_SUCCESS &&
                Hash_DRBG_Generate(rng, output, sz) == DRBG_SUCCESS) {

            ret = 0;
        }
        else {
            ret = RNG_FAILURE_E;
            rng->status = DRBG_FAILED;
        }

        XMEMSET(entropy, 0, ENTROPY_SZ);
    }
    else {
        ret = RNG_FAILURE_E;
        rng->status = DRBG_FAILED;
    }

    return ret;
}


int RNG_GenerateByte(RNG* rng, byte* b)
{
    return RNG_GenerateBlock(rng, b, 1);
}


int FreeRng(RNG* rng)
{
    int ret = BAD_FUNC_ARG;

    if (rng != NULL) {
        if (Hash_DRBG_Uninstantiate(rng) == DRBG_SUCCESS)
            ret = 0;
        else
            ret = RNG_FAILURE_E;
    }

    return ret;
}


int RNG_HealthTest(int reseed, const byte* entropyA, word32 entropyASz,
                               const byte* entropyB, word32 entropyBSz,
                               const byte* output, word32 outputSz)
{
    RNG rng;
    byte check[SHA256_DIGEST_SIZE * 4];

    if (Hash_DRBG_Instantiate(&rng, entropyA, entropyASz, NULL, 0) != 0)
        return -1;

    if (reseed) {
        if (Hash_DRBG_Reseed(&rng, entropyB, entropyBSz) != 0) {
            Hash_DRBG_Uninstantiate(&rng);
            return -1;
        }
    }

    if (Hash_DRBG_Generate(&rng, check, sizeof(check)) != 0) {
        Hash_DRBG_Uninstantiate(&rng);
        return -1;
    }

    if (Hash_DRBG_Generate(&rng, check, sizeof(check)) != 0) {
        Hash_DRBG_Uninstantiate(&rng);
        return -1;
    }

    if (outputSz != sizeof(check) || XMEMCMP(output, check, sizeof(check))) {
        Hash_DRBG_Uninstantiate(&rng);
        return -1;
    }

    Hash_DRBG_Uninstantiate(&rng);

    return 0;
}


#else /* HAVE_HASHDRBG || NO_RC4 */

/* Get seed and key cipher */
int InitRng(RNG* rng)
{
    int  ret;
#ifdef CYASSL_SMALL_STACK
    byte* key;
    byte* junk;
#else
    byte key[32];
    byte junk[256];
#endif

#ifdef HAVE_CAVIUM
    if (rng->magic == CYASSL_RNG_CAVIUM_MAGIC)
        return 0;
#endif

#ifdef CYASSL_SMALL_STACK
    key = (byte*)XMALLOC(32, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (key == NULL)
        return MEMORY_E;

    junk = (byte*)XMALLOC(256, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (junk == NULL) {
        XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
#endif

    ret = GenerateSeed(&rng->seed, key, 32);

    if (ret == 0) {
        Arc4SetKey(&rng->cipher, key, sizeof(key));

        ret = RNG_GenerateBlock(rng, junk, 256); /*rid initial state*/
    }

#ifdef CYASSL_SMALL_STACK
    XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(junk, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#ifdef HAVE_CAVIUM
    static void CaviumRNG_GenerateBlock(RNG* rng, byte* output, word32 sz);
#endif

/* place a generated block in output */
int RNG_GenerateBlock(RNG* rng, byte* output, word32 sz)
{
#ifdef HAVE_CAVIUM
    if (rng->magic == CYASSL_RNG_CAVIUM_MAGIC)
        return CaviumRNG_GenerateBlock(rng, output, sz);
#endif
    XMEMSET(output, 0, sz);
    Arc4Process(&rng->cipher, output, output, sz);

    return 0;
}


int RNG_GenerateByte(RNG* rng, byte* b)
{
    return RNG_GenerateBlock(rng, b, 1);
}


#ifdef HAVE_CAVIUM

#include <cyassl/ctaocrypt/logging.h>
#include "cavium_common.h"

/* Initiliaze RNG for use with Nitrox device */
int InitRngCavium(RNG* rng, int devId)
{
    if (rng == NULL)
        return -1;

    rng->devId = devId;
    rng->magic = CYASSL_RNG_CAVIUM_MAGIC;

    return 0;
}


static void CaviumRNG_GenerateBlock(RNG* rng, byte* output, word32 sz)
{
    word   offset = 0;
    word32 requestId;

    while (sz > CYASSL_MAX_16BIT) {
        word16 slen = (word16)CYASSL_MAX_16BIT;
        if (CspRandom(CAVIUM_BLOCKING, slen, output + offset, &requestId,
                      rng->devId) != 0) {
            CYASSL_MSG("Cavium RNG failed");
        }
        sz     -= CYASSL_MAX_16BIT;
        offset += CYASSL_MAX_16BIT;
    }
    if (sz) {
        word16 slen = (word16)sz;
        if (CspRandom(CAVIUM_BLOCKING, slen, output + offset, &requestId,
                      rng->devId) != 0) {
            CYASSL_MSG("Cavium RNG failed");
        }
    }
}

#endif /* HAVE_CAVIUM */

#endif /* HAVE_HASHDRBG || NO_RC4 */


#if defined(USE_WINDOWS_API)


int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
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


int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
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

int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
{
    #if (NET_SECURE_MGR_CFG_EN == DEF_ENABLED)
        NetSecure_InitSeed(output, sz);
    #endif
    return 0;
}

#elif defined(MBED)

/* write a real one !!!, just for testing board */
int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
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
    #if !defined(CYASSL_MICROCHIP_PIC32MZ)
        #include <peripheral/timer.h>
    #endif
    #define PIC32_SEED_COUNT ReadCoreTimer
#endif
    #ifdef CYASSL_MIC32MZ_RNG
        #include "xc.h"
        int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
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
#ifdef DEBUG_CYASSL
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
    #else  /* CYASSL_MIC32MZ_RNG */
        /* uses the core timer, in nanoseconds to seed srand */
        int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
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
    #endif /* CYASSL_MIC32MZ_RNG */

#elif defined(FREESCALE_MQX)

    #ifdef FREESCALE_K70_RNGA
        /*
         * Generates a RNG seed using the Random Number Generator Accelerator
         * on the Kinetis K70. Documentation located in Chapter 37 of
         * K70 Sub-Family Reference Manual (see Note 3 in the README for link).
         */
        int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
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
         * Generates a RNG seed using the Random Number Generator (RNGB)
         * on the Kinetis K53. Documentation located in Chapter 33 of
         * K53 Sub-Family Reference Manual (see note in the README for link).
         */
        int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
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

        int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
        {
            int i;
            for (i = 0; i < sz; i++ )
                output[i] = i;

            return 0;
        }
	#endif /* FREESCALE_K70_RNGA */

#elif defined(CYASSL_SAFERTOS) || defined(CYASSL_LEANPSK) \
   || defined(CYASSL_IAR_ARM)  || defined(CYASSL_MDK_ARM)

#warning "write a real random seed!!!!, just for testing now"

int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
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
     * Generate a RNG seed using the hardware random number generator
     * on the STM32F2. Documentation located in STM32F2xx Standard Peripheral
     * Library document (See note in README).
     */
    int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
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
#elif defined(CYASSL_LPC43xx) || defined(CYASSL_STM32F2xx)

    #warning "write a real random seed!!!!, just for testing now"

    int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
    {
        int i;

        for (i = 0; i < sz; i++ )
            output[i] = i;

        return 0;
    }

#elif defined(CUSTOM_RAND_GENERATE)

   /* Implement your own random generation function
    * word32 rand_gen(void);
    * #define CUSTOM_RAND_GENERATE  rand_gen  */

   int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
   {
     int i;

     for (i = 0; i < sz; i++ )
         output[i] = CUSTOM_RAND_GENERATE();

     return 0;
   }

#elif defined(NO_DEV_RANDOM)

#error "you need to write an os specific GenerateSeed() here"

/*
int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
{
    return 0;
}
*/


#else /* !USE_WINDOWS_API && !HAVE_RPT_SYS && !MICRIUM && !NO_DEV_RANDOM */


/* may block */
int GenerateSeed(OS_Seed* os, byte* output, word32 sz)
{
    int ret = 0;

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

