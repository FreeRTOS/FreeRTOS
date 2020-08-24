/* fips.c
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

/* in case user set HAVE_FIPS there */
#include <wolfssl/wolfcrypt/settings.h>

#ifdef HAVE_FIPS

#ifdef USE_WINDOWS_API
    #pragma code_seg(".fipsA$o")
    #pragma const_seg(".fipsB$o")
#endif


/* set FIPS_NO_WRAPPERS before headers, use direct internal f()s not wrappers */
#define FIPS_NO_WRAPPERS

#include <wolfssl/wolfcrypt/aes.h>
#include <wolfssl/wolfcrypt/des3.h>
#include <wolfssl/wolfcrypt/sha.h>
#include <wolfssl/wolfcrypt/sha256.h>
#include <wolfssl/wolfcrypt/sha512.h>
#include <wolfssl/wolfcrypt/sha3.h>
#include <wolfssl/wolfcrypt/hmac.h>
#include <wolfssl/wolfcrypt/cmac.h>
#include <wolfssl/wolfcrypt/rsa.h>
#include <wolfssl/wolfcrypt/ecc.h>
#include <wolfssl/wolfcrypt/dh.h>
#include <wolfssl/wolfcrypt/fips_test.h>
#include <wolfssl/wolfcrypt/random.h>
#include <wolfssl/wolfcrypt/error-crypt.h>


#ifdef HAVE_FORCE_FIPS_FAILURE
    #include <stdio.h>
    static void FIPS_MSG(const char* msg)
    {
        printf("%s\n", msg);
    }
#else
    #define FIPS_MSG(m)
#endif

#ifdef WOLFSSL_STM32L4
    extern HAL_StatusTypeDef HAL_Init(void);
    extern void wolfSSL_POS_SystemClock_Config(void);
#endif /* WOLFSSL_STM32L4 */


#ifdef USE_WINDOWS_API

    #define CCALL __cdecl
    #pragma section(".CRT$XCU",read)
    #define INITIALIZER(f) \
       static void __cdecl f(void); \
       __declspec(allocate(".CRT$XCU")) void (__cdecl*f##_)(void) = f; \
       static void __cdecl f(void)

#elif defined(NO_ATTRIBUTE_CONSTRUCTOR)

    #define INITIALIZER(f) void f(void)

#else

    #define INITIALIZER(f) static void __attribute__((constructor)) f(void)

#endif


/* power on self (pos) test status */
enum POS_STATUS {
    POS_NOT_DONE,    /* in progress, not complete yet */
    POS_FAILURE,     /* done, but failed  */
    POS_SUCCESS      /* done, and SUCCESS */
};

static enum POS_STATUS posStatus = POS_NOT_DONE;   /* our pos status */
static int             posReturn = 0;              /* pos return value */
static char base16_hash[WC_SHA256_DIGEST_SIZE*2+1];   /* caclulated hash */


/*
 * HAVE_THREAD_LS: means compiler provides a primitive local storage type.
 *
 * NO_THREAD_LS: works in SINGLE_THREADED mode OR where the compiler doesn't
 * provide local storage. It MUST be guaranteed that this is run in a single
 * task/thread and we are absolutely certain no other task/thread can access
 * the wolfcrypt module before execution of the power on self test has finished.
 * Note GetThisThreadInPos() MUST return correct value therefore no ops would
 * not work.
 */
#if defined(HAVE_THREAD_LS) || defined(NO_THREAD_LS)
    /* Note: this thread local stuff doesn't work in pre-Vista DLLs.
     * Need to use TlsAlloc, etc, in that case. */

    static THREAD_LS_T int thisThreadInPOS = 0;          /* per thread in pos */

    static INLINE int InitThisThreadInPOS(void)
    {
        return 0;
    }

    static INLINE int GetThisThreadInPOS(void)
    {
        return thisThreadInPOS;
    }

    static INLINE void SetThisThreadInPOS(int inPOS)
    {
        thisThreadInPOS = inPOS;
    }

#elif defined(USE_WINDOWS_API)
    /* Uses the WINAPI calls that TlsAlloc() the thread local
	 * storage rather than using the _declspec(thread) tags.
	 * pre-Vista DLLs, and DLLs loaded at runtime cannot use
	 * the declspec tag. */

    static DWORD thisThreadInPOSKey;

    static INLINE int InitThisThreadInPOS(void)
    {
        int* thisThreadInPOS;

        thisThreadInPOSKey = TlsAlloc();
        if (thisThreadInPOSKey == TLS_OUT_OF_INDEXES)
            return THREAD_STORE_KEY_E;

        thisThreadInPOS = (int*)malloc(sizeof(int));
        if (thisThreadInPOS == NULL)
            return MEMORY_E;

        *thisThreadInPOS = 0;

        if (TlsSetValue(thisThreadInPOSKey, (LPVOID)thisThreadInPOS) == 0) {
            free(thisThreadInPOS);
            return THREAD_STORE_SET_E;
        }

        return 0;
    }

    static INLINE int GetThisThreadInPOS(void)
    {
        int *thisThreadInPOS = TlsGetValue(thisThreadInPOSKey);

        if (thisThreadInPOS != NULL)
            return *thisThreadInPOS;

        return 0;
    }

    static INLINE void SetThisThreadInPOS(int inPOS)
    {
        int *thisThreadInPOS = TlsGetValue(thisThreadInPOSKey);

        if (thisThreadInPOS != NULL)
            *thisThreadInPOS = inPOS;
    }

    static INLINE void FreeThisThreadInPOS(void)
    {
        int* thisThreadInPOS = TlsGetValue(thisThreadInPOSKey);

        if (thisThreadInPOS != NULL)
            free(thisThreadInPOS);
        TlsFree(thisThreadInPOSKey);
    }

#else

    static pthread_key_t thisThreadInPOSKey;

    static INLINE int InitThisThreadInPOS(void)
    {
        int* thisThreadInPOS;

        if (pthread_key_create(&thisThreadInPOSKey, NULL) != 0)
            return THREAD_STORE_KEY_E;

        thisThreadInPOS = (int*)malloc(sizeof(int));
        if (thisThreadInPOS == NULL)
            return MEMORY_E;

        *thisThreadInPOS = 0;

        if (pthread_setspecific(thisThreadInPOSKey, thisThreadInPOS) != 0) {
            free(thisThreadInPOS);
            return THREAD_STORE_SET_E;
        }

        return 0;
    }

    static INLINE int GetThisThreadInPOS(void)
    {
        int *thisThreadInPOS = pthread_getspecific(thisThreadInPOSKey);

        if (thisThreadInPOS != NULL)
            return *thisThreadInPOS;

        return 0;
    }

    static INLINE void SetThisThreadInPOS(int inPOS)
    {
        int *thisThreadInPOS = pthread_getspecific(thisThreadInPOSKey);

        if (thisThreadInPOS != NULL)
            *thisThreadInPOS = inPOS;
    }

#endif

#ifndef NO_RNG
static wolfSSL_Mutex conTestMutex;       /* continous test mutex */
static int           conTestFailure = 0; /* in failure mode */
#endif

wolfCrypt_fips_cb errCb = NULL;                    /* error callback */

/* user callback setter for err result */
int wolfCrypt_SetCb_fips(wolfCrypt_fips_cb cbf)
{
    errCb = cbf;

    return 0;
}


/* check continuous test status, return 0 if status ok, else < 0 */
#ifndef NO_RNG
static int CheckConTestStatus(void)
{
    int localFailure = 0;

    if (LockMutex(&conTestMutex) != 0) {
        conTestFailure = 1;
        localFailure   = 1;
    } else {
        if (conTestFailure)
            localFailure = 1;
        UnLockMutex(&conTestMutex);
    }

    if (localFailure) {
        return -1;
    }

    return 0;
}
#endif

/* set continuous test failure status, return 0 on success */
#ifndef NO_RNG
static int SetConTestFailure(void)
{
    if (LockMutex(&conTestMutex) != 0) {
        conTestFailure = 1;
    } else {
        conTestFailure = 1;
        UnLockMutex(&conTestMutex);
    }

    return 0;
}
#endif


#ifdef HAVE_FORCE_FIPS_FAILURE

int wolfCrypt_SetStatus_fips(int status)
{
    if (status == DRBG_CONT_FIPS_E) {
#ifndef NO_RNG
        SetConTestFailure();
        return 0;
#else
        return NOT_COMPILED_IN;
#endif
    }
    else if (status < 0) {
        posStatus = POS_FAILURE;
        posReturn = status;
        return 0;
    }

    return BAD_FUNC_ARG;
}

#endif /* HAVE_FORCE_FIPS_FAILURE */


/* return 0 on allowed (success), < 0 on error */
static int FipsAllowed(void)
{
    if (posStatus == POS_NOT_DONE && GetThisThreadInPOS() == 1)
        return 0;  /* allow POS on this thread only */
    else if (posStatus == POS_FAILURE) {
        if (errCb)
            errCb(0, posReturn, base16_hash);
        return -1;
    }

#ifndef NO_RNG
    if (CheckConTestStatus() != 0) {
        if (errCb)
            errCb(0, DRBG_CONT_FIPS_E, base16_hash);
        return -1;
    }
#endif

    if (posStatus == POS_SUCCESS)
        return 0;

    return -1;  /* default failure */
}


/* power on self test proper, only function to change POS status, only called
 * by entry point */
static void DoSelfTest(void)
{
    FIPS_MSG("Starting Power On Self Test");

    /* switch to not done, mark this thread as in pos */
    posStatus = POS_NOT_DONE;

    if ( (posReturn = InitThisThreadInPOS()) != 0) {
        posStatus = POS_FAILURE;
        FIPS_MSG("Power On Self Test FAILURE");
        return;
    }

    SetThisThreadInPOS(1);

    /* do tests proper */
    if ( (posReturn = DoKnownAnswerTests(base16_hash,
                                         sizeof(base16_hash))) != 0) {
        posStatus = POS_FAILURE;
        SetThisThreadInPOS(0);
        FIPS_MSG("Power On Self Test FAILURE");
        return;
    }

    /* completed success */
    posStatus = POS_SUCCESS;
    SetThisThreadInPOS(0);

    FIPS_MSG("Power On Self Test SUCCESS");
}


/* fips entry point, auto */
INITIALIZER(fipsEntry)
{
#ifdef WOLFSSL_STM32L4
    /* Configure clock peripheral at 120MHz otherwise the tests take
     * more than 12 minutes to complete. With peripheral configured
     * takes 32 seconds */
    HAL_Init();
    wolfSSL_POS_SystemClock_Config();
#endif
#ifndef NO_RNG
    if (InitMutex(&conTestMutex) != 0) {
        conTestFailure = 1;
    }
#endif

    DoSelfTest();
}


#if defined(USE_WINDOWS_API) && defined(WOLFSSL_DLL)

BOOL WINAPI DllMain( HINSTANCE hinstDLL, DWORD fdwReason, LPVOID lpReserved )
{
    (void)hinstDLL;
    (void)lpReserved;

    switch (fdwReason) {
        case DLL_PROCESS_ATTACH:
            fipsEntry();
            break;
        case DLL_PROCESS_DETACH:
            #ifndef HAVE_THREAD_LS
                FreeThisThreadInPOS();
            #endif
            break;
    }

    return TRUE;
}

#endif


/* get current error status, 0 on ok */
int wolfCrypt_GetStatus_fips(void)
{
    if (posStatus != POS_SUCCESS)
        return posReturn;

#ifndef NO_RNG
    if (CheckConTestStatus() != 0)
        return DRBG_CONT_FIPS_E;
#endif

    return 0;
}


/* get current inCore hash */
const char* wolfCrypt_GetCoreHash_fips(void)
{
    return base16_hash;
}


const char* wolfCrypt_GetVersion_fips(void)
{
    return "v4.0";
}


/* Aes wrappers */
/* setkey wrapper */
#ifndef NO_AES
int AesSetKey_fips(Aes* aes, const byte* userKey, word32 keylen, const byte* iv,
                   int dir)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_AesSetKey(aes, userKey, keylen, iv, dir);
}


/* set iv wrapper */
int AesSetIV_fips(Aes* aes, const byte* iv)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_AesSetIV(aes, iv);
}

#ifdef HAVE_AES_ECB
/* ecb encrypt wrapper */
int AesEcbEncrypt_fips(Aes* aes, byte* out, const byte* in, word32 sz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_AesEcbEncrypt(aes, out, in, sz);
}


/* ecb decrypt wrapper */
int AesEcbDecrypt_fips(Aes* aes, byte* out, const byte* in, word32 sz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_AesEcbDecrypt(aes, out, in, sz);
}
#endif

#ifdef HAVE_AES_CBC
/* cbc encrypt wrapper */
int AesCbcEncrypt_fips(Aes* aes, byte* out, const byte* in, word32 sz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_AesCbcEncrypt(aes, out, in, sz);
}


/* cbc decrypt wrapper */
int AesCbcDecrypt_fips(Aes* aes, byte* out, const byte* in, word32 sz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_AesCbcDecrypt(aes, out, in, sz);
}
#endif

#ifdef WOLFSSL_AES_COUNTER
/* ctr encrypt wrapper */
int AesCtrEncrypt_fips(Aes* aes, byte* out, const byte* in, word32 sz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_AesCtrEncrypt(aes, out, in, sz);
}
#endif
#endif /* NO_AES */


/* gcm set key wrapper */
#ifdef HAVE_AESGCM
int AesGcmSetKey_fips(Aes* aes, const byte* key, word32 len)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_AesGcmSetKey(aes, key, len);
}


/* gcm set external iv wrapper */
int AesGcmSetExtIV_fips(Aes* aes, const byte* iv, word32 ivSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_AesGcmSetExtIV(aes, iv, ivSz);
}


/* gcm set internal iv wrapper */
int AesGcmSetIV_fips(Aes* aes, word32 ivSz, const byte* ivFixed,
                     word32 ivFixedSz, WC_RNG* rng)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_AesGcmSetIV(aes, ivSz, ivFixed, ivFixedSz, rng);
}


/* gcm encrypt wrapper */
int AesGcmEncrypt_fips(Aes* aes, byte* out, const byte* in, word32 sz,
                       byte* ivOut, word32 ivOutSz,
                       byte* authTag, word32 authTagSz,
                       const byte* authIn, word32 authInSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_AesGcmEncrypt_ex(aes, out, in, sz, ivOut, ivOutSz,
                               authTag, authTagSz, authIn, authInSz);
}


/* gcm decrypt wrapper */
int AesGcmDecrypt_fips(Aes* aes, byte* out, const byte* in,
                       word32 sz, const byte* iv, word32 ivSz,
                       const byte* authTag, word32 authTagSz,
                       const byte* authIn, word32 authInSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_AesGcmDecrypt(aes, out, in, sz, iv, ivSz, authTag, authTagSz,
                         authIn, authInSz);
}


/* GMAC convenience wrapper */
int Gmac_fips(const byte* key, word32 keySz, byte* iv, word32 ivSz,
              const byte* authIn, word32 authInSz,
              byte* authTag, word32 authTagSz, WC_RNG* rng)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Gmac(key, keySz, iv, ivSz, authIn, authInSz,
                   authTag, authTagSz, rng);
}


/* GMAC verify convenience wrapper */
int GmacVerify_fips(const byte* key, word32 keySz,
                    const byte* iv, word32 ivSz,
                    const byte* authIn, word32 authInSz,
                    const byte* authTag, word32 authTagSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_GmacVerify(key, keySz, iv, ivSz,
                         authIn, authInSz, authTag, authTagSz);
}
#endif /* HAVE_AESGCM */


#if defined(HAVE_AESCCM) && \
    defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2)
/* ccm set key wrapper */
int AesCcmSetKey_fips(Aes* aes, const byte* key, word32 len)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_AesCcmSetKey(aes, key, len);
}


/* ccm set nonce wrapper */
int AesCcmSetNonce_fips(Aes* aes, const byte* nonce, word32 nonceSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_AesCcmSetNonce(aes, nonce, nonceSz);
}


/* ccm encrypt wrapper */
int AesCcmEncrypt_fips(Aes* aes, byte* out, const byte* in,
                       word32 sz, byte* ivOut, word32 ivOutSz,
                       byte* authTag, word32 authTagSz,
                       const byte* authIn, word32 authInSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_AesCcmEncrypt_ex(aes, out, in, sz, ivOut, ivOutSz,
                               authTag, authTagSz, authIn, authInSz);
}


/* ccm decrypt wrapper */
int AesCcmDecrypt_fips(Aes* aes, byte* out, const byte* in,
                       word32 sz, const byte* iv, word32 ivSz,
                       const byte* authTag, word32 authTagSz,
                       const byte* authIn, word32 authInSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_AesCcmDecrypt(aes, out, in, sz, iv, ivSz, authTag, authTagSz,
                         authIn, authInSz);
}
#endif /* HAVE_AESCCM && HAVE_FIPS_VERSION 2 */


/* Des3 wrappers */
/* setkey wrapper */
#ifndef NO_DES3
int Des3_SetKey_fips(Des3* des, const byte* userKey, const byte* iv, int dir)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Des3_SetKey(des, userKey, iv, dir);
}


/* set iv wrapper */
int Des3_SetIV_fips(Des3* des, const byte* iv)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Des3_SetIV(des, iv);
}


/* cbc encrypt wrapper */
int Des3_CbcEncrypt_fips(Des3* des, byte* out, const byte* in, word32 sz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Des3_CbcEncrypt(des, out, in, sz);
}


/* cbc decrypt wrapper */
int Des3_CbcDecrypt_fips(Des3* des, byte* out, const byte* in, word32 sz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Des3_CbcDecrypt(des, out, in, sz);
}
#endif /* NO_DES3 */



/* Hash wrappers */
#ifndef NO_SHA
/* Init SHA wrapper */
int InitSha_fips(wc_Sha* sha)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_InitSha(sha);
}


/* SHA Update wrapper */
int ShaUpdate_fips(wc_Sha* sha, const byte* data, word32 len)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_ShaUpdate(sha, data, len);
}


/* SHA Final wrapper */
int ShaFinal_fips(wc_Sha* sha, byte* hash)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_ShaFinal(sha, hash);
}
#endif /* NO_SHA */


#ifndef NO_SHA256
/* Init SHA256 wrapper */
int InitSha256_fips(wc_Sha256* sha)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_InitSha256(sha);
}


/* SHA256 Update wrapper */
int Sha256Update_fips(wc_Sha256* sha, const byte* data, word32 len)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Sha256Update(sha, data, len);
}


/* SHA256 Final wrapper */
int Sha256Final_fips(wc_Sha256* sha, byte* hash)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Sha256Final(sha, hash);
}


#ifdef WOLFSSL_SHA224

/* Init SHA224 wrapper */
int InitSha224_fips(wc_Sha224* sha224)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_InitSha224(sha224);
}


/* SHA224 Update wrapper */
int Sha224Update_fips(wc_Sha224* sha224, const byte* data, word32 len)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Sha224Update(sha224, data, len);
}


/* SHA224 Final wrapper */
int Sha224Final_fips(wc_Sha224* sha224, byte* hash)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Sha224Final(sha224, hash);
}

#endif /* WOLFSSL_SHA224 */
#endif /* NO_SHA256 */


#ifdef WOLFSSL_SHA512
/* Init SHA512 wrapper */
int InitSha512_fips(wc_Sha512* sha)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_InitSha512(sha);
}


/* SHA512 Update wrapper */
int Sha512Update_fips(wc_Sha512* sha, const byte* data, word32 len)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Sha512Update(sha, data, len);
}


/* SHA512 Final wrapper */
int Sha512Final_fips(wc_Sha512* sha, byte* hash)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Sha512Final(sha, hash);
}
#endif /* WOLFSSL_SHA512 */


/* Init SHA384 wrapper */
#ifdef WOLFSSL_SHA384
int InitSha384_fips(wc_Sha384* sha)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_InitSha384(sha);
}


/* SHA384 Update wrapper */
int Sha384Update_fips(wc_Sha384* sha, const byte* data, word32 len)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Sha384Update(sha, data, len);
}


/* SHA384 Final wrapper */
int Sha384Final_fips(wc_Sha384* sha, byte* hash)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Sha384Final(sha, hash);
}
#endif /* WOLFSSL_SHA384 */


#ifdef WOLFSSL_SHA3
/* Base SHA-3 Functions */
int InitSha3_224_fips(wc_Sha3* sha3, void* heap, int devId)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    (void)heap;
    (void)devId;
    return wc_InitSha3_224(sha3, NULL, -1);
}


int Sha3_224_Update_fips(wc_Sha3* sha3, const byte* data, word32 len)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Sha3_224_Update(sha3, data, len);
}


int Sha3_224_Final_fips(wc_Sha3* sha3, byte* hash)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Sha3_224_Final(sha3, hash);
}


int InitSha3_256_fips(wc_Sha3* sha3, void* heap, int devId)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    (void)heap;
    (void)devId;
    return wc_InitSha3_256(sha3, NULL, -1);
}


int Sha3_256_Update_fips(wc_Sha3* sha3, const byte* data, word32 len)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Sha3_256_Update(sha3, data, len);
}


int Sha3_256_Final_fips(wc_Sha3* sha3, byte* hash)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Sha3_256_Final(sha3, hash);
}


int InitSha3_384_fips(wc_Sha3* sha3, void* heap, int devId)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    (void)heap;
    (void)devId;
    return wc_InitSha3_384(sha3, NULL, -1);
}


int Sha3_384_Update_fips(wc_Sha3* sha3, const byte* data, word32 len)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Sha3_384_Update(sha3, data, len);
}


int Sha3_384_Final_fips(wc_Sha3* sha3, byte* hash)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Sha3_384_Final(sha3, hash);
}


int InitSha3_512_fips(wc_Sha3* sha3, void* heap, int devId)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    (void)heap;
    (void)devId;
    return wc_InitSha3_512(sha3, NULL, -1);
}


int Sha3_512_Update_fips(wc_Sha3* sha3, const byte* data, word32 len)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Sha3_512_Update(sha3, data, len);
}


int Sha3_512_Final_fips(wc_Sha3* sha3, byte* hash)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_Sha3_512_Final(sha3, hash);
}
#endif /* WOLFSSL_SHA3 */


/* HMAC wrappers */
/* HMAC SetKey wrapper */
int HmacSetKey_fips(Hmac* hmac, int type, const byte* key, word32 keySz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_HmacSetKey(hmac, type, key, keySz);
}


/* HMAC Update wrapper */
int HmacUpdate_fips(Hmac* hmac, const byte* data, word32 len)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_HmacUpdate(hmac, data, len);
}


/* HMAC Final wrapper */
int HmacFinal_fips(Hmac* hmac, byte* hash)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_HmacFinal(hmac, hash);
}


#ifdef HAVE_HKDF

/* HDKF */
int HKDF_fips(int type, const byte* inKey, word32 inKeySz,
              const byte* salt, word32 saltSz,
              const byte* info, word32 infoSz,
              byte* out, word32 outSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_HKDF(type, inKey, inKeySz, salt, saltSz,
                   info, infoSz, out, outSz);
}


#endif /* HAVE_HKDF */


/* RSA wrappers */
#ifndef NO_RSA
/* Init RsaKey */
int InitRsaKey_fips(RsaKey* key, void* p)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_InitRsaKey(key, p);
}
int InitRsaKeyEx_fips(RsaKey* key, void* p, int devId)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_InitRsaKey_ex(key, p, devId);
}

/* Free RsaKey */
int FreeRsaKey_fips(RsaKey* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_FreeRsaKey(key);
}


/* Check RsaKey */
int CheckRsaKey_fips(RsaKey* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_CheckRsaKey(key);
}


/* Rsa Public Encrypt */
int RsaPublicEncrypt_fips(const byte* in,word32 inLen,byte* out,
                          word32 outLen, RsaKey* key, WC_RNG* rng)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaPublicEncrypt(in, inLen, out, outLen, key, rng);
}


/* Rsa Public Encrypt Extended */
int RsaPublicEncryptEx_fips(const byte* in, word32 inLen, byte* out,
                            word32 outLen, RsaKey* key, WC_RNG* rng, int type,
                            enum wc_HashType hash, int mgf, byte* label,
                            word32 labelSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaPublicEncrypt_ex(in, inLen, out, outLen, key, rng, type,
                                  hash, mgf, label, labelSz);
}


/* Rsa Private Decrypt Inline */
int RsaPrivateDecryptInline_fips(byte* in, word32 inLen,
                                 byte** out, RsaKey* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaPrivateDecryptInline(in, inLen, out, key);
}


/* Rsa Private Decrypt Inline Extended */
int RsaPrivateDecryptInlineEx_fips(byte* in, word32 inLen,
                                   byte** out, RsaKey* key, int type,
                                   enum wc_HashType hash, int mgf, byte* label,
                                   word32 labelSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaPrivateDecryptInline_ex(in, inLen, out, key, type,
                                         hash, mgf, label, labelSz);
}


/* Rsa Private Decrypt */
int RsaPrivateDecrypt_fips(const byte* in, word32 inLen,
                           byte* out,word32 outLen,RsaKey* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaPrivateDecrypt(in, inLen, out, outLen, key);
}


/* Rsa Private Decrypt Extended */
int RsaPrivateDecryptEx_fips(const byte* in, word32 inLen,
                             byte* out, word32 outLen, RsaKey* key, int type,
                             enum wc_HashType hash, int mgf, byte* label,
                             word32 labelSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaPrivateDecrypt_ex(in, inLen, out, outLen, key, type,
                                   hash, mgf, label, labelSz);
}


/* Rsa SSL Sign */
int RsaSSL_Sign_fips(const byte* in, word32 inLen, byte* out,
                     word32 outLen, RsaKey* key, WC_RNG* rng)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaSSL_Sign(in, inLen, out, outLen, key, rng);
}


/* Rsa SSL Verify Inline */
int RsaSSL_VerifyInline_fips(byte* in, word32 inLen, byte** out, RsaKey* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaSSL_VerifyInline(in, inLen, out, key);
}


/* Rsa SSL Verify */
int RsaSSL_Verify_fips(const byte* in, word32 inLen, byte* out,
                       word32 outLen, RsaKey* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaSSL_Verify(in, inLen, out, outLen, key);
}


#ifdef WC_RSA_PSS
/* Rsa PSS Sign */
int RsaPSS_Sign_fips(const byte* in, word32 inLen, byte* out, word32 outLen,
                     enum wc_HashType hash, int mgf, RsaKey* key, WC_RNG* rng)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaPSS_Sign(in, inLen, out, outLen, hash, mgf, key, rng);
}


/* Rsa PSS Sign Extended */
int RsaPSS_SignEx_fips(const byte* in, word32 inLen, byte* out, word32 outLen,
                       enum wc_HashType hash, int mgf, int saltLen,
                       RsaKey* key, WC_RNG* rng)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaPSS_Sign_ex(in, inLen, out, outLen,
                             hash, mgf, saltLen, key, rng);
}


/* Rsa PSS Verify Inline */
int RsaPSS_VerifyInline_fips(byte* in, word32 inLen, byte** out,
                             enum wc_HashType hash, int mgf, RsaKey* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaPSS_VerifyInline(in, inLen, out, hash, mgf, key);
}


/* Rsa PSS Verify Inline Extended */
int RsaPSS_VerifyInlineEx_fips(byte* in, word32 inLen, byte** out,
                               enum wc_HashType hash, int mgf,
                               int saltLen, RsaKey* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaPSS_VerifyInline_ex(in, inLen, out, hash, mgf, saltLen, key);
}


/* Rsa PSS Verify */
int RsaPSS_Verify_fips(byte* in, word32 inLen, byte* out, word32 outLen,
                       enum wc_HashType hash, int mgf, RsaKey* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaPSS_Verify(in, inLen, out, outLen, hash, mgf, key);
}


/* Rsa PSS Verify Extended */
int RsaPSS_VerifyEx_fips(byte* in, word32 inLen, byte* out, word32 outLen,
                               enum wc_HashType hash, int mgf,
                               int saltLen, RsaKey* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaPSS_Verify_ex(in, inLen, out, outLen, hash,
                               mgf, saltLen, key);
}


/* Rsa PSS Check Padding */
int RsaPSS_CheckPadding_fips(const byte* in, word32 inSz,
                             byte* sig, word32 sigSz,
                             enum wc_HashType hashType)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaPSS_CheckPadding(in, inSz, sig, sigSz, hashType);
}


/* Rsa PSS Check Padding Extended */
int RsaPSS_CheckPaddingEx_fips(const byte* in, word32 inSz,
                               byte* sig, word32 sigSz,
                               enum wc_HashType hashType,
                               int saltLen, int bits)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaPSS_CheckPadding_ex(in, inSz, sig, sigSz, hashType,
                                     saltLen, bits);
}
#endif

/* Rsa Encrypt Size */
int RsaEncryptSize_fips(RsaKey* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaEncryptSize(key);
}

#if 0
/* Rsa PrivateKey Decode */
int RsaPrivateKeyDecode_fips(const byte* input, word32* inOutIdx, RsaKey* key,
                             word32 inSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaPrivateKeyDecode(input, inOutIdx, key, inSz);
}


/* Rsa PublicKey Decode */
int RsaPublicKeyDecode_fips(const byte* input, word32* inOutIdx, RsaKey* key,
                            word32 inSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaPublicKeyDecode(input, inOutIdx, key, inSz);
}
#endif


/* Rsa Export Key */
int RsaExportKey_fips(RsaKey* key,
                      byte* e, word32* eSz, byte* n, word32* nSz,
                      byte* d, word32* dSz, byte* p, word32* pSz,
                      byte* q, word32* qSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_RsaExportKey(key, e, eSz, n, nSz, d, dSz, p, pSz, q, qSz);
}


#ifdef WOLFSSL_KEY_GEN
/* Rsa Check Probable Prime */
int CheckProbablePrime_fips(const byte* p, word32 pSz,
                            const byte* q, word32 qSz,
                            const byte* e, word32 eSz,
                            int nlen, int* isPrime)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_CheckProbablePrime(p, pSz, q, qSz, e, eSz, nlen, isPrime);
}

/* Rsa Key Gen */
int MakeRsaKey_fips(RsaKey* key, int size, long e, WC_RNG* rng)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_MakeRsaKey(key, size, e, rng);
}
#endif

#endif /* NO_RSA */


/* Base ECC Functions */
#ifdef HAVE_ECC

/* init ECC key */
WOLFSSL_API int ecc_init_fips(ecc_key* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_ecc_init(key);
}


/* free ECC key */
WOLFSSL_API int ecc_free_fips(ecc_key* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_ecc_free(key);
}


/* check ECC key */
WOLFSSL_API int ecc_check_key_fips(ecc_key* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_ecc_check_key(key);
}


/* make ECC key */
WOLFSSL_API int ecc_make_key_fips(WC_RNG* rng, int keysize, ecc_key* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_ecc_make_key(rng, keysize, key);
}


/* make ECC key extended */
WOLFSSL_API int ecc_make_key_ex_fips(WC_RNG* rng, int keysize, ecc_key* key,
                                     int curve_id)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_ecc_make_key_ex(rng, keysize, key, curve_id);
}

#endif /* HAVE_ECC */


#if defined(HAVE_ECC) && defined(HAVE_ECC_KEY_EXPORT)

/* ECC Key Export Function */
WOLFSSL_API int ecc_export_x963_fips(ecc_key* key,
                                     byte* out, word32* outLen)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_ecc_export_x963(key, out, outLen);
}

#endif /* HAVE_ECC && HAVE_ECC_KEY_EXPORT */


#if defined(HAVE_ECC) && defined(HAVE_ECC_KEY_IMPORT)

/* ECC Key Import Function */
WOLFSSL_API int ecc_import_x963_fips(const byte* in, word32 inLen,
                                     ecc_key* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_ecc_import_x963(in, inLen, key);
}

#endif /* HAVE_ECC && HAVE_ECC_KEY_EXPORT */


#if defined(HAVE_ECC) && defined(HAVE_ECC_DHE)

/* ECC DHE Function */
WOLFSSL_API int ecc_shared_secret_fips(ecc_key* private_key,
                                       ecc_key* public_key,
                                       byte* out, word32* outlen)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_ecc_shared_secret(private_key, public_key, out, outlen);
}

#endif /* HAVE_ECC && HAVE_ECC_DHE */


#if defined(HAVE_ECC) && defined(HAVE_ECC_SIGN)

/* ECDSA Signing Function */
WOLFSSL_API int ecc_sign_hash_fips(const byte* in, word32 inlen,
                                   byte* out, word32 *outlen,
                                   WC_RNG* rng, ecc_key* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_ecc_sign_hash(in, inlen, out, outlen, rng, key);
}

#endif /* HAVE_ECC && HAVE_ECC_SIGN */


/* ECDSA Signature Verify Function */
#if defined(HAVE_ECC) && defined(HAVE_ECC_VERIFY)

WOLFSSL_API int ecc_verify_hash_fips(const byte* sig, word32 siglen,
                                     const byte* hash, word32 hashlen,
                                     int* stat, ecc_key* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_ecc_verify_hash(sig, siglen, hash, hashlen, stat, key);
}

#endif /* HAVE_ECC && HAVE_ECC_VERIFY */


/* Base DH Functions */
#ifndef NO_DH

/* Init DH key */
int InitDhKey_fips(DhKey* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_InitDhKey(key);
}


/* Free DH Key */
int FreeDhKey_fips(DhKey* key)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_FreeDhKey(key);
}


/* Set DH Key */
int DhSetKeyEx_fips(DhKey* key, const byte* p, word32 pSz,
                    const byte* g, word32 gSz, const byte* q, word32 qSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_DhSetKey_ex(key, p, pSz, g, gSz, q, qSz);
}


/* Generate a DH key pair */
int DhGenerateKeyPair_fips(DhKey* key, WC_RNG* rng, byte* priv, word32* privSz,
                           byte* pub, word32* pubSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_DhGenerateKeyPair(key, rng, priv, privSz, pub, pubSz);
}


/* Check a DH public key for mathematical correctness */
int DhCheckPubKeyEx_fips(DhKey* key, const byte* pub, word32 pubSz,
                         const byte* prime, word32 primeSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_DhCheckPubKey_ex(key, pub, pubSz, prime, primeSz);
}


/* Check a DH private key for mathematical correctness */
int DhCheckPrivKeyEx_fips(DhKey* key, const byte* priv, word32 privSz,
                          const byte* prime, word32 primeSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_DhCheckPrivKey_ex(key, priv, privSz, prime, primeSz);
}


/* Check a DH public and private key for pair-wise consistency */
int DhCheckKeyPair_fips(DhKey* key, const byte* pub, word32 pubSz,
                        const byte* priv, word32 privSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_DhCheckKeyPair(key, pub, pubSz, priv, privSz);
}


/* Generate shared secret with DH */
int DhAgree_fips(DhKey* key, byte* agree, word32* agreeSz,
                 const byte* priv, word32 privSz, const byte* otherPub,
                 word32 pubSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_DhAgree(key, agree, agreeSz, priv, privSz, otherPub, pubSz);
}

#endif /* NO_DH */


/* Init RNG */
#ifndef NO_RNG
int InitRng_fips(WC_RNG* rng)
{
    int ret;

    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    ret = wc_InitRng(rng);
    if (ret == DRBG_CONT_FIPS_E) {
        SetConTestFailure();
        return DRBG_CONT_FIPS_E;
    }

    return ret;
}


/* Init RNG with Nonce */
int InitRngNonce_fips(WC_RNG* rng, byte* nonce, word32 nonceSz)
{
    int ret;

    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    ret = wc_InitRngNonce(rng, nonce, nonceSz);
    if (ret == DRBG_CONT_FIPS_E) {
        SetConTestFailure();
        return DRBG_CONT_FIPS_E;
    }

    return ret;
}


/* Free RNG */
int FreeRng_fips(WC_RNG* rng)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_FreeRng(rng);
}


/* Generate block of pseudo random numbers */
int RNG_GenerateBlock_fips(WC_RNG* rng, byte* buf, word32 bufSz)
{
    int ret;

    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    ret = wc_RNG_GenerateBlock(rng, buf, bufSz);
    if (ret == DRBG_CONT_FIPS_E) {
        SetConTestFailure();
        return DRBG_CONT_FIPS_E;
    }

    return ret;
}


/* RNG Health Test */
int RNG_HealthTest_fips(int reseed, const byte* entropyA, word32 entropyASz,
                                    const byte* entropyB, word32 entropyBSz,
                                    byte* output, word32 outputSz)
{
    int ret;

    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    ret = wc_RNG_HealthTest(reseed, entropyA, entropyASz, entropyB, entropyBSz,
                                                              output, outputSz);
    if (ret == DRBG_CONT_FIPS_E) {
        SetConTestFailure();
        return DRBG_CONT_FIPS_E;
    }

    return ret;
}
#endif /* NO_RNG */


/* CMAC API */
#ifdef WOLFSSL_CMAC

/* Init CMAC */
int InitCmac_fips(Cmac* cmac, const byte* key, word32 keySz,
                                    int type, void* unused)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_InitCmac(cmac, key, keySz, type, unused);
}


/*  CMAC Update */
int CmacUpdate_fips(Cmac* cmac, const byte* in, word32 inSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_CmacUpdate(cmac, in, inSz);
}


/*  CMAC Final */
int CmacFinal_fips(Cmac* cmac, byte* out, word32* outSz)
{
    if (FipsAllowed() != 0)
        return FIPS_NOT_ALLOWED_E;

    return wc_CmacFinal(cmac, out, outSz);
}

#endif /* WOLFSSL_CMAC */


#endif /* HAVE_FIPS */
