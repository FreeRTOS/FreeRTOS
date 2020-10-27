/* test.c
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

#ifndef WOLFSSL_USER_SETTINGS
    #include <wolfssl/options.h>
#endif
#include <wolfssl/wolfcrypt/settings.h>
#include <wolfssl/version.h>
#include <wolfssl/wolfcrypt/wc_port.h>

#ifndef NO_CRYPT_TEST

/* only for stack size check */
#ifdef HAVE_STACK_SIZE
    #include <wolfssl/ssl.h>
    #define err_sys err_sys_remap /* remap err_sys */
    #include <wolfssl/test.h>
    #undef err_sys
#endif

#ifdef USE_FLAT_TEST_H
    #include "test.h"
#else
    #include "wolfcrypt/test/test.h"
#endif

/* printf mappings */
#if defined(FREESCALE_MQX) || defined(FREESCALE_KSDK_MQX)
    #include <mqx.h>
    #include <stdlib.h>
    /* see wc_port.h for fio.h and nio.h includes */
#elif defined(FREESCALE_KSDK_BM)
    #include "fsl_debug_console.h"
    #undef printf
    #define printf PRINTF
#elif defined(WOLFSSL_APACHE_MYNEWT)
    #include <assert.h>
    #include <string.h>
    #include "sysinit/sysinit.h"
    #include "os/os.h"
    #ifdef ARCH_sim
    #include "mcu/mcu_sim.h"
    #endif
    #include "os/os_time.h"
#elif defined(WOLFSSL_ESPIDF)
    #include <time.h>
    #include <sys/time.h>
#elif defined(WOLFSSL_ZEPHYR)
    #include <stdio.h>

    #define printf printk
#elif defined(MICRIUM)
    #include <bsp_ser.h>
    void BSP_Ser_Printf (CPU_CHAR* format, ...);
    #undef printf
    #define printf BSP_Ser_Printf
#elif defined(WOLFSSL_PB)
    #include <stdarg.h>
    int wolfssl_pb_print(const char*, ...);
    #undef printf
    #define printf wolfssl_pb_print
#elif defined(WOLFSSL_TELIT_M2MB)
    #include "wolfssl/wolfcrypt/wc_port.h" /* for m2mb headers */
    #include "m2m_log.h" /* for M2M_LOG_INFO - not standard API */
    /* remap printf */
    #undef printf
    #define printf M2M_LOG_INFO
    /* OS requires occasional sleep() */
    #ifndef TEST_SLEEP_MS
        #define TEST_SLEEP_MS 50
    #endif
    #define TEST_SLEEP() m2mb_os_taskSleep(M2MB_OS_MS2TICKS(TEST_SLEEP_MS))
    /* don't use file system for these tests, since ./certs dir isn't loaded */
    #undef  NO_FILESYSTEM
    #define NO_FILESYSTEM
#elif defined(THREADX) && !defined(WOLFSSL_WICED) && !defined(THREADX_NO_DC_PRINTF)
    /* since just testing, use THREADX log printf instead */
    int dc_log_printf(char*, ...);
    #undef printf
    #define printf dc_log_printf
#else
    #ifdef XMALLOC_USER
        #include <stdlib.h>  /* we're using malloc / free direct here */
    #endif
    #ifndef STRING_USER
        #include <stdio.h>
    #endif

    /* enable way for customer to override test/bench printf */
    #ifdef XPRINTF
        #undef  printf
        #define printf XPRINTF
    #endif
#endif

#include <wolfssl/wolfcrypt/memory.h>
#include <wolfssl/wolfcrypt/wc_port.h>
#include <wolfssl/wolfcrypt/logging.h>
#include <wolfssl/wolfcrypt/types.h>
#include <wolfssl/wolfcrypt/asn.h>
#include <wolfssl/wolfcrypt/md2.h>
#include <wolfssl/wolfcrypt/md5.h>
#include <wolfssl/wolfcrypt/md4.h>
#include <wolfssl/wolfcrypt/sha.h>
#include <wolfssl/wolfcrypt/sha256.h>
#include <wolfssl/wolfcrypt/sha512.h>
#include <wolfssl/wolfcrypt/arc4.h>
#if defined(WC_NO_RNG)
    #include <wolfssl/wolfcrypt/integer.h>
#else
    #include <wolfssl/wolfcrypt/random.h>
#endif
#include <wolfssl/wolfcrypt/coding.h>
#include <wolfssl/wolfcrypt/signature.h>
#include <wolfssl/wolfcrypt/rsa.h>
#include <wolfssl/wolfcrypt/des3.h>
#include <wolfssl/wolfcrypt/aes.h>
#include <wolfssl/wolfcrypt/wc_encrypt.h>
#include <wolfssl/wolfcrypt/cmac.h>
#include <wolfssl/wolfcrypt/poly1305.h>
#include <wolfssl/wolfcrypt/camellia.h>
#include <wolfssl/wolfcrypt/hmac.h>
#include <wolfssl/wolfcrypt/dh.h>
#include <wolfssl/wolfcrypt/dsa.h>
#include <wolfssl/wolfcrypt/srp.h>
#include <wolfssl/wolfcrypt/idea.h>
#include <wolfssl/wolfcrypt/hc128.h>
#include <wolfssl/wolfcrypt/rabbit.h>
#include <wolfssl/wolfcrypt/chacha.h>
#include <wolfssl/wolfcrypt/chacha20_poly1305.h>
#include <wolfssl/wolfcrypt/pwdbased.h>
#include <wolfssl/wolfcrypt/ripemd.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#ifdef HAVE_ECC
    #include <wolfssl/wolfcrypt/ecc.h>
#endif
#ifdef HAVE_CURVE25519
    #include <wolfssl/wolfcrypt/curve25519.h>
#endif
#ifdef HAVE_ED25519
    #include <wolfssl/wolfcrypt/ed25519.h>
#endif
#ifdef HAVE_CURVE448
    #include <wolfssl/wolfcrypt/curve448.h>
#endif
#ifdef HAVE_ED448
    #include <wolfssl/wolfcrypt/ed448.h>
#endif
#if defined(HAVE_BLAKE2) || defined(HAVE_BLAKE2S)
    #include <wolfssl/wolfcrypt/blake2.h>
#endif
#ifdef WOLFSSL_SHA3
    #include <wolfssl/wolfcrypt/sha3.h>
#endif
#ifdef HAVE_LIBZ
    #include <wolfssl/wolfcrypt/compress.h>
#endif
#ifdef HAVE_PKCS7
    #include <wolfssl/wolfcrypt/pkcs7.h>
#endif
#ifdef HAVE_FIPS
    #include <wolfssl/wolfcrypt/fips_test.h>
#endif
#ifdef HAVE_SELFTEST
    #include <wolfssl/wolfcrypt/selftest.h>
#endif
#ifdef WOLFSSL_ASYNC_CRYPT
    #include <wolfssl/wolfcrypt/async.h>
#endif
#if defined(OPENSSL_EXTRA) || defined(DEBUG_WOLFSSL_VERBOSE)
    #include <wolfssl/wolfcrypt/logging.h>
#endif
#ifdef WOLFSSL_IMX6_CAAM_BLOB
    #include <wolfssl/wolfcrypt/port/caam/wolfcaam.h>
#endif
#ifdef WOLF_CRYPTO_CB
    #include <wolfssl/wolfcrypt/cryptocb.h>
    #ifdef HAVE_INTEL_QA_SYNC
        #include <wolfssl/wolfcrypt/port/intel/quickassist_sync.h>
    #endif
    #ifdef HAVE_CAVIUM_OCTEON_SYNC
        #include <wolfssl/wolfcrypt/port/cavium/cavium_octeon_sync.h>
    #endif
#endif

#ifdef _MSC_VER
    /* 4996 warning to use MS extensions e.g., strcpy_s instead of strncpy */
    #pragma warning(disable: 4996)
#endif

#ifdef OPENSSL_EXTRA
  #ifndef WOLFCRYPT_ONLY
    #include <wolfssl/openssl/evp.h>
  #endif
    #include <wolfssl/openssl/rand.h>
    #include <wolfssl/openssl/hmac.h>
    #include <wolfssl/openssl/aes.h>
    #include <wolfssl/openssl/des.h>
#endif

#if defined(NO_FILESYSTEM)
    #if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048) && \
        !defined(USE_CERT_BUFFERS_3072) && !defined(USE_CERT_BUFFERS_4096)
        #define USE_CERT_BUFFERS_2048
    #endif
    #if !defined(USE_CERT_BUFFERS_256)
        #define USE_CERT_BUFFERS_256
    #endif
#endif

#if defined(WOLFSSL_CERT_GEN) && (defined(HAVE_ECC384) || defined(HAVE_ALL_CURVES))
    #define ENABLE_ECC384_CERT_GEN_TEST
#endif

#include <wolfssl/certs_test.h>

#ifdef HAVE_NTRU
    #include "libntruencrypt/ntru_crypto.h"
#endif

#ifdef WOLFSSL_STATIC_MEMORY
    static WOLFSSL_HEAP_HINT* HEAP_HINT;
#else
    #define HEAP_HINT NULL
#endif /* WOLFSSL_STATIC_MEMORY */

/* these cases do not have intermediate hashing support */
#if (defined(WOLFSSL_AFALG_XILINX_SHA3) && !defined(WOLFSSL_AFALG_HASH_KEEP)) \
        && !defined(WOLFSSL_XILINX_CRYPT)
    #define NO_INTM_HASH_TEST
#endif

#if defined(WOLFSSL_CERT_GEN) && defined(WOLFSSL_MULTI_ATTRIB)
static void initDefaultName(void);
#endif

/* for async devices */
static int devId = INVALID_DEVID;

#ifdef HAVE_WNR
    const char* wnrConfigFile = "wnr-example.conf";
#endif

typedef struct testVector {
    const char*  input;
    const char*  output;
    size_t inLen;
    size_t outLen;
} testVector;

int  error_test(void);
int  base64_test(void);
int  base16_test(void);
int  asn_test(void);
int  md2_test(void);
int  md5_test(void);
int  md4_test(void);
int  sha_test(void);
int  sha224_test(void);
int  sha256_test(void);
int  sha512_test(void);
int  sha384_test(void);
int  sha3_test(void);
int  shake256_test(void);
int  hash_test(void);
int  hmac_md5_test(void);
int  hmac_sha_test(void);
int  hmac_sha224_test(void);
int  hmac_sha256_test(void);
int  hmac_sha384_test(void);
int  hmac_sha512_test(void);
int  hmac_sha3_test(void);
int  hkdf_test(void);
int  x963kdf_test(void);
int  arc4_test(void);
int  hc128_test(void);
int  rabbit_test(void);
int  chacha_test(void);
int  chacha20_poly1305_aead_test(void);
int  des_test(void);
int  des3_test(void);
int  aes_test(void);
int  aes192_test(void);
int  aes256_test(void);
int  aesofb_test(void);
int  cmac_test(void);
int  poly1305_test(void);
int  aesgcm_test(void);
int  aesgcm_default_test(void);
int  gmac_test(void);
int  aesccm_test(void);
int  aeskeywrap_test(void);
int  camellia_test(void);
int  rsa_no_pad_test(void);
int  rsa_test(void);
int  dh_test(void);
int  dsa_test(void);
int  srp_test(void);
#ifndef WC_NO_RNG
int  random_test(void);
#endif /* WC_NO_RNG */
int  pwdbased_test(void);
int  ripemd_test(void);
#if defined(OPENSSL_EXTRA) && !defined(WOLFCRYPT_ONLY)
int  openssl_test(void);   /* test mini api */

int  openssl_pkey_test(void);
int  openssl_pkey0_test(void);
int  openssl_pkey1_test(void);
int  openSSL_evpMD_test(void);
int  openssl_evpSig_test(void);
#endif

int pbkdf1_test(void);
int pkcs12_test(void);
int pbkdf2_test(void);
int scrypt_test(void);
#ifdef HAVE_ECC
    int  ecc_test(void);
    #ifdef HAVE_ECC_ENCRYPT
        int  ecc_encrypt_test(void);
    #endif
    #if defined(USE_CERT_BUFFERS_256) && !defined(WOLFSSL_ATECC508A) && \
        !defined(WOLFSSL_ATECC608A) && !defined(NO_ECC256)
        /* skip for ATECC508/608A, cannot import private key buffers */
        int ecc_test_buffers(void);
    #endif
#endif
#ifdef HAVE_CURVE25519
    int  curve25519_test(void);
#endif
#ifdef HAVE_ED25519
    int  ed25519_test(void);
#endif
#ifdef HAVE_CURVE448
    int  curve448_test(void);
#endif
#ifdef HAVE_ED448
    int  ed448_test(void);
#endif
#ifdef HAVE_BLAKE2
    int  blake2b_test(void);
#endif
#ifdef HAVE_BLAKE2S
    int  blake2s_test(void);
#endif
#ifdef HAVE_LIBZ
    int compress_test(void);
#endif
#ifdef HAVE_PKCS7
    #ifndef NO_PKCS7_ENCRYPTED_DATA
        int pkcs7encrypted_test(void);
    #endif
    #if defined(HAVE_LIBZ) && !defined(NO_PKCS7_COMPRESSED_DATA)
        int pkcs7compressed_test(void);
    #endif
    int pkcs7signed_test(void);
    int pkcs7enveloped_test(void);
    #if defined(HAVE_AESGCM) || defined(HAVE_AESCCM)
        int pkcs7authenveloped_test(void);
    #endif
    #ifndef NO_AES
        int pkcs7callback_test(byte* cert, word32 certSz, byte* key,
                word32 keySz);
    #endif
#endif
#if !defined(NO_ASN_TIME) && !defined(NO_RSA) && defined(WOLFSSL_TEST_CERT) && \
    !defined(NO_FILESYSTEM)
int cert_test(void);
#endif
#if defined(WOLFSSL_CERT_EXT) && defined(WOLFSSL_TEST_CERT) && \
   !defined(NO_FILESYSTEM)
int  certext_test(void);
#endif
#if defined(WOLFSSL_CERT_GEN_CACHE) && defined(WOLFSSL_TEST_CERT) && \
    defined(WOLFSSL_CERT_EXT) && defined(WOLFSSL_CERT_GEN)
int decodedCertCache_test(void);
#endif
#ifdef HAVE_IDEA
int idea_test(void);
#endif
int memory_test(void);
#ifdef HAVE_VALGRIND
int mp_test(void);
#endif
#if defined(WOLFSSL_PUBLIC_MP) && defined(WOLFSSL_KEY_GEN)
int prime_test(void);
#endif
#ifdef ASN_BER_TO_DER
int berder_test(void);
#endif
int logging_test(void);
int mutex_test(void);
#if defined(USE_WOLFSSL_MEMORY) && !defined(FREERTOS)
int memcb_test(void);
#endif
#ifdef WOLFSSL_IMX6_CAAM_BLOB
int blob_test(void);
#endif

#ifdef WOLF_CRYPTO_CB
int cryptocb_test(void);
#endif
#ifdef WOLFSSL_CERT_PIV
int certpiv_test(void);
#endif

/* General big buffer size for many tests. */
#define FOURK_BUF 4096


#define ERROR_OUT(err, eLabel) { ret = (err); goto eLabel; }

#ifdef HAVE_STACK_SIZE
static THREAD_RETURN err_sys(const char* msg, int es)
#else
static int err_sys(const char* msg, int es)
#endif
{
    printf("%s error = %d\n", msg, es);

    EXIT_TEST(-1);
}

#ifndef HAVE_STACK_SIZE
/* func_args from test.h, so don't have to pull in other stuff */
typedef struct func_args {
    int    argc;
    char** argv;
    int    return_code;
} func_args;
#endif /* !HAVE_STACK_SIZE */

#ifdef HAVE_FIPS

static void myFipsCb(int ok, int err, const char* hash)
{
    printf("in my Fips callback, ok = %d, err = %d\n", ok, err);
    printf("message = %s\n", wc_GetErrorString(err));
    printf("hash = %s\n", hash);

    if (err == IN_CORE_FIPS_E) {
        printf("In core integrity hash check failure, copy above hash\n");
        printf("into verifyCore[] in fips_test.c and rebuild\n");
    }
}

#endif /* HAVE_FIPS */

#ifdef WOLFSSL_STATIC_MEMORY
    #ifdef BENCH_EMBEDDED
        static byte gTestMemory[14000];
    #elif defined(WOLFSSL_CERT_EXT)
        static byte gTestMemory[140000];
    #elif defined(USE_FAST_MATH) && !defined(ALT_ECC_SIZE)
        static byte gTestMemory[160000];
    #else
        static byte gTestMemory[80000];
    #endif
#endif

#ifdef WOLFSSL_PB
int wolfssl_pb_print(const char* msg, ...)
{
    int ret;
    va_list args;
    char tmpBuf[80];

    va_start(args, msg);
    ret = vsprint(tmpBuf, msg, args);
    va_end(args);

    fnDumpStringToSystemLog(tmpBuf);

    return ret;
}
#endif /* WOLFSSL_PB */

/* optional macro to add sleep between tests */
#ifdef TEST_SLEEP
    #include <stdarg.h> /* for var args */
    static WC_INLINE void test_pass(const char* fmt, ...)
    {
        va_list args;
        va_start(args, fmt);
        printf(fmt, args);
        va_end(args);
        TEST_SLEEP();
    }
#else
    /* redirect to printf */
    #define test_pass printf
    /* stub the sleep macro */
    #define TEST_SLEEP()
#endif

#ifdef HAVE_STACK_SIZE
THREAD_RETURN WOLFSSL_THREAD wolfcrypt_test(void* args)
#else
int wolfcrypt_test(void* args)
#endif
{
    int ret;

    printf("------------------------------------------------------------------------------\n");
    printf(" wolfSSL version %s\n", LIBWOLFSSL_VERSION_STRING);
    printf("------------------------------------------------------------------------------\n");

    if (args)
        ((func_args*)args)->return_code = -1; /* error state */

#ifdef WOLFSSL_STATIC_MEMORY
    if (wc_LoadStaticMemory(&HEAP_HINT, gTestMemory, sizeof(gTestMemory),
                                                WOLFMEM_GENERAL, 1) != 0) {
        printf("unable to load static memory");
        return(EXIT_FAILURE);
    }
#endif

#if defined(DEBUG_WOLFSSL) && !defined(HAVE_VALGRIND)
    wolfSSL_Debugging_ON();
#endif

#if defined(OPENSSL_EXTRA) || defined(DEBUG_WOLFSSL_VERBOSE)
    wc_SetLoggingHeap(HEAP_HINT);
#endif

#ifdef HAVE_FIPS
    wolfCrypt_SetCb_fips(myFipsCb);
#endif

#if !defined(NO_BIG_INT)
    if (CheckCtcSettings() != 1) {
        printf("Sizeof mismatch (build) %x != (run) %x\n",
            CTC_SETTINGS, CheckRunTimeSettings());
        return err_sys("Build vs runtime math mismatch\n", -1000);
    }

#if defined(USE_FAST_MATH) && \
	(!defined(NO_RSA) || !defined(NO_DH) || defined(HAVE_ECC))
    if (CheckFastMathSettings() != 1)
        return err_sys("Build vs runtime fastmath FP_MAX_BITS mismatch\n",
                       -1001);
#endif /* USE_FAST_MATH */
#endif /* !NO_BIG_INT */

#if defined(WOLFSSL_CERT_GEN) && defined(WOLFSSL_MULTI_ATTRIB)
initDefaultName();
#endif

#ifdef WOLFSSL_ASYNC_CRYPT
    ret = wolfAsync_DevOpen(&devId);
    if (ret < 0) {
        printf("Async device open failed\nRunning without async\n");
    }
#else
    (void)devId;
#endif /* WOLFSSL_ASYNC_CRYPT */

#ifdef WOLF_CRYPTO_CB
#ifdef HAVE_INTEL_QA_SYNC
    devId = wc_CryptoCb_InitIntelQa();
    if (INVALID_DEVID == devId) {
        printf("Couldn't init the Intel QA\n");
    }
#endif
#ifdef HAVE_CAVIUM_OCTEON_SYNC
    devId = wc_CryptoCb_InitOcteon();
    if (INVALID_DEVID == devId) {
        printf("Couldn't init the Cavium Octeon\n");
    }
#endif
#endif

#ifdef HAVE_SELFTEST
    if ( (ret = wolfCrypt_SelfTest()) != 0)
        return err_sys("CAVP selftest failed!\n", ret);
    else
        test_pass("CAVP selftest passed!\n");
#endif

    if ( (ret = error_test()) != 0)
        return err_sys("error    test failed!\n", ret);
    else
        test_pass("error    test passed!\n");

    if ( (ret = memory_test()) != 0)
        return err_sys("MEMORY   test failed!\n", ret);
    else
        test_pass("MEMORY   test passed!\n");

#ifndef NO_CODING
    if ( (ret = base64_test()) != 0)
        return err_sys("base64   test failed!\n", ret);
    else
        test_pass("base64   test passed!\n");
#ifdef WOLFSSL_BASE16
    if ( (ret = base16_test()) != 0)
        return err_sys("base16   test failed!\n", ret);
    else
        test_pass("base16   test passed!\n");
#endif
#endif /* !NO_CODING */

#ifndef NO_ASN
    if ( (ret = asn_test()) != 0)
        return err_sys("asn      test failed!\n", ret);
    else
        test_pass("asn      test passed!\n");
#endif

#ifndef WC_NO_RNG
    if ( (ret = random_test()) != 0)
        return err_sys("RANDOM   test failed!\n", ret);
    else
        test_pass("RANDOM   test passed!\n");
#endif /* WC_NO_RNG */

#ifndef NO_MD5
    if ( (ret = md5_test()) != 0)
        return err_sys("MD5      test failed!\n", ret);
    else
        test_pass("MD5      test passed!\n");
#endif

#ifdef WOLFSSL_MD2
    if ( (ret = md2_test()) != 0)
        return err_sys("MD2      test failed!\n", ret);
    else
        test_pass("MD2      test passed!\n");
#endif

#ifndef NO_MD4
    if ( (ret = md4_test()) != 0)
        return err_sys("MD4      test failed!\n", ret);
    else
        test_pass("MD4      test passed!\n");
#endif

#ifndef NO_SHA
    if ( (ret = sha_test()) != 0)
        return err_sys("SHA      test failed!\n", ret);
    else
        test_pass("SHA      test passed!\n");
#endif

#ifdef WOLFSSL_SHA224
    if ( (ret = sha224_test()) != 0)
        return err_sys("SHA-224  test failed!\n", ret);
    else
        test_pass("SHA-224  test passed!\n");
#endif

#ifndef NO_SHA256
    if ( (ret = sha256_test()) != 0)
        return err_sys("SHA-256  test failed!\n", ret);
    else
        test_pass("SHA-256  test passed!\n");
#endif

#ifdef WOLFSSL_SHA384
    if ( (ret = sha384_test()) != 0)
        return err_sys("SHA-384  test failed!\n", ret);
    else
        test_pass("SHA-384  test passed!\n");
#endif

#ifdef WOLFSSL_SHA512
    if ( (ret = sha512_test()) != 0)
        return err_sys("SHA-512  test failed!\n", ret);
    else
        test_pass("SHA-512  test passed!\n");
#endif

#ifdef WOLFSSL_SHA3
    if ( (ret = sha3_test()) != 0)
        return err_sys("SHA-3    test failed!\n", ret);
    else
        test_pass("SHA-3    test passed!\n");
#endif

#ifdef WOLFSSL_SHAKE256
    if ( (ret = shake256_test()) != 0)
        return err_sys("SHAKE256 test failed!\n", ret);
    else
        test_pass("SHAKE256 test passed!\n");
#endif

    if ( (ret = hash_test()) != 0)
        return err_sys("Hash     test failed!\n", ret);
    else
        test_pass("Hash     test passed!\n");

#ifdef WOLFSSL_RIPEMD
    if ( (ret = ripemd_test()) != 0)
        return err_sys("RIPEMD   test failed!\n", ret);
    else
        test_pass("RIPEMD   test passed!\n");
#endif

#ifdef HAVE_BLAKE2
    if ( (ret = blake2b_test()) != 0)
        return err_sys("BLAKE2b  test failed!\n", ret);
    else
        test_pass("BLAKE2b  test passed!\n");
#endif
#ifdef HAVE_BLAKE2S
    if ( (ret = blake2s_test()) != 0)
        return err_sys("BLAKE2s  test failed!\n", ret);
    else
        test_pass("BLAKE2s  test passed!\n");
#endif

#ifndef NO_HMAC
    #ifndef NO_MD5
        if ( (ret = hmac_md5_test()) != 0)
            return err_sys("HMAC-MD5 test failed!\n", ret);
        else
            test_pass("HMAC-MD5 test passed!\n");
    #endif

    #ifndef NO_SHA
    if ( (ret = hmac_sha_test()) != 0)
        return err_sys("HMAC-SHA test failed!\n", ret);
    else
        test_pass("HMAC-SHA test passed!\n");
    #endif

    #ifdef WOLFSSL_SHA224
        if ( (ret = hmac_sha224_test()) != 0)
            return err_sys("HMAC-SHA224 test failed!\n", ret);
        else
            test_pass("HMAC-SHA224 test passed!\n");
    #endif

    #ifndef NO_SHA256
        if ( (ret = hmac_sha256_test()) != 0)
            return err_sys("HMAC-SHA256 test failed!\n", ret);
        else
            test_pass("HMAC-SHA256 test passed!\n");
    #endif

    #ifdef WOLFSSL_SHA384
        if ( (ret = hmac_sha384_test()) != 0)
            return err_sys("HMAC-SHA384 test failed!\n", ret);
        else
            test_pass("HMAC-SHA384 test passed!\n");
    #endif

    #ifdef WOLFSSL_SHA512
        if ( (ret = hmac_sha512_test()) != 0)
            return err_sys("HMAC-SHA512 test failed!\n", ret);
        else
            test_pass("HMAC-SHA512 test passed!\n");
    #endif

    #if !defined(NO_HMAC) && defined(WOLFSSL_SHA3) && \
      !defined(WOLFSSL_NOSHA3_224) && !defined(WOLFSSL_NOSHA3_256) && \
      !defined(WOLFSSL_NOSHA3_384) && !defined(WOLFSSL_NOSHA3_512)
        if ( (ret = hmac_sha3_test()) != 0)
            return err_sys("HMAC-SHA3   test failed!\n", ret);
        else
            test_pass("HMAC-SHA3   test passed!\n");
    #endif

    #ifdef HAVE_HKDF
        if ( (ret = hkdf_test()) != 0)
            return err_sys("HMAC-KDF    test failed!\n", ret);
        else
            test_pass("HMAC-KDF    test passed!\n");
    #endif
#endif /* !NO_HMAC */

#if defined(HAVE_X963_KDF) && defined(HAVE_ECC)
    if ( (ret = x963kdf_test()) != 0)
        return err_sys("X963-KDF    test failed!\n", ret);
    else
        test_pass("X963-KDF    test passed!\n");
#endif

#if defined(HAVE_AESGCM) && defined(WOLFSSL_AES_128) && \
   !defined(WOLFSSL_AFALG_XILINX_AES) && !defined(WOLFSSL_XILINX_CRYPT)
    if ( (ret = gmac_test()) != 0)
        return err_sys("GMAC     test failed!\n", ret);
    else
        test_pass("GMAC     test passed!\n");
#endif

#ifndef NO_RC4
    if ( (ret = arc4_test()) != 0)
        return err_sys("ARC4     test failed!\n", ret);
    else
        test_pass("ARC4     test passed!\n");
#endif

#ifndef NO_HC128
    if ( (ret = hc128_test()) != 0)
        return err_sys("HC-128   test failed!\n", ret);
    else
        test_pass("HC-128   test passed!\n");
#endif

#ifndef NO_RABBIT
    if ( (ret = rabbit_test()) != 0)
        return err_sys("Rabbit   test failed!\n", ret);
    else
        test_pass("Rabbit   test passed!\n");
#endif

#ifdef HAVE_CHACHA
    if ( (ret = chacha_test()) != 0)
        return err_sys("Chacha   test failed!\n", ret);
    else
        test_pass("Chacha   test passed!\n");
#endif

#ifdef HAVE_POLY1305
    if ( (ret = poly1305_test()) != 0)
        return err_sys("POLY1305 test failed!\n", ret);
    else
        test_pass("POLY1305 test passed!\n");
#endif

#if defined(HAVE_CHACHA) && defined(HAVE_POLY1305)
    if ( (ret = chacha20_poly1305_aead_test()) != 0)
        return err_sys("ChaCha20-Poly1305 AEAD test failed!\n", ret);
    else
        test_pass("ChaCha20-Poly1305 AEAD test passed!\n");
#endif

#ifndef NO_DES3
    if ( (ret = des_test()) != 0)
        return err_sys("DES      test failed!\n", ret);
    else
        test_pass("DES      test passed!\n");
#endif

#ifndef NO_DES3
    if ( (ret = des3_test()) != 0)
        return err_sys("DES3     test failed!\n", ret);
    else
        test_pass("DES3     test passed!\n");
#endif

#ifndef NO_AES
    if ( (ret = aes_test()) != 0)
        return err_sys("AES      test failed!\n", ret);
    else
        test_pass("AES      test passed!\n");

#ifdef WOLFSSL_AES_192
    if ( (ret = aes192_test()) != 0)
        return err_sys("AES192   test failed!\n", ret);
    else
        test_pass("AES192   test passed!\n");
#endif

#ifdef WOLFSSL_AES_256
    if ( (ret = aes256_test()) != 0)
        return err_sys("AES256   test failed!\n", ret);
    else
        test_pass("AES256   test passed!\n");
#endif

#ifdef WOLFSSL_AES_OFB
    if ( (ret = aesofb_test()) != 0)
        return err_sys("AES-OFB  test failed!\n", ret);
    else
        test_pass("AESOFB   test passed!\n");
#endif

#ifdef HAVE_AESGCM
    #if !defined(WOLFSSL_AFALG) && !defined(WOLFSSL_DEVCRYPTO)
    if ( (ret = aesgcm_test()) != 0)
        return err_sys("AES-GCM  test failed!\n", ret);
    #endif
    #if !defined(WOLFSSL_AFALG_XILINX_AES) && !defined(WOLFSSL_XILINX_CRYPT) && \
        !(defined(WOLF_CRYPTO_CB) && \
            (defined(HAVE_INTEL_QA_SYNC) || defined(HAVE_CAVIUM_OCTEON_SYNC)))
    if ((ret = aesgcm_default_test()) != 0) {
        return err_sys("AES-GCM  test failed!\n", ret);
    }
    #endif
    test_pass("AES-GCM  test passed!\n");
#endif

#if defined(HAVE_AESCCM) && defined(WOLFSSL_AES_128)
    if ( (ret = aesccm_test()) != 0)
        return err_sys("AES-CCM  test failed!\n", ret);
    else
        test_pass("AES-CCM  test passed!\n");
#endif
#ifdef HAVE_AES_KEYWRAP
    if ( (ret = aeskeywrap_test()) != 0)
        return err_sys("AES Key Wrap test failed!\n", ret);
    else
        test_pass("AES Key Wrap test passed!\n");
#endif
#endif

#ifdef HAVE_CAMELLIA
    if ( (ret = camellia_test()) != 0)
        return err_sys("CAMELLIA test failed!\n", ret);
    else
        test_pass("CAMELLIA test passed!\n");
#endif

#ifdef HAVE_IDEA
    if ( (ret = idea_test()) != 0)
        return err_sys("IDEA     test failed!\n", ret);
    else
        test_pass("IDEA     test passed!\n");
#endif

#ifndef NO_RSA
    #ifdef WC_RSA_NO_PADDING
    if ( (ret = rsa_no_pad_test()) != 0)
        return err_sys("RSA NOPAD test failed!\n", ret);
    else
        test_pass("RSA NOPAD test passed!\n");
    #endif
    if ( (ret = rsa_test()) != 0)
        return err_sys("RSA      test failed!\n", ret);
    else
        test_pass("RSA      test passed!\n");
#endif

#ifndef NO_DH
    if ( (ret = dh_test()) != 0)
        return err_sys("DH       test failed!\n", ret);
    else
        test_pass("DH       test passed!\n");
#endif

#ifndef NO_DSA
    if ( (ret = dsa_test()) != 0)
        return err_sys("DSA      test failed!\n", ret);
    else
        test_pass("DSA      test passed!\n");
#endif

#ifdef WOLFCRYPT_HAVE_SRP
    if ( (ret = srp_test()) != 0)
        return err_sys("SRP      test failed!\n", ret);
    else
        test_pass("SRP      test passed!\n");
#endif

#ifndef NO_PWDBASED
    if ( (ret = pwdbased_test()) != 0)
        return err_sys("PWDBASED test failed!\n", ret);
    else
        test_pass("PWDBASED test passed!\n");
#endif

#if defined(OPENSSL_EXTRA) && !defined(WOLFCRYPT_ONLY)
    if ( (ret = openssl_test()) != 0)
        return err_sys("OPENSSL  test failed!\n", ret);
    else
        test_pass("OPENSSL  test passed!\n");

    if ( (ret = openSSL_evpMD_test()) != 0)
        return err_sys("OPENSSL (EVP MD) test failed!\n", ret);
    else
        test_pass("OPENSSL (EVP MD) passed!\n");

    if ( (ret = openssl_pkey0_test()) != 0)
        return err_sys("OPENSSL (PKEY0) test failed!\n", ret);
    else
        test_pass("OPENSSL (PKEY0) passed!\n");

    if ( (ret = openssl_pkey1_test()) != 0)
        return err_sys("OPENSSL (PKEY1) test failed!\n", ret);
    else
        test_pass("OPENSSL (PKEY1) passed!\n");

    if ( (ret = openssl_evpSig_test()) != 0)
        return err_sys("OPENSSL (EVP Sign/Verify) test failed!\n", ret);
    else
        test_pass("OPENSSL (EVP Sign/Verify) passed!\n");

#endif

#ifdef HAVE_ECC
    if ( (ret = ecc_test()) != 0)
        return err_sys("ECC      test failed!\n", ret);
    else
        test_pass("ECC      test passed!\n");
    #if defined(HAVE_ECC_ENCRYPT) && defined(WOLFSSL_AES_128)
        if ( (ret = ecc_encrypt_test()) != 0)
            return err_sys("ECC Enc  test failed!\n", ret);
        else
            test_pass("ECC Enc  test passed!\n");
    #endif
    #if defined(USE_CERT_BUFFERS_256) && !defined(WOLFSSL_ATECC508A) && \
        !defined(WOLFSSL_ATECC608A) && !defined(NO_ECC256)
        /* skip for ATECC508/608A, cannot import private key buffers */
        if ( (ret = ecc_test_buffers()) != 0)
            return err_sys("ECC buffer test failed!\n", ret);
        else
            test_pass("ECC buffer test passed!\n");
    #endif
#endif

#if !defined(NO_ASN_TIME) && !defined(NO_RSA) && defined(WOLFSSL_TEST_CERT) && \
    !defined(NO_FILESYSTEM)
    if ( (ret = cert_test()) != 0)
        return err_sys("CERT     test failed!\n", ret);
    else
        test_pass("CERT     test passed!\n");
#endif

#if defined(WOLFSSL_CERT_EXT) && defined(WOLFSSL_TEST_CERT) && \
   !defined(NO_FILESYSTEM)
    if ( (ret = certext_test()) != 0)
        return err_sys("CERT EXT test failed!\n", ret);
    else
        test_pass("CERT EXT test passed!\n");
#endif

#if defined(WOLFSSL_CERT_GEN_CACHE) && defined(WOLFSSL_TEST_CERT) && \
    defined(WOLFSSL_CERT_EXT) && defined(WOLFSSL_CERT_GEN)
    if ( (ret = decodedCertCache_test()) != 0)
        return err_sys("DECODED CERT CACHE test failed!\n", ret);
    else
        test_pass("DECODED CERT CACHE test passed!\n");
#endif

#ifdef HAVE_CURVE25519
    if ( (ret = curve25519_test()) != 0)
        return err_sys("CURVE25519 test failed!\n", ret);
    else
        test_pass("CURVE25519 test passed!\n");
#endif

#ifdef HAVE_ED25519
    if ( (ret = ed25519_test()) != 0)
        return err_sys("ED25519  test failed!\n", ret);
    else
        test_pass("ED25519  test passed!\n");
#endif

#ifdef HAVE_CURVE448
    if ( (ret = curve448_test()) != 0)
        return err_sys("CURVE448 test failed!\n", ret);
    else
        test_pass("CURVE448 test passed!\n");
#endif

#ifdef HAVE_ED448
    if ( (ret = ed448_test()) != 0)
        return err_sys("ED448  test failed!\n", ret);
    else
        test_pass("ED448  test passed!\n");
#endif

#if defined(WOLFSSL_CMAC) && !defined(NO_AES)
    if ( (ret = cmac_test()) != 0)
        return err_sys("CMAC     test failed!\n", ret);
    else
        test_pass("CMAC     test passed!\n");
#endif

#ifdef HAVE_LIBZ
    if ( (ret = compress_test()) != 0)
        return err_sys("COMPRESS test failed!\n", ret);
    else
        test_pass("COMPRESS test passed!\n");
#endif

#ifdef HAVE_PKCS7
    #ifndef NO_PKCS7_ENCRYPTED_DATA
        if ( (ret = pkcs7encrypted_test()) != 0)
            return err_sys("PKCS7encrypted  test failed!\n", ret);
        else
            test_pass("PKCS7encrypted  test passed!\n");
    #endif
    #if defined(HAVE_LIBZ) && !defined(NO_PKCS7_COMPRESSED_DATA)
        if ( (ret = pkcs7compressed_test()) != 0)
            return err_sys("PKCS7compressed test failed!\n", ret);
        else
            test_pass("PKCS7compressed test passed!\n");
    #endif
    if ( (ret = pkcs7signed_test()) != 0)
        return err_sys("PKCS7signed     test failed!\n", ret);
    else
        test_pass("PKCS7signed     test passed!\n");

    if ( (ret = pkcs7enveloped_test()) != 0)
        return err_sys("PKCS7enveloped  test failed!\n", ret);
    else
        test_pass("PKCS7enveloped  test passed!\n");

    #if defined(HAVE_AESGCM) || defined(HAVE_AESCCM)
        if ( (ret = pkcs7authenveloped_test()) != 0)
            return err_sys("PKCS7authenveloped  test failed!\n", ret);
        else
            test_pass("PKCS7authenveloped  test passed!\n");
    #endif
#endif

#ifdef HAVE_VALGRIND
    if ( (ret = mp_test()) != 0)
        return err_sys("mp       test failed!\n", ret);
    else
        test_pass("mp       test passed!\n");
#endif

#if defined(WOLFSSL_PUBLIC_MP) && defined(WOLFSSL_KEY_GEN)
    if ( (ret = prime_test()) != 0)
        return err_sys("prime    test failed!\n", ret);
    else
        test_pass("prime    test passed!\n");
#endif

#if defined(ASN_BER_TO_DER) && \
    (defined(WOLFSSL_TEST_CERT) || defined(OPENSSL_EXTRA) || \
     defined(OPENSSL_EXTRA_X509_SMALL))
    if ( (ret = berder_test()) != 0)
        return err_sys("ber-der  test failed!\n", ret);
    else
        test_pass("ber-der  test passed!\n");
#endif

    if ( (ret = logging_test()) != 0)
        return err_sys("logging  test failed!\n", ret);
    else
        test_pass("logging  test passed!\n");

    if ( (ret = mutex_test()) != 0)
        return err_sys("mutex    test failed!\n", ret);
    else
        test_pass("mutex    test passed!\n");

#if defined(USE_WOLFSSL_MEMORY) && !defined(FREERTOS)
    if ( (ret = memcb_test()) != 0)
        return err_sys("memcb    test failed!\n", ret);
    else
        test_pass("memcb    test passed!\n");
#endif

#ifdef WOLFSSL_IMX6_CAAM_BLOB
    if ( (ret = blob_test()) != 0)
        return err_sys("blob     test failed!\n", ret);
    else
        test_pass("blob     test passed!\n");
#endif

#if defined(WOLF_CRYPTO_CB) && \
    !(defined(HAVE_INTEL_QAT_SYNC) || defined(HAVE_CAVIUM_OCTEON_SYNC))
    if ( (ret = cryptocb_test()) != 0)
        return err_sys("crypto callback test failed!\n", ret);
    else
        test_pass("crypto callback test passed!\n");
#endif

#ifdef WOLFSSL_CERT_PIV
    if ( (ret = certpiv_test()) != 0)
        return err_sys("cert piv test failed!\n", ret);
    else
        test_pass("cert piv test passed!\n");
#endif

#ifdef WOLF_CRYPTO_CB
#ifdef HAVE_INTEL_QA_SYNC
    wc_CryptoCb_CleanupIntelQa(&devId);
#endif
#ifdef HAVE_CAVIUM_OCTEON_SYNC
    wc_CryptoCb_CleanupOcteon(&devId);
#endif
#endif

#ifdef WOLFSSL_ASYNC_CRYPT
    wolfAsync_DevClose(&devId);
#endif

    /* cleanup the thread if fixed point cache is enabled and have thread local */
#if defined(HAVE_THREAD_LS) && defined(HAVE_ECC) && defined(FP_ECC)
    wc_ecc_fp_free();
#endif

    if (args)
        ((func_args*)args)->return_code = ret;

    test_pass("Test complete\n");

    EXIT_TEST(ret);
}


#ifndef NO_MAIN_DRIVER

    /* so overall tests can pull in test function */
#ifdef WOLFSSL_ESPIDF
    void app_main( )
#else
    int main(int argc, char** argv)
#endif
    {
        int ret;
        func_args args;
#ifdef WOLFSSL_ESPIDF
        /* set dummy wallclock time. */
        struct timeval utctime;
        struct timezone tz;
        utctime.tv_sec = 1521725159; /* dummy time: 2018-03-22T13:25:59+00:00 */
        utctime.tv_usec = 0;
        tz.tz_minuteswest = 0;
        tz.tz_dsttime = 0;
        settimeofday(&utctime, &tz);
#endif
#ifdef WOLFSSL_APACHE_MYNEWT
        #ifdef ARCH_sim
        mcu_sim_parse_args(argc, argv);
        #endif
        sysinit();

        /* set dummy wallclock time. */
        struct os_timeval utctime;
        struct os_timezone tz;
        utctime.tv_sec = 1521725159; /* dummy time: 2018-03-22T13:25:59+00:00 */
        utctime.tv_usec = 0;
        tz.tz_minuteswest = 0;
        tz.tz_dsttime = 0;
        os_settimeofday(&utctime, &tz);
#endif

#ifdef HAVE_WNR
        if (wc_InitNetRandom(wnrConfigFile, NULL, 5000) != 0) {
            err_sys("Whitewood netRandom global config failed", -1001);
            return -1002;
        }
#endif
#ifndef WOLFSSL_ESPIDF
        args.argc = argc;
        args.argv = argv;
#endif
        if ((ret = wolfCrypt_Init()) != 0) {
            printf("wolfCrypt_Init failed %d\n", ret);
            err_sys("Error with wolfCrypt_Init!\n", -1003);
        }

    #ifdef HAVE_STACK_SIZE
        StackSizeCheck(&args, wolfcrypt_test);
    #else
        wolfcrypt_test(&args);
    #endif

        if ((ret = wolfCrypt_Cleanup()) != 0) {
            printf("wolfCrypt_Cleanup failed %d\n", ret);
            err_sys("Error with wolfCrypt_Cleanup!\n", -1004);
        }

#ifdef HAVE_WNR
        if (wc_FreeNetRandom() < 0)
            err_sys("Failed to free netRandom context", -1005);
#endif /* HAVE_WNR */
#ifndef WOLFSSL_ESPIDF
        return args.return_code;
#endif
    }

#endif /* NO_MAIN_DRIVER */

/* helper to save DER, convert to PEM and save PEM */
#if !defined(NO_ASN) && (defined(HAVE_ECC) || \
    (!defined(NO_RSA) && (defined(WOLFSSL_KEY_GEN) || defined(WOLFSSL_CERT_GEN))))

#if !defined(NO_FILESYSTEM) && !defined(NO_WRITE_TEMP_FILES)
#define SaveDerAndPem(d, dSz, fD, fP, pT, eB) _SaveDerAndPem(d, dSz, fD, fP, pT, eB)
#else
#define SaveDerAndPem(d, dSz, fD, fP, pT, eB) _SaveDerAndPem(d, dSz, NULL, NULL, pT, eB)
#endif

static int _SaveDerAndPem(const byte* der, int derSz,
    const char* fileDer, const char* filePem, int pemType, int errBase)
{
#if !defined(NO_FILESYSTEM) && !defined(NO_WRITE_TEMP_FILES)
    int ret;
    XFILE derFile;

    derFile = XFOPEN(fileDer, "wb");
    if (!derFile) {
        return errBase + 0;
    }
    ret = (int)XFWRITE(der, 1, derSz, derFile);
    XFCLOSE(derFile);
    if (ret != derSz) {
        return errBase + 1;
    }
#endif

#ifdef WOLFSSL_DER_TO_PEM
    if (filePem) {
    #if !defined(NO_FILESYSTEM) && !defined(NO_WRITE_TEMP_FILES)
        XFILE pemFile;
    #endif
        byte* pem;
        int pemSz;

        /* calculate PEM size */
        pemSz = wc_DerToPem(der, derSz, NULL, 0, pemType);
        if (pemSz < 0) {
            return pemSz;
        }
        pem = (byte*)XMALLOC(pemSz, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        if (pem == NULL) {
            return MEMORY_E;
        }
        /* Convert to PEM */
        pemSz = wc_DerToPem(der, derSz, pem, pemSz, pemType);
        if (pemSz < 0) {
            XFREE(pem, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
            return errBase + 2;
        }
    #if !defined(NO_FILESYSTEM) && !defined(NO_WRITE_TEMP_FILES)
        pemFile = XFOPEN(filePem, "wb");
        if (!pemFile) {
            XFREE(pem, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
            return errBase + 3;
        }
        ret = (int)XFWRITE(pem, 1, pemSz, pemFile);
        XFCLOSE(pemFile);
        if (ret != pemSz) {
            XFREE(pem, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
            return errBase + 4;
        }
    #endif
        XFREE(pem, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif /* WOLFSSL_DER_TO_PEM */

    /* suppress unused variable warnings */
    (void)der;
    (void)derSz;
    (void)filePem;
    (void)fileDer;
    (void)pemType;
    (void)errBase;

    return 0;
}
#endif /* WOLFSSL_KEY_GEN || WOLFSSL_CERT_GEN */

int error_test(void)
{
    const char* errStr;
    char        out[WOLFSSL_MAX_ERROR_SZ];
    const char* unknownStr = wc_GetErrorString(0);

#ifdef NO_ERROR_STRINGS
    /* Ensure a valid error code's string matches an invalid code's.
     * The string is that error strings are not available.
     */
    errStr = wc_GetErrorString(OPEN_RAN_E);
    wc_ErrorString(OPEN_RAN_E, out);
    if (XSTRNCMP(errStr, unknownStr, XSTRLEN(unknownStr)) != 0)
        return -1100;
    if (XSTRNCMP(out, unknownStr, XSTRLEN(unknownStr)) != 0)
        return -1101;
#else
    int i;
    int j = 0;
    /* Values that are not or no longer error codes. */
    int missing[] = { -122, -123, -124,       -127, -128, -129,
                      -163, -164, -165, -166, -167, -168, -169,
                      -179,       -233,
                      0 };

    /* Check that all errors have a string and it's the same through the two
     * APIs. Check that the values that are not errors map to the unknown
     * string.
     */
    for (i = MAX_CODE_E-1; i >= WC_LAST_E; i--) {
        errStr = wc_GetErrorString(i);
        wc_ErrorString(i, out);

        if (i != missing[j]) {
            if (XSTRNCMP(errStr, unknownStr, XSTRLEN(unknownStr)) == 0)
                return -1102;
            if (XSTRNCMP(out, unknownStr, XSTRLEN(unknownStr)) == 0)
                return -1103;
            if (XSTRNCMP(errStr, out, XSTRLEN(errStr)) != 0)
                return -1104;
            if (XSTRLEN(errStr) >= WOLFSSL_MAX_ERROR_SZ)
                return -1105;
        }
        else {
            j++;
            if (XSTRNCMP(errStr, unknownStr, XSTRLEN(unknownStr)) != 0)
                return -1106;
            if (XSTRNCMP(out, unknownStr, XSTRLEN(unknownStr)) != 0)
                return -1107;
        }
    }

    /* Check if the next possible value has been given a string. */
    errStr = wc_GetErrorString(i);
    wc_ErrorString(i, out);
    if (XSTRNCMP(errStr, unknownStr, XSTRLEN(unknownStr)) != 0)
        return -1108;
    if (XSTRNCMP(out, unknownStr, XSTRLEN(unknownStr)) != 0)
        return -1109;
#endif

    return 0;
}

#ifndef NO_CODING

int base64_test(void)
{
    int        ret;
    const byte good[] = "A+Gd\0\0\0";
    const byte goodEnd[] = "A+Gd \r\n";
    byte       out[128];
    word32     outLen;
#ifdef WOLFSSL_BASE64_ENCODE
    byte       data[3];
    word32     dataLen;
    byte       longData[79] = { 0 };
    const byte symbols[] = "+/A=";
#endif
    const byte badSmall[] = "AAA Gdj=";
    const byte badLarge[] = "AAA~Gdj=";
    const byte badEOL[] = "A+Gd AA";
    int        i;

    /* Good Base64 encodings. */
    outLen = sizeof(out);
    ret = Base64_Decode(good, sizeof(good), out, &outLen);
    if (ret != 0)
        return -1200;
    outLen = sizeof(out);
    ret = Base64_Decode(goodEnd, sizeof(goodEnd), out, &outLen);
    if (ret != 0)
        return -1201;

    /* Bad parameters. */
    outLen = 1;
    ret = Base64_Decode(good, sizeof(good), out, &outLen);
    if (ret != BAD_FUNC_ARG)
        return -1202;

    outLen = sizeof(out);
    ret = Base64_Decode(badEOL, sizeof(badEOL), out, &outLen);
    if (ret != ASN_INPUT_E)
        return -1203;
    /* Bad character at each offset 0-3. */
    for (i = 0; i < 4; i++) {
        outLen = sizeof(out);
        ret = Base64_Decode(badSmall + i, 4, out, &outLen);
        if (ret != ASN_INPUT_E)
            return -1204 - i;
        ret = Base64_Decode(badLarge + i, 4, out, &outLen);
        if (ret != ASN_INPUT_E)
            return -1214 - i;
    }

#ifdef WOLFSSL_BASE64_ENCODE
    /* Decode and encode all symbols - non-alphanumeric. */
    dataLen = sizeof(data);
    ret = Base64_Decode(symbols, sizeof(symbols), data, &dataLen);
    if (ret != 0)
        return -1224;
    outLen = sizeof(out);
    ret = Base64_Encode(data, dataLen, NULL, &outLen);
    if (ret != LENGTH_ONLY_E)
        return -1225;
    outLen = sizeof(out);
    ret = Base64_Encode(data, dataLen, out, &outLen);
    if (ret != 0)
        return -1226;
    outLen = 7;
    ret = Base64_EncodeEsc(data, dataLen, out, &outLen);
    if (ret != BUFFER_E)
        return -1227;
    outLen = sizeof(out);
    ret = Base64_EncodeEsc(data, dataLen, NULL, &outLen);
    if (ret != LENGTH_ONLY_E)
        return -1228;
    outLen = sizeof(out);
    ret = Base64_EncodeEsc(data, dataLen, out, &outLen);
    if (ret != 0)
        return -1229;
    outLen = sizeof(out);
    ret = Base64_Encode_NoNl(data, dataLen, out, &outLen);
    if (ret != 0)
        return -1230;

    /* Data that results in an encoding longer than one line. */
    outLen = sizeof(out);
    dataLen = sizeof(longData);
    ret = Base64_Encode(longData, dataLen, out, &outLen);
    if (ret != 0)
        return -1231;
    outLen = sizeof(out);
    ret = Base64_EncodeEsc(longData, dataLen, out, &outLen);
    if (ret != 0)
        return -1232;
    outLen = sizeof(out);
    ret = Base64_Encode_NoNl(longData, dataLen, out, &outLen);
    if (ret != 0)
        return -1233;
#endif

    return 0;
}

#ifdef WOLFSSL_BASE16
int base16_test(void)
{
    int ret;
    const byte testData[] = "SomeDataToEncode\n";
    const byte encodedTestData[] = "536F6D6544617461546F456E636F64650A00";
    byte   encoded[40];
    word32 encodedLen;
    byte   plain[40];
    word32 len;

    /* length returned includes null termination */
    encodedLen = sizeof(encoded);
    ret = Base16_Encode(testData, sizeof(testData), encoded, &encodedLen);
    if (ret != 0)
        return -1300;

    len = (word32)XSTRLEN((char*)encoded);
    if (len != encodedLen - 1)
        return -1301;

    len = sizeof(plain);
    ret = Base16_Decode(encoded, encodedLen - 1, plain, &len);
    if (ret != 0)
        return -1302;

    if (len != sizeof(testData) || XMEMCMP(testData, plain, len) != 0)
        return -1303;

    if (encodedLen != sizeof(encodedTestData) ||
        XMEMCMP(encoded, encodedTestData, encodedLen) != 0) {
        return -1304;
    }

    return 0;
}
#endif /* WOLFSSL_BASE16 */
#endif /* !NO_CODING */

#ifndef NO_ASN
int asn_test(void)
{
    int ret;
    /* ASN1 encoded date buffer */
    const byte dateBuf[] = {0x17, 0x0d, 0x31, 0x36, 0x30, 0x38, 0x31, 0x31,
                            0x32, 0x30, 0x30, 0x37, 0x33, 0x37, 0x5a};
    byte format;
    int length;
    const byte* datePart;
#ifndef NO_ASN_TIME
    struct tm timearg;
    time_t now;
#endif

    ret = wc_GetDateInfo(dateBuf, (int)sizeof(dateBuf), &datePart, &format,
                         &length);
    if (ret != 0)
        return -1400;

#ifndef NO_ASN_TIME
    /* Parameter Validation tests. */
    if (wc_GetTime(NULL, sizeof(now)) != BAD_FUNC_ARG)
        return -1401;
    if (wc_GetTime(&now, 0) != BUFFER_E)
        return -1402;

    now = 0;
    if (wc_GetTime(&now, sizeof(now)) != 0) {
        return -1403;
    }
    if (now == 0) {
        printf("RTC/Time not set!\n");
        return -1404;
    }

    ret = wc_GetDateAsCalendarTime(datePart, length, format, &timearg);
    if (ret != 0)
        return -1405;
#endif /* !NO_ASN_TIME */

    return 0;
}
#endif /* !NO_ASN */

#ifdef WOLFSSL_MD2
int md2_test(void)
{
    Md2  md2;
    byte hash[MD2_DIGEST_SIZE];

    testVector a, b, c, d, e, f, g;
    testVector test_md2[7];
    int times = sizeof(test_md2) / sizeof(testVector), i;

    a.input  = "";
    a.output = "\x83\x50\xe5\xa3\xe2\x4c\x15\x3d\xf2\x27\x5c\x9f\x80\x69"
               "\x27\x73";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = MD2_DIGEST_SIZE;

    b.input  = "a";
    b.output = "\x32\xec\x01\xec\x4a\x6d\xac\x72\xc0\xab\x96\xfb\x34\xc0"
               "\xb5\xd1";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = MD2_DIGEST_SIZE;

    c.input  = "abc";
    c.output = "\xda\x85\x3b\x0d\x3f\x88\xd9\x9b\x30\x28\x3a\x69\xe6\xde"
               "\xd6\xbb";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = MD2_DIGEST_SIZE;

    d.input  = "message digest";
    d.output = "\xab\x4f\x49\x6b\xfb\x2a\x53\x0b\x21\x9f\xf3\x30\x31\xfe"
               "\x06\xb0";
    d.inLen  = XSTRLEN(d.input);
    d.outLen = MD2_DIGEST_SIZE;

    e.input  = "abcdefghijklmnopqrstuvwxyz";
    e.output = "\x4e\x8d\xdf\xf3\x65\x02\x92\xab\x5a\x41\x08\xc3\xaa\x47"
               "\x94\x0b";
    e.inLen  = XSTRLEN(e.input);
    e.outLen = MD2_DIGEST_SIZE;

    f.input  = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz012345"
               "6789";
    f.output = "\xda\x33\xde\xf2\xa4\x2d\xf1\x39\x75\x35\x28\x46\xc3\x03"
               "\x38\xcd";
    f.inLen  = XSTRLEN(f.input);
    f.outLen = MD2_DIGEST_SIZE;

    g.input  = "1234567890123456789012345678901234567890123456789012345678"
               "9012345678901234567890";
    g.output = "\xd5\x97\x6f\x79\xd8\x3d\x3a\x0d\xc9\x80\x6c\x3c\x66\xf3"
               "\xef\xd8";
    g.inLen  = XSTRLEN(g.input);
    g.outLen = MD2_DIGEST_SIZE;

    test_md2[0] = a;
    test_md2[1] = b;
    test_md2[2] = c;
    test_md2[3] = d;
    test_md2[4] = e;
    test_md2[5] = f;
    test_md2[6] = g;

    wc_InitMd2(&md2);

    for (i = 0; i < times; ++i) {
        wc_Md2Update(&md2, (byte*)test_md2[i].input, (word32)test_md2[i].inLen);
        wc_Md2Final(&md2, hash);

        if (XMEMCMP(hash, test_md2[i].output, MD2_DIGEST_SIZE) != 0)
            return -1500 - i;
    }

    return 0;
}
#endif

#ifndef NO_MD5
int md5_test(void)
{
    int ret = 0;
    wc_Md5 md5, md5Copy;
    byte hash[WC_MD5_DIGEST_SIZE];
    byte hashcopy[WC_MD5_DIGEST_SIZE];
    testVector a, b, c, d, e, f;
    testVector test_md5[6];
    int times = sizeof(test_md5) / sizeof(testVector), i;

    a.input  = "";
    a.output = "\xd4\x1d\x8c\xd9\x8f\x00\xb2\x04\xe9\x80\x09\x98\xec\xf8\x42"
               "\x7e";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = WC_MD5_DIGEST_SIZE;

    b.input  = "abc";
    b.output = "\x90\x01\x50\x98\x3c\xd2\x4f\xb0\xd6\x96\x3f\x7d\x28\xe1\x7f"
               "\x72";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_MD5_DIGEST_SIZE;

    c.input  = "message digest";
    c.output = "\xf9\x6b\x69\x7d\x7c\xb7\x93\x8d\x52\x5a\x2f\x31\xaa\xf1\x61"
               "\xd0";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = WC_MD5_DIGEST_SIZE;

    d.input  = "abcdefghijklmnopqrstuvwxyz";
    d.output = "\xc3\xfc\xd3\xd7\x61\x92\xe4\x00\x7d\xfb\x49\x6c\xca\x67\xe1"
               "\x3b";
    d.inLen  = XSTRLEN(d.input);
    d.outLen = WC_MD5_DIGEST_SIZE;

    e.input  = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz012345"
               "6789";
    e.output = "\xd1\x74\xab\x98\xd2\x77\xd9\xf5\xa5\x61\x1c\x2c\x9f\x41\x9d"
               "\x9f";
    e.inLen  = XSTRLEN(e.input);
    e.outLen = WC_MD5_DIGEST_SIZE;

    f.input  = "1234567890123456789012345678901234567890123456789012345678"
               "9012345678901234567890";
    f.output = "\x57\xed\xf4\xa2\x2b\xe3\xc9\x55\xac\x49\xda\x2e\x21\x07\xb6"
               "\x7a";
    f.inLen  = XSTRLEN(f.input);
    f.outLen = WC_MD5_DIGEST_SIZE;

    test_md5[0] = a;
    test_md5[1] = b;
    test_md5[2] = c;
    test_md5[3] = d;
    test_md5[4] = e;
    test_md5[5] = f;

    ret = wc_InitMd5_ex(&md5, HEAP_HINT, devId);
    if (ret != 0)
        return -1600;
    ret = wc_InitMd5_ex(&md5Copy, HEAP_HINT, devId);
    if (ret != 0) {
        wc_Md5Free(&md5);
        return -1601;
    }

    for (i = 0; i < times; ++i) {
        ret = wc_Md5Update(&md5, (byte*)test_md5[i].input,
            (word32)test_md5[i].inLen);
        if (ret != 0)
            ERROR_OUT(-1602 - i, exit);

        ret = wc_Md5GetHash(&md5, hashcopy);
        if (ret != 0)
            ERROR_OUT(-1603 - i, exit);

        ret = wc_Md5Copy(&md5, &md5Copy);
        if (ret != 0)
            ERROR_OUT(-1604 - i, exit);

        ret = wc_Md5Final(&md5, hash);
        if (ret != 0)
            ERROR_OUT(-1605 - i, exit);

        wc_Md5Free(&md5Copy);

        if (XMEMCMP(hash, test_md5[i].output, WC_MD5_DIGEST_SIZE) != 0)
            ERROR_OUT(-1606 - i, exit);

        if (XMEMCMP(hash, hashcopy, WC_MD5_DIGEST_SIZE) != 0)
            ERROR_OUT(-1607 - i, exit);
    }

    /* BEGIN LARGE HASH TEST */ {
    byte large_input[1024];
    const char* large_digest =
        "\x44\xd0\x88\xce\xf1\x36\xd1\x78\xe9\xc8\xba\x84\xc3\xfd\xf6\xca";

    for (i = 0; i < (int)sizeof(large_input); i++) {
        large_input[i] = (byte)(i & 0xFF);
    }
    times = 100;
#ifdef WOLFSSL_PIC32MZ_HASH
    wc_Md5SizeSet(&md5, times * sizeof(large_input));
#endif
    for (i = 0; i < times; ++i) {
        ret = wc_Md5Update(&md5, (byte*)large_input,
            (word32)sizeof(large_input));
        if (ret != 0)
            ERROR_OUT(-1608, exit);
    }
    ret = wc_Md5Final(&md5, hash);
    if (ret != 0)
        ERROR_OUT(-1609, exit);
    if (XMEMCMP(hash, large_digest, WC_MD5_DIGEST_SIZE) != 0)
        ERROR_OUT(-1610, exit);
    } /* END LARGE HASH TEST */

exit:

    wc_Md5Free(&md5);
    wc_Md5Free(&md5Copy);

    return ret;
}
#endif /* NO_MD5 */


#ifndef NO_MD4

int md4_test(void)
{
    Md4  md4;
    byte hash[MD4_DIGEST_SIZE];

    testVector a, b, c, d, e, f, g;
    testVector test_md4[7];
    int times = sizeof(test_md4) / sizeof(testVector), i;

    a.input  = "";
    a.output = "\x31\xd6\xcf\xe0\xd1\x6a\xe9\x31\xb7\x3c\x59\xd7\xe0\xc0\x89"
               "\xc0";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = MD4_DIGEST_SIZE;

    b.input  = "a";
    b.output = "\xbd\xe5\x2c\xb3\x1d\xe3\x3e\x46\x24\x5e\x05\xfb\xdb\xd6\xfb"
               "\x24";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = MD4_DIGEST_SIZE;

    c.input  = "abc";
    c.output = "\xa4\x48\x01\x7a\xaf\x21\xd8\x52\x5f\xc1\x0a\xe8\x7a\xa6\x72"
               "\x9d";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = MD4_DIGEST_SIZE;

    d.input  = "message digest";
    d.output = "\xd9\x13\x0a\x81\x64\x54\x9f\xe8\x18\x87\x48\x06\xe1\xc7\x01"
               "\x4b";
    d.inLen  = XSTRLEN(d.input);
    d.outLen = MD4_DIGEST_SIZE;

    e.input  = "abcdefghijklmnopqrstuvwxyz";
    e.output = "\xd7\x9e\x1c\x30\x8a\xa5\xbb\xcd\xee\xa8\xed\x63\xdf\x41\x2d"
               "\xa9";
    e.inLen  = XSTRLEN(e.input);
    e.outLen = MD4_DIGEST_SIZE;

    f.input  = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz012345"
               "6789";
    f.output = "\x04\x3f\x85\x82\xf2\x41\xdb\x35\x1c\xe6\x27\xe1\x53\xe7\xf0"
               "\xe4";
    f.inLen  = XSTRLEN(f.input);
    f.outLen = MD4_DIGEST_SIZE;

    g.input  = "1234567890123456789012345678901234567890123456789012345678"
               "9012345678901234567890";
    g.output = "\xe3\x3b\x4d\xdc\x9c\x38\xf2\x19\x9c\x3e\x7b\x16\x4f\xcc\x05"
               "\x36";
    g.inLen  = XSTRLEN(g.input);
    g.outLen = MD4_DIGEST_SIZE;

    test_md4[0] = a;
    test_md4[1] = b;
    test_md4[2] = c;
    test_md4[3] = d;
    test_md4[4] = e;
    test_md4[5] = f;
    test_md4[6] = g;

    wc_InitMd4(&md4);

    for (i = 0; i < times; ++i) {
        wc_Md4Update(&md4, (byte*)test_md4[i].input, (word32)test_md4[i].inLen);
        wc_Md4Final(&md4, hash);

        if (XMEMCMP(hash, test_md4[i].output, MD4_DIGEST_SIZE) != 0)
            return -1700 - i;
    }

    return 0;
}

#endif /* NO_MD4 */

#ifndef NO_SHA

int sha_test(void)
{
    int ret = 0;
    wc_Sha sha, shaCopy;
    byte hash[WC_SHA_DIGEST_SIZE];
    byte hashcopy[WC_SHA_DIGEST_SIZE];
    testVector a, b, c, d, e;
    testVector test_sha[5];
    int times = sizeof(test_sha) / sizeof(struct testVector), i;

    a.input  = "";
    a.output = "\xda\x39\xa3\xee\x5e\x6b\x4b\x0d\x32\x55\xbf\xef\x95\x60\x18"
               "\x90\xaf\xd8\x07\x09";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = WC_SHA_DIGEST_SIZE;

    b.input  = "abc";
    b.output = "\xA9\x99\x3E\x36\x47\x06\x81\x6A\xBA\x3E\x25\x71\x78\x50\xC2"
               "\x6C\x9C\xD0\xD8\x9D";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_SHA_DIGEST_SIZE;

    c.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    c.output = "\x84\x98\x3E\x44\x1C\x3B\xD2\x6E\xBA\xAE\x4A\xA1\xF9\x51\x29"
               "\xE5\xE5\x46\x70\xF1";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = WC_SHA_DIGEST_SIZE;

    d.input  = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
               "aaaaaa";
    d.output = "\x00\x98\xBA\x82\x4B\x5C\x16\x42\x7B\xD7\xA1\x12\x2A\x5A\x44"
               "\x2A\x25\xEC\x64\x4D";
    d.inLen  = XSTRLEN(d.input);
    d.outLen = WC_SHA_DIGEST_SIZE;

    e.input  = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
               "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
               "aaaaaaaaaa";
    e.output = "\xAD\x5B\x3F\xDB\xCB\x52\x67\x78\xC2\x83\x9D\x2F\x15\x1E\xA7"
               "\x53\x99\x5E\x26\xA0";
    e.inLen  = XSTRLEN(e.input);
    e.outLen = WC_SHA_DIGEST_SIZE;

    test_sha[0] = a;
    test_sha[1] = b;
    test_sha[2] = c;
    test_sha[3] = d;
    test_sha[4] = e;

    ret = wc_InitSha_ex(&sha, HEAP_HINT, devId);
    if (ret != 0)
        return -1800;
    ret = wc_InitSha_ex(&shaCopy, HEAP_HINT, devId);
    if (ret != 0) {
        wc_ShaFree(&sha);
        return -1801;
    }

    for (i = 0; i < times; ++i) {
        ret = wc_ShaUpdate(&sha, (byte*)test_sha[i].input,
            (word32)test_sha[i].inLen);
        if (ret != 0)
            ERROR_OUT(-1802 - i, exit);
        ret = wc_ShaGetHash(&sha, hashcopy);
        if (ret != 0)
            ERROR_OUT(-1803 - i, exit);
        ret = wc_ShaCopy(&sha, &shaCopy);
        if (ret != 0)
            ERROR_OUT(-1804 - i, exit);
        ret = wc_ShaFinal(&sha, hash);
        if (ret != 0)
            ERROR_OUT(-1805 - i, exit);
        wc_ShaFree(&shaCopy);

        if (XMEMCMP(hash, test_sha[i].output, WC_SHA_DIGEST_SIZE) != 0)
            ERROR_OUT(-1806 - i, exit);
        if (XMEMCMP(hash, hashcopy, WC_SHA_DIGEST_SIZE) != 0)
            ERROR_OUT(-1807 - i, exit);
    }

    /* BEGIN LARGE HASH TEST */ {
    byte large_input[1024];
#ifdef WOLFSSL_RENESAS_TSIP
    const char* large_digest =
            "\x1d\x6a\x5a\xf6\xe5\x7c\x86\xce\x7f\x7c\xaf\xd5\xdb\x08\xcd\x59"
            "\x15\x8c\x6d\xb6";
#else
    const char* large_digest =
           "\x8b\x77\x02\x48\x39\xe8\xdb\xd3\x9a\xf4\x05\x24\x66\x12\x2d\x9e"
           "\xc5\xd9\x0a\xac";
#endif
    for (i = 0; i < (int)sizeof(large_input); i++) {
        large_input[i] = (byte)(i & 0xFF);
    }
#ifdef WOLFSSL_RENESAS_TSIP
    times = 20;
#else
    times = 100;
#endif
#ifdef WOLFSSL_PIC32MZ_HASH
    wc_ShaSizeSet(&sha, times * sizeof(large_input));
#endif
    for (i = 0; i < times; ++i) {
        ret = wc_ShaUpdate(&sha, (byte*)large_input,
            (word32)sizeof(large_input));
        if (ret != 0)
            ERROR_OUT(-1808, exit);
    }
    ret = wc_ShaFinal(&sha, hash);
    if (ret != 0)
        ERROR_OUT(-1809, exit);
    if (XMEMCMP(hash, large_digest, WC_SHA_DIGEST_SIZE) != 0)
        ERROR_OUT(-1810, exit);
    } /* END LARGE HASH TEST */

exit:

    wc_ShaFree(&sha);
    wc_ShaFree(&shaCopy);

    return ret;
}

#endif /* NO_SHA */

#ifdef WOLFSSL_RIPEMD
int ripemd_test(void)
{
    RipeMd  ripemd;
    int ret;
    byte hash[RIPEMD_DIGEST_SIZE];

    testVector a, b, c, d;
    testVector test_ripemd[4];
    int times = sizeof(test_ripemd) / sizeof(struct testVector), i;

    a.input  = "abc";
    a.output = "\x8e\xb2\x08\xf7\xe0\x5d\x98\x7a\x9b\x04\x4a\x8e\x98\xc6"
               "\xb0\x87\xf1\x5a\x0b\xfc";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = RIPEMD_DIGEST_SIZE;

    b.input  = "message digest";
    b.output = "\x5d\x06\x89\xef\x49\xd2\xfa\xe5\x72\xb8\x81\xb1\x23\xa8"
               "\x5f\xfa\x21\x59\x5f\x36";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = RIPEMD_DIGEST_SIZE;

    c.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    c.output = "\x12\xa0\x53\x38\x4a\x9c\x0c\x88\xe4\x05\xa0\x6c\x27\xdc"
               "\xf4\x9a\xda\x62\xeb\x2b";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = RIPEMD_DIGEST_SIZE;

    d.input  = "12345678901234567890123456789012345678901234567890123456"
               "789012345678901234567890";
    d.output = "\x9b\x75\x2e\x45\x57\x3d\x4b\x39\xf4\xdb\xd3\x32\x3c\xab"
               "\x82\xbf\x63\x32\x6b\xfb";
    d.inLen  = XSTRLEN(d.input);
    d.outLen = RIPEMD_DIGEST_SIZE;

    test_ripemd[0] = a;
    test_ripemd[1] = b;
    test_ripemd[2] = c;
    test_ripemd[3] = d;

    ret = wc_InitRipeMd(&ripemd);
    if (ret != 0) {
        return -1900;
    }

    for (i = 0; i < times; ++i) {
        ret = wc_RipeMdUpdate(&ripemd, (byte*)test_ripemd[i].input,
                              (word32)test_ripemd[i].inLen);
        if (ret != 0) {
            return -1901 - i;
        }

        ret = wc_RipeMdFinal(&ripemd, hash);
        if (ret != 0) {
            return -1911 - i;
        }

        if (XMEMCMP(hash, test_ripemd[i].output, RIPEMD_DIGEST_SIZE) != 0)
            return -1921 - i;
    }

    return 0;
}
#endif /* WOLFSSL_RIPEMD */


#ifdef HAVE_BLAKE2


#define BLAKE2B_TESTS 3

static const byte blake2b_vec[BLAKE2B_TESTS][BLAKE2B_OUTBYTES] =
{
  {
    0x78, 0x6A, 0x02, 0xF7, 0x42, 0x01, 0x59, 0x03,
    0xC6, 0xC6, 0xFD, 0x85, 0x25, 0x52, 0xD2, 0x72,
    0x91, 0x2F, 0x47, 0x40, 0xE1, 0x58, 0x47, 0x61,
    0x8A, 0x86, 0xE2, 0x17, 0xF7, 0x1F, 0x54, 0x19,
    0xD2, 0x5E, 0x10, 0x31, 0xAF, 0xEE, 0x58, 0x53,
    0x13, 0x89, 0x64, 0x44, 0x93, 0x4E, 0xB0, 0x4B,
    0x90, 0x3A, 0x68, 0x5B, 0x14, 0x48, 0xB7, 0x55,
    0xD5, 0x6F, 0x70, 0x1A, 0xFE, 0x9B, 0xE2, 0xCE
  },
  {
    0x2F, 0xA3, 0xF6, 0x86, 0xDF, 0x87, 0x69, 0x95,
    0x16, 0x7E, 0x7C, 0x2E, 0x5D, 0x74, 0xC4, 0xC7,
    0xB6, 0xE4, 0x8F, 0x80, 0x68, 0xFE, 0x0E, 0x44,
    0x20, 0x83, 0x44, 0xD4, 0x80, 0xF7, 0x90, 0x4C,
    0x36, 0x96, 0x3E, 0x44, 0x11, 0x5F, 0xE3, 0xEB,
    0x2A, 0x3A, 0xC8, 0x69, 0x4C, 0x28, 0xBC, 0xB4,
    0xF5, 0xA0, 0xF3, 0x27, 0x6F, 0x2E, 0x79, 0x48,
    0x7D, 0x82, 0x19, 0x05, 0x7A, 0x50, 0x6E, 0x4B
  },
  {
    0x1C, 0x08, 0x79, 0x8D, 0xC6, 0x41, 0xAB, 0xA9,
    0xDE, 0xE4, 0x35, 0xE2, 0x25, 0x19, 0xA4, 0x72,
    0x9A, 0x09, 0xB2, 0xBF, 0xE0, 0xFF, 0x00, 0xEF,
    0x2D, 0xCD, 0x8E, 0xD6, 0xF8, 0xA0, 0x7D, 0x15,
    0xEA, 0xF4, 0xAE, 0xE5, 0x2B, 0xBF, 0x18, 0xAB,
    0x56, 0x08, 0xA6, 0x19, 0x0F, 0x70, 0xB9, 0x04,
    0x86, 0xC8, 0xA7, 0xD4, 0x87, 0x37, 0x10, 0xB1,
    0x11, 0x5D, 0x3D, 0xEB, 0xBB, 0x43, 0x27, 0xB5
  }
};



int blake2b_test(void)
{
    Blake2b b2b;
    byte    digest[64];
    byte    input[64];
    int     i, ret;

    for (i = 0; i < (int)sizeof(input); i++)
        input[i] = (byte)i;

    for (i = 0; i < BLAKE2B_TESTS; i++) {
        ret = wc_InitBlake2b(&b2b, 64);
        if (ret != 0)
            return -2000 - i;

        ret = wc_Blake2bUpdate(&b2b, input, i);
        if (ret != 0)
            return -2010 - 1;

        ret = wc_Blake2bFinal(&b2b, digest, 64);
        if (ret != 0)
            return -2020 - i;

        if (XMEMCMP(digest, blake2b_vec[i], 64) != 0) {
            return -2030 - i;
        }
    }

    return 0;
}
#endif /* HAVE_BLAKE2 */

#ifdef HAVE_BLAKE2S


#define BLAKE2S_TESTS 3

static const byte blake2s_vec[BLAKE2S_TESTS][BLAKE2S_OUTBYTES] =
{
  {
    0x69, 0x21, 0x7a, 0x30, 0x79, 0x90, 0x80, 0x94,
    0xe1, 0x11, 0x21, 0xd0, 0x42, 0x35, 0x4a, 0x7c,
    0x1f, 0x55, 0xb6, 0x48, 0x2c, 0xa1, 0xa5, 0x1e,
    0x1b, 0x25, 0x0d, 0xfd, 0x1e, 0xd0, 0xee, 0xf9,
  },
  {
    0xe3, 0x4d, 0x74, 0xdb, 0xaf, 0x4f, 0xf4, 0xc6,
    0xab, 0xd8, 0x71, 0xcc, 0x22, 0x04, 0x51, 0xd2,
    0xea, 0x26, 0x48, 0x84, 0x6c, 0x77, 0x57, 0xfb,
    0xaa, 0xc8, 0x2f, 0xe5, 0x1a, 0xd6, 0x4b, 0xea,
  },
  {
    0xdd, 0xad, 0x9a, 0xb1, 0x5d, 0xac, 0x45, 0x49,
    0xba, 0x42, 0xf4, 0x9d, 0x26, 0x24, 0x96, 0xbe,
    0xf6, 0xc0, 0xba, 0xe1, 0xdd, 0x34, 0x2a, 0x88,
    0x08, 0xf8, 0xea, 0x26, 0x7c, 0x6e, 0x21, 0x0c,
  }
};



int blake2s_test(void)
{
    Blake2s b2s;
    byte    digest[32];
    byte    input[64];
    int     i, ret;

    for (i = 0; i < (int)sizeof(input); i++)
        input[i] = (byte)i;

    for (i = 0; i < BLAKE2S_TESTS; i++) {
        ret = wc_InitBlake2s(&b2s, 32);
        if (ret != 0)
            return -2100 - i;

        ret = wc_Blake2sUpdate(&b2s, input, i);
        if (ret != 0)
            return -2110 - 1;

        ret = wc_Blake2sFinal(&b2s, digest, 32);
        if (ret != 0)
            return -2120 - i;

        if (XMEMCMP(digest, blake2s_vec[i], 32) != 0) {
            return -2130 - i;
        }
    }

    return 0;
}
#endif /* HAVE_BLAKE2S */


#ifdef WOLFSSL_SHA224
int sha224_test(void)
{
    wc_Sha224 sha, shaCopy;
    byte      hash[WC_SHA224_DIGEST_SIZE];
    byte      hashcopy[WC_SHA224_DIGEST_SIZE];
    int       ret = 0;

    testVector a, b, c;
    testVector test_sha[3];
    int times = sizeof(test_sha) / sizeof(struct testVector), i;

    a.input  = "";
    a.output = "\xd1\x4a\x02\x8c\x2a\x3a\x2b\xc9\x47\x61\x02\xbb\x28\x82\x34"
               "\xc4\x15\xa2\xb0\x1f\x82\x8e\xa6\x2a\xc5\xb3\xe4\x2f";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = WC_SHA224_DIGEST_SIZE;

    b.input  = "abc";
    b.output = "\x23\x09\x7d\x22\x34\x05\xd8\x22\x86\x42\xa4\x77\xbd\xa2\x55"
               "\xb3\x2a\xad\xbc\xe4\xbd\xa0\xb3\xf7\xe3\x6c\x9d\xa7";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_SHA224_DIGEST_SIZE;

    c.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    c.output = "\x75\x38\x8b\x16\x51\x27\x76\xcc\x5d\xba\x5d\xa1\xfd\x89\x01"
               "\x50\xb0\xc6\x45\x5c\xb4\xf5\x8b\x19\x52\x52\x25\x25";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = WC_SHA224_DIGEST_SIZE;

    test_sha[0] = a;
    test_sha[1] = b;
    test_sha[2] = c;

    ret = wc_InitSha224_ex(&sha, HEAP_HINT, devId);
    if (ret != 0)
        return -2200;
    ret = wc_InitSha224_ex(&shaCopy, HEAP_HINT, devId);
    if (ret != 0) {
        wc_Sha224Free(&sha);
        return -2201;
    }

    for (i = 0; i < times; ++i) {
        ret = wc_Sha224Update(&sha, (byte*)test_sha[i].input,
            (word32)test_sha[i].inLen);
        if (ret != 0)
            ERROR_OUT(-2202 - i, exit);
        ret = wc_Sha224GetHash(&sha, hashcopy);
        if (ret != 0)
            ERROR_OUT(-2203 - i, exit);
        ret = wc_Sha224Copy(&sha, &shaCopy);
        if (ret != 0)
            ERROR_OUT(-2204 - i, exit);
        ret = wc_Sha224Final(&sha, hash);
        if (ret != 0)
            ERROR_OUT(-2205 - i, exit);
        wc_Sha224Free(&shaCopy);

        if (XMEMCMP(hash, test_sha[i].output, WC_SHA224_DIGEST_SIZE) != 0)
            ERROR_OUT(-2206 - i, exit);
        if (XMEMCMP(hash, hashcopy, WC_SHA224_DIGEST_SIZE) != 0)
            ERROR_OUT(-2207 - i, exit);
    }

exit:
    wc_Sha224Free(&sha);
    wc_Sha224Free(&shaCopy);

    return ret;
}
#endif


#ifndef NO_SHA256
int sha256_test(void)
{
    wc_Sha256 sha, shaCopy;
    byte      hash[WC_SHA256_DIGEST_SIZE];
    byte      hashcopy[WC_SHA256_DIGEST_SIZE];
    int       ret = 0;

    testVector a, b, c;
    testVector test_sha[3];
    int times = sizeof(test_sha) / sizeof(struct testVector), i;

    a.input  = "";
    a.output = "\xe3\xb0\xc4\x42\x98\xfc\x1c\x14\x9a\xfb\xf4\xc8\x99\x6f\xb9"
               "\x24\x27\xae\x41\xe4\x64\x9b\x93\x4c\xa4\x95\x99\x1b\x78\x52"
               "\xb8\x55";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = WC_SHA256_DIGEST_SIZE;

    b.input  = "abc";
    b.output = "\xBA\x78\x16\xBF\x8F\x01\xCF\xEA\x41\x41\x40\xDE\x5D\xAE\x22"
               "\x23\xB0\x03\x61\xA3\x96\x17\x7A\x9C\xB4\x10\xFF\x61\xF2\x00"
               "\x15\xAD";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_SHA256_DIGEST_SIZE;

    c.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    c.output = "\x24\x8D\x6A\x61\xD2\x06\x38\xB8\xE5\xC0\x26\x93\x0C\x3E\x60"
               "\x39\xA3\x3C\xE4\x59\x64\xFF\x21\x67\xF6\xEC\xED\xD4\x19\xDB"
               "\x06\xC1";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = WC_SHA256_DIGEST_SIZE;

    test_sha[0] = a;
    test_sha[1] = b;
    test_sha[2] = c;

    ret = wc_InitSha256_ex(&sha, HEAP_HINT, devId);
    if (ret != 0)
        return -2300;
    ret = wc_InitSha256_ex(&shaCopy, HEAP_HINT, devId);
    if (ret != 0) {
        wc_Sha256Free(&sha);
        return -2301;
    }

    for (i = 0; i < times; ++i) {
        ret = wc_Sha256Update(&sha, (byte*)test_sha[i].input,
            (word32)test_sha[i].inLen);
        if (ret != 0) {
            ERROR_OUT(-2302 - i, exit);
	}
        ret = wc_Sha256GetHash(&sha, hashcopy);
        if (ret != 0)
            ERROR_OUT(-2303 - i, exit);
        ret = wc_Sha256Copy(&sha, &shaCopy);
        if (ret != 0)
            ERROR_OUT(-2304 - i, exit);
        ret = wc_Sha256Final(&sha, hash);
        if (ret != 0)
            ERROR_OUT(-2305 - i, exit);
        wc_Sha256Free(&shaCopy);

        if (XMEMCMP(hash, test_sha[i].output, WC_SHA256_DIGEST_SIZE) != 0)
            ERROR_OUT(-2306 - i, exit);
        if (XMEMCMP(hash, hashcopy, WC_SHA256_DIGEST_SIZE) != 0)
            ERROR_OUT(-2307 - i, exit);
    }

    /* BEGIN LARGE HASH TEST */ {
    byte large_input[1024];
#ifdef WOLFSSL_RENESAS_TSIP_CRYPT
    const char* large_digest =
            "\xa4\x75\x9e\x7a\xa2\x03\x38\x32\x88\x66\xa2\xea\x17\xea\xf8\xc7"
            "\xfe\x4e\xc6\xbb\xe3\xbb\x71\xce\xe7\xdf\x7c\x04\x61\xb3\xc2\x2f";
#else
    const char* large_digest =
           "\x27\x78\x3e\x87\x96\x3a\x4e\xfb\x68\x29\xb5\x31\xc9\xba\x57\xb4"
           "\x4f\x45\x79\x7f\x67\x70\xbd\x63\x7f\xbf\x0d\x80\x7c\xbd\xba\xe0";
#endif
    for (i = 0; i < (int)sizeof(large_input); i++) {
        large_input[i] = (byte)(i & 0xFF);
    }
#ifdef WOLFSSL_RENESAS_TSIP
    times = 20;
#else
    times = 100;
#endif
#ifdef WOLFSSL_PIC32MZ_HASH
    wc_Sha256SizeSet(&sha, times * sizeof(large_input));
#endif
    for (i = 0; i < times; ++i) {
        ret = wc_Sha256Update(&sha, (byte*)large_input,
            (word32)sizeof(large_input));
        if (ret != 0)
            ERROR_OUT(-2308, exit);
    }
    ret = wc_Sha256Final(&sha, hash);
    if (ret != 0)
        ERROR_OUT(-2309, exit);
    if (XMEMCMP(hash, large_digest, WC_SHA256_DIGEST_SIZE) != 0)
        ERROR_OUT(-2310, exit);
    } /* END LARGE HASH TEST */

exit:

    wc_Sha256Free(&sha);
    wc_Sha256Free(&shaCopy);

    return ret;
}
#endif


#ifdef WOLFSSL_SHA512
int sha512_test(void)
{
    wc_Sha512 sha, shaCopy;
    byte      hash[WC_SHA512_DIGEST_SIZE];
    byte      hashcopy[WC_SHA512_DIGEST_SIZE];
    int       ret = 0;

    testVector a, b, c;
    testVector test_sha[3];
    int times = sizeof(test_sha) / sizeof(struct testVector), i;

    a.input  = "";
    a.output = "\xcf\x83\xe1\x35\x7e\xef\xb8\xbd\xf1\x54\x28\x50\xd6\x6d\x80"
               "\x07\xd6\x20\xe4\x05\x0b\x57\x15\xdc\x83\xf4\xa9\x21\xd3\x6c"
               "\xe9\xce\x47\xd0\xd1\x3c\x5d\x85\xf2\xb0\xff\x83\x18\xd2\x87"
               "\x7e\xec\x2f\x63\xb9\x31\xbd\x47\x41\x7a\x81\xa5\x38\x32\x7a"
               "\xf9\x27\xda\x3e";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = WC_SHA512_DIGEST_SIZE;

    b.input  = "abc";
    b.output = "\xdd\xaf\x35\xa1\x93\x61\x7a\xba\xcc\x41\x73\x49\xae\x20\x41"
               "\x31\x12\xe6\xfa\x4e\x89\xa9\x7e\xa2\x0a\x9e\xee\xe6\x4b\x55"
               "\xd3\x9a\x21\x92\x99\x2a\x27\x4f\xc1\xa8\x36\xba\x3c\x23\xa3"
               "\xfe\xeb\xbd\x45\x4d\x44\x23\x64\x3c\xe8\x0e\x2a\x9a\xc9\x4f"
               "\xa5\x4c\xa4\x9f";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_SHA512_DIGEST_SIZE;

    c.input  = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhi"
               "jklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    c.output = "\x8e\x95\x9b\x75\xda\xe3\x13\xda\x8c\xf4\xf7\x28\x14\xfc\x14"
               "\x3f\x8f\x77\x79\xc6\xeb\x9f\x7f\xa1\x72\x99\xae\xad\xb6\x88"
               "\x90\x18\x50\x1d\x28\x9e\x49\x00\xf7\xe4\x33\x1b\x99\xde\xc4"
               "\xb5\x43\x3a\xc7\xd3\x29\xee\xb6\xdd\x26\x54\x5e\x96\xe5\x5b"
               "\x87\x4b\xe9\x09";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = WC_SHA512_DIGEST_SIZE;

    test_sha[0] = a;
    test_sha[1] = b;
    test_sha[2] = c;

    ret = wc_InitSha512_ex(&sha, HEAP_HINT, devId);
    if (ret != 0)
        return -2400;
    ret = wc_InitSha512_ex(&shaCopy, HEAP_HINT, devId);
    if (ret != 0) {
        wc_Sha512Free(&sha);
        return -2401;
    }

    for (i = 0; i < times; ++i) {
        ret = wc_Sha512Update(&sha, (byte*)test_sha[i].input,
            (word32)test_sha[i].inLen);
        if (ret != 0)
            ERROR_OUT(-2402 - i, exit);
        ret = wc_Sha512GetHash(&sha, hashcopy);
        if (ret != 0)
            ERROR_OUT(-2403 - i, exit);
        ret = wc_Sha512Copy(&sha, &shaCopy);
        if (ret != 0)
            ERROR_OUT(-2404 - i, exit);
        ret = wc_Sha512Final(&sha, hash);
        if (ret != 0)
            ERROR_OUT(-2405 - i, exit);
        wc_Sha512Free(&shaCopy);

        if (XMEMCMP(hash, test_sha[i].output, WC_SHA512_DIGEST_SIZE) != 0)
            ERROR_OUT(-2406 - i, exit);
        if (XMEMCMP(hash, hashcopy, WC_SHA512_DIGEST_SIZE) != 0)
            ERROR_OUT(-2407 - i, exit);
    }

    /* BEGIN LARGE HASH TEST */ {
    byte large_input[1024];
    const char* large_digest =
        "\x5a\x1f\x73\x90\xbd\x8c\xe4\x63\x54\xce\xa0\x9b\xef\x32\x78\x2d"
        "\x2e\xe7\x0d\x5e\x2f\x9d\x15\x1b\xdd\x2d\xde\x65\x0c\x7b\xfa\x83"
        "\x5e\x80\x02\x13\x84\xb8\x3f\xff\x71\x62\xb5\x09\x89\x63\xe1\xdc"
        "\xa5\xdc\xfc\xfa\x9d\x1a\x4d\xc0\xfa\x3a\x14\xf6\x01\x51\x90\xa4";

    for (i = 0; i < (int)sizeof(large_input); i++) {
        large_input[i] = (byte)(i & 0xFF);
    }
    times = 100;
    for (i = 0; i < times; ++i) {
        ret = wc_Sha512Update(&sha, (byte*)large_input,
            (word32)sizeof(large_input));
        if (ret != 0)
            ERROR_OUT(-2408, exit);
    }
    ret = wc_Sha512Final(&sha, hash);
    if (ret != 0)
        ERROR_OUT(-2409, exit);
    if (XMEMCMP(hash, large_digest, WC_SHA512_DIGEST_SIZE) != 0)
        ERROR_OUT(-2410, exit);
    } /* END LARGE HASH TEST */

exit:
    wc_Sha512Free(&sha);
    wc_Sha512Free(&shaCopy);

    return ret;
}
#endif


#ifdef WOLFSSL_SHA384
int sha384_test(void)
{
    wc_Sha384 sha, shaCopy;
    byte      hash[WC_SHA384_DIGEST_SIZE];
    byte      hashcopy[WC_SHA384_DIGEST_SIZE];
    int       ret = 0;

    testVector a, b, c;
    testVector test_sha[3];
    int times = sizeof(test_sha) / sizeof(struct testVector), i;

    a.input  = "";

    a.output = "\x38\xb0\x60\xa7\x51\xac\x96\x38\x4c\xd9\x32\x7e\xb1\xb1\xe3"
               "\x6a\x21\xfd\xb7\x11\x14\xbe\x07\x43\x4c\x0c\xc7\xbf\x63\xf6"
               "\xe1\xda\x27\x4e\xde\xbf\xe7\x6f\x65\xfb\xd5\x1a\xd2\xf1\x48"
               "\x98\xb9\x5b";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = WC_SHA384_DIGEST_SIZE;

    b.input  = "abc";
    b.output = "\xcb\x00\x75\x3f\x45\xa3\x5e\x8b\xb5\xa0\x3d\x69\x9a\xc6\x50"
               "\x07\x27\x2c\x32\xab\x0e\xde\xd1\x63\x1a\x8b\x60\x5a\x43\xff"
               "\x5b\xed\x80\x86\x07\x2b\xa1\xe7\xcc\x23\x58\xba\xec\xa1\x34"
               "\xc8\x25\xa7";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_SHA384_DIGEST_SIZE;

    c.input  = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhi"
               "jklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    c.output = "\x09\x33\x0c\x33\xf7\x11\x47\xe8\x3d\x19\x2f\xc7\x82\xcd\x1b"
               "\x47\x53\x11\x1b\x17\x3b\x3b\x05\xd2\x2f\xa0\x80\x86\xe3\xb0"
               "\xf7\x12\xfc\xc7\xc7\x1a\x55\x7e\x2d\xb9\x66\xc3\xe9\xfa\x91"
               "\x74\x60\x39";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = WC_SHA384_DIGEST_SIZE;

    test_sha[0] = a;
    test_sha[1] = b;
    test_sha[2] = c;

    ret = wc_InitSha384_ex(&sha, HEAP_HINT, devId);
    if (ret != 0)
        return -2500;
    ret = wc_InitSha384_ex(&shaCopy, HEAP_HINT, devId);
    if (ret != 0) {
        wc_Sha384Free(&sha);
        return -2501;
    }

    for (i = 0; i < times; ++i) {
        ret = wc_Sha384Update(&sha, (byte*)test_sha[i].input,
            (word32)test_sha[i].inLen);
        if (ret != 0)
            ERROR_OUT(-2502 - i, exit);
        ret = wc_Sha384GetHash(&sha, hashcopy);
        if (ret != 0)
            ERROR_OUT(-2503 - i, exit);
        ret = wc_Sha384Copy(&sha, &shaCopy);
        if (ret != 0)
            ERROR_OUT(-2504 - i, exit);
        ret = wc_Sha384Final(&sha, hash);
        if (ret != 0)
            ERROR_OUT(-2505 - i, exit);
        wc_Sha384Free(&shaCopy);

        if (XMEMCMP(hash, test_sha[i].output, WC_SHA384_DIGEST_SIZE) != 0)
            ERROR_OUT(-2506 - i, exit);
        if (XMEMCMP(hash, hashcopy, WC_SHA384_DIGEST_SIZE) != 0)
            ERROR_OUT(-2507 - i, exit);
    }

    /* BEGIN LARGE HASH TEST */ {
    byte large_input[1024];
    const char* large_digest =
        "\x37\x01\xdb\xff\x1e\x40\x4f\xe1\xe2\xea\x0b\x40\xbb\x3b\x39\x9a"
        "\xcc\xe8\x44\x8e\x7e\xe5\x64\xb5\x6b\x7f\x56\x64\xa7\x2b\x84\xe3"
        "\xc5\xd7\x79\x03\x25\x90\xf7\xa4\x58\xcb\x97\xa8\x8b\xb1\xa4\x81";

    for (i = 0; i < (int)sizeof(large_input); i++) {
        large_input[i] = (byte)(i & 0xFF);
    }
    times = 100;
    for (i = 0; i < times; ++i) {
        ret = wc_Sha384Update(&sha, (byte*)large_input,
            (word32)sizeof(large_input));
        if (ret != 0)
            ERROR_OUT(-2508, exit);
    }
    ret = wc_Sha384Final(&sha, hash);
    if (ret != 0)
        ERROR_OUT(-2509, exit);
    if (XMEMCMP(hash, large_digest, WC_SHA384_DIGEST_SIZE) != 0)
        ERROR_OUT(-2510, exit);
    } /* END LARGE HASH TEST */

exit:

    wc_Sha384Free(&sha);
    wc_Sha384Free(&shaCopy);

    return ret;
}
#endif /* WOLFSSL_SHA384 */

#ifdef WOLFSSL_SHA3
#ifndef WOLFSSL_NOSHA3_224
static int sha3_224_test(void)
{
    wc_Sha3  sha;
    byte  hash[WC_SHA3_224_DIGEST_SIZE];
    byte  hashcopy[WC_SHA3_224_DIGEST_SIZE];

    testVector a, b, c;
    testVector test_sha[3];
    int ret = 0;
    int times = sizeof(test_sha) / sizeof(struct testVector), i;

    a.input  = "";
    a.output = "\x6b\x4e\x03\x42\x36\x67\xdb\xb7\x3b\x6e\x15\x45\x4f\x0e\xb1"
               "\xab\xd4\x59\x7f\x9a\x1b\x07\x8e\x3f\x5b\x5a\x6b\xc7";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = WC_SHA3_224_DIGEST_SIZE;

    b.input  = "abc";
    b.output = "\xe6\x42\x82\x4c\x3f\x8c\xf2\x4a\xd0\x92\x34\xee\x7d\x3c\x76"
               "\x6f\xc9\xa3\xa5\x16\x8d\x0c\x94\xad\x73\xb4\x6f\xdf";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_SHA3_224_DIGEST_SIZE;

    c.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    c.output = "\x8a\x24\x10\x8b\x15\x4a\xda\x21\xc9\xfd\x55\x74\x49\x44\x79"
               "\xba\x5c\x7e\x7a\xb7\x6e\xf2\x64\xea\xd0\xfc\xce\x33";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = WC_SHA3_224_DIGEST_SIZE;

    test_sha[0] = a;
    test_sha[1] = b;
    test_sha[2] = c;

    ret = wc_InitSha3_224(&sha, HEAP_HINT, devId);
    if (ret != 0)
        return -2600;

    for (i = 0; i < times; ++i) {
        ret = wc_Sha3_224_Update(&sha, (byte*)test_sha[i].input,
            (word32)test_sha[i].inLen);
        if (ret != 0)
            ERROR_OUT(-2601 - i, exit);
        ret = wc_Sha3_224_GetHash(&sha, hashcopy);
        if (ret != 0)
            ERROR_OUT(-2602 - i, exit);
        ret = wc_Sha3_224_Final(&sha, hash);
        if (ret != 0)
            ERROR_OUT(-2603 - i, exit);

        if (XMEMCMP(hash, test_sha[i].output, WC_SHA3_224_DIGEST_SIZE) != 0)
            ERROR_OUT(-2604 - i, exit);
        if (XMEMCMP(hash, hashcopy, WC_SHA3_224_DIGEST_SIZE) != 0)
            ERROR_OUT(-2605 - i, exit);
    }

    /* BEGIN LARGE HASH TEST */ {
    byte large_input[1024];
    const char* large_digest =
        "\x13\xe5\xd3\x98\x7b\x94\xda\x41\x12\xc7\x1e\x92\x3a\x19"
        "\x21\x20\x86\x6f\x24\xbf\x0a\x31\xbc\xfd\xd6\x70\x36\xf3";

    for (i = 0; i < (int)sizeof(large_input); i++) {
        large_input[i] = (byte)(i & 0xFF);
    }
    times = 100;
    for (i = 0; i < times; ++i) {
        ret = wc_Sha3_224_Update(&sha, (byte*)large_input,
            (word32)sizeof(large_input));
        if (ret != 0)
            ERROR_OUT(-2606, exit);
    }
    ret = wc_Sha3_224_Final(&sha, hash);
    if (ret != 0)
        ERROR_OUT(-2607, exit);
    if (XMEMCMP(hash, large_digest, WC_SHA3_224_DIGEST_SIZE) != 0)
        ERROR_OUT(-2608, exit);
    } /* END LARGE HASH TEST */

exit:
    wc_Sha3_224_Free(&sha);

    return ret;
}
#endif /* WOLFSSL_NOSHA3_224 */

#ifndef WOLFSSL_NOSHA3_256
static int sha3_256_test(void)
{
    wc_Sha3  sha;
    byte  hash[WC_SHA3_256_DIGEST_SIZE];
    byte  hashcopy[WC_SHA3_256_DIGEST_SIZE];

    testVector a, b, c;
    testVector test_sha[3];
    int ret = 0;
    int times = sizeof(test_sha) / sizeof(struct testVector), i;

    byte large_input[1024];
    const char* large_digest =
        "\xdc\x90\xc0\xb1\x25\xdb\x2c\x34\x81\xa3\xff\xbc\x1e\x2e\x87\xeb"
        "\x6d\x70\x85\x61\xe0\xe9\x63\x61\xff\xe5\x84\x4b\x1f\x68\x05\x15";

#if defined(WOLFSSL_HASH_FLAGS) && !defined(WOLFSSL_ASYNC_CRYPT)
    /* test vector with hash of empty string */
    const char* Keccak256EmptyOut =
        "\xc5\xd2\x46\x01\x86\xf7\x23\x3c\x92\x7e\x7d\xb2\xdc\xc7\x03\xc0"
        "\xe5\x00\xb6\x53\xca\x82\x27\x3b\x7b\xfa\xd8\x04\x5d\x85\xa4\x70";
#endif

    a.input  = "";
    a.output = "\xa7\xff\xc6\xf8\xbf\x1e\xd7\x66\x51\xc1\x47\x56\xa0\x61\xd6"
               "\x62\xf5\x80\xff\x4d\xe4\x3b\x49\xfa\x82\xd8\x0a\x4b\x80\xf8"
               "\x43\x4a";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = WC_SHA3_256_DIGEST_SIZE;

    b.input  = "abc";
    b.output = "\x3a\x98\x5d\xa7\x4f\xe2\x25\xb2\x04\x5c\x17\x2d\x6b\xd3\x90"
               "\xbd\x85\x5f\x08\x6e\x3e\x9d\x52\x5b\x46\xbf\xe2\x45\x11\x43"
               "\x15\x32";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_SHA3_256_DIGEST_SIZE;

    c.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    c.output = "\x41\xc0\xdb\xa2\xa9\xd6\x24\x08\x49\x10\x03\x76\xa8\x23\x5e"
               "\x2c\x82\xe1\xb9\x99\x8a\x99\x9e\x21\xdb\x32\xdd\x97\x49\x6d"
               "\x33\x76";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = WC_SHA3_256_DIGEST_SIZE;

    test_sha[0] = a;
    test_sha[1] = b;
    test_sha[2] = c;

    ret = wc_InitSha3_256(&sha, HEAP_HINT, devId);
    if (ret != 0)
        return -2700;

    for (i = 0; i < times; ++i) {
        ret = wc_Sha3_256_Update(&sha, (byte*)test_sha[i].input,
            (word32)test_sha[i].inLen);
        if (ret != 0)
            ERROR_OUT(-2701 - i, exit);
        ret = wc_Sha3_256_GetHash(&sha, hashcopy);
        if (ret != 0)
            ERROR_OUT(-2702 - i, exit);
        ret = wc_Sha3_256_Final(&sha, hash);
        if (ret != 0)
            ERROR_OUT(-2703 - i, exit);

        if (XMEMCMP(hash, test_sha[i].output, WC_SHA3_256_DIGEST_SIZE) != 0)
            ERROR_OUT(-2704 - i, exit);
        if (XMEMCMP(hash, hashcopy, WC_SHA3_256_DIGEST_SIZE) != 0)
            ERROR_OUT(-2705 - i, exit);
    }

    /* BEGIN LARGE HASH TEST */ {
    for (i = 0; i < (int)sizeof(large_input); i++) {
        large_input[i] = (byte)(i & 0xFF);
    }
    times = 100;
    for (i = 0; i < times; ++i) {
        ret = wc_Sha3_256_Update(&sha, (byte*)large_input,
            (word32)sizeof(large_input));
        if (ret != 0)
            ERROR_OUT(-2706, exit);
    }
    ret = wc_Sha3_256_Final(&sha, hash);
    if (ret != 0)
        ERROR_OUT(-2707, exit);
    if (XMEMCMP(hash, large_digest, WC_SHA3_256_DIGEST_SIZE) != 0)
        ERROR_OUT(-2708, exit);
    } /* END LARGE HASH TEST */

    /* this is a software only variant of SHA3 not supported by external hardware devices */
#if defined(WOLFSSL_HASH_FLAGS) && !defined(WOLFSSL_ASYNC_CRYPT)
    /* Test for Keccak256 */
    ret = wc_Sha3_SetFlags(&sha, WC_HASH_SHA3_KECCAK256);
    if (ret != 0) {
        ERROR_OUT(-2709, exit);
    }
    ret = wc_Sha3_256_Update(&sha, (byte*)"", 0);
    if (ret != 0) {
        ERROR_OUT(-2710, exit);
    }
    ret = wc_Sha3_256_Final(&sha, hash);
    if (ret != 0) {
        ERROR_OUT(-2711, exit);
    }
    if (XMEMCMP(hash, Keccak256EmptyOut, WC_SHA3_256_DIGEST_SIZE) != 0) {
        ERROR_OUT(-2712, exit);
    }
#endif /* WOLFSSL_HASH_FLAGS && !WOLFSSL_ASYNC_CRYPT */

exit:
    wc_Sha3_256_Free(&sha);

    return ret;
}
#endif /* WOLFSSL_NOSHA3_256 */

#ifndef WOLFSSL_NOSHA3_384
static int sha3_384_test(void)
{
    wc_Sha3  sha;
    byte  hash[WC_SHA3_384_DIGEST_SIZE];
#ifndef NO_INTM_HASH_TEST
    byte  hashcopy[WC_SHA3_384_DIGEST_SIZE];
#endif

    testVector a, b, c;
    testVector test_sha[3];
    int ret;
    int times = sizeof(test_sha) / sizeof(struct testVector), i;

    a.input  = "";
    a.output = "\x0c\x63\xa7\x5b\x84\x5e\x4f\x7d\x01\x10\x7d\x85\x2e\x4c\x24"
               "\x85\xc5\x1a\x50\xaa\xaa\x94\xfc\x61\x99\x5e\x71\xbb\xee\x98"
               "\x3a\x2a\xc3\x71\x38\x31\x26\x4a\xdb\x47\xfb\x6b\xd1\xe0\x58"
               "\xd5\xf0\x04";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = WC_SHA3_384_DIGEST_SIZE;

#if defined(WOLFSSL_AFALG_XILINX_SHA3) || defined(WOLFSSL_XILINX_CRYPT)
    /* NIST test vector with a length that is a multiple of 4 */
    b.input  = "\x7d\x80\xb1\x60\xc4\xb5\x36\xa3\xbe\xb7\x99\x80\x59\x93\x44"
               "\x04\x7c\x5f\x82\xa1\xdf\xc3\xee\xd4";
    b.output = "\x04\x1c\xc5\x86\x1b\xa3\x34\x56\x3c\x61\xd4\xef\x97\x10\xd4"
               "\x89\x6c\x31\x1c\x92\xed\xbe\x0d\x7c\xd5\x3e\x80\x3b\xf2\xf4"
               "\xeb\x60\x57\x23\x55\x70\x77\x0c\xe8\x7c\x55\x20\xd7\xec\x14"
               "\x19\x87\x22";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_SHA3_384_DIGEST_SIZE;
#else
    b.input  = "abc";
    b.output = "\xec\x01\x49\x82\x88\x51\x6f\xc9\x26\x45\x9f\x58\xe2\xc6\xad"
               "\x8d\xf9\xb4\x73\xcb\x0f\xc0\x8c\x25\x96\xda\x7c\xf0\xe4\x9b"
               "\xe4\xb2\x98\xd8\x8c\xea\x92\x7a\xc7\xf5\x39\xf1\xed\xf2\x28"
               "\x37\x6d\x25";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_SHA3_384_DIGEST_SIZE;
#endif
    c.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    c.output = "\x99\x1c\x66\x57\x55\xeb\x3a\x4b\x6b\xbd\xfb\x75\xc7\x8a\x49"
               "\x2e\x8c\x56\xa2\x2c\x5c\x4d\x7e\x42\x9b\xfd\xbc\x32\xb9\xd4"
               "\xad\x5a\xa0\x4a\x1f\x07\x6e\x62\xfe\xa1\x9e\xef\x51\xac\xd0"
               "\x65\x7c\x22";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = WC_SHA3_384_DIGEST_SIZE;

#ifdef WOLFSSL_XILINX_CRYPT
    test_sha[0] = b; /* hardware acc. can not handle "" string */
#else
    test_sha[0] = a;
#endif
    test_sha[1] = b;
    test_sha[2] = c;

    ret = wc_InitSha3_384(&sha, HEAP_HINT, devId);
    if (ret != 0)
        return -2800;

    for (i = 0; i < times; ++i) {
        ret = wc_Sha3_384_Update(&sha, (byte*)test_sha[i].input,
            (word32)test_sha[i].inLen);
        if (ret != 0)
            ERROR_OUT(-2801 - i, exit);
    #ifndef NO_INTM_HASH_TEST
        ret = wc_Sha3_384_GetHash(&sha, hashcopy);
        if (ret != 0)
            ERROR_OUT(-2802 - i, exit);
    #endif
        ret = wc_Sha3_384_Final(&sha, hash);
        if (ret != 0)
            ERROR_OUT(-2803 - i, exit);

        if (XMEMCMP(hash, test_sha[i].output, WC_SHA3_384_DIGEST_SIZE) != 0)
            ERROR_OUT(-2804 - i, exit);
    #ifndef NO_INTM_HASH_TEST
        if (XMEMCMP(hash, hashcopy, WC_SHA3_384_DIGEST_SIZE) != 0)
            ERROR_OUT(-2805 - i, exit);
    #endif
    }

    /* BEGIN LARGE HASH TEST */ {
    byte large_input[1024];
    const char* large_digest =
        "\x30\x44\xec\x17\xef\x47\x9f\x55\x36\x11\xd6\x3f\x8a\x31\x5a\x71"
        "\x8a\x71\xa7\x1d\x8e\x84\xe8\x6c\x24\x02\x2f\x7a\x08\x4e\xea\xd7"
        "\x42\x36\x5d\xa8\xc2\xb7\x42\xad\xec\x19\xfb\xca\xc6\x64\xb3\xa4";

    for (i = 0; i < (int)sizeof(large_input); i++) {
        large_input[i] = (byte)(i & 0xFF);
    }
    times = 100;
    for (i = 0; i < times; ++i) {
        ret = wc_Sha3_384_Update(&sha, (byte*)large_input,
            (word32)sizeof(large_input));
        if (ret != 0)
            ERROR_OUT(-2806, exit);
    }
    ret = wc_Sha3_384_Final(&sha, hash);
    if (ret != 0)
        ERROR_OUT(-2807, exit);
    if (XMEMCMP(hash, large_digest, WC_SHA3_384_DIGEST_SIZE) != 0)
        ERROR_OUT(-2808, exit);
    } /* END LARGE HASH TEST */

exit:
    wc_Sha3_384_Free(&sha);

    return ret;
}
#endif /* WOLFSSL_NOSHA3_384 */

#ifndef WOLFSSL_NOSHA3_512
static int sha3_512_test(void)
{
    wc_Sha3  sha;
    byte  hash[WC_SHA3_512_DIGEST_SIZE];
    byte  hashcopy[WC_SHA3_512_DIGEST_SIZE];

    testVector a, b, c;
    testVector test_sha[3];
    int ret;
    int times = sizeof(test_sha) / sizeof(struct testVector), i;

    a.input  = "";
    a.output = "\xa6\x9f\x73\xcc\xa2\x3a\x9a\xc5\xc8\xb5\x67\xdc\x18\x5a\x75"
               "\x6e\x97\xc9\x82\x16\x4f\xe2\x58\x59\xe0\xd1\xdc\xc1\x47\x5c"
               "\x80\xa6\x15\xb2\x12\x3a\xf1\xf5\xf9\x4c\x11\xe3\xe9\x40\x2c"
               "\x3a\xc5\x58\xf5\x00\x19\x9d\x95\xb6\xd3\xe3\x01\x75\x85\x86"
               "\x28\x1d\xcd\x26";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = WC_SHA3_512_DIGEST_SIZE;

    b.input  = "abc";
    b.output = "\xb7\x51\x85\x0b\x1a\x57\x16\x8a\x56\x93\xcd\x92\x4b\x6b\x09"
               "\x6e\x08\xf6\x21\x82\x74\x44\xf7\x0d\x88\x4f\x5d\x02\x40\xd2"
               "\x71\x2e\x10\xe1\x16\xe9\x19\x2a\xf3\xc9\x1a\x7e\xc5\x76\x47"
               "\xe3\x93\x40\x57\x34\x0b\x4c\xf4\x08\xd5\xa5\x65\x92\xf8\x27"
               "\x4e\xec\x53\xf0";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_SHA3_512_DIGEST_SIZE;

    c.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    c.output = "\x04\xa3\x71\xe8\x4e\xcf\xb5\xb8\xb7\x7c\xb4\x86\x10\xfc\xa8"
               "\x18\x2d\xd4\x57\xce\x6f\x32\x6a\x0f\xd3\xd7\xec\x2f\x1e\x91"
               "\x63\x6d\xee\x69\x1f\xbe\x0c\x98\x53\x02\xba\x1b\x0d\x8d\xc7"
               "\x8c\x08\x63\x46\xb5\x33\xb4\x9c\x03\x0d\x99\xa2\x7d\xaf\x11"
               "\x39\xd6\xe7\x5e";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = WC_SHA3_512_DIGEST_SIZE;

    test_sha[0] = a;
    test_sha[1] = b;
    test_sha[2] = c;

    ret = wc_InitSha3_512(&sha, HEAP_HINT, devId);
    if (ret != 0)
        return -2900;

    for (i = 0; i < times; ++i) {
        ret = wc_Sha3_512_Update(&sha, (byte*)test_sha[i].input,
            (word32)test_sha[i].inLen);
        if (ret != 0)
            ERROR_OUT(-2901 - i, exit);
        ret = wc_Sha3_512_GetHash(&sha, hashcopy);
        if (ret != 0)
            ERROR_OUT(-2902 - i, exit);
        ret = wc_Sha3_512_Final(&sha, hash);
        if (ret != 0)
            ERROR_OUT(-2903 - i, exit);

        if (XMEMCMP(hash, test_sha[i].output, WC_SHA3_512_DIGEST_SIZE) != 0)
            ERROR_OUT(-2904 - i, exit);
        if (XMEMCMP(hash, hashcopy, WC_SHA3_512_DIGEST_SIZE) != 0)
            ERROR_OUT(-2905 - i, exit);
    }

    /* BEGIN LARGE HASH TEST */ {
    byte large_input[1024];
    const char* large_digest =
        "\x9c\x13\x26\xb6\x26\xb2\x94\x31\xbc\xf4\x34\xe9\x6f\xf2\xd6\x29"
        "\x9a\xd0\x9b\x32\x63\x2f\x18\xa7\x5f\x23\xc9\x60\xc2\x32\x0c\xbc"
        "\x57\x77\x33\xf1\x83\x81\x8a\xd3\x15\x7c\x93\xdc\x80\x9f\xed\x61"
        "\x41\xa7\x5b\xfd\x32\x0e\x38\x15\xb0\x46\x3b\x7a\x4f\xfd\x44\x88";

    for (i = 0; i < (int)sizeof(large_input); i++) {
        large_input[i] = (byte)(i & 0xFF);
    }
    times = 100;
    for (i = 0; i < times; ++i) {
        ret = wc_Sha3_512_Update(&sha, (byte*)large_input,
            (word32)sizeof(large_input));
        if (ret != 0)
            ERROR_OUT(-2906, exit);
    }
    ret = wc_Sha3_512_Final(&sha, hash);
    if (ret != 0)
        ERROR_OUT(-2907, exit);
    if (XMEMCMP(hash, large_digest, WC_SHA3_512_DIGEST_SIZE) != 0)
        ERROR_OUT(-2908, exit);
    } /* END LARGE HASH TEST */

exit:
    wc_Sha3_512_Free(&sha);

    return ret;
}
#endif /* WOLFSSL_NOSHA3_512 */

int sha3_test(void)
{
    int ret;

    (void)ret;

#ifndef WOLFSSL_NOSHA3_224
    if ((ret = sha3_224_test()) != 0)
        return ret;
#endif
#ifndef WOLFSSL_NOSHA3_256
    if ((ret = sha3_256_test()) != 0)
        return ret;
#endif
#ifndef WOLFSSL_NOSHA3_384
    if ((ret = sha3_384_test()) != 0)
        return ret;
#endif
#ifndef WOLFSSL_NOSHA3_512
    if ((ret = sha3_512_test()) != 0)
        return ret;
#endif

    return 0;
}
#endif /* WOLFSSL_SHA3 */

#ifdef WOLFSSL_SHAKE256
int shake256_test(void)
{
#ifndef WOLFSSL_NO_SHAKE256
    wc_Shake  sha;
    byte  hash[114];

    testVector a, b, c;
    testVector test_sha[3];
    int ret = 0;
    int times = sizeof(test_sha) / sizeof(struct testVector), i;

    byte large_input[1024];
    const char* large_digest =
        "\x90\x32\x4a\xcc\xd1\xdf\xb8\x0b\x79\x1f\xb8\xc8\x5b\x54\xc8\xe7"
        "\x45\xf5\x60\x6b\x38\x26\xb2\x0a\xee\x38\x01\xf3\xd9\xfa\x96\x9f"
        "\x6a\xd7\x15\xdf\xb6\xc2\xf4\x20\x33\x44\x55\xe8\x2a\x09\x2b\x68"
        "\x2e\x18\x65\x5e\x65\x93\x28\xbc\xb1\x9e\xe2\xb1\x92\xea\x98\xac"
        "\x21\xef\x4c\xe1\xb4\xb7\xbe\x81\x5c\x1d\xd3\xb7\x17\xe5\xbb\xc5"
        "\x8c\x68\xb7\xfb\xac\x55\x8a\x9b\x4d\x91\xe4\x9f\x72\xbb\x6e\x38"
        "\xaf\x21\x7d\x21\xaa\x98\x4e\x75\xc4\xb4\x1c\x7c\x50\x45\x54\xf9"
        "\xea\x26";

    a.input  = "";
    a.output = "\x46\xb9\xdd\x2b\x0b\xa8\x8d\x13\x23\x3b\x3f\xeb\x74\x3e\xeb"
               "\x24\x3f\xcd\x52\xea\x62\xb8\x1b\x82\xb5\x0c\x27\x64\x6e\xd5"
               "\x76\x2f\xd7\x5d\xc4\xdd\xd8\xc0\xf2\x00\xcb\x05\x01\x9d\x67"
               "\xb5\x92\xf6\xfc\x82\x1c\x49\x47\x9a\xb4\x86\x40\x29\x2e\xac"
               "\xb3\xb7\xc4\xbe\x14\x1e\x96\x61\x6f\xb1\x39\x57\x69\x2c\xc7"
               "\xed\xd0\xb4\x5a\xe3\xdc\x07\x22\x3c\x8e\x92\x93\x7b\xef\x84"
               "\xbc\x0e\xab\x86\x28\x53\x34\x9e\xc7\x55\x46\xf5\x8f\xb7\xc2"
               "\x77\x5c\x38\x46\x2c\x50\x10\xd8\x46";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = sizeof(hash);

    b.input  = "abc";
    b.output = "\x48\x33\x66\x60\x13\x60\xa8\x77\x1c\x68\x63\x08\x0c\xc4\x11"
               "\x4d\x8d\xb4\x45\x30\xf8\xf1\xe1\xee\x4f\x94\xea\x37\xe7\x8b"
               "\x57\x39\xd5\xa1\x5b\xef\x18\x6a\x53\x86\xc7\x57\x44\xc0\x52"
               "\x7e\x1f\xaa\x9f\x87\x26\xe4\x62\xa1\x2a\x4f\xeb\x06\xbd\x88"
               "\x01\xe7\x51\xe4\x13\x85\x14\x12\x04\xf3\x29\x97\x9f\xd3\x04"
               "\x7a\x13\xc5\x65\x77\x24\xad\xa6\x4d\x24\x70\x15\x7b\x3c\xdc"
               "\x28\x86\x20\x94\x4d\x78\xdb\xcd\xdb\xd9\x12\x99\x3f\x09\x13"
               "\xf1\x64\xfb\x2c\xe9\x51\x31\xa2\xd0";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = sizeof(hash);

    c.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    c.output = "\x4d\x8c\x2d\xd2\x43\x5a\x01\x28\xee\xfb\xb8\xc3\x6f\x6f\x87"
               "\x13\x3a\x79\x11\xe1\x8d\x97\x9e\xe1\xae\x6b\xe5\xd4\xfd\x2e"
               "\x33\x29\x40\xd8\x68\x8a\x4e\x6a\x59\xaa\x80\x60\xf1\xf9\xbc"
               "\x99\x6c\x05\xac\xa3\xc6\x96\xa8\xb6\x62\x79\xdc\x67\x2c\x74"
               "\x0b\xb2\x24\xec\x37\xa9\x2b\x65\xdb\x05\x39\xc0\x20\x34\x55"
               "\xf5\x1d\x97\xcc\xe4\xcf\xc4\x91\x27\xd7\x26\x0a\xfc\x67\x3a"
               "\xf2\x08\xba\xf1\x9b\xe2\x12\x33\xf3\xde\xbe\x78\xd0\x67\x60"
               "\xcf\xa5\x51\xee\x1e\x07\x91\x41\xd4";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = sizeof(hash);

    test_sha[0] = a;
    test_sha[1] = b;
    test_sha[2] = c;

    ret = wc_InitShake256(&sha, HEAP_HINT, devId);
    if (ret != 0)
        return -3100;

    for (i = 0; i < times; ++i) {
        ret = wc_Shake256_Update(&sha, (byte*)test_sha[i].input,
            (word32)test_sha[i].inLen);
        if (ret != 0)
            ERROR_OUT(-3101 - i, exit);
        ret = wc_Shake256_Final(&sha, hash, (word32)test_sha[i].outLen);
        if (ret != 0)
            ERROR_OUT(-3102 - i, exit);

        if (XMEMCMP(hash, test_sha[i].output, test_sha[i].outLen) != 0)
            ERROR_OUT(-3103 - i, exit);
    }

    /* BEGIN LARGE HASH TEST */ {
    for (i = 0; i < (int)sizeof(large_input); i++) {
        large_input[i] = (byte)(i & 0xFF);
    }
    times = 100;
    for (i = 0; i < times; ++i) {
        ret = wc_Shake256_Update(&sha, (byte*)large_input,
            (word32)sizeof(large_input));
        if (ret != 0)
            ERROR_OUT(-3104, exit);
    }
    ret = wc_Shake256_Final(&sha, hash, (word32)sizeof(hash));
    if (ret != 0)
        ERROR_OUT(-3105, exit);
    if (XMEMCMP(hash, large_digest, sizeof(hash)) != 0)
        ERROR_OUT(-3106, exit);
    } /* END LARGE HASH TEST */

exit:
    wc_Shake256_Free(&sha);

    return ret;
#else
    return 0;
#endif
}
#endif


int hash_test(void)
{
    wc_HashAlg       hash;
    int              ret, exp_ret;
    int              i, j;
    int              digestSz;
    byte             data[] = "0123456789abcdef0123456789abcdef0123456";
    byte             out[WC_MAX_DIGEST_SIZE];
    byte             hashOut[WC_MAX_DIGEST_SIZE];
#if !defined(NO_ASN) || !defined(NO_DH) || defined(HAVE_ECC)
    enum wc_HashType hashType;
#endif
    enum wc_HashType typesGood[] = { WC_HASH_TYPE_MD5, WC_HASH_TYPE_SHA,
                                     WC_HASH_TYPE_SHA224, WC_HASH_TYPE_SHA256,
                                     WC_HASH_TYPE_SHA384, WC_HASH_TYPE_SHA512,
                                     WC_HASH_TYPE_SHA3_224,
                                     WC_HASH_TYPE_SHA3_256,
                                     WC_HASH_TYPE_SHA3_384,
                                     WC_HASH_TYPE_SHA3_512 };
    enum wc_HashType typesNoImpl[] = {
#ifdef NO_MD5
                                        WC_HASH_TYPE_MD5,
#endif
#ifdef NO_SHA
                                        WC_HASH_TYPE_SHA,
#endif
#ifndef WOLFSSL_SHA224
                                        WC_HASH_TYPE_SHA224,
#endif
#ifdef NO_SHA256
                                        WC_HASH_TYPE_SHA256,
#endif
#ifndef WOLFSSL_SHA384
                                        WC_HASH_TYPE_SHA384,
#endif
#ifndef WOLFSSL_SHA512
                                        WC_HASH_TYPE_SHA512,
#endif
#if !defined(WOLFSSL_SHA3) || defined(WOLFSSL_NOSHA3_224)
                                        WC_HASH_TYPE_SHA3_224,
#endif
#if !defined(WOLFSSL_SHA3) || defined(WOLFSSL_NOSHA3_256)
                                        WC_HASH_TYPE_SHA3_256,
#endif
#if !defined(WOLFSSL_SHA3) || defined(WOLFSSL_NOSHA3_384)
                                        WC_HASH_TYPE_SHA3_384,
#endif
#if !defined(WOLFSSL_SHA3) || defined(WOLFSSL_NOSHA3_512)
                                        WC_HASH_TYPE_SHA3_512,
#endif
                                        WC_HASH_TYPE_NONE
                                     };
    enum wc_HashType typesBad[]  = { WC_HASH_TYPE_NONE, WC_HASH_TYPE_MD5_SHA,
                                     WC_HASH_TYPE_MD2, WC_HASH_TYPE_MD4 };
    enum wc_HashType typesHashBad[] = { WC_HASH_TYPE_MD2, WC_HASH_TYPE_MD4,
                                        WC_HASH_TYPE_BLAKE2B,
                                        WC_HASH_TYPE_NONE };

    /* Parameter Validation testing. */
    ret = wc_HashInit(NULL, WC_HASH_TYPE_SHA256);
    if (ret != BAD_FUNC_ARG)
        return -3200;
    ret = wc_HashUpdate(NULL, WC_HASH_TYPE_SHA256, NULL, sizeof(data));
    if (ret != BAD_FUNC_ARG)
        return -3201;
    ret = wc_HashUpdate(&hash, WC_HASH_TYPE_SHA256, NULL, sizeof(data));
    if (ret != BAD_FUNC_ARG)
        return -3202;
    ret = wc_HashUpdate(NULL, WC_HASH_TYPE_SHA256, data, sizeof(data));
    if (ret != BAD_FUNC_ARG)
        return -3203;
    ret = wc_HashFinal(NULL, WC_HASH_TYPE_SHA256, NULL);
    if (ret != BAD_FUNC_ARG)
        return -3204;
    ret = wc_HashFinal(&hash, WC_HASH_TYPE_SHA256, NULL);
    if (ret != BAD_FUNC_ARG)
        return -3205;
    ret = wc_HashFinal(NULL, WC_HASH_TYPE_SHA256, out);
    if (ret != BAD_FUNC_ARG)
        return -3206;

    /* Try invalid hash algorithms. */
    for (i = 0; i < (int)(sizeof(typesBad)/sizeof(*typesBad)); i++) {
        ret = wc_HashInit(&hash, typesBad[i]);
        if (ret != BAD_FUNC_ARG)
            return -3207 - i;
        ret = wc_HashUpdate(&hash, typesBad[i], data, sizeof(data));
        if (ret != BAD_FUNC_ARG)
            return -3217 - i;
        ret = wc_HashFinal(&hash, typesBad[i], out);
        if (ret != BAD_FUNC_ARG)
            return -3227 - i;
        wc_HashFree(&hash, typesBad[i]);
    }

    /* Try valid hash algorithms. */
    for (i = 0, j = 0; i < (int)(sizeof(typesGood)/sizeof(*typesGood)); i++) {
        exp_ret = 0;
        if (typesGood[i] == typesNoImpl[j]) {
            /* Recognized but no implementation compiled in. */
            exp_ret = HASH_TYPE_E;
            j++;
        }
        ret = wc_HashInit(&hash, typesGood[i]);
        if (ret != exp_ret)
            return -3237 - i;
        ret = wc_HashUpdate(&hash, typesGood[i], data, sizeof(data));
        if (ret != exp_ret)
            return -3247 - i;
        ret = wc_HashFinal(&hash, typesGood[i], out);
        if (ret != exp_ret)
            return -3257 - i;
        wc_HashFree(&hash, typesGood[i]);

        digestSz = wc_HashGetDigestSize(typesGood[i]);
        if (exp_ret < 0 && digestSz != exp_ret)
            return -3267 - i;
        if (exp_ret == 0 && digestSz < 0)
            return -3277 - i;
        if (exp_ret == 0) {
            ret = wc_Hash(typesGood[i], data, sizeof(data), hashOut,
                                                                  digestSz - 1);
            if (ret != BUFFER_E)
                return -3287 - i;
        }
        ret = wc_Hash(typesGood[i], data, sizeof(data), hashOut, digestSz);
        if (ret != exp_ret)
            return -3297 - i;
        if (exp_ret == 0 && XMEMCMP(out, hashOut, digestSz) != 0)
            return -3307 -i;

        ret = wc_HashGetBlockSize(typesGood[i]);
        if (exp_ret < 0 && ret != exp_ret)
            return -3308 - i;
        if (exp_ret == 0 && ret < 0)
            return -3318 - i;

#if !defined(NO_ASN) || !defined(NO_DH) || defined(HAVE_ECC)
        ret = wc_HashGetOID(typesGood[i]);
        if (ret == BAD_FUNC_ARG ||
                (exp_ret == 0 && ret == HASH_TYPE_E) ||
                (exp_ret != 0 && ret != HASH_TYPE_E)) {
            return -3328 - i;
        }

        hashType = wc_OidGetHash(ret);
        if (exp_ret == 0 && hashType != typesGood[i])
            return -3348 - i;
#endif /* !defined(NO_ASN) || !defined(NO_DH) || defined(HAVE_ECC) */
    }

    for (i = 0; i < (int)(sizeof(typesHashBad)/sizeof(*typesHashBad)); i++) {
        ret = wc_Hash(typesHashBad[i], data, sizeof(data), out, sizeof(out));
        if (ret != BAD_FUNC_ARG && ret != BUFFER_E)
            return -3358 - i;
    }

#if !defined(NO_ASN) || !defined(NO_DH) || defined(HAVE_ECC)
    ret = wc_HashGetOID(WC_HASH_TYPE_MD2);
#ifdef WOLFSSL_MD2
    if (ret == HASH_TYPE_E || ret == BAD_FUNC_ARG)
        return -3368;
#else
    if (ret != HASH_TYPE_E)
        return -3369;
#endif
    hashType = wc_OidGetHash(646); /* Md2h */
#ifdef WOLFSSL_MD2
    if (hashType != WC_HASH_TYPE_MD2)
        return -3370;
#else
    if (hashType != WC_HASH_TYPE_NONE)
        return -3371;
#endif

    ret = wc_HashGetOID(WC_HASH_TYPE_MD5_SHA);
#ifndef NO_MD5
    if (ret == HASH_TYPE_E || ret == BAD_FUNC_ARG)
        return -3372;
#else
    if (ret != HASH_TYPE_E)
        return -3373;
#endif
    ret = wc_HashGetOID(WC_HASH_TYPE_MD4);
    if (ret != BAD_FUNC_ARG)
        return -3374;
    ret = wc_HashGetOID(WC_HASH_TYPE_NONE);
    if (ret != BAD_FUNC_ARG)
        return -3375;

    hashType = wc_OidGetHash(0);
    if (hashType != WC_HASH_TYPE_NONE)
        return -3376;
#endif /* !defined(NO_ASN) || !defined(NO_DH) || defined(HAVE_ECC) */

    ret = wc_HashGetBlockSize(WC_HASH_TYPE_MD2);
#ifdef WOLFSSL_MD2
    if (ret == HASH_TYPE_E || ret == BAD_FUNC_ARG)
        return -3377;
#else
    if (ret != HASH_TYPE_E)
        return -3378;
#endif
    ret = wc_HashGetDigestSize(WC_HASH_TYPE_MD2);
#ifdef WOLFSSL_MD2
    if (ret == HASH_TYPE_E || ret == BAD_FUNC_ARG)
        return -3379;
#else
    if (ret != HASH_TYPE_E)
        return -3380;
#endif

    ret = wc_HashGetBlockSize(WC_HASH_TYPE_MD4);
#ifndef NO_MD4
    if (ret == HASH_TYPE_E || ret == BAD_FUNC_ARG)
        return -3381;
#else
    if (ret != HASH_TYPE_E)
        return -3382;
#endif
    ret = wc_HashGetDigestSize(WC_HASH_TYPE_MD4);
#ifndef NO_MD4
    if (ret == HASH_TYPE_E || ret == BAD_FUNC_ARG)
        return -3383;
#else
    if (ret != HASH_TYPE_E)
        return -3384;
#endif
    ret = wc_HashGetBlockSize(WC_HASH_TYPE_MD5_SHA);
#if !defined(NO_MD5) && !defined(NO_SHA)
    if (ret == HASH_TYPE_E || ret == BAD_FUNC_ARG)
        return -3385;
#else
    if (ret != HASH_TYPE_E)
        return -3386;
#endif

    ret = wc_HashGetBlockSize(WC_HASH_TYPE_BLAKE2B);
#if defined(HAVE_BLAKE2) || defined(HAVE_BLAKE2S)
    if (ret == HASH_TYPE_E || ret == BAD_FUNC_ARG)
        return -3387;
#else
    if (ret != HASH_TYPE_E)
        return -3388;
#endif
    ret = wc_HashGetDigestSize(WC_HASH_TYPE_BLAKE2B);
#if defined(HAVE_BLAKE2) || defined(HAVE_BLAKE2S)
    if (ret == HASH_TYPE_E || ret == BAD_FUNC_ARG)
        return -3389;
#else
    if (ret != HASH_TYPE_E)
        return -3390;
#endif

    ret = wc_HashGetBlockSize(WC_HASH_TYPE_NONE);
    if (ret != BAD_FUNC_ARG)
        return -3391;
    ret = wc_HashGetDigestSize(WC_HASH_TYPE_NONE);
    if (ret != BAD_FUNC_ARG)
        return -3392;

#ifndef NO_CERTS
#if defined(WOLFSSL_MD2) && !defined(HAVE_SELFTEST)
    ret = wc_GetCTC_HashOID(MD2);
    if (ret == 0)
        return -3393;
#endif
#ifndef NO_MD5
    ret = wc_GetCTC_HashOID(WC_MD5);
    if (ret == 0)
        return -3394;
#endif
#ifndef NO_SHA
    ret = wc_GetCTC_HashOID(WC_SHA);
    if (ret == 0)
        return -3395;
#endif
#ifdef WOLFSSL_SHA224
    ret = wc_GetCTC_HashOID(WC_SHA224);
    if (ret == 0)
        return -3396;
#endif
#ifndef NO_SHA256
    ret = wc_GetCTC_HashOID(WC_SHA256);
    if (ret == 0)
        return -3397;
#endif
#ifdef WOLFSSL_SHA384
    ret = wc_GetCTC_HashOID(WC_SHA384);
    if (ret == 0)
        return -3398;
#endif
#ifdef WOLFSSL_SHA512
    ret = wc_GetCTC_HashOID(WC_SHA512);
    if (ret == 0)
        return -3399;
#endif
    ret = wc_GetCTC_HashOID(-1);
    if (ret != 0)
        return -3400;
#endif

    return 0;
}

#if !defined(NO_HMAC) && !defined(NO_MD5)
int hmac_md5_test(void)
{
    Hmac hmac;
    byte hash[WC_MD5_DIGEST_SIZE];

    const char* keys[]=
    {
        "\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b",
        "Jefe",
        "\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA"
    };

    testVector a, b, c;
    testVector test_hmac[3];

    int ret;
    int times = sizeof(test_hmac) / sizeof(testVector), i;

    a.input  = "Hi There";
    a.output = "\x92\x94\x72\x7a\x36\x38\xbb\x1c\x13\xf4\x8e\xf8\x15\x8b\xfc"
               "\x9d";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = WC_MD5_DIGEST_SIZE;

    b.input  = "what do ya want for nothing?";
    b.output = "\x75\x0c\x78\x3e\x6a\xb0\xb5\x03\xea\xa8\x6e\x31\x0a\x5d\xb7"
               "\x38";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_MD5_DIGEST_SIZE;

    c.input  = "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD";
    c.output = "\x56\xbe\x34\x52\x1d\x14\x4c\x88\xdb\xb8\xc7\x33\xf0\xe8\xb3"
               "\xf6";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = WC_MD5_DIGEST_SIZE;

    test_hmac[0] = a;
    test_hmac[1] = b;
    test_hmac[2] = c;

    for (i = 0; i < times; ++i) {
    #if defined(HAVE_FIPS) || defined(HAVE_CAVIUM)
        if (i == 1) {
            continue; /* cavium can't handle short keys, fips not allowed */
        }
    #endif

        if (wc_HmacInit(&hmac, HEAP_HINT, devId) != 0) {
            return -3500;
        }

        ret = wc_HmacSetKey(&hmac, WC_MD5, (byte*)keys[i],
            (word32)XSTRLEN(keys[i]));
        if (ret != 0)
            return -3501;
        ret = wc_HmacUpdate(&hmac, (byte*)test_hmac[i].input,
                   (word32)test_hmac[i].inLen);
        if (ret != 0)
            return -3502;
        ret = wc_HmacFinal(&hmac, hash);
        if (ret != 0)
            return -3503;

        if (XMEMCMP(hash, test_hmac[i].output, WC_MD5_DIGEST_SIZE) != 0)
            return -3504 - i;

        wc_HmacFree(&hmac);
    }

#ifndef HAVE_FIPS
    if (wc_HmacSizeByType(WC_MD5) != WC_MD5_DIGEST_SIZE)
        return -3514;
#endif

    return 0;
}
#endif /* NO_HMAC && NO_MD5 */

#if !defined(NO_HMAC) && !defined(NO_SHA)
int hmac_sha_test(void)
{
    Hmac hmac;
    byte hash[WC_SHA_DIGEST_SIZE];

    const char* keys[]=
    {
        "\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b"
                                                                "\x0b\x0b\x0b",
        "Jefe",
        "\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA"
                                                                "\xAA\xAA\xAA"
    };

    testVector a, b, c;
    testVector test_hmac[3];

    int ret;
    int times = sizeof(test_hmac) / sizeof(testVector), i;

    a.input  = "Hi There";
    a.output = "\xb6\x17\x31\x86\x55\x05\x72\x64\xe2\x8b\xc0\xb6\xfb\x37\x8c"
               "\x8e\xf1\x46\xbe\x00";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = WC_SHA_DIGEST_SIZE;

    b.input  = "what do ya want for nothing?";
    b.output = "\xef\xfc\xdf\x6a\xe5\xeb\x2f\xa2\xd2\x74\x16\xd5\xf1\x84\xdf"
               "\x9c\x25\x9a\x7c\x79";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_SHA_DIGEST_SIZE;

    c.input  = "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD";
    c.output = "\x12\x5d\x73\x42\xb9\xac\x11\xcd\x91\xa3\x9a\xf4\x8a\xa1\x7b"
               "\x4f\x63\xf1\x75\xd3";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = WC_SHA_DIGEST_SIZE;

    test_hmac[0] = a;
    test_hmac[1] = b;
    test_hmac[2] = c;

    for (i = 0; i < times; ++i) {
#if defined(HAVE_FIPS) || defined(HAVE_CAVIUM)
        if (i == 1)
            continue; /* cavium can't handle short keys, fips not allowed */
#endif

        if (wc_HmacInit(&hmac, HEAP_HINT, devId) != 0)
            return -3600;

        ret = wc_HmacSetKey(&hmac, WC_SHA, (byte*)keys[i],
            (word32)XSTRLEN(keys[i]));
        if (ret != 0)
            return -3601;
        ret = wc_HmacUpdate(&hmac, (byte*)test_hmac[i].input,
                   (word32)test_hmac[i].inLen);
        if (ret != 0)
            return -3602;
        ret = wc_HmacFinal(&hmac, hash);
        if (ret != 0)
            return -3603;

        if (XMEMCMP(hash, test_hmac[i].output, WC_SHA_DIGEST_SIZE) != 0)
            return -3604 - i;

        wc_HmacFree(&hmac);
    }

#ifndef HAVE_FIPS
    if (wc_HmacSizeByType(WC_SHA) != WC_SHA_DIGEST_SIZE)
        return -3614;
#endif

    return 0;
}
#endif


#if !defined(NO_HMAC) && defined(WOLFSSL_SHA224)
int hmac_sha224_test(void)
{
    Hmac hmac;
    byte hash[WC_SHA224_DIGEST_SIZE];

    const char* keys[]=
    {
        "\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b"
                                                                "\x0b\x0b\x0b",
        "Jefe",
        "\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA"
                                                                "\xAA\xAA\xAA",
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
    };

    testVector a, b, c, d;
    testVector test_hmac[4];

    int ret;
    int times = sizeof(test_hmac) / sizeof(testVector), i;

    a.input  = "Hi There";
    a.output = "\x89\x6f\xb1\x12\x8a\xbb\xdf\x19\x68\x32\x10\x7c\xd4\x9d\xf3"
               "\x3f\x47\xb4\xb1\x16\x99\x12\xba\x4f\x53\x68\x4b\x22";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = WC_SHA224_DIGEST_SIZE;

    b.input  = "what do ya want for nothing?";
    b.output = "\xa3\x0e\x01\x09\x8b\xc6\xdb\xbf\x45\x69\x0f\x3a\x7e\x9e\x6d"
               "\x0f\x8b\xbe\xa2\xa3\x9e\x61\x48\x00\x8f\xd0\x5e\x44";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_SHA224_DIGEST_SIZE;

    c.input  = "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD";
    c.output = "\x7f\xb3\xcb\x35\x88\xc6\xc1\xf6\xff\xa9\x69\x4d\x7d\x6a\xd2"
               "\x64\x93\x65\xb0\xc1\xf6\x5d\x69\xd1\xec\x83\x33\xea";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = WC_SHA224_DIGEST_SIZE;

    d.input  = "Big Key Input";
    d.output = "\xe7\x4e\x2b\x8a\xa9\xf0\x37\x2f\xed\xae\x70\x0c\x49\x47\xf1"
               "\x46\x54\xa7\x32\x6b\x55\x01\x87\xd2\xc8\x02\x0e\x3a";
    d.inLen  = XSTRLEN(d.input);
    d.outLen = WC_SHA224_DIGEST_SIZE;

    test_hmac[0] = a;
    test_hmac[1] = b;
    test_hmac[2] = c;
    test_hmac[3] = d;

    for (i = 0; i < times; ++i) {
#if defined(HAVE_FIPS) || defined(HAVE_CAVIUM)
        if (i == 1)
            continue; /* cavium can't handle short keys, fips not allowed */
#endif

        if (wc_HmacInit(&hmac, HEAP_HINT, devId) != 0)
            return -3700;

        ret = wc_HmacSetKey(&hmac, WC_SHA224, (byte*)keys[i],
            (word32)XSTRLEN(keys[i]));
        if (ret != 0)
            return -3701;
        ret = wc_HmacUpdate(&hmac, (byte*)test_hmac[i].input,
                   (word32)test_hmac[i].inLen);
        if (ret != 0)
            return -3702;
        ret = wc_HmacFinal(&hmac, hash);
        if (ret != 0)
            return -3703;

        if (XMEMCMP(hash, test_hmac[i].output, WC_SHA224_DIGEST_SIZE) != 0)
            return -3704 - i;

        wc_HmacFree(&hmac);
    }

#ifndef HAVE_FIPS
    if (wc_HmacSizeByType(WC_SHA224) != WC_SHA224_DIGEST_SIZE)
        return -3714;
#endif

    return 0;
}
#endif


#if !defined(NO_HMAC) && !defined(NO_SHA256)
int hmac_sha256_test(void)
{
    Hmac hmac;
    byte hash[WC_SHA256_DIGEST_SIZE];

    const char* keys[]=
    {
        "\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b"
                                                                "\x0b\x0b\x0b",
        "Jefe",
        "\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA"
                                                                "\xAA\xAA\xAA",
        "\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA"
                                                                "\xAA\xAA\xAA",
    };

    testVector a, b, c, d;
    testVector test_hmac[4];

    int ret;
    int times = sizeof(test_hmac) / sizeof(testVector), i;

    a.input  = "Hi There";
    a.output = "\xb0\x34\x4c\x61\xd8\xdb\x38\x53\x5c\xa8\xaf\xce\xaf\x0b\xf1"
               "\x2b\x88\x1d\xc2\x00\xc9\x83\x3d\xa7\x26\xe9\x37\x6c\x2e\x32"
               "\xcf\xf7";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = WC_SHA256_DIGEST_SIZE;

    b.input  = "what do ya want for nothing?";
    b.output = "\x5b\xdc\xc1\x46\xbf\x60\x75\x4e\x6a\x04\x24\x26\x08\x95\x75"
               "\xc7\x5a\x00\x3f\x08\x9d\x27\x39\x83\x9d\xec\x58\xb9\x64\xec"
               "\x38\x43";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_SHA256_DIGEST_SIZE;

    c.input  = "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD";
    c.output = "\x77\x3e\xa9\x1e\x36\x80\x0e\x46\x85\x4d\xb8\xeb\xd0\x91\x81"
               "\xa7\x29\x59\x09\x8b\x3e\xf8\xc1\x22\xd9\x63\x55\x14\xce\xd5"
               "\x65\xfe";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = WC_SHA256_DIGEST_SIZE;

    d.input  = 0;
    d.output = "\x86\xe5\x4f\xd4\x48\x72\x5d\x7e\x5d\xcf\xe2\x23\x53\xc8\x28"
               "\xaf\x48\x78\x1e\xb4\x8c\xae\x81\x06\xa7\xe1\xd4\x98\x94\x9f"
               "\x3e\x46";
    d.inLen  = 0;
    d.outLen = WC_SHA256_DIGEST_SIZE;

    test_hmac[0] = a;
    test_hmac[1] = b;
    test_hmac[2] = c;
    test_hmac[3] = d;

    for (i = 0; i < times; ++i) {
#if defined(HAVE_FIPS) || defined(HAVE_CAVIUM)
        if (i == 1)
            continue; /* cavium can't handle short keys, fips not allowed */
#endif
#if defined(HAVE_INTEL_QA) || defined(HAVE_CAVIUM)
        if (i == 3)
            continue; /* QuickAssist can't handle empty HMAC */
#endif

        if (wc_HmacInit(&hmac, HEAP_HINT, devId) != 0)
            return -3800 - i;

        ret = wc_HmacSetKey(&hmac, WC_SHA256, (byte*)keys[i],
            (word32)XSTRLEN(keys[i]));
        if (ret != 0)
            return -3810 - i;
        if (test_hmac[i].input != NULL) {
            ret = wc_HmacUpdate(&hmac, (byte*)test_hmac[i].input,
                       (word32)test_hmac[i].inLen);
            if (ret != 0)
                return -3820 - i;
        }
        ret = wc_HmacFinal(&hmac, hash);
        if (ret != 0)
            return -3830 - i;

        if (XMEMCMP(hash, test_hmac[i].output, WC_SHA256_DIGEST_SIZE) != 0)
            return -3840 - i;

        wc_HmacFree(&hmac);
    }

#ifndef HAVE_FIPS
    if (wc_HmacSizeByType(WC_SHA256) != WC_SHA256_DIGEST_SIZE)
        return -3850;
    if (wc_HmacSizeByType(20) != BAD_FUNC_ARG)
        return -3851;
#endif
    if (wolfSSL_GetHmacMaxSize() != WC_MAX_DIGEST_SIZE)
        return -3852;

    return 0;
}
#endif


#if !defined(NO_HMAC) && defined(WOLFSSL_SHA384)
int hmac_sha384_test(void)
{
    Hmac hmac;
    byte hash[WC_SHA384_DIGEST_SIZE];

    const char* keys[]=
    {
        "\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b"
                                                                "\x0b\x0b\x0b",
        "Jefe",
        "\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA"
                                                                "\xAA\xAA\xAA",
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
    };

    testVector a, b, c, d;
    testVector test_hmac[4];

    int ret;
    int times = sizeof(test_hmac) / sizeof(testVector), i;

    a.input  = "Hi There";
    a.output = "\xaf\xd0\x39\x44\xd8\x48\x95\x62\x6b\x08\x25\xf4\xab\x46\x90"
               "\x7f\x15\xf9\xda\xdb\xe4\x10\x1e\xc6\x82\xaa\x03\x4c\x7c\xeb"
               "\xc5\x9c\xfa\xea\x9e\xa9\x07\x6e\xde\x7f\x4a\xf1\x52\xe8\xb2"
               "\xfa\x9c\xb6";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = WC_SHA384_DIGEST_SIZE;

    b.input  = "what do ya want for nothing?";
    b.output = "\xaf\x45\xd2\xe3\x76\x48\x40\x31\x61\x7f\x78\xd2\xb5\x8a\x6b"
               "\x1b\x9c\x7e\xf4\x64\xf5\xa0\x1b\x47\xe4\x2e\xc3\x73\x63\x22"
               "\x44\x5e\x8e\x22\x40\xca\x5e\x69\xe2\xc7\x8b\x32\x39\xec\xfa"
               "\xb2\x16\x49";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_SHA384_DIGEST_SIZE;

    c.input  = "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD";
    c.output = "\x88\x06\x26\x08\xd3\xe6\xad\x8a\x0a\xa2\xac\xe0\x14\xc8\xa8"
               "\x6f\x0a\xa6\x35\xd9\x47\xac\x9f\xeb\xe8\x3e\xf4\xe5\x59\x66"
               "\x14\x4b\x2a\x5a\xb3\x9d\xc1\x38\x14\xb9\x4e\x3a\xb6\xe1\x01"
               "\xa3\x4f\x27";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = WC_SHA384_DIGEST_SIZE;

    d.input  = "Big Key Input";
    d.output = "\xd2\x3d\x29\x6e\xf5\x1e\x23\x23\x49\x18\xb3\xbf\x4c\x38\x7b"
               "\x31\x21\x17\xbb\x09\x73\x27\xf8\x12\x9d\xe9\xc6\x5d\xf9\x54"
               "\xd6\x38\x5a\x68\x53\x14\xee\xe0\xa6\x4f\x36\x7e\xb2\xf3\x1a"
               "\x57\x41\x69";
    d.inLen  = XSTRLEN(d.input);
    d.outLen = WC_SHA384_DIGEST_SIZE;

    test_hmac[0] = a;
    test_hmac[1] = b;
    test_hmac[2] = c;
    test_hmac[3] = d;

    for (i = 0; i < times; ++i) {
#if defined(HAVE_FIPS)
        if (i == 1)
            continue; /* fips not allowed */
#endif

        if (wc_HmacInit(&hmac, HEAP_HINT, devId) != 0)
            return -3900;

        ret = wc_HmacSetKey(&hmac, WC_SHA384, (byte*)keys[i],
            (word32)XSTRLEN(keys[i]));
        if (ret != 0)
            return -3901;
        ret = wc_HmacUpdate(&hmac, (byte*)test_hmac[i].input,
                   (word32)test_hmac[i].inLen);
        if (ret != 0)
            return -3902;
        ret = wc_HmacFinal(&hmac, hash);
        if (ret != 0)
            return -3903;

        if (XMEMCMP(hash, test_hmac[i].output, WC_SHA384_DIGEST_SIZE) != 0)
            return -3904 - i;

        wc_HmacFree(&hmac);
    }

#ifndef HAVE_FIPS
    if (wc_HmacSizeByType(WC_SHA384) != WC_SHA384_DIGEST_SIZE)
        return -3914;
#endif

    return 0;
}
#endif


#if !defined(NO_HMAC) && defined(WOLFSSL_SHA512)
int hmac_sha512_test(void)
{
    Hmac hmac;
    byte hash[WC_SHA512_DIGEST_SIZE];

    const char* keys[]=
    {
        "\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b"
                                                                "\x0b\x0b\x0b",
        "Jefe",
        "\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA"
                                                                "\xAA\xAA\xAA",
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
    };

    testVector a, b, c, d;
    testVector test_hmac[4];

    int ret;
    int times = sizeof(test_hmac) / sizeof(testVector), i;

    a.input  = "Hi There";
    a.output = "\x87\xaa\x7c\xde\xa5\xef\x61\x9d\x4f\xf0\xb4\x24\x1a\x1d\x6c"
               "\xb0\x23\x79\xf4\xe2\xce\x4e\xc2\x78\x7a\xd0\xb3\x05\x45\xe1"
               "\x7c\xde\xda\xa8\x33\xb7\xd6\xb8\xa7\x02\x03\x8b\x27\x4e\xae"
               "\xa3\xf4\xe4\xbe\x9d\x91\x4e\xeb\x61\xf1\x70\x2e\x69\x6c\x20"
               "\x3a\x12\x68\x54";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = WC_SHA512_DIGEST_SIZE;

    b.input  = "what do ya want for nothing?";
    b.output = "\x16\x4b\x7a\x7b\xfc\xf8\x19\xe2\xe3\x95\xfb\xe7\x3b\x56\xe0"
               "\xa3\x87\xbd\x64\x22\x2e\x83\x1f\xd6\x10\x27\x0c\xd7\xea\x25"
               "\x05\x54\x97\x58\xbf\x75\xc0\x5a\x99\x4a\x6d\x03\x4f\x65\xf8"
               "\xf0\xe6\xfd\xca\xea\xb1\xa3\x4d\x4a\x6b\x4b\x63\x6e\x07\x0a"
               "\x38\xbc\xe7\x37";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_SHA512_DIGEST_SIZE;

    c.input  = "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD";
    c.output = "\xfa\x73\xb0\x08\x9d\x56\xa2\x84\xef\xb0\xf0\x75\x6c\x89\x0b"
               "\xe9\xb1\xb5\xdb\xdd\x8e\xe8\x1a\x36\x55\xf8\x3e\x33\xb2\x27"
               "\x9d\x39\xbf\x3e\x84\x82\x79\xa7\x22\xc8\x06\xb4\x85\xa4\x7e"
               "\x67\xc8\x07\xb9\x46\xa3\x37\xbe\xe8\x94\x26\x74\x27\x88\x59"
               "\xe1\x32\x92\xfb";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = WC_SHA512_DIGEST_SIZE;

    d.input  = "Big Key Input";
    d.output = "\x3f\xa9\xc9\xe1\xbd\xbb\x04\x55\x1f\xef\xcc\x92\x33\x08\xeb"
               "\xcf\xc1\x9a\x5b\x5b\xc0\x7c\x86\x84\xae\x8c\x40\xaf\xb1\x27"
               "\x87\x38\x92\x04\xa8\xed\xd7\xd7\x07\xa9\x85\xa0\xc2\xcd\x30"
               "\xc0\x56\x14\x49\xbc\x2f\x69\x15\x6a\x97\xd8\x79\x2f\xb3\x3b"
               "\x1e\x18\xfe\xfa";
    d.inLen  = XSTRLEN(d.input);
    d.outLen = WC_SHA512_DIGEST_SIZE;

    test_hmac[0] = a;
    test_hmac[1] = b;
    test_hmac[2] = c;
    test_hmac[3] = d;

    for (i = 0; i < times; ++i) {
#if defined(HAVE_FIPS)
        if (i == 1)
            continue; /* fips not allowed */
#endif

        if (wc_HmacInit(&hmac, HEAP_HINT, devId) != 0)
            return -4000;

        ret = wc_HmacSetKey(&hmac, WC_SHA512, (byte*)keys[i],
            (word32)XSTRLEN(keys[i]));
        if (ret != 0)
            return -4001;
        ret = wc_HmacUpdate(&hmac, (byte*)test_hmac[i].input,
                   (word32)test_hmac[i].inLen);
        if (ret != 0)
            return -4002;
        ret = wc_HmacFinal(&hmac, hash);
        if (ret != 0)
            return -4003;

        if (XMEMCMP(hash, test_hmac[i].output, WC_SHA512_DIGEST_SIZE) != 0)
            return -4004 - i;

        wc_HmacFree(&hmac);
    }

#ifndef HAVE_FIPS
    if (wc_HmacSizeByType(WC_SHA512) != WC_SHA512_DIGEST_SIZE)
        return -4014;
#endif

    return 0;
}
#endif


#if !defined(NO_HMAC) && defined(WOLFSSL_SHA3) && \
    !defined(WOLFSSL_NOSHA3_224) && !defined(WOLFSSL_NOSHA3_256) && \
    !defined(WOLFSSL_NOSHA3_384) && !defined(WOLFSSL_NOSHA3_512)
int hmac_sha3_test(void)
{
    Hmac hmac;
    byte hash[WC_SHA3_512_DIGEST_SIZE];

    const char* key[4] =
    {
        "Jefe",

        "\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b"
        "\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b",

        "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa"
        "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa",

        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
        "\x01\x02\x03\x04\x05\x06\x07\x08\x01\x02\x03\x04\x05\x06\x07\x08"
    };

    const char* input[4] =
    {
        "what do ya want for nothing?",

        "Hi There",

        "\xdd\xdd\xdd\xdd\xdd\xdd\xdd\xdd\xdd\xdd"
        "\xdd\xdd\xdd\xdd\xdd\xdd\xdd\xdd\xdd\xdd"
        "\xdd\xdd\xdd\xdd\xdd\xdd\xdd\xdd\xdd\xdd"
        "\xdd\xdd\xdd\xdd\xdd\xdd\xdd\xdd\xdd\xdd"
        "\xdd\xdd\xdd\xdd\xdd\xdd\xdd\xdd\xdd\xdd",

        "Big Key Input"
    };

    const int hashType[4] =
    {
        WC_SHA3_224, WC_SHA3_256, WC_SHA3_384, WC_SHA3_512
    };

    const int hashSz[4] =
    {
        WC_SHA3_224_DIGEST_SIZE, WC_SHA3_256_DIGEST_SIZE,
        WC_SHA3_384_DIGEST_SIZE, WC_SHA3_512_DIGEST_SIZE
    };

    const char* output[16] =
    {
        /* key = jefe, input = what do ya want for nothing? */
            /* HMAC-SHA3-224 */
            "\x7f\xdb\x8d\xd8\x8b\xd2\xf6\x0d\x1b\x79\x86\x34\xad\x38\x68\x11"
            "\xc2\xcf\xc8\x5b\xfa\xf5\xd5\x2b\xba\xce\x5e\x66",
            /* HMAC-SHA3-256 */
            "\xc7\xd4\x07\x2e\x78\x88\x77\xae\x35\x96\xbb\xb0\xda\x73\xb8\x87"
            "\xc9\x17\x1f\x93\x09\x5b\x29\x4a\xe8\x57\xfb\xe2\x64\x5e\x1b\xa5",
            /* HMAC-SHA3-384 */
            "\xf1\x10\x1f\x8c\xbf\x97\x66\xfd\x67\x64\xd2\xed\x61\x90\x3f\x21"
            "\xca\x9b\x18\xf5\x7c\xf3\xe1\xa2\x3c\xa1\x35\x08\xa9\x32\x43\xce"
            "\x48\xc0\x45\xdc\x00\x7f\x26\xa2\x1b\x3f\x5e\x0e\x9d\xf4\xc2\x0a",
            /* HMAC-SHA3-512 */
            "\x5a\x4b\xfe\xab\x61\x66\x42\x7c\x7a\x36\x47\xb7\x47\x29\x2b\x83"
            "\x84\x53\x7c\xdb\x89\xaf\xb3\xbf\x56\x65\xe4\xc5\xe7\x09\x35\x0b"
            "\x28\x7b\xae\xc9\x21\xfd\x7c\xa0\xee\x7a\x0c\x31\xd0\x22\xa9\x5e"
            "\x1f\xc9\x2b\xa9\xd7\x7d\xf8\x83\x96\x02\x75\xbe\xb4\xe6\x20\x24",

        /* key = 0b..., input = Hi There */
            /* HMAC-SHA3-224 */
            "\x3b\x16\x54\x6b\xbc\x7b\xe2\x70\x6a\x03\x1d\xca\xfd\x56\x37\x3d"
            "\x98\x84\x36\x76\x41\xd8\xc5\x9a\xf3\xc8\x60\xf7",
            /* HMAC-SHA3-256 */
            "\xba\x85\x19\x23\x10\xdf\xfa\x96\xe2\xa3\xa4\x0e\x69\x77\x43\x51"
            "\x14\x0b\xb7\x18\x5e\x12\x02\xcd\xcc\x91\x75\x89\xf9\x5e\x16\xbb",
            /* HMAC-SHA3-384 */
            "\x68\xd2\xdc\xf7\xfd\x4d\xdd\x0a\x22\x40\xc8\xa4\x37\x30\x5f\x61"
            "\xfb\x73\x34\xcf\xb5\xd0\x22\x6e\x1b\xc2\x7d\xc1\x0a\x2e\x72\x3a"
            "\x20\xd3\x70\xb4\x77\x43\x13\x0e\x26\xac\x7e\x3d\x53\x28\x86\xbd",
            /* HMAC-SHA3-512 */
            "\xeb\x3f\xbd\x4b\x2e\xaa\xb8\xf5\xc5\x04\xbd\x3a\x41\x46\x5a\xac"
            "\xec\x15\x77\x0a\x7c\xab\xac\x53\x1e\x48\x2f\x86\x0b\x5e\xc7\xba"
            "\x47\xcc\xb2\xc6\xf2\xaf\xce\x8f\x88\xd2\x2b\x6d\xc6\x13\x80\xf2"
            "\x3a\x66\x8f\xd3\x88\x8b\xb8\x05\x37\xc0\xa0\xb8\x64\x07\x68\x9e",

        /* key = aa..., output = dd... */
            /* HMAC-SHA3-224 */
            "\x67\x6c\xfc\x7d\x16\x15\x36\x38\x78\x03\x90\x69\x2b\xe1\x42\xd2"
            "\xdf\x7c\xe9\x24\xb9\x09\xc0\xc0\x8d\xbf\xdc\x1a",
            /* HMAC-SHA3-256 */
            "\x84\xec\x79\x12\x4a\x27\x10\x78\x65\xce\xdd\x8b\xd8\x2d\xa9\x96"
            "\x5e\x5e\xd8\xc3\x7b\x0a\xc9\x80\x05\xa7\xf3\x9e\xd5\x8a\x42\x07",
            /* HMAC-SHA3-384 */
            "\x27\x5c\xd0\xe6\x61\xbb\x8b\x15\x1c\x64\xd2\x88\xf1\xf7\x82\xfb"
            "\x91\xa8\xab\xd5\x68\x58\xd7\x2b\xab\xb2\xd4\x76\xf0\x45\x83\x73"
            "\xb4\x1b\x6a\xb5\xbf\x17\x4b\xec\x42\x2e\x53\xfc\x31\x35\xac\x6e",
            /* HMAC-SHA3-512 */
            "\x30\x9e\x99\xf9\xec\x07\x5e\xc6\xc6\xd4\x75\xed\xa1\x18\x06\x87"
            "\xfc\xf1\x53\x11\x95\x80\x2a\x99\xb5\x67\x74\x49\xa8\x62\x51\x82"
            "\x85\x1c\xb3\x32\xaf\xb6\xa8\x9c\x41\x13\x25\xfb\xcb\xcd\x42\xaf"
            "\xcb\x7b\x6e\x5a\xab\x7e\xa4\x2c\x66\x0f\x97\xfd\x85\x84\xbf\x03",

        /* key = big key, input = Big Key Input */
            /* HMAC-SHA3-224 */
            "\x29\xe0\x5e\x46\xc4\xa4\x5e\x46\x74\xbf\xd7\x2d\x1a\xd8\x66\xdb"
            "\x2d\x0d\x10\x4e\x2b\xfa\xad\x53\x7d\x15\x69\x8b",
            /* HMAC-SHA3-256 */
            "\xb5\x5b\x8d\x64\xb6\x9c\x21\xd0\xbf\x20\x5c\xa2\xf7\xb9\xb1\x4e"
            "\x88\x21\x61\x2c\x66\xc3\x91\xae\x6c\x95\x16\x85\x83\xe6\xf4\x9b",
            /* HMAC-SHA3-384 */
            "\xaa\x91\xb3\xa6\x2f\x56\xa1\xbe\x8c\x3e\x74\x38\xdb\x58\xd9\xd3"
            "\x34\xde\xa0\x60\x6d\x8d\x46\xe0\xec\xa9\xf6\x06\x35\x14\xe6\xed"
            "\x83\xe6\x7c\x77\x24\x6c\x11\xb5\x90\x82\xb5\x75\xda\x7b\x83\x2d",
            /* HMAC-SHA3-512 */
            "\x1c\xc3\xa9\x24\x4a\x4a\x3f\xbd\xc7\x20\x00\x16\x9b\x79\x47\x03"
            "\x78\x75\x2c\xb5\xf1\x2e\x62\x7c\xbe\xef\x4e\x8f\x0b\x11\x2b\x32"
            "\xa0\xee\xc9\xd0\x4d\x64\x64\x0b\x37\xf4\xdd\x66\xf7\x8b\xb3\xad"
            "\x52\x52\x6b\x65\x12\xde\x0d\x7c\xc0\x8b\x60\x01\x6c\x37\xd7\xa8"

    };

    int i = 0, iMax = sizeof(input) / sizeof(input[0]),
        j, jMax = sizeof(hashType) / sizeof(hashType[0]),
        ret;

#ifdef HAVE_FIPS
    /* FIPS requires a minimum length for HMAC keys, and "Jefe" is too
     * short. Skip it in FIPS builds. */
    i = 1;
#endif
    for (; i < iMax; i++) {
        for (j = 0; j < jMax; j++) {
            if (wc_HmacInit(&hmac, HEAP_HINT, devId) != 0)
                return -4100;

            ret = wc_HmacSetKey(&hmac, hashType[j], (byte*)key[i],
                                                       (word32)XSTRLEN(key[i]));
            if (ret != 0)
                return -4101;
            ret = wc_HmacUpdate(&hmac, (byte*)input[i],
                                                     (word32)XSTRLEN(input[i]));
            if (ret != 0)
                return -4102;
            ret = wc_HmacFinal(&hmac, hash);
            if (ret != 0)
                return -4103;
            if (XMEMCMP(hash, output[(i*jMax) + j], hashSz[j]) != 0)
                return -4104;

            wc_HmacFree(&hmac);

            if (i > 0)
                continue;

        #ifndef HAVE_FIPS
            ret = wc_HmacSizeByType(hashType[j]);
            if (ret != hashSz[j])
                return -4105;
        #endif
        }
    }

    return 0;
}
#endif


#ifndef NO_RC4
int arc4_test(void)
{
    byte cipher[16];
    byte plain[16];

    const char* keys[] =
    {
        "\x01\x23\x45\x67\x89\xab\xcd\xef",
        "\x01\x23\x45\x67\x89\xab\xcd\xef",
        "\x00\x00\x00\x00\x00\x00\x00\x00",
        "\xef\x01\x23\x45"
    };

    testVector a, b, c, d;
    testVector test_arc4[4];

    int times = sizeof(test_arc4) / sizeof(testVector), i;

    a.input  = "\x01\x23\x45\x67\x89\xab\xcd\xef";
    a.output = "\x75\xb7\x87\x80\x99\xe0\xc5\x96";
    a.inLen  = 8;
    a.outLen = 8;

    b.input  = "\x00\x00\x00\x00\x00\x00\x00\x00";
    b.output = "\x74\x94\xc2\xe7\x10\x4b\x08\x79";
    b.inLen  = 8;
    b.outLen = 8;

    c.input  = "\x00\x00\x00\x00\x00\x00\x00\x00";
    c.output = "\xde\x18\x89\x41\xa3\x37\x5d\x3a";
    c.inLen  = 8;
    c.outLen = 8;

    d.input  = "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00";
    d.output = "\xd6\xa1\x41\xa7\xec\x3c\x38\xdf\xbd\x61";
    d.inLen  = 10;
    d.outLen = 10;

    test_arc4[0] = a;
    test_arc4[1] = b;
    test_arc4[2] = c;
    test_arc4[3] = d;

    for (i = 0; i < times; ++i) {
        Arc4 enc;
        Arc4 dec;
        int  keylen = 8;  /* XSTRLEN with key 0x00 not good */
        if (i == 3)
            keylen = 4;

        if (wc_Arc4Init(&enc, HEAP_HINT, devId) != 0)
            return -4200;
        if (wc_Arc4Init(&dec, HEAP_HINT, devId) != 0)
            return -4201;

        wc_Arc4SetKey(&enc, (byte*)keys[i], keylen);
        wc_Arc4SetKey(&dec, (byte*)keys[i], keylen);

        wc_Arc4Process(&enc, cipher, (byte*)test_arc4[i].input,
                    (word32)test_arc4[i].outLen);
        wc_Arc4Process(&dec, plain,  cipher, (word32)test_arc4[i].outLen);

        if (XMEMCMP(plain, test_arc4[i].input, test_arc4[i].outLen))
            return -4202 - i;

        if (XMEMCMP(cipher, test_arc4[i].output, test_arc4[i].outLen))
            return -4212 - i;

        wc_Arc4Free(&enc);
        wc_Arc4Free(&dec);
    }

    return 0;
}
#endif


int hc128_test(void)
{
#ifdef HAVE_HC128
    byte cipher[16];
    byte plain[16];

    const char* keys[] =
    {
        "\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00",
        "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00",
        "\x00\x53\xA6\xF9\x4C\x9F\xF2\x45\x98\xEB\x3E\x91\xE4\x37\x8A\xDD",
        "\x0F\x62\xB5\x08\x5B\xAE\x01\x54\xA7\xFA\x4D\xA0\xF3\x46\x99\xEC"
    };

    const char* ivs[] =
    {
        "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00",
        "\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00",
        "\x0D\x74\xDB\x42\xA9\x10\x77\xDE\x45\xAC\x13\x7A\xE1\x48\xAF\x16",
        "\x28\x8F\xF6\x5D\xC4\x2B\x92\xF9\x60\xC7\x2E\x95\xFC\x63\xCA\x31"
    };


    testVector a, b, c, d;
    testVector test_hc128[4];

    int times = sizeof(test_hc128) / sizeof(testVector), i;

    a.input  = "\x00\x00\x00\x00\x00\x00\x00\x00";
    a.output = "\x37\x86\x02\xB9\x8F\x32\xA7\x48";
    a.inLen  = 8;
    a.outLen = 8;

    b.input  = "\x00\x00\x00\x00\x00\x00\x00\x00";
    b.output = "\x33\x7F\x86\x11\xC6\xED\x61\x5F";
    b.inLen  = 8;
    b.outLen = 8;

    c.input  = "\x00\x00\x00\x00\x00\x00\x00\x00";
    c.output = "\x2E\x1E\xD1\x2A\x85\x51\xC0\x5A";
    c.inLen  = 8;
    c.outLen = 8;

    d.input  = "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00";
    d.output = "\x1C\xD8\xAE\xDD\xFE\x52\xE2\x17\xE8\x35\xD0\xB7\xE8\x4E\x29";
    d.inLen  = 15;
    d.outLen = 15;

    test_hc128[0] = a;
    test_hc128[1] = b;
    test_hc128[2] = c;
    test_hc128[3] = d;

    for (i = 0; i < times; ++i) {
        HC128 enc;
        HC128 dec;

        /* align keys/ivs in plain/cipher buffers */
        XMEMCPY(plain,  keys[i], 16);
        XMEMCPY(cipher, ivs[i],  16);

        wc_Hc128_SetKey(&enc, plain, cipher);
        wc_Hc128_SetKey(&dec, plain, cipher);

        /* align input */
        XMEMCPY(plain, test_hc128[i].input, test_hc128[i].outLen);
        if (wc_Hc128_Process(&enc, cipher, plain,
                                           (word32)test_hc128[i].outLen) != 0) {
            return -4300;
        }
        if (wc_Hc128_Process(&dec, plain, cipher,
                                           (word32)test_hc128[i].outLen) != 0) {
            return -4301;
        }

        if (XMEMCMP(plain, test_hc128[i].input, test_hc128[i].outLen))
            return -4302 - i;

        if (XMEMCMP(cipher, test_hc128[i].output, test_hc128[i].outLen))
            return -4312 - i;
    }

#endif /* HAVE_HC128 */
    return 0;
}


#ifndef NO_RABBIT
int rabbit_test(void)
{
    byte cipher[16];
    byte plain[16];

    const char* keys[] =
    {
        "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00",
        "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00",
        "\xAC\xC3\x51\xDC\xF1\x62\xFC\x3B\xFE\x36\x3D\x2E\x29\x13\x28\x91"
    };

    const char* ivs[] =
    {
        "\x00\x00\x00\x00\x00\x00\x00\x00",
        "\x59\x7E\x26\xC1\x75\xF5\x73\xC3",
        0
    };

    testVector a, b, c;
    testVector test_rabbit[3];

    int times = sizeof(test_rabbit) / sizeof(testVector), i;

    a.input  = "\x00\x00\x00\x00\x00\x00\x00\x00";
    a.output = "\xED\xB7\x05\x67\x37\x5D\xCD\x7C";
    a.inLen  = 8;
    a.outLen = 8;

    b.input  = "\x00\x00\x00\x00\x00\x00\x00\x00";
    b.output = "\x6D\x7D\x01\x22\x92\xCC\xDC\xE0";
    b.inLen  = 8;
    b.outLen = 8;

    c.input  = "\x00\x00\x00\x00\x00\x00\x00\x00";
    c.output = "\x04\xCE\xCA\x7A\x1A\x86\x6E\x77";
    c.inLen  = 8;
    c.outLen = 8;

    test_rabbit[0] = a;
    test_rabbit[1] = b;
    test_rabbit[2] = c;

    for (i = 0; i < times; ++i) {
        Rabbit enc;
        Rabbit dec;
        byte*  iv;

        /* align keys/ivs in plain/cipher buffers */
        XMEMCPY(plain,  keys[i], 16);
        if (ivs[i]) {
            XMEMCPY(cipher, ivs[i],   8);
            iv = cipher;
        } else
            iv = NULL;
        wc_RabbitSetKey(&enc, plain, iv);
        wc_RabbitSetKey(&dec, plain, iv);

        /* align input */
        XMEMCPY(plain, test_rabbit[i].input, test_rabbit[i].outLen);
        wc_RabbitProcess(&enc, cipher, plain,  (word32)test_rabbit[i].outLen);
        wc_RabbitProcess(&dec, plain,  cipher, (word32)test_rabbit[i].outLen);

        if (XMEMCMP(plain, test_rabbit[i].input, test_rabbit[i].outLen))
            return -4400 - i;

        if (XMEMCMP(cipher, test_rabbit[i].output, test_rabbit[i].outLen))
            return -4410 - i;
    }

    return 0;
}
#endif /* NO_RABBIT */


#ifdef HAVE_CHACHA
int chacha_test(void)
{
    ChaCha enc;
    ChaCha dec;
    byte   cipher[128];
    byte   plain[128];
    byte   sliver[64];
    byte   input[] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
    word32 keySz = 32;
    int    ret = 0;
    int    i;
    int    times = 4;

    static const byte key1[] =
    {
         0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
         0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
         0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
         0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
    };

    static const byte key2[] =
    {
         0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
         0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
         0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
         0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x01
    };

    static const byte key3[] =
    {
         0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
         0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
         0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
         0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
    };

    /* 128 bit key */
    static const byte key4[] =
    {
         0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
         0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
    };


    const byte* keys[] = {key1, key2, key3, key4};

    static const byte ivs1[] = {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00};
    static const byte ivs2[] = {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00};
    static const byte ivs3[] = {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x01,0x00,0x00,0x00,0x00};
    static const byte ivs4[] = {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00};


    const byte* ivs[] = {ivs1, ivs2, ivs3, ivs4};

#ifndef BENCH_EMBEDDED
    static const byte cipher_big_result[] = {
        0x06, 0xa6, 0x5d, 0x31, 0x21, 0x6c, 0xdb, 0x37, 0x48, 0x7c, 0x01, 0x9d,
        0x72, 0xdf, 0x0a, 0x5b, 0x64, 0x74, 0x20, 0xba, 0x9e, 0xe0, 0x26, 0x7a,
        0xbf, 0xdf, 0x83, 0x34, 0x3b, 0x4f, 0x94, 0x3f, 0x37, 0x89, 0xaf, 0x00,
        0xdf, 0x0f, 0x2e, 0x75, 0x16, 0x41, 0xf6, 0x7a, 0x86, 0x94, 0x9d, 0x32,
        0x56, 0xf0, 0x79, 0x71, 0x68, 0x6f, 0xa6, 0x6b, 0xc6, 0x59, 0x49, 0xf6,
        0x10, 0x34, 0x03, 0x03, 0x16, 0x53, 0x9a, 0x98, 0x2a, 0x46, 0xde, 0x17,
        0x06, 0x65, 0x70, 0xca, 0x0a, 0x1f, 0xab, 0x80, 0x26, 0x96, 0x3f, 0x3e,
        0x7a, 0x3c, 0xa8, 0x87, 0xbb, 0x65, 0xdd, 0x5e, 0x07, 0x7b, 0x34, 0xe0,
        0x56, 0xda, 0x32, 0x13, 0x30, 0xc9, 0x0c, 0xd7, 0xba, 0xe4, 0x1f, 0xa6,
        0x91, 0x4f, 0x72, 0x9f, 0xd9, 0x5c, 0x62, 0x7d, 0xa6, 0xc2, 0xbc, 0x87,
        0xae, 0x64, 0x11, 0x94, 0x3b, 0xbc, 0x6c, 0x23, 0xbd, 0x7d, 0x00, 0xb4,
        0x99, 0xf2, 0x68, 0xb5, 0x59, 0x70, 0x93, 0xad, 0x69, 0xd0, 0xb1, 0x28,
        0x70, 0x92, 0xeb, 0xec, 0x39, 0x80, 0x82, 0xde, 0x44, 0xe2, 0x8a, 0x26,
        0xb3, 0xe9, 0x45, 0xcf, 0x83, 0x76, 0x9f, 0x6a, 0xa0, 0x46, 0x4a, 0x3d,
        0x26, 0x56, 0xaf, 0x49, 0x41, 0x26, 0x1b, 0x6a, 0x41, 0x37, 0x65, 0x91,
        0x72, 0xc4, 0xe7, 0x3c, 0x17, 0x31, 0xae, 0x2e, 0x2b, 0x31, 0x45, 0xe4,
        0x93, 0xd3, 0x10, 0xaa, 0xc5, 0x62, 0xd5, 0x11, 0x4b, 0x57, 0x1d, 0xad,
        0x48, 0x06, 0xd0, 0x0d, 0x98, 0xa5, 0xc6, 0x5b, 0xd0, 0x9e, 0x22, 0xc0,
        0x00, 0x32, 0x5a, 0xf5, 0x1c, 0x89, 0x6d, 0x54, 0x97, 0x55, 0x6b, 0x46,
        0xc5, 0xc7, 0xc4, 0x48, 0x9c, 0xbf, 0x47, 0xdc, 0x03, 0xc4, 0x1b, 0xcb,
        0x65, 0xa6, 0x91, 0x9d, 0x6d, 0xf1, 0xb0, 0x7a, 0x4d, 0x3b, 0x03, 0x95,
        0xf4, 0x8b, 0x0b, 0xae, 0x39, 0xff, 0x3f, 0xf6, 0xc0, 0x14, 0x18, 0x8a,
        0xe5, 0x19, 0xbd, 0xc1, 0xb4, 0x05, 0x4e, 0x29, 0x2f, 0x0b, 0x33, 0x76,
        0x28, 0x16, 0xa4, 0xa6, 0x93, 0x04, 0xb5, 0x55, 0x6b, 0x89, 0x3d, 0xa5,
        0x0f, 0xd3, 0xad, 0xfa, 0xd9, 0xfd, 0x05, 0x5d, 0x48, 0x94, 0x25, 0x5a,
        0x2c, 0x9a, 0x94, 0x80, 0xb0, 0xe7, 0xcb, 0x4d, 0x77, 0xbf, 0xca, 0xd8,
        0x55, 0x48, 0xbd, 0x66, 0xb1, 0x85, 0x81, 0xb1, 0x37, 0x79, 0xab, 0x52,
        0x08, 0x14, 0x12, 0xac, 0xcd, 0x45, 0x4d, 0x53, 0x6b, 0xca, 0x96, 0xc7,
        0x3b, 0x2f, 0x73, 0xb1, 0x5a, 0x23, 0xbd, 0x65, 0xd5, 0xea, 0x17, 0xb3,
        0xdc, 0xa1, 0x17, 0x1b, 0x2d, 0xb3, 0x9c, 0xd0, 0xdb, 0x41, 0x77, 0xef,
        0x93, 0x20, 0x52, 0x3e, 0x9d, 0xf5, 0xbf, 0x33, 0xf7, 0x52, 0xc1, 0x90,
        0xa0, 0x15, 0x17, 0xce, 0xf7, 0xf7, 0xd0, 0x3a, 0x3b, 0xd1, 0x72, 0x56,
        0x31, 0x81, 0xae, 0x60, 0xab, 0x40, 0xc1, 0xd1, 0x28, 0x77, 0x53, 0xac,
        0x9f, 0x11, 0x0a, 0x88, 0x36, 0x4b, 0xda, 0x57, 0xa7, 0x28, 0x5c, 0x85,
        0xd3, 0x85, 0x9b, 0x79, 0xad, 0x05, 0x1c, 0x37, 0x14, 0x5e, 0x0d, 0xd0,
        0x23, 0x03, 0x42, 0x1d, 0x48, 0x5d, 0xc5, 0x3c, 0x5a, 0x08, 0xa9, 0x0d,
        0x6e, 0x82, 0x7c, 0x2e, 0x3c, 0x41, 0xcc, 0x96, 0x8e, 0xad, 0xee, 0x2a,
        0x61, 0x0b, 0x16, 0x0f, 0xa9, 0x24, 0x40, 0x85, 0xbc, 0x9f, 0x28, 0x8d,
        0xe6, 0x68, 0x4d, 0x8f, 0x30, 0x48, 0xd9, 0x73, 0x73, 0x6c, 0x9a, 0x7f,
        0x67, 0xf7, 0xde, 0x4c, 0x0a, 0x8b, 0xe4, 0xb3, 0x08, 0x2a, 0x52, 0xda,
        0x54, 0xee, 0xcd, 0xb5, 0x62, 0x4a, 0x26, 0x20, 0xfb, 0x40, 0xbb, 0x39,
        0x3a, 0x0f, 0x09, 0xe8, 0x00, 0xd1, 0x24, 0x97, 0x60, 0xe9, 0x83, 0x83,
        0xfe, 0x9f, 0x9c, 0x15, 0xcf, 0x69, 0x03, 0x9f, 0x03, 0xe1, 0xe8, 0x6e,
        0xbd, 0x87, 0x58, 0x68, 0xee, 0xec, 0xd8, 0x29, 0x46, 0x23, 0x49, 0x92,
        0x72, 0x95, 0x5b, 0x49, 0xca, 0xe0, 0x45, 0x59, 0xb2, 0xca, 0xf4, 0xfc,
        0xb7, 0x59, 0x37, 0x49, 0x28, 0xbc, 0xf3, 0xd7, 0x61, 0xbc, 0x4b, 0xf3,
        0xa9, 0x4b, 0x2f, 0x05, 0xa8, 0x01, 0xa5, 0xdc, 0x00, 0x6e, 0x01, 0xb6,
        0x45, 0x3c, 0xd5, 0x49, 0x7d, 0x5c, 0x25, 0xe8, 0x31, 0x87, 0xb2, 0xb9,
        0xbf, 0xb3, 0x01, 0x62, 0x0c, 0xd0, 0x48, 0x77, 0xa2, 0x34, 0x0f, 0x16,
        0x22, 0x28, 0xee, 0x54, 0x08, 0x93, 0x3b, 0xe4, 0xde, 0x7e, 0x63, 0xf7,
        0x97, 0x16, 0x5d, 0x71, 0x58, 0xc2, 0x2e, 0xf2, 0x36, 0xa6, 0x12, 0x65,
        0x94, 0x17, 0xac, 0x66, 0x23, 0x7e, 0xc6, 0x72, 0x79, 0x24, 0xce, 0x8f,
        0x55, 0x19, 0x97, 0x44, 0xfc, 0x55, 0xec, 0x85, 0x26, 0x27, 0xdb, 0x38,
        0xb1, 0x42, 0x0a, 0xdd, 0x05, 0x99, 0x28, 0xeb, 0x03, 0x6c, 0x9a, 0xe9,
        0x17, 0xf6, 0x2c, 0xb0, 0xfe, 0xe7, 0xa4, 0xa7, 0x31, 0xda, 0x4d, 0xb0,
        0x29, 0xdb, 0xdd, 0x8d, 0x12, 0x13, 0x9c, 0xb4, 0xcc, 0x83, 0x97, 0xfb,
        0x1a, 0xdc, 0x08, 0xd6, 0x30, 0x62, 0xe8, 0xeb, 0x8b, 0x61, 0xcb, 0x1d,
        0x06, 0xe3, 0xa5, 0x4d, 0x35, 0xdb, 0x59, 0xa8, 0x2d, 0x87, 0x27, 0x44,
        0x6f, 0xc0, 0x38, 0x97, 0xe4, 0x85, 0x00, 0x02, 0x09, 0xf6, 0x69, 0x3a,
        0xcf, 0x08, 0x1b, 0x21, 0xbb, 0x79, 0xb1, 0xa1, 0x34, 0x09, 0xe0, 0x80,
        0xca, 0xb0, 0x78, 0x8a, 0x11, 0x97, 0xd4, 0x07, 0xbe, 0x1b, 0x6a, 0x5d,
        0xdb, 0xd6, 0x1f, 0x76, 0x6b, 0x16, 0xf0, 0x58, 0x84, 0x5f, 0x59, 0xce,
        0x62, 0x34, 0xc3, 0xdf, 0x94, 0xb8, 0x2f, 0x84, 0x68, 0xf0, 0xb8, 0x51,
        0xd9, 0x6d, 0x8e, 0x4a, 0x1d, 0xe6, 0x5c, 0xd8, 0x86, 0x25, 0xe3, 0x24,
        0xfd, 0x21, 0x61, 0x13, 0x48, 0x3e, 0xf6, 0x7d, 0xa6, 0x71, 0x9b, 0xd2,
        0x6e, 0xe6, 0xd2, 0x08, 0x94, 0x62, 0x6c, 0x98, 0xfe, 0x2f, 0x9c, 0x88,
        0x7e, 0x78, 0x15, 0x02, 0x00, 0xf0, 0xba, 0x24, 0x91, 0xf2, 0xdc, 0x47,
        0x51, 0x4d, 0x15, 0x5e, 0x91, 0x5f, 0x57, 0x5b, 0x1d, 0x35, 0x24, 0x45,
        0x75, 0x9b, 0x88, 0x75, 0xf1, 0x2f, 0x85, 0xe7, 0x89, 0xd1, 0x01, 0xb4,
        0xc8, 0x18, 0xb7, 0x97, 0xef, 0x4b, 0x90, 0xf4, 0xbf, 0x10, 0x27, 0x3c,
        0x60, 0xff, 0xc4, 0x94, 0x20, 0x2f, 0x93, 0x4b, 0x4d, 0xe3, 0x80, 0xf7,
        0x2c, 0x71, 0xd9, 0xe3, 0x68, 0xb4, 0x77, 0x2b, 0xc7, 0x0d, 0x39, 0x92,
        0xef, 0x91, 0x0d, 0xb2, 0x11, 0x50, 0x0e, 0xe8, 0xad, 0x3b, 0xf6, 0xb5,
        0xc6, 0x14, 0x4d, 0x33, 0x53, 0xa7, 0x60, 0x15, 0xc7, 0x27, 0x51, 0xdc,
        0x54, 0x29, 0xa7, 0x0d, 0x6a, 0x7b, 0x72, 0x13, 0xad, 0x7d, 0x41, 0x19,
        0x4e, 0x42, 0x49, 0xcc, 0x42, 0xe4, 0xbd, 0x99, 0x13, 0xd9, 0x7f, 0xf3,
        0x38, 0xa4, 0xb6, 0x33, 0xed, 0x07, 0x48, 0x7e, 0x8e, 0x82, 0xfe, 0x3a,
        0x9d, 0x75, 0x93, 0xba, 0x25, 0x4e, 0x37, 0x3c, 0x0c, 0xd5, 0x69, 0xa9,
        0x2d, 0x9e, 0xfd, 0xe8, 0xbb, 0xf5, 0x0c, 0xe2, 0x86, 0xb9, 0x5e, 0x6f,
        0x28, 0xe4, 0x19, 0xb3, 0x0b, 0xa4, 0x86, 0xd7, 0x24, 0xd0, 0xb8, 0x89,
        0x7b, 0x76, 0xec, 0x05, 0x10, 0x5b, 0x68, 0xe9, 0x58, 0x66, 0xa3, 0xc5,
        0xb6, 0x63, 0x20, 0x0e, 0x0e, 0xea, 0x3d, 0x61, 0x5e, 0xda, 0x3d, 0x3c,
        0xf9, 0xfd, 0xed, 0xa9, 0xdb, 0x52, 0x94, 0x8a, 0x00, 0xca, 0x3c, 0x8d,
        0x66, 0x8f, 0xb0, 0xf0, 0x5a, 0xca, 0x3f, 0x63, 0x71, 0xbf, 0xca, 0x99,
        0x37, 0x9b, 0x75, 0x97, 0x89, 0x10, 0x6e, 0xcf, 0xf2, 0xf5, 0xe3, 0xd5,
        0x45, 0x9b, 0xad, 0x10, 0x71, 0x6c, 0x5f, 0x6f, 0x7f, 0x22, 0x77, 0x18,
        0x2f, 0xf9, 0x99, 0xc5, 0x69, 0x58, 0x03, 0x12, 0x86, 0x82, 0x3e, 0xbf,
        0xc2, 0x12, 0x35, 0x43, 0xa3, 0xd9, 0x18, 0x4f, 0x41, 0x11, 0x6b, 0xf3,
        0x67, 0xaf, 0x3d, 0x78, 0xe4, 0x22, 0x2d, 0xb3, 0x48, 0x43, 0x31, 0x1d,
        0xef, 0xa8, 0xba, 0x49, 0x8e, 0xa9, 0xa7, 0xb6, 0x18, 0x77, 0x84, 0xca,
        0xbd, 0xa2, 0x02, 0x1b, 0x6a, 0xf8, 0x5f, 0xda, 0xff, 0xcf, 0x01, 0x6a,
        0x86, 0x69, 0xa9, 0xe9, 0xcb, 0x60, 0x1e, 0x15, 0xdc, 0x8f, 0x5d, 0x39,
        0xb5, 0xce, 0x55, 0x5f, 0x47, 0x97, 0xb1, 0x19, 0x6e, 0x21, 0xd6, 0x13,
        0x39, 0xb2, 0x24, 0xe0, 0x62, 0x82, 0x9f, 0xed, 0x12, 0x81, 0xed, 0xee,
        0xab, 0xd0, 0x2f, 0x19, 0x89, 0x3f, 0x57, 0x2e, 0xc2, 0xe2, 0x67, 0xe8,
        0xae, 0x03, 0x56, 0xba, 0xd4, 0xd0, 0xa4, 0x89, 0x03, 0x06, 0x5b, 0xcc,
        0xf2, 0x22, 0xb8, 0x0e, 0x76, 0x79, 0x4a, 0x42, 0x1d, 0x37, 0x51, 0x5a,
        0xaa, 0x46, 0x6c, 0x2a, 0xdd, 0x66, 0xfe, 0xc6, 0x68, 0xc3, 0x38, 0xa2,
        0xae, 0x5b, 0x98, 0x24, 0x5d, 0x43, 0x05, 0x82, 0x38, 0x12, 0xd3, 0xd1,
        0x75, 0x2d, 0x4f, 0x61, 0xbd, 0xb9, 0x10, 0x87, 0x44, 0x2a, 0x78, 0x07,
        0xff, 0xf4, 0x0f, 0xa1, 0xf3, 0x68, 0x9f, 0xbe, 0xae, 0xa2, 0x91, 0xf0,
        0xc7, 0x55, 0x7a, 0x52, 0xd5, 0xa3, 0x8d, 0x6f, 0xe4, 0x90, 0x5c, 0xf3,
        0x5f, 0xce, 0x3d, 0x23, 0xf9, 0x8e, 0xae, 0x14, 0xfb, 0x82, 0x9a, 0xa3,
        0x04, 0x5f, 0xbf, 0xad, 0x3e, 0xf2, 0x97, 0x0a, 0x60, 0x40, 0x70, 0x19,
        0x72, 0xad, 0x66, 0xfb, 0x78, 0x1b, 0x84, 0x6c, 0x98, 0xbc, 0x8c, 0xf8,
        0x4f, 0xcb, 0xb5, 0xf6, 0xaf, 0x7a, 0xb7, 0x93, 0xef, 0x67, 0x48, 0x02,
        0x2c, 0xcb, 0xe6, 0x77, 0x0f, 0x7b, 0xc1, 0xee, 0xc5, 0xb6, 0x2d, 0x7e,
        0x62, 0xa0, 0xc0, 0xa7, 0xa5, 0x80, 0x31, 0x92, 0x50, 0xa1, 0x28, 0x22,
        0x95, 0x03, 0x17, 0xd1, 0x0f, 0xf6, 0x08, 0xe5, 0xec
    };
#define CHACHA_BIG_TEST_SIZE 1305
#ifndef WOLFSSL_SMALL_STACK
    byte   cipher_big[CHACHA_BIG_TEST_SIZE] = {0};
    byte   plain_big[CHACHA_BIG_TEST_SIZE] = {0};
    byte   input_big[CHACHA_BIG_TEST_SIZE] = {0};
#else
    byte*  cipher_big;
    byte*  plain_big;
    byte*  input_big;
#endif /* WOLFSSL_SMALL_STACK */
    int    block_size;
#endif /* BENCH_EMBEDDED */

    byte a[] = {0x76,0xb8,0xe0,0xad,0xa0,0xf1,0x3d,0x90};
    byte b[] = {0x45,0x40,0xf0,0x5a,0x9f,0x1f,0xb2,0x96};
    byte c[] = {0xde,0x9c,0xba,0x7b,0xf3,0xd6,0x9e,0xf5};
    byte d[] = {0x89,0x67,0x09,0x52,0x60,0x83,0x64,0xfd};

    byte* test_chacha[4];

    test_chacha[0] = a;
    test_chacha[1] = b;
    test_chacha[2] = c;
    test_chacha[3] = d;

#ifndef BENCH_EMBEDDED
#ifdef WOLFSSL_SMALL_STACK
    cipher_big = (byte*)XMALLOC(CHACHA_BIG_TEST_SIZE, NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (cipher_big == NULL) {
        return MEMORY_E;
    }
    plain_big = (byte*)XMALLOC(CHACHA_BIG_TEST_SIZE, NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (plain_big == NULL) {
        return MEMORY_E;
    }
    input_big = (byte*)XMALLOC(CHACHA_BIG_TEST_SIZE, NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (input_big == NULL) {
        return MEMORY_E;
    }
    XMEMSET(cipher_big, 0, CHACHA_BIG_TEST_SIZE);
    XMEMSET(plain_big, 0, CHACHA_BIG_TEST_SIZE);
    XMEMSET(input_big, 0, CHACHA_BIG_TEST_SIZE);
#endif /* WOLFSSL_SMALL_STACK */
#endif /* BENCH_EMBEDDED */

    for (i = 0; i < times; ++i) {
        if (i < 3) {
            keySz = 32;
        }
        else {
            keySz = 16;
        }

        XMEMCPY(plain, keys[i], keySz);
        XMEMSET(cipher, 0, 32);
        XMEMCPY(cipher + 4, ivs[i], 8);

        ret |= wc_Chacha_SetKey(&enc, keys[i], keySz);
        ret |= wc_Chacha_SetKey(&dec, keys[i], keySz);
        if (ret != 0)
            return ret;

        ret |= wc_Chacha_SetIV(&enc, cipher, 0);
        ret |= wc_Chacha_SetIV(&dec, cipher, 0);
        if (ret != 0)
            return ret;
        XMEMCPY(plain, input, 8);

        ret |= wc_Chacha_Process(&enc, cipher, plain,  (word32)8);
        ret |= wc_Chacha_Process(&dec, plain,  cipher, (word32)8);
        if (ret != 0)
            return ret;

        if (XMEMCMP(test_chacha[i], cipher, 8))
            return -4500 - i;

        if (XMEMCMP(plain, input, 8))
            return -4510 - i;
    }

    /* test of starting at a different counter
       encrypts all of the information and decrypts starting at 2nd chunk */
    XMEMSET(plain,  0, sizeof(plain));
    XMEMSET(sliver, 1, sizeof(sliver)); /* set as 1's to not match plain */
    XMEMSET(cipher, 0, sizeof(cipher));
    XMEMCPY(cipher + 4, ivs[0], 8);

    ret |= wc_Chacha_SetKey(&enc, keys[0], keySz);
    ret |= wc_Chacha_SetKey(&dec, keys[0], keySz);
    if (ret != 0)
        return ret;

    ret |= wc_Chacha_SetIV(&enc, cipher, 0);
    ret |= wc_Chacha_SetIV(&dec, cipher, 1);
    if (ret != 0)
        return ret;

    ret |= wc_Chacha_Process(&enc, cipher, plain,  sizeof(plain));
    ret |= wc_Chacha_Process(&dec, sliver,  cipher + 64, sizeof(sliver));
    if (ret != 0)
        return ret;

    if (XMEMCMP(plain + 64, sliver, 64))
        return -4520;

#ifndef BENCH_EMBEDDED
    /* test of encrypting more data */
    keySz = 32;

    ret |= wc_Chacha_SetKey(&enc, keys[0], keySz);
    ret |= wc_Chacha_SetKey(&dec, keys[0], keySz);
    if (ret != 0)
        return ret;

    ret |= wc_Chacha_SetIV(&enc, ivs[2], 0);
    ret |= wc_Chacha_SetIV(&dec, ivs[2], 0);
    if (ret != 0)
        return ret;

    ret |= wc_Chacha_Process(&enc, cipher_big, plain_big, CHACHA_BIG_TEST_SIZE);
    ret |= wc_Chacha_Process(&dec, plain_big,  cipher_big,
                                                          CHACHA_BIG_TEST_SIZE);
    if (ret != 0)
        return ret;

    if (XMEMCMP(plain_big, input_big, CHACHA_BIG_TEST_SIZE))
        return -4521;

    if (XMEMCMP(cipher_big, cipher_big_result, CHACHA_BIG_TEST_SIZE))
        return -4522;

    for (i = 0; i < 18; ++i) {
        /* this will test all paths */
        // block sizes: 1 2 3 4 7 8 15 16 31 32 63 64 127 128 255 256 511 512
        block_size = (2 << (i%9)) - (i<9?1:0);
        keySz = 32;

        ret |= wc_Chacha_SetKey(&enc, keys[0], keySz);
        ret |= wc_Chacha_SetKey(&dec, keys[0], keySz);
        if (ret != 0)
            return ret;

        ret |= wc_Chacha_SetIV(&enc, ivs[2], 0);
        ret |= wc_Chacha_SetIV(&dec, ivs[2], 0);
        if (ret != 0)
            return ret;

        ret |= wc_Chacha_Process(&enc, cipher_big, plain_big,  block_size);
        ret |= wc_Chacha_Process(&dec, plain_big,  cipher_big, block_size);
        if (ret != 0)
            return ret;

        if (XMEMCMP(plain_big, input_big, block_size))
            return -4523-i;

        if (XMEMCMP(cipher_big, cipher_big_result, block_size))
            return -4524-i;
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(cipher_big, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(plain_big, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(input_big, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif /* WOLFSSL_SMALL_STACK */
#endif /* BENCH_EMBEDDED */

    return 0;
}
#endif /* HAVE_CHACHA */


#ifdef HAVE_POLY1305
int poly1305_test(void)
{
    int      ret = 0;
    int      i;
    byte     tag[16];
    Poly1305 enc;

    static const byte msg1[] =
    {
        0x43,0x72,0x79,0x70,0x74,0x6f,0x67,0x72,
        0x61,0x70,0x68,0x69,0x63,0x20,0x46,0x6f,
        0x72,0x75,0x6d,0x20,0x52,0x65,0x73,0x65,
        0x61,0x72,0x63,0x68,0x20,0x47,0x72,0x6f,
        0x75,0x70
    };

    static const byte msg2[] =
    {
        0x48,0x65,0x6c,0x6c,0x6f,0x20,0x77,0x6f,0x72,
        0x6c,0x64,0x21
    };

    static const byte msg3[] =
    {
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
    };

    static const byte msg4[] =
    {
        0xd3,0x1a,0x8d,0x34,0x64,0x8e,0x60,0xdb,
        0x7b,0x86,0xaf,0xbc,0x53,0xef,0x7e,0xc2,
        0xa4,0xad,0xed,0x51,0x29,0x6e,0x08,0xfe,
        0xa9,0xe2,0xb5,0xa7,0x36,0xee,0x62,0xd6,
        0x3d,0xbe,0xa4,0x5e,0x8c,0xa9,0x67,0x12,
        0x82,0xfa,0xfb,0x69,0xda,0x92,0x72,0x8b,
        0x1a,0x71,0xde,0x0a,0x9e,0x06,0x0b,0x29,
        0x05,0xd6,0xa5,0xb6,0x7e,0xcd,0x3b,0x36,
        0x92,0xdd,0xbd,0x7f,0x2d,0x77,0x8b,0x8c,
        0x98,0x03,0xae,0xe3,0x28,0x09,0x1b,0x58,
        0xfa,0xb3,0x24,0xe4,0xfa,0xd6,0x75,0x94,
        0x55,0x85,0x80,0x8b,0x48,0x31,0xd7,0xbc,
        0x3f,0xf4,0xde,0xf0,0x8e,0x4b,0x7a,0x9d,
        0xe5,0x76,0xd2,0x65,0x86,0xce,0xc6,0x4b,
        0x61,0x16
    };

    static const byte msg5[] =
    {
        0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
        0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
    };

    static const byte msg6[] =
    {
        0xd3,0x1a,0x8d,0x34,0x64,0x8e,0x60,0xdb,
        0x7b,0x86,0xaf,0xbc,0x53,0xef,0x7e,0xc2,
        0xa4,0xad,0xed,0x51,0x29,0x6e,0x08,0xfe,
        0xa9,0xe2,0xb5,0xa7,0x36,0xee,0x62,0xd6,
        0x3d,0xbe,0xa4,0x5e,0x8c,0xa9,0x67,0x12,
        0x82,0xfa,0xfb,0x69,0xda,0x92,0x72,0x8b,
        0xfa,0xb3,0x24,0xe4,0xfa,0xd6,0x75,0x94,
        0x1a,0x71,0xde,0x0a,0x9e,0x06,0x0b,0x29,
        0xa9,0xe2,0xb5,0xa7,0x36,0xee,0x62,0xd6,
        0x3d,0xbe,0xa4,0x5e,0x8c,0xa9,0x67,0x12,
        0xfa,0xb3,0x24,0xe4,0xfa,0xd6,0x75,0x94,
        0x05,0xd6,0xa5,0xb6,0x7e,0xcd,0x3b,0x36,
        0x92,0xdd,0xbd,0x7f,0x2d,0x77,0x8b,0x8c,
        0x7b,0x86,0xaf,0xbc,0x53,0xef,0x7e,0xc2,
        0x98,0x03,0xae,0xe3,0x28,0x09,0x1b,0x58,
        0xfa,0xb3,0x24,0xe4,0xfa,0xd6,0x75,0x94,
        0x55,0x85,0x80,0x8b,0x48,0x31,0xd7,0xbc,
        0x3f,0xf4,0xde,0xf0,0x8e,0x4b,0x7a,0x9d,
        0xe5,0x76,0xd2,0x65,0x86,0xce,0xc6,0x4b,
        0x61,0x16
    };

    byte additional[] =
    {
        0x50,0x51,0x52,0x53,0xc0,0xc1,0xc2,0xc3,
        0xc4,0xc5,0xc6,0xc7
    };

    static const byte correct0[] =
    {
        0x01,0x03,0x80,0x8a,0xfb,0x0d,0xb2,0xfd,
        0x4a,0xbf,0xf6,0xaf,0x41,0x49,0xf5,0x1b
    };

    static const byte correct1[] =
    {
        0xa8,0x06,0x1d,0xc1,0x30,0x51,0x36,0xc6,
        0xc2,0x2b,0x8b,0xaf,0x0c,0x01,0x27,0xa9
    };

    static const byte correct2[] =
    {
        0xa6,0xf7,0x45,0x00,0x8f,0x81,0xc9,0x16,
        0xa2,0x0d,0xcc,0x74,0xee,0xf2,0xb2,0xf0
    };

    static const byte correct3[] =
    {
        0x49,0xec,0x78,0x09,0x0e,0x48,0x1e,0xc6,
        0xc2,0x6b,0x33,0xb9,0x1c,0xcc,0x03,0x07
    };

    static const byte correct4[] =
    {
        0x1a,0xe1,0x0b,0x59,0x4f,0x09,0xe2,0x6a,
        0x7e,0x90,0x2e,0xcb,0xd0,0x60,0x06,0x91
    };

    static const byte correct5[] =
    {
        0x03,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
    };

    static const byte correct6[] =
    {
        0xea,0x11,0x5c,0x4f,0xd0,0xc0,0x10,0xae,
        0xf7,0xdf,0xda,0x77,0xa2,0xe9,0xaf,0xca
    };

    static const byte key[] = {
        0x85,0xd6,0xbe,0x78,0x57,0x55,0x6d,0x33,
        0x7f,0x44,0x52,0xfe,0x42,0xd5,0x06,0xa8,
        0x01,0x03,0x80,0x8a,0xfb,0x0d,0xb2,0xfd,
        0x4a,0xbf,0xf6,0xaf,0x41,0x49,0xf5,0x1b
    };

    static const byte key2[] = {
        0x74,0x68,0x69,0x73,0x20,0x69,0x73,0x20,
        0x33,0x32,0x2d,0x62,0x79,0x74,0x65,0x20,
        0x6b,0x65,0x79,0x20,0x66,0x6f,0x72,0x20,
        0x50,0x6f,0x6c,0x79,0x31,0x33,0x30,0x35
    };

    static const byte key4[] = {
        0x7b,0xac,0x2b,0x25,0x2d,0xb4,0x47,0xaf,
        0x09,0xb6,0x7a,0x55,0xa4,0xe9,0x55,0x84,
        0x0a,0xe1,0xd6,0x73,0x10,0x75,0xd9,0xeb,
        0x2a,0x93,0x75,0x78,0x3e,0xd5,0x53,0xff
    };

    static const byte key5[] = {
        0x02,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
    };

    const byte* msgs[]  = {NULL, msg1, msg2, msg3, msg5, msg6};
    word32      szm[]   = {0, sizeof(msg1), sizeof(msg2),
                           sizeof(msg3), sizeof(msg5), sizeof(msg6)};
    const byte* keys[]  = {key, key, key2, key2, key5, key};
    const byte* tests[] = {correct0, correct1, correct2, correct3, correct5,
                           correct6};

    for (i = 0; i < 6; i++) {
        ret = wc_Poly1305SetKey(&enc, keys[i], 32);
        if (ret != 0)
            return -4600 - i;

        ret = wc_Poly1305Update(&enc, msgs[i], szm[i]);
        if (ret != 0)
            return -4610 - i;

        ret = wc_Poly1305Final(&enc, tag);
        if (ret != 0)
            return -4620 - i;

        if (XMEMCMP(tag, tests[i], sizeof(tag)))
            return -4630 - i;
    }

    /* Check TLS MAC function from 2.8.2 https://tools.ietf.org/html/rfc7539 */
    XMEMSET(tag, 0, sizeof(tag));
    ret = wc_Poly1305SetKey(&enc, key4, sizeof(key4));
    if (ret != 0)
        return -4640;

    ret = wc_Poly1305_MAC(&enc, additional, sizeof(additional),
                                   (byte*)msg4, sizeof(msg4), tag, sizeof(tag));
    if (ret != 0)
        return -4641;

    if (XMEMCMP(tag, correct4, sizeof(tag)))
        return -4642;

    /* Check fail of TLS MAC function if altering additional data */
    XMEMSET(tag, 0, sizeof(tag));
	additional[0]++;
    ret = wc_Poly1305_MAC(&enc, additional, sizeof(additional),
                                   (byte*)msg4, sizeof(msg4), tag, sizeof(tag));
    if (ret != 0)
        return -4643;

    if (XMEMCMP(tag, correct4, sizeof(tag)) == 0)
        return -4644;


    return 0;
}
#endif /* HAVE_POLY1305 */


#if defined(HAVE_CHACHA) && defined(HAVE_POLY1305)
int chacha20_poly1305_aead_test(void)
{
    /* Test #1 from Section 2.8.2 of draft-irtf-cfrg-chacha20-poly1305-10 */
    /* https://tools.ietf.org/html/draft-irtf-cfrg-chacha20-poly1305-10  */

    const byte key1[] = {
        0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87,
        0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d, 0x8e, 0x8f,
        0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97,
        0x98, 0x99, 0x9a, 0x9b, 0x9c, 0x9d, 0x9e, 0x9f
    };

    const byte plaintext1[] = {
        0x4c, 0x61, 0x64, 0x69, 0x65, 0x73, 0x20, 0x61,
        0x6e, 0x64, 0x20, 0x47, 0x65, 0x6e, 0x74, 0x6c,
        0x65, 0x6d, 0x65, 0x6e, 0x20, 0x6f, 0x66, 0x20,
        0x74, 0x68, 0x65, 0x20, 0x63, 0x6c, 0x61, 0x73,
        0x73, 0x20, 0x6f, 0x66, 0x20, 0x27, 0x39, 0x39,
        0x3a, 0x20, 0x49, 0x66, 0x20, 0x49, 0x20, 0x63,
        0x6f, 0x75, 0x6c, 0x64, 0x20, 0x6f, 0x66, 0x66,
        0x65, 0x72, 0x20, 0x79, 0x6f, 0x75, 0x20, 0x6f,
        0x6e, 0x6c, 0x79, 0x20, 0x6f, 0x6e, 0x65, 0x20,
        0x74, 0x69, 0x70, 0x20, 0x66, 0x6f, 0x72, 0x20,
        0x74, 0x68, 0x65, 0x20, 0x66, 0x75, 0x74, 0x75,
        0x72, 0x65, 0x2c, 0x20, 0x73, 0x75, 0x6e, 0x73,
        0x63, 0x72, 0x65, 0x65, 0x6e, 0x20, 0x77, 0x6f,
        0x75, 0x6c, 0x64, 0x20, 0x62, 0x65, 0x20, 0x69,
        0x74, 0x2e
    };

    const byte iv1[] = {
        0x07, 0x00, 0x00, 0x00, 0x40, 0x41, 0x42, 0x43,
        0x44, 0x45, 0x46, 0x47
    };

    const byte aad1[] = { /* additional data */
        0x50, 0x51, 0x52, 0x53, 0xc0, 0xc1, 0xc2, 0xc3,
        0xc4, 0xc5, 0xc6, 0xc7
    };

    const byte cipher1[] = { /* expected output from operation */
        0xd3, 0x1a, 0x8d, 0x34, 0x64, 0x8e, 0x60, 0xdb,
        0x7b, 0x86, 0xaf, 0xbc, 0x53, 0xef, 0x7e, 0xc2,
        0xa4, 0xad, 0xed, 0x51, 0x29, 0x6e, 0x08, 0xfe,
        0xa9, 0xe2, 0xb5, 0xa7, 0x36, 0xee, 0x62, 0xd6,
        0x3d, 0xbe, 0xa4, 0x5e, 0x8c, 0xa9, 0x67, 0x12,
        0x82, 0xfa, 0xfb, 0x69, 0xda, 0x92, 0x72, 0x8b,
        0x1a, 0x71, 0xde, 0x0a, 0x9e, 0x06, 0x0b, 0x29,
        0x05, 0xd6, 0xa5, 0xb6, 0x7e, 0xcd, 0x3b, 0x36,
        0x92, 0xdd, 0xbd, 0x7f, 0x2d, 0x77, 0x8b, 0x8c,
        0x98, 0x03, 0xae, 0xe3, 0x28, 0x09, 0x1b, 0x58,
        0xfa, 0xb3, 0x24, 0xe4, 0xfa, 0xd6, 0x75, 0x94,
        0x55, 0x85, 0x80, 0x8b, 0x48, 0x31, 0xd7, 0xbc,
        0x3f, 0xf4, 0xde, 0xf0, 0x8e, 0x4b, 0x7a, 0x9d,
        0xe5, 0x76, 0xd2, 0x65, 0x86, 0xce, 0xc6, 0x4b,
        0x61, 0x16
    };

    const byte authTag1[] = { /* expected output from operation */
        0x1a, 0xe1, 0x0b, 0x59, 0x4f, 0x09, 0xe2, 0x6a,
        0x7e, 0x90, 0x2e, 0xcb, 0xd0, 0x60, 0x06, 0x91
    };

    /* Test #2 from Appendix A.2 in draft-irtf-cfrg-chacha20-poly1305-10 */
    /* https://tools.ietf.org/html/draft-irtf-cfrg-chacha20-poly1305-10  */

    const byte key2[] = {
        0x1c, 0x92, 0x40, 0xa5, 0xeb, 0x55, 0xd3, 0x8a,
        0xf3, 0x33, 0x88, 0x86, 0x04, 0xf6, 0xb5, 0xf0,
        0x47, 0x39, 0x17, 0xc1, 0x40, 0x2b, 0x80, 0x09,
        0x9d, 0xca, 0x5c, 0xbc, 0x20, 0x70, 0x75, 0xc0
    };

    const byte plaintext2[] = {
        0x49, 0x6e, 0x74, 0x65, 0x72, 0x6e, 0x65, 0x74,
        0x2d, 0x44, 0x72, 0x61, 0x66, 0x74, 0x73, 0x20,
        0x61, 0x72, 0x65, 0x20, 0x64, 0x72, 0x61, 0x66,
        0x74, 0x20, 0x64, 0x6f, 0x63, 0x75, 0x6d, 0x65,
        0x6e, 0x74, 0x73, 0x20, 0x76, 0x61, 0x6c, 0x69,
        0x64, 0x20, 0x66, 0x6f, 0x72, 0x20, 0x61, 0x20,
        0x6d, 0x61, 0x78, 0x69, 0x6d, 0x75, 0x6d, 0x20,
        0x6f, 0x66, 0x20, 0x73, 0x69, 0x78, 0x20, 0x6d,
        0x6f, 0x6e, 0x74, 0x68, 0x73, 0x20, 0x61, 0x6e,
        0x64, 0x20, 0x6d, 0x61, 0x79, 0x20, 0x62, 0x65,
        0x20, 0x75, 0x70, 0x64, 0x61, 0x74, 0x65, 0x64,
        0x2c, 0x20, 0x72, 0x65, 0x70, 0x6c, 0x61, 0x63,
        0x65, 0x64, 0x2c, 0x20, 0x6f, 0x72, 0x20, 0x6f,
        0x62, 0x73, 0x6f, 0x6c, 0x65, 0x74, 0x65, 0x64,
        0x20, 0x62, 0x79, 0x20, 0x6f, 0x74, 0x68, 0x65,
        0x72, 0x20, 0x64, 0x6f, 0x63, 0x75, 0x6d, 0x65,
        0x6e, 0x74, 0x73, 0x20, 0x61, 0x74, 0x20, 0x61,
        0x6e, 0x79, 0x20, 0x74, 0x69, 0x6d, 0x65, 0x2e,
        0x20, 0x49, 0x74, 0x20, 0x69, 0x73, 0x20, 0x69,
        0x6e, 0x61, 0x70, 0x70, 0x72, 0x6f, 0x70, 0x72,
        0x69, 0x61, 0x74, 0x65, 0x20, 0x74, 0x6f, 0x20,
        0x75, 0x73, 0x65, 0x20, 0x49, 0x6e, 0x74, 0x65,
        0x72, 0x6e, 0x65, 0x74, 0x2d, 0x44, 0x72, 0x61,
        0x66, 0x74, 0x73, 0x20, 0x61, 0x73, 0x20, 0x72,
        0x65, 0x66, 0x65, 0x72, 0x65, 0x6e, 0x63, 0x65,
        0x20, 0x6d, 0x61, 0x74, 0x65, 0x72, 0x69, 0x61,
        0x6c, 0x20, 0x6f, 0x72, 0x20, 0x74, 0x6f, 0x20,
        0x63, 0x69, 0x74, 0x65, 0x20, 0x74, 0x68, 0x65,
        0x6d, 0x20, 0x6f, 0x74, 0x68, 0x65, 0x72, 0x20,
        0x74, 0x68, 0x61, 0x6e, 0x20, 0x61, 0x73, 0x20,
        0x2f, 0xe2, 0x80, 0x9c, 0x77, 0x6f, 0x72, 0x6b,
        0x20, 0x69, 0x6e, 0x20, 0x70, 0x72, 0x6f, 0x67,
        0x72, 0x65, 0x73, 0x73, 0x2e, 0x2f, 0xe2, 0x80,
        0x9d
    };

    const byte iv2[] = {
        0x00, 0x00, 0x00, 0x00, 0x01, 0x02, 0x03, 0x04,
        0x05, 0x06, 0x07, 0x08
    };

    const byte aad2[] = { /* additional data */
        0xf3, 0x33, 0x88, 0x86, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x4e, 0x91
    };

    const byte cipher2[] = { /* expected output from operation */
        0x64, 0xa0, 0x86, 0x15, 0x75, 0x86, 0x1a, 0xf4,
        0x60, 0xf0, 0x62, 0xc7, 0x9b, 0xe6, 0x43, 0xbd,
        0x5e, 0x80, 0x5c, 0xfd, 0x34, 0x5c, 0xf3, 0x89,
        0xf1, 0x08, 0x67, 0x0a, 0xc7, 0x6c, 0x8c, 0xb2,
        0x4c, 0x6c, 0xfc, 0x18, 0x75, 0x5d, 0x43, 0xee,
        0xa0, 0x9e, 0xe9, 0x4e, 0x38, 0x2d, 0x26, 0xb0,
        0xbd, 0xb7, 0xb7, 0x3c, 0x32, 0x1b, 0x01, 0x00,
        0xd4, 0xf0, 0x3b, 0x7f, 0x35, 0x58, 0x94, 0xcf,
        0x33, 0x2f, 0x83, 0x0e, 0x71, 0x0b, 0x97, 0xce,
        0x98, 0xc8, 0xa8, 0x4a, 0xbd, 0x0b, 0x94, 0x81,
        0x14, 0xad, 0x17, 0x6e, 0x00, 0x8d, 0x33, 0xbd,
        0x60, 0xf9, 0x82, 0xb1, 0xff, 0x37, 0xc8, 0x55,
        0x97, 0x97, 0xa0, 0x6e, 0xf4, 0xf0, 0xef, 0x61,
        0xc1, 0x86, 0x32, 0x4e, 0x2b, 0x35, 0x06, 0x38,
        0x36, 0x06, 0x90, 0x7b, 0x6a, 0x7c, 0x02, 0xb0,
        0xf9, 0xf6, 0x15, 0x7b, 0x53, 0xc8, 0x67, 0xe4,
        0xb9, 0x16, 0x6c, 0x76, 0x7b, 0x80, 0x4d, 0x46,
        0xa5, 0x9b, 0x52, 0x16, 0xcd, 0xe7, 0xa4, 0xe9,
        0x90, 0x40, 0xc5, 0xa4, 0x04, 0x33, 0x22, 0x5e,
        0xe2, 0x82, 0xa1, 0xb0, 0xa0, 0x6c, 0x52, 0x3e,
        0xaf, 0x45, 0x34, 0xd7, 0xf8, 0x3f, 0xa1, 0x15,
        0x5b, 0x00, 0x47, 0x71, 0x8c, 0xbc, 0x54, 0x6a,
        0x0d, 0x07, 0x2b, 0x04, 0xb3, 0x56, 0x4e, 0xea,
        0x1b, 0x42, 0x22, 0x73, 0xf5, 0x48, 0x27, 0x1a,
        0x0b, 0xb2, 0x31, 0x60, 0x53, 0xfa, 0x76, 0x99,
        0x19, 0x55, 0xeb, 0xd6, 0x31, 0x59, 0x43, 0x4e,
        0xce, 0xbb, 0x4e, 0x46, 0x6d, 0xae, 0x5a, 0x10,
        0x73, 0xa6, 0x72, 0x76, 0x27, 0x09, 0x7a, 0x10,
        0x49, 0xe6, 0x17, 0xd9, 0x1d, 0x36, 0x10, 0x94,
        0xfa, 0x68, 0xf0, 0xff, 0x77, 0x98, 0x71, 0x30,
        0x30, 0x5b, 0xea, 0xba, 0x2e, 0xda, 0x04, 0xdf,
        0x99, 0x7b, 0x71, 0x4d, 0x6c, 0x6f, 0x2c, 0x29,
        0xa6, 0xad, 0x5c, 0xb4, 0x02, 0x2b, 0x02, 0x70,
        0x9b
    };

    const byte authTag2[] = { /* expected output from operation */
        0xee, 0xad, 0x9d, 0x67, 0x89, 0x0c, 0xbb, 0x22,
        0x39, 0x23, 0x36, 0xfe, 0xa1, 0x85, 0x1f, 0x38
    };

    byte generatedCiphertext[265]; /* max plaintext2/cipher2 */
    byte generatedPlaintext[265];  /* max plaintext2/cipher2 */
    byte generatedAuthTag[CHACHA20_POLY1305_AEAD_AUTHTAG_SIZE];
    int err;

    ChaChaPoly_Aead aead;

#if !defined(USE_INTEL_CHACHA_SPEEDUP) && !defined(WOLFSSL_ARMASM)
    #define TEST_SMALL_CHACHA_CHUNKS 32
#else
    #define TEST_SMALL_CHACHA_CHUNKS 64
#endif
    #ifdef TEST_SMALL_CHACHA_CHUNKS
    word32 testLen;
    #endif

    XMEMSET(generatedCiphertext, 0, sizeof(generatedCiphertext));
    XMEMSET(generatedAuthTag, 0, sizeof(generatedAuthTag));
    XMEMSET(generatedPlaintext, 0, sizeof(generatedPlaintext));

    /* Parameter Validation testing */
    /* Encrypt */
    err = wc_ChaCha20Poly1305_Encrypt(NULL, iv1, aad1, sizeof(aad1), plaintext1,
            sizeof(plaintext1), generatedCiphertext, generatedAuthTag);
    if (err != BAD_FUNC_ARG)
        return -4700;
    err = wc_ChaCha20Poly1305_Encrypt(key1, NULL, aad1, sizeof(aad1),
            plaintext1, sizeof(plaintext1), generatedCiphertext,
            generatedAuthTag);
    if (err != BAD_FUNC_ARG)
        return -4701;
    err = wc_ChaCha20Poly1305_Encrypt(key1, iv1, aad1, sizeof(aad1), NULL,
            sizeof(plaintext1), generatedCiphertext, generatedAuthTag);
    if (err != BAD_FUNC_ARG)
        return -4702;
    err = wc_ChaCha20Poly1305_Encrypt(key1, iv1, aad1, sizeof(aad1), plaintext1,
            sizeof(plaintext1), NULL, generatedAuthTag);
    if (err != BAD_FUNC_ARG)
        return -4703;
    err = wc_ChaCha20Poly1305_Encrypt(key1, iv1, aad1, sizeof(aad1), plaintext1,
            sizeof(plaintext1), generatedCiphertext, NULL);
    if (err != BAD_FUNC_ARG)
        return -4704;
    err = wc_ChaCha20Poly1305_Encrypt(key1, iv1, aad1, sizeof(aad1), plaintext1,
            0, generatedCiphertext, generatedAuthTag);
    if (err != BAD_FUNC_ARG)
        return -4705;
    /* Decrypt */
    err = wc_ChaCha20Poly1305_Decrypt(NULL, iv2, aad2, sizeof(aad2), cipher2,
            sizeof(cipher2), authTag2, generatedPlaintext);
    if (err != BAD_FUNC_ARG)
        return -4706;
    err = wc_ChaCha20Poly1305_Decrypt(key2, NULL, aad2, sizeof(aad2), cipher2,
            sizeof(cipher2), authTag2, generatedPlaintext);
    if (err != BAD_FUNC_ARG)
        return -4707;
    err = wc_ChaCha20Poly1305_Decrypt(key2, iv2, aad2, sizeof(aad2), NULL,
            sizeof(cipher2), authTag2, generatedPlaintext);
    if (err != BAD_FUNC_ARG)
        return -4708;
    err = wc_ChaCha20Poly1305_Decrypt(key2, iv2, aad2, sizeof(aad2), cipher2,
            sizeof(cipher2), NULL, generatedPlaintext);
    if (err != BAD_FUNC_ARG)
        return -4709;
    err = wc_ChaCha20Poly1305_Decrypt(key2, iv2, aad2, sizeof(aad2), cipher2,
            sizeof(cipher2), authTag2, NULL);
    if (err != BAD_FUNC_ARG)
        return -4710;
    err = wc_ChaCha20Poly1305_Decrypt(key2, iv2, aad2, sizeof(aad2), cipher2,
            0, authTag2, generatedPlaintext);
    if (err != BAD_FUNC_ARG)
        return -4711;


    /* Test #1 */
    err = wc_ChaCha20Poly1305_Encrypt(key1, iv1,
                                       aad1, sizeof(aad1),
                                       plaintext1, sizeof(plaintext1),
                                       generatedCiphertext, generatedAuthTag);
    if (err) {
        return err;
    }

    /* -- Check the ciphertext and authtag */
    if (XMEMCMP(generatedCiphertext, cipher1, sizeof(cipher1))) {
        return -4712;
    }
    if (XMEMCMP(generatedAuthTag, authTag1, sizeof(authTag1))) {
        return -4713;
    }

    /* -- Verify decryption works */
    err = wc_ChaCha20Poly1305_Decrypt(key1, iv1,
                                       aad1, sizeof(aad1),
                                       cipher1, sizeof(cipher1),
                                       authTag1, generatedPlaintext);
    if (err) {
        return err;
    }
    if (XMEMCMP(generatedPlaintext, plaintext1, sizeof(plaintext1))) {
        return -4714;
    }


    XMEMSET(generatedCiphertext, 0, sizeof(generatedCiphertext));
    XMEMSET(generatedAuthTag, 0, sizeof(generatedAuthTag));
    XMEMSET(generatedPlaintext, 0, sizeof(generatedPlaintext));

    /* Test #2 */
    err = wc_ChaCha20Poly1305_Encrypt(key2, iv2,
                                       aad2, sizeof(aad2),
                                       plaintext2, sizeof(plaintext2),
                                       generatedCiphertext, generatedAuthTag);
    if (err) {
        return err;
    }

    /* -- Check the ciphertext and authtag */
    if (XMEMCMP(generatedCiphertext, cipher2, sizeof(cipher2))) {
        return -4715;
    }
    if (XMEMCMP(generatedAuthTag, authTag2, sizeof(authTag2))) {
        return -4716;
    }

    /* -- Verify decryption works */
    err = wc_ChaCha20Poly1305_Decrypt(key2, iv2,
                                      aad2, sizeof(aad2),
                                      cipher2, sizeof(cipher2),
                                      authTag2, generatedPlaintext);
    if (err) {
        return err;
    }

    if (XMEMCMP(generatedPlaintext, plaintext2, sizeof(plaintext2))) {
        return -4717;
    }


    /* AEAD init/update/final */
    err = wc_ChaCha20Poly1305_Init(NULL, key1, iv1,
        CHACHA20_POLY1305_AEAD_DECRYPT);
    if (err != BAD_FUNC_ARG)
        return -4718;
    err = wc_ChaCha20Poly1305_Init(&aead, NULL, iv1,
        CHACHA20_POLY1305_AEAD_DECRYPT);
    if (err != BAD_FUNC_ARG)
        return -4719;
    err = wc_ChaCha20Poly1305_Init(&aead, key1, NULL,
        CHACHA20_POLY1305_AEAD_DECRYPT);
    if (err != BAD_FUNC_ARG)
        return -4720;
    err = wc_ChaCha20Poly1305_UpdateAad(NULL, aad1, sizeof(aad1));
    if (err != BAD_FUNC_ARG)
        return -4721;
    err = wc_ChaCha20Poly1305_UpdateAad(&aead, NULL, sizeof(aad1));
    if (err != BAD_FUNC_ARG)
        return -4722;
    err = wc_ChaCha20Poly1305_UpdateData(NULL, generatedPlaintext,
        generatedPlaintext, sizeof(plaintext1));
    if (err != BAD_FUNC_ARG)
        return -4723;
    err = wc_ChaCha20Poly1305_UpdateData(&aead, generatedPlaintext, NULL,
        sizeof(plaintext1));
    if (err != BAD_FUNC_ARG)
        return -4724;
    err = wc_ChaCha20Poly1305_UpdateData(&aead, NULL, generatedPlaintext,
        sizeof(plaintext1));
    if (err != BAD_FUNC_ARG)
        return -4725;
    err = wc_ChaCha20Poly1305_Final(NULL, generatedAuthTag);
    if (err != BAD_FUNC_ARG)
        return -4726;
    err = wc_ChaCha20Poly1305_Final(&aead, NULL);
    if (err != BAD_FUNC_ARG)
        return -4727;

    /* AEAD init/update/final - state tests */
    aead.state = CHACHA20_POLY1305_STATE_INIT;
    err = wc_ChaCha20Poly1305_UpdateAad(&aead, aad1, sizeof(aad1));
    if (err != BAD_STATE_E)
        return -4728;
    aead.state = CHACHA20_POLY1305_STATE_DATA;
    err = wc_ChaCha20Poly1305_UpdateAad(&aead, aad1, sizeof(aad1));
    if (err != BAD_STATE_E)
        return -4729;
    aead.state = CHACHA20_POLY1305_STATE_INIT;
    err = wc_ChaCha20Poly1305_UpdateData(&aead, generatedPlaintext,
        generatedPlaintext, sizeof(plaintext1));
    if (err != BAD_STATE_E)
        return -4730;
    aead.state = CHACHA20_POLY1305_STATE_INIT;
    err = wc_ChaCha20Poly1305_Final(&aead, generatedAuthTag);
    if (err != BAD_STATE_E)
        return -4731;
    aead.state = CHACHA20_POLY1305_STATE_READY;
    err = wc_ChaCha20Poly1305_Final(&aead, generatedAuthTag);
    if (err != BAD_STATE_E)
        return -4732;

    XMEMSET(generatedCiphertext, 0, sizeof(generatedCiphertext));
    XMEMSET(generatedAuthTag, 0, sizeof(generatedAuthTag));
    XMEMSET(generatedPlaintext, 0, sizeof(generatedPlaintext));

    /* Test 1 - Encrypt */
    err = wc_ChaCha20Poly1305_Init(&aead, key1, iv1,
        CHACHA20_POLY1305_AEAD_ENCRYPT);
    if (err != 0)
        return -4733;
    err = wc_ChaCha20Poly1305_UpdateAad(&aead, aad1, sizeof(aad1));
    if (err != 0)
        return -4734;
#ifdef TEST_SMALL_CHACHA_CHUNKS
    /* test doing data in smaller chunks */
    for (testLen=0; testLen<sizeof(plaintext1); ) {
        word32 dataLen = sizeof(plaintext1) - testLen;
        if (dataLen > TEST_SMALL_CHACHA_CHUNKS)
            dataLen = TEST_SMALL_CHACHA_CHUNKS;
        err = wc_ChaCha20Poly1305_UpdateData(&aead, &plaintext1[testLen],
            &generatedCiphertext[testLen], dataLen);
        if (err != 0)
            return -4735;
        testLen += dataLen;
    }
#else
    err = wc_ChaCha20Poly1305_UpdateData(&aead, plaintext1,
        generatedCiphertext, sizeof(plaintext1));
#endif
    err = wc_ChaCha20Poly1305_Final(&aead, generatedAuthTag);
    if (err != 0)
        return -4736;
    err = wc_ChaCha20Poly1305_CheckTag(generatedAuthTag, authTag1);
    if (err != 0)
        return -4737;
    if (XMEMCMP(generatedCiphertext, cipher1, sizeof(cipher1))) {
        return -4738;
    }

    /* Test 1 - Decrypt */
    err = wc_ChaCha20Poly1305_Init(&aead, key1, iv1,
        CHACHA20_POLY1305_AEAD_DECRYPT);
    if (err != 0)
        return -4739;
    err = wc_ChaCha20Poly1305_UpdateAad(&aead, aad1, sizeof(aad1));
    if (err != 0)
        return -4740;
#ifdef TEST_SMALL_CHACHA_CHUNKS
    /* test doing data in smaller chunks */
    for (testLen=0; testLen<sizeof(plaintext1); ) {
        word32 dataLen = sizeof(plaintext1) - testLen;
        if (dataLen > TEST_SMALL_CHACHA_CHUNKS)
            dataLen = TEST_SMALL_CHACHA_CHUNKS;
        err = wc_ChaCha20Poly1305_UpdateData(&aead,
            &generatedCiphertext[testLen], &generatedPlaintext[testLen],
            dataLen);
        if (err != 0)
            return -4741;
        testLen += dataLen;
    }
#else
    err = wc_ChaCha20Poly1305_UpdateData(&aead, generatedCiphertext,
        generatedPlaintext, sizeof(cipher1));
#endif
    err = wc_ChaCha20Poly1305_Final(&aead, generatedAuthTag);
    if (err != 0)
        return -4742;
    err = wc_ChaCha20Poly1305_CheckTag(generatedAuthTag, authTag1);
    if (err != 0)
        return -4743;
    if (XMEMCMP(generatedPlaintext, plaintext1, sizeof(plaintext1))) {
        return -4744;
    }

    XMEMSET(generatedCiphertext, 0, sizeof(generatedCiphertext));
    XMEMSET(generatedAuthTag, 0, sizeof(generatedAuthTag));
    XMEMSET(generatedPlaintext, 0, sizeof(generatedPlaintext));

    /* Test 2 - Encrypt */
    err = wc_ChaCha20Poly1305_Init(&aead, key2, iv2,
        CHACHA20_POLY1305_AEAD_ENCRYPT);
    if (err != 0)
        return -4745;
    err = wc_ChaCha20Poly1305_UpdateAad(&aead, aad2, sizeof(aad2));
    if (err != 0)
        return -4746;
#ifdef TEST_SMALL_CHACHA_CHUNKS
    /* test doing data in smaller chunks */
    for (testLen=0; testLen<sizeof(plaintext2); ) {
        word32 dataLen = sizeof(plaintext2) - testLen;
        if (dataLen > TEST_SMALL_CHACHA_CHUNKS)
            dataLen = TEST_SMALL_CHACHA_CHUNKS;
        err = wc_ChaCha20Poly1305_UpdateData(&aead, &plaintext2[testLen],
            &generatedCiphertext[testLen], dataLen);
        if (err != 0)
            return -4747;
        testLen += dataLen;
    }
#else
    err = wc_ChaCha20Poly1305_UpdateData(&aead, plaintext2, generatedCiphertext,
        sizeof(plaintext2));
#endif
    err = wc_ChaCha20Poly1305_Final(&aead, generatedAuthTag);
    if (err != 0)
        return -4748;
    err = wc_ChaCha20Poly1305_CheckTag(generatedAuthTag, authTag2);
    if (err != 0)
        return -4749;
    if (XMEMCMP(generatedCiphertext, cipher2, sizeof(cipher2))) {
        return -4750;
    }

    /* Test 2 - Decrypt */
    err = wc_ChaCha20Poly1305_Init(&aead, key2, iv2,
        CHACHA20_POLY1305_AEAD_DECRYPT);
    if (err != 0)
        return -4751;
    err = wc_ChaCha20Poly1305_UpdateAad(&aead, aad2, sizeof(aad2));
    if (err != 0)
        return -4752;
#ifdef TEST_SMALL_CHACHA_CHUNKS
    /* test doing data in smaller chunks */
    for (testLen=0; testLen<sizeof(plaintext2); ) {
        word32 dataLen = sizeof(plaintext2) - testLen;
        if (dataLen > TEST_SMALL_CHACHA_CHUNKS)
            dataLen = TEST_SMALL_CHACHA_CHUNKS;
        err = wc_ChaCha20Poly1305_UpdateData(&aead,
            &generatedCiphertext[testLen], &generatedPlaintext[testLen],
            dataLen);
        if (err != 0)
            return -4753;
        testLen += dataLen;
    }
#else
    err = wc_ChaCha20Poly1305_UpdateData(&aead, generatedCiphertext,
        generatedPlaintext, sizeof(cipher2));
#endif
    err = wc_ChaCha20Poly1305_Final(&aead, generatedAuthTag);
    if (err != 0)
        return -4754;
    err = wc_ChaCha20Poly1305_CheckTag(generatedAuthTag, authTag2);
    if (err != 0)
        return -4755;
    if (XMEMCMP(generatedPlaintext, plaintext2, sizeof(plaintext2))) {
        return -4756;
    }

    return err;
}
#endif /* HAVE_CHACHA && HAVE_POLY1305 */


#ifndef NO_DES3
int des_test(void)
{
    const byte vector[] = { /* "now is the time for all " w/o trailing 0 */
        0x6e,0x6f,0x77,0x20,0x69,0x73,0x20,0x74,
        0x68,0x65,0x20,0x74,0x69,0x6d,0x65,0x20,
        0x66,0x6f,0x72,0x20,0x61,0x6c,0x6c,0x20
    };

    byte plain[24];
    byte cipher[24];

    Des enc;
    Des dec;

    const byte key[] =
    {
        0x01,0x23,0x45,0x67,0x89,0xab,0xcd,0xef
    };

    const byte iv[] =
    {
        0x12,0x34,0x56,0x78,0x90,0xab,0xcd,0xef
    };

    const byte verify[] =
    {
        0x8b,0x7c,0x52,0xb0,0x01,0x2b,0x6c,0xb8,
        0x4f,0x0f,0xeb,0xf3,0xfb,0x5f,0x86,0x73,
        0x15,0x85,0xb3,0x22,0x4b,0x86,0x2b,0x4b
    };

    int ret;

    ret = wc_Des_SetKey(&enc, key, iv, DES_ENCRYPTION);
    if (ret != 0)
        return -4800;

    ret = wc_Des_CbcEncrypt(&enc, cipher, vector, sizeof(vector));
    if (ret != 0)
        return -4801;

    ret = wc_Des_SetKey(&dec, key, iv, DES_DECRYPTION);
    if (ret != 0)
        return -4802;

    ret = wc_Des_CbcDecrypt(&dec, plain, cipher, sizeof(cipher));
    if (ret != 0)
        return -4803;

    if (XMEMCMP(plain, vector, sizeof(plain)))
        return -4804;

    if (XMEMCMP(cipher, verify, sizeof(cipher)))
        return -4805;

    ret = wc_Des_CbcEncryptWithKey(cipher, vector, sizeof(vector), key, iv);
    if (ret != 0)
        return -4806;

#if defined(WOLFSSL_ENCRYPTED_KEYS) && !defined(NO_SHA)
    {
        EncryptedInfo info;
        XMEMSET(&info, 0, sizeof(EncryptedInfo));
        XMEMCPY(info.iv, iv, sizeof(iv));
        info.ivSz = sizeof(iv);
        info.keySz = sizeof(key);
        info.cipherType = WC_CIPHER_DES;

        ret = wc_BufferKeyEncrypt(&info, cipher, sizeof(cipher), key,
                sizeof(key), WC_HASH_TYPE_SHA);
        if (ret != 0)
            return -4807;

        /* Test invalid info ptr */
        ret = wc_BufferKeyEncrypt(NULL, cipher, sizeof(cipher), key,
                sizeof(key), WC_HASH_TYPE_SHA);
        if (ret != BAD_FUNC_ARG)
            return -4808;

        /* Test invalid hash type */
        ret = wc_BufferKeyEncrypt(&info, cipher, sizeof(cipher), key,
                sizeof(key), WC_HASH_TYPE_NONE);
        if (ret == 0)
            return -4809;
    }
#endif

    return 0;
}
#endif /* NO_DES3 */


#ifndef NO_DES3
int des3_test(void)
{
    const byte vector[] = { /* "Now is the time for all " w/o trailing 0 */
        0x4e,0x6f,0x77,0x20,0x69,0x73,0x20,0x74,
        0x68,0x65,0x20,0x74,0x69,0x6d,0x65,0x20,
        0x66,0x6f,0x72,0x20,0x61,0x6c,0x6c,0x20
    };

    byte plain[24];
    byte cipher[24];

    Des3 enc;
    Des3 dec;

    const byte key3[] =
    {
        0x01,0x23,0x45,0x67,0x89,0xab,0xcd,0xef,
        0xfe,0xde,0xba,0x98,0x76,0x54,0x32,0x10,
        0x89,0xab,0xcd,0xef,0x01,0x23,0x45,0x67
    };
    const byte iv3[] =
    {
        0x12,0x34,0x56,0x78,0x90,0xab,0xcd,0xef,
        0x01,0x01,0x01,0x01,0x01,0x01,0x01,0x01,
        0x11,0x21,0x31,0x41,0x51,0x61,0x71,0x81

    };

    const byte verify3[] =
    {
        0x43,0xa0,0x29,0x7e,0xd1,0x84,0xf8,0x0e,
        0x89,0x64,0x84,0x32,0x12,0xd5,0x08,0x98,
        0x18,0x94,0x15,0x74,0x87,0x12,0x7d,0xb0
    };

    int ret;


    if (wc_Des3Init(&enc, HEAP_HINT, devId) != 0)
        return -4900;
    if (wc_Des3Init(&dec, HEAP_HINT, devId) != 0)
        return -4901;

    ret = wc_Des3_SetKey(&enc, key3, iv3, DES_ENCRYPTION);
    if (ret != 0)
        return -4902;
    ret = wc_Des3_SetKey(&dec, key3, iv3, DES_DECRYPTION);
    if (ret != 0)
        return -4903;
    ret = wc_Des3_CbcEncrypt(&enc, cipher, vector, sizeof(vector));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -4904;
    ret = wc_Des3_CbcDecrypt(&dec, plain, cipher, sizeof(cipher));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &dec.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -4905;

    if (XMEMCMP(plain, vector, sizeof(plain)))
        return -4906;

    if (XMEMCMP(cipher, verify3, sizeof(cipher)))
        return -4907;

#if defined(OPENSSL_EXTRA) && !defined(WOLFCRYPT_ONLY)
    /* test the same vectors with using compatibility layer */
    {
        DES_key_schedule ks1;
        DES_key_schedule ks2;
        DES_key_schedule ks3;
        DES_cblock iv4;

        XMEMCPY(ks1, key3, sizeof(DES_key_schedule));
        XMEMCPY(ks2, key3 + 8, sizeof(DES_key_schedule));
        XMEMCPY(ks3, key3 + 16, sizeof(DES_key_schedule));
        XMEMCPY(iv4, iv3, sizeof(DES_cblock));

        XMEMSET(plain, 0, sizeof(plain));
        XMEMSET(cipher, 0, sizeof(cipher));

        DES_ede3_cbc_encrypt(vector, cipher, sizeof(vector), &ks1, &ks2, &ks3,
                &iv4, DES_ENCRYPT);
        DES_ede3_cbc_encrypt(cipher, plain, sizeof(cipher), &ks1, &ks2, &ks3,
                &iv4, DES_DECRYPT);

        if (XMEMCMP(plain, vector, sizeof(plain)))
            return -4908;

        if (XMEMCMP(cipher, verify3, sizeof(cipher)))
            return -4909;
    }
#endif /* OPENSSL_EXTRA */

    wc_Des3Free(&enc);
    wc_Des3Free(&dec);

#if defined(WOLFSSL_ENCRYPTED_KEYS) && !defined(NO_SHA)
    {
        EncryptedInfo info;
        XMEMSET(&info, 0, sizeof(EncryptedInfo));
        XMEMCPY(info.iv, iv3, sizeof(iv3));
        info.ivSz = sizeof(iv3);
        info.keySz = sizeof(key3);
        info.cipherType = WC_CIPHER_DES3;

        ret = wc_BufferKeyEncrypt(&info, cipher, sizeof(cipher), key3,
                sizeof(key3), WC_HASH_TYPE_SHA);
        if (ret != 0)
            return -4910;
    }
#endif

    return 0;
}
#endif /* NO_DES */


#ifndef NO_AES

#if defined(WOLFSSL_AES_OFB) || defined(WOLFSSL_AES_CFB) || \
    defined(WOLFSSL_AES_XTS)
#if defined(OPENSSL_EXTRA) && !defined(HAVE_SELFTEST) && !defined(HAVE_FIPS)
/* pass in the function, key, iv, plain text and expected and this function
 * tests that the encryption and decryption is successful */
static int EVP_test(const WOLFSSL_EVP_CIPHER* type, const byte* key,
        const byte* iv, const byte* plain, int plainSz,
        const byte* expected, int expectedSz)
{
    EVP_CIPHER_CTX ctx;
    int idx, ret = 0, cipherSz;
    byte* cipher;

    cipher = (byte*)XMALLOC(plainSz, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (cipher == NULL) {
        return -4911;
    }

    /* test encrypt */
    EVP_CIPHER_CTX_init(&ctx);
    if (EVP_CipherInit(&ctx, type, key, iv, 1) == 0) {
        ret = -4912;
        goto EVP_TEST_END;
    }

    if (EVP_CipherUpdate(&ctx, cipher, &idx, plain, expectedSz) == 0) {
        ret = -4913;
        goto EVP_TEST_END;
    }

    cipherSz = idx;
    if (EVP_CipherFinal(&ctx, cipher + cipherSz, &idx) == 0) {
        ret = -4914;
        goto EVP_TEST_END;
    }
    cipherSz += idx;

    if (XMEMCMP(cipher, expected, plainSz)) {
        ret = -4915;
        goto EVP_TEST_END;
    }

    /* test decrypt */
    EVP_CIPHER_CTX_init(&ctx);
    if (EVP_CipherInit(&ctx, type, key, iv, 0) == 0) {
        ret = -4916;
        goto EVP_TEST_END;
    }

    if (EVP_CipherUpdate(&ctx, cipher, &idx, cipher, expectedSz) == 0) {
        ret = -4917;
        goto EVP_TEST_END;
    }

    cipherSz = idx;
    if (EVP_CipherFinal(&ctx, cipher + cipherSz, &idx) == 0) {
        ret = -4918;
        goto EVP_TEST_END;
    }
    cipherSz += idx;

    if ((expectedSz != cipherSz) || XMEMCMP(plain, cipher, plainSz)) {
        ret = -4919;
        goto EVP_TEST_END;
    }

EVP_TEST_END:
    XFREE(cipher, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    (void)cipherSz;
    return ret;
}
#endif /* OPENSSL_EXTRA */
#endif /* WOLFSSL_AES_OFB || WOLFSSL_AES_CFB */

#ifdef WOLFSSL_AES_OFB
    /* test vector from https://csrc.nist.gov/Projects/cryptographic-algorithm-validation-program/Block-Ciphers */
    int aesofb_test(void)
    {
    #ifdef WOLFSSL_AES_256
        const byte key1[] =
        {
            0xc4,0xc7,0xfa,0xd6,0x53,0x5c,0xb8,0x71,
            0x4a,0x5c,0x40,0x77,0x9a,0x8b,0xa1,0xd2,
            0x53,0x3e,0x23,0xb4,0xb2,0x58,0x73,0x2a,
            0x5b,0x78,0x01,0xf4,0xe3,0x71,0xa7,0x94
        };
        const byte iv1[] =
        {
            0x5e,0xb9,0x33,0x13,0xb8,0x71,0xff,0x16,
            0xb9,0x8a,0x9b,0xcb,0x43,0x33,0x0d,0x6f
        };
        const byte plain1[] =
        {
            0x6d,0x0b,0xb0,0x79,0x63,0x84,0x71,0xe9,
            0x39,0xd4,0x53,0x14,0x86,0xc1,0x4c,0x25,
            0x9a,0xee,0xc6,0xf3,0xc0,0x0d,0xfd,0xd6,
            0xc0,0x50,0xa8,0xba,0xa8,0x20,0xdb,0x71,
            0xcc,0x12,0x2c,0x4e,0x0c,0x17,0x15,0xef,
            0x55,0xf3,0x99,0x5a,0x6b,0xf0,0x2a,0x4c
        };
        const byte cipher1[] =
        {
            0x0f,0x54,0x61,0x71,0x59,0xd0,0x3f,0xfc,
            0x1b,0xfa,0xfb,0x60,0x29,0x30,0xd7,0x00,
            0xf4,0xa4,0xa8,0xe6,0xdd,0x93,0x94,0x46,
            0x64,0xd2,0x19,0xc4,0xc5,0x4d,0xde,0x1b,
            0x04,0x53,0xe1,0x73,0xf5,0x18,0x74,0xae,
            0xfd,0x64,0xa2,0xe1,0xe2,0x76,0x13,0xb0
        };
    #endif /* WOLFSSL_AES_256 */


    #ifdef WOLFSSL_AES_128
        const byte key2[] =
        {
            0x10,0xa5,0x88,0x69,0xd7,0x4b,0xe5,0xa3,
            0x74,0xcf,0x86,0x7c,0xfb,0x47,0x38,0x59
        };
        const byte iv2[] =
        {
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
        };
        const byte plain2[] =
        {
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
        };
        const byte cipher2[] =
        {
            0x6d,0x25,0x1e,0x69,0x44,0xb0,0x51,0xe0,
            0x4e,0xaa,0x6f,0xb4,0xdb,0xf7,0x84,0x65
        };
    #endif /* WOLFSSL_AES_128 */


    #ifdef WOLFSSL_AES_192
        const byte key3[] = {
            0xd0,0x77,0xa0,0x3b,0xd8,0xa3,0x89,0x73,
            0x92,0x8c,0xca,0xfe,0x4a,0x9d,0x2f,0x45,
            0x51,0x30,0xbd,0x0a,0xf5,0xae,0x46,0xa9
        };
        const byte iv3[] =
        {
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
        };
        const byte cipher3[] =
        {
            0xab,0xc7,0x86,0xfb,0x1e,0xdb,0x50,0x45,
            0x80,0xc4,0xd8,0x82,0xef,0x29,0xa0,0xc7
        };
        const byte plain3[] =
        {
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
        };
    #endif /* WOLFSSL_AES_192 */

        Aes enc;
        byte cipher[AES_BLOCK_SIZE * 4];
    #ifdef HAVE_AES_DECRYPT
        Aes dec;
        byte plain [AES_BLOCK_SIZE * 4];
    #endif
        int  ret = 0;

        (void)enc;
    #ifdef HAVE_AES_DECRYPT
        (void)dec;
    #endif

#ifdef WOLFSSL_AES_128
        /* 128 key size test */
    #ifdef OPENSSL_EXTRA
        ret = EVP_test(EVP_aes_128_ofb(), key2, iv2, plain2, sizeof(plain2),
                cipher2, sizeof(cipher2));
        if (ret != 0) {
            return ret;
        }
    #endif

        ret = wc_AesSetKey(&enc, key2, sizeof(key2), iv2, AES_ENCRYPTION);
        if (ret != 0)
            return -4920;
    #ifdef HAVE_AES_DECRYPT
        /* decrypt uses AES_ENCRYPTION */
        ret = wc_AesSetKey(&dec, key2, sizeof(key2), iv2, AES_ENCRYPTION);
        if (ret != 0)
            return -4921;
    #endif

        XMEMSET(cipher, 0, sizeof(cipher));
        ret = wc_AesOfbEncrypt(&enc, cipher, plain2, AES_BLOCK_SIZE);
        if (ret != 0)
            return -4922;

        if (XMEMCMP(cipher, cipher2, AES_BLOCK_SIZE))
            return -4923;

    #ifdef HAVE_AES_DECRYPT
        ret = wc_AesOfbDecrypt(&dec, plain, cipher2, AES_BLOCK_SIZE);
        if (ret != 0)
            return -4924;

        if (XMEMCMP(plain, plain2, AES_BLOCK_SIZE))
            return -4925;
    #endif /* HAVE_AES_DECRYPT */
#endif /* WOLFSSL_AES_128 */

#ifdef WOLFSSL_AES_192
        /* 192 key size test */
    #ifdef OPENSSL_EXTRA
        ret = EVP_test(EVP_aes_192_ofb(), key3, iv3, plain3, sizeof(plain3),
                cipher3, sizeof(cipher3));
        if (ret != 0) {
            return ret;
        }
    #endif

        ret = wc_AesSetKey(&enc, key3, sizeof(key3), iv3, AES_ENCRYPTION);
        if (ret != 0)
            return -4926;
    #ifdef HAVE_AES_DECRYPT
        /* decrypt uses AES_ENCRYPTION */
        ret = wc_AesSetKey(&dec, key3, sizeof(key3), iv3, AES_ENCRYPTION);
        if (ret != 0)
            return -4927;
    #endif

        XMEMSET(cipher, 0, sizeof(cipher));
        ret = wc_AesOfbEncrypt(&enc, cipher, plain3, AES_BLOCK_SIZE);
        if (ret != 0)
            return -4928;

        if (XMEMCMP(cipher, cipher3, AES_BLOCK_SIZE))
            return -4929;

    #ifdef HAVE_AES_DECRYPT
        ret = wc_AesOfbDecrypt(&dec, plain, cipher3, AES_BLOCK_SIZE);
        if (ret != 0)
            return -4930;

        if (XMEMCMP(plain, plain3, AES_BLOCK_SIZE))
            return -4931;
    #endif /* HAVE_AES_DECRYPT */
#endif /* WOLFSSL_AES_192 */

#ifdef WOLFSSL_AES_256
        /* 256 key size test */
    #ifdef OPENSSL_EXTRA
        ret = EVP_test(EVP_aes_256_ofb(), key1, iv1, plain1, sizeof(plain1),
                cipher1, sizeof(cipher1));
        if (ret != 0) {
            return ret;
        }
    #endif

        ret = wc_AesSetKey(&enc, key1, sizeof(key1), iv1, AES_ENCRYPTION);
        if (ret != 0)
            return -4932;
    #ifdef HAVE_AES_DECRYPT
        /* decrypt uses AES_ENCRYPTION */
        ret = wc_AesSetKey(&dec, key1, sizeof(key1), iv1, AES_ENCRYPTION);
        if (ret != 0)
            return -4933;
    #endif

        XMEMSET(cipher, 0, sizeof(cipher));
        ret = wc_AesOfbEncrypt(&enc, cipher, plain1, AES_BLOCK_SIZE);
        if (ret != 0)
            return -4934;

        if (XMEMCMP(cipher, cipher1, AES_BLOCK_SIZE))
            return -4935;

        ret = wc_AesOfbEncrypt(&enc, cipher + AES_BLOCK_SIZE,
                plain1 + AES_BLOCK_SIZE, AES_BLOCK_SIZE);
        if (ret != 0)
            return -4936;

        if (XMEMCMP(cipher + AES_BLOCK_SIZE, cipher1 + AES_BLOCK_SIZE,
                    AES_BLOCK_SIZE))
            return -4937;

    #ifdef HAVE_AES_DECRYPT
        ret = wc_AesOfbDecrypt(&dec, plain, cipher1, AES_BLOCK_SIZE);
        if (ret != 0)
            return -4938;

        if (XMEMCMP(plain, plain1, AES_BLOCK_SIZE))
            return -4939;

        ret = wc_AesOfbDecrypt(&dec, plain + AES_BLOCK_SIZE,
                cipher1 + AES_BLOCK_SIZE, AES_BLOCK_SIZE);
        if (ret != 0)
            return -4940;

        if (XMEMCMP(plain + AES_BLOCK_SIZE, plain1 + AES_BLOCK_SIZE,
                    AES_BLOCK_SIZE))
            return -4941;
    #endif /* HAVE_AES_DECRYPT */

        /* multiple blocks at once */
        ret = wc_AesSetKey(&enc, key1, sizeof(key1), iv1, AES_ENCRYPTION);
        if (ret != 0)
            return -4942;
    #ifdef HAVE_AES_DECRYPT
        /* decrypt uses AES_ENCRYPTION */
        ret = wc_AesSetKey(&dec, key1, sizeof(key1), iv1, AES_ENCRYPTION);
        if (ret != 0)
            return -4943;
    #endif

        XMEMSET(cipher, 0, sizeof(cipher));
        ret = wc_AesOfbEncrypt(&enc, cipher, plain1, AES_BLOCK_SIZE * 3);
        if (ret != 0)
            return -4944;

        if (XMEMCMP(cipher, cipher1, AES_BLOCK_SIZE * 3))
            return -4945;

    #ifdef HAVE_AES_DECRYPT
        ret = wc_AesOfbDecrypt(&dec, plain, cipher1, AES_BLOCK_SIZE * 3);
        if (ret != 0)
            return -4946;

        if (XMEMCMP(plain, plain1, AES_BLOCK_SIZE * 3))
            return -4947;
    #endif /* HAVE_AES_DECRYPT */

        /* inline decrypt/encrypt*/
        ret = wc_AesSetKey(&enc, key1, sizeof(key1), iv1, AES_ENCRYPTION);
        if (ret != 0)
            return -4948;
    #ifdef HAVE_AES_DECRYPT
        /* decrypt uses AES_ENCRYPTION */
        ret = wc_AesSetKey(&dec, key1, sizeof(key1), iv1, AES_ENCRYPTION);
        if (ret != 0)
            return -4949;
    #endif

        XMEMCPY(cipher, plain1, AES_BLOCK_SIZE * 2);
        ret = wc_AesOfbEncrypt(&enc, cipher, cipher, AES_BLOCK_SIZE * 2);
        if (ret != 0)
            return -4950;

        if (XMEMCMP(cipher, cipher1, AES_BLOCK_SIZE * 2))
            return -4951;

    #ifdef HAVE_AES_DECRYPT
        ret = wc_AesOfbDecrypt(&dec, cipher, cipher, AES_BLOCK_SIZE * 2);
        if (ret != 0)
            return -4952;

        if (XMEMCMP(cipher, plain1, AES_BLOCK_SIZE * 2))
            return -4953;
    #endif /* HAVE_AES_DECRYPT */

        /* 256 key size test leftover support */
        ret = wc_AesSetKey(&enc, key1, sizeof(key1), iv1, AES_ENCRYPTION);
        if (ret != 0)
            return -4954;
    #ifdef HAVE_AES_DECRYPT
        /* decrypt uses AES_ENCRYPTION */
        ret = wc_AesSetKey(&dec, key1, sizeof(key1), iv1, AES_ENCRYPTION);
        if (ret != 0)
            return -4955;
    #endif

        XMEMSET(cipher, 0, sizeof(cipher));
        ret = wc_AesOfbEncrypt(&enc, cipher, plain1, 3);
        if (ret != 0)
            return -4956;

        if (XMEMCMP(cipher, cipher1, 3))
            return -4957;

        ret = wc_AesOfbEncrypt(&enc, cipher + 3, plain1 + 3, AES_BLOCK_SIZE);
        if (ret != 0)
            return -4958;

        if (XMEMCMP(cipher + 3, cipher1 + 3, AES_BLOCK_SIZE))
            return -4959;

    #ifdef HAVE_AES_DECRYPT
        ret = wc_AesOfbDecrypt(&dec, plain, cipher1, 6);
        if (ret != 0)
            return -4960;

        if (XMEMCMP(plain, plain1, 6))
            return -4961;

        ret = wc_AesOfbDecrypt(&dec, plain + 6, cipher1 + 6, AES_BLOCK_SIZE);
        if (ret != 0)
            return -4962;

        if (XMEMCMP(plain + 6, plain1 + 6, AES_BLOCK_SIZE))
            return -4963;
    #endif /* HAVE_AES_DECRYPT */
#endif /* WOLFSSL_AES_256 */

        return 0;
    }
#endif /* WOLFSSL_AES_OFB */

#if defined(WOLFSSL_AES_CFB)
    /* Test cases from NIST SP 800-38A, Recommendation for Block Cipher Modes of Operation Methods an*/
    static int aescfb_test(void)
    {
        Aes enc;
        byte cipher[AES_BLOCK_SIZE * 4];
    #ifdef HAVE_AES_DECRYPT
        Aes dec;
        byte plain [AES_BLOCK_SIZE * 4];
    #endif
        int  ret = 0;

        const byte iv[] = {
            0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
            0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f
        };

#ifdef WOLFSSL_AES_128
        const byte key1[] =
        {
            0x2b,0x7e,0x15,0x16,0x28,0xae,0xd2,0xa6,
            0xab,0xf7,0x15,0x88,0x09,0xcf,0x4f,0x3c
        };

        const byte cipher1[] =
        {
            0x3b,0x3f,0xd9,0x2e,0xb7,0x2d,0xad,0x20,
            0x33,0x34,0x49,0xf8,0xe8,0x3c,0xfb,0x4a,
            0xc8,0xa6,0x45,0x37,0xa0,0xb3,0xa9,0x3f,
            0xcd,0xe3,0xcd,0xad,0x9f,0x1c,0xe5,0x8b,
            0x26,0x75,0x1f,0x67,0xa3,0xcb,0xb1,0x40,
            0xb1,0x80,0x8c,0xf1,0x87,0xa4,0xf4,0xdf
        };

        const byte msg1[] =
        {
            0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
            0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a,
            0xae,0x2d,0x8a,0x57,0x1e,0x03,0xac,0x9c,
            0x9e,0xb7,0x6f,0xac,0x45,0xaf,0x8e,0x51,
            0x30,0xc8,0x1c,0x46,0xa3,0x5c,0xe4,0x11,
            0xe5,0xfb,0xc1,0x19,0x1a,0x0a,0x52,0xef
        };
#endif /* WOLFSSL_AES_128 */

#ifdef WOLFSSL_AES_192
        /* 192 size key test */
        const byte key2[] =
        {
            0x8e,0x73,0xb0,0xf7,0xda,0x0e,0x64,0x52,
            0xc8,0x10,0xf3,0x2b,0x80,0x90,0x79,0xe5,
            0x62,0xf8,0xea,0xd2,0x52,0x2c,0x6b,0x7b
        };

        const byte cipher2[] =
        {
            0xcd,0xc8,0x0d,0x6f,0xdd,0xf1,0x8c,0xab,
            0x34,0xc2,0x59,0x09,0xc9,0x9a,0x41,0x74,
            0x67,0xce,0x7f,0x7f,0x81,0x17,0x36,0x21,
            0x96,0x1a,0x2b,0x70,0x17,0x1d,0x3d,0x7a,
            0x2e,0x1e,0x8a,0x1d,0xd5,0x9b,0x88,0xb1,
            0xc8,0xe6,0x0f,0xed,0x1e,0xfa,0xc4,0xc9,
            0xc0,0x5f,0x9f,0x9c,0xa9,0x83,0x4f,0xa0,
            0x42,0xae,0x8f,0xba,0x58,0x4b,0x09,0xff
        };

        const byte msg2[] =
        {
            0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
            0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a,
            0xae,0x2d,0x8a,0x57,0x1e,0x03,0xac,0x9c,
            0x9e,0xb7,0x6f,0xac,0x45,0xaf,0x8e,0x51,
            0x30,0xc8,0x1c,0x46,0xa3,0x5c,0xe4,0x11,
            0xe5,0xfb,0xc1,0x19,0x1a,0x0a,0x52,0xef,
            0xf6,0x9f,0x24,0x45,0xdf,0x4f,0x9b,0x17,
            0xad,0x2b,0x41,0x7b,0xe6,0x6c,0x37,0x10
        };
#endif /* WOLFSSL_AES_192 */

#ifdef WOLFSSL_AES_256
        /* 256 size key simple test */
        const byte key3[] =
        {
            0x60,0x3d,0xeb,0x10,0x15,0xca,0x71,0xbe,
            0x2b,0x73,0xae,0xf0,0x85,0x7d,0x77,0x81,
            0x1f,0x35,0x2c,0x07,0x3b,0x61,0x08,0xd7,
            0x2d,0x98,0x10,0xa3,0x09,0x14,0xdf,0xf4
        };

        const byte cipher3[] =
        {
            0xdc,0x7e,0x84,0xbf,0xda,0x79,0x16,0x4b,
            0x7e,0xcd,0x84,0x86,0x98,0x5d,0x38,0x60,
            0x39,0xff,0xed,0x14,0x3b,0x28,0xb1,0xc8,
            0x32,0x11,0x3c,0x63,0x31,0xe5,0x40,0x7b,
            0xdf,0x10,0x13,0x24,0x15,0xe5,0x4b,0x92,
            0xa1,0x3e,0xd0,0xa8,0x26,0x7a,0xe2,0xf9,
            0x75,0xa3,0x85,0x74,0x1a,0xb9,0xce,0xf8,
            0x20,0x31,0x62,0x3d,0x55,0xb1,0xe4,0x71
        };

        const byte msg3[] =
        {
            0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
            0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a,
            0xae,0x2d,0x8a,0x57,0x1e,0x03,0xac,0x9c,
            0x9e,0xb7,0x6f,0xac,0x45,0xaf,0x8e,0x51,
            0x30,0xc8,0x1c,0x46,0xa3,0x5c,0xe4,0x11,
            0xe5,0xfb,0xc1,0x19,0x1a,0x0a,0x52,0xef,
            0xf6,0x9f,0x24,0x45,0xdf,0x4f,0x9b,0x17,
            0xad,0x2b,0x41,0x7b,0xe6,0x6c,0x37,0x10
        };
#endif /* WOLFSSL_AES_256 */


    if (wc_AesInit(&enc, HEAP_HINT, devId) != 0)
        return -4964;
#ifdef HAVE_AES_DECRYPT
    if (wc_AesInit(&dec, HEAP_HINT, devId) != 0)
        return -4965;
#endif

#ifdef WOLFSSL_AES_128
        /* 128 key tests */
    #if defined(OPENSSL_EXTRA) && !defined(HAVE_SELFTEST) && !defined(HAVE_FIPS)
        ret = EVP_test(EVP_aes_128_cfb128(), key1, iv, msg1, sizeof(msg1),
                cipher1, sizeof(cipher1));
        if (ret != 0) {
            return ret;
        }
    #endif

        ret = wc_AesSetKey(&enc, key1, AES_BLOCK_SIZE, iv, AES_ENCRYPTION);
        if (ret != 0)
            return -4966;
    #ifdef HAVE_AES_DECRYPT
        /* decrypt uses AES_ENCRYPTION */
        ret = wc_AesSetKey(&dec, key1, AES_BLOCK_SIZE, iv, AES_ENCRYPTION);
        if (ret != 0)
            return -4967;
    #endif

        XMEMSET(cipher, 0, sizeof(cipher));
        ret = wc_AesCfbEncrypt(&enc, cipher, msg1, AES_BLOCK_SIZE * 2);
        if (ret != 0)
            return -4968;

        if (XMEMCMP(cipher, cipher1, AES_BLOCK_SIZE * 2))
            return -4969;

        /* test restarting encryption process */
        ret = wc_AesCfbEncrypt(&enc, cipher + (AES_BLOCK_SIZE * 2),
                msg1 + (AES_BLOCK_SIZE * 2), AES_BLOCK_SIZE);
        if (ret != 0)
            return -4970;

        if (XMEMCMP(cipher + (AES_BLOCK_SIZE * 2),
                    cipher1 + (AES_BLOCK_SIZE * 2), AES_BLOCK_SIZE))
            return -4971;

    #ifdef HAVE_AES_DECRYPT
        ret = wc_AesCfbDecrypt(&dec, plain, cipher, AES_BLOCK_SIZE * 3);
        if (ret != 0)
            return -4972;

        if (XMEMCMP(plain, msg1, AES_BLOCK_SIZE * 3))
            return -4973;
    #endif /* HAVE_AES_DECRYPT */
#endif /* WOLFSSL_AES_128 */

#ifdef WOLFSSL_AES_192
        /* 192 key size test */
    #if defined(OPENSSL_EXTRA) && !defined(HAVE_SELFTEST) && !defined(HAVE_FIPS)
        ret = EVP_test(EVP_aes_192_cfb128(), key2, iv, msg2, sizeof(msg2),
                cipher2, sizeof(cipher2));
        if (ret != 0) {
            return ret;
        }
    #endif

        ret = wc_AesSetKey(&enc, key2, sizeof(key2), iv, AES_ENCRYPTION);
        if (ret != 0)
            return -4974;
    #ifdef HAVE_AES_DECRYPT
        /* decrypt uses AES_ENCRYPTION */
        ret = wc_AesSetKey(&dec, key2, sizeof(key2), iv, AES_ENCRYPTION);
        if (ret != 0)
            return -4975;
    #endif

        XMEMSET(cipher, 0, sizeof(cipher));
        ret = wc_AesCfbEncrypt(&enc, cipher, msg2, AES_BLOCK_SIZE * 4);
        if (ret != 0)
            return -4976;

        if (XMEMCMP(cipher, cipher2, AES_BLOCK_SIZE * 4))
            return -4977;

    #ifdef HAVE_AES_DECRYPT
        ret = wc_AesCfbDecrypt(&dec, plain, cipher, AES_BLOCK_SIZE * 4);
        if (ret != 0)
            return -4978;

        if (XMEMCMP(plain, msg2, AES_BLOCK_SIZE * 4))
            return -4979;
    #endif /* HAVE_AES_DECRYPT */
#endif /* WOLFSSL_AES_192 */

#ifdef WOLFSSL_AES_256
        /* 256 key size test */
    #if defined(OPENSSL_EXTRA) && !defined(HAVE_SELFTEST) && !defined(HAVE_FIPS)
        ret = EVP_test(EVP_aes_256_cfb128(), key3, iv, msg3, sizeof(msg3),
                cipher3, sizeof(cipher3));
        if (ret != 0) {
            return ret;
        }
    #endif
        ret = wc_AesSetKey(&enc, key3, sizeof(key3), iv, AES_ENCRYPTION);
        if (ret != 0)
            return -4980;
    #ifdef HAVE_AES_DECRYPT
        /* decrypt uses AES_ENCRYPTION */
        ret = wc_AesSetKey(&dec, key3, sizeof(key3), iv, AES_ENCRYPTION);
        if (ret != 0)
            return -4981;
    #endif

        /* test with data left overs, magic lengths are checking near edges */
        XMEMSET(cipher, 0, sizeof(cipher));
        ret = wc_AesCfbEncrypt(&enc, cipher, msg3, 4);
        if (ret != 0)
            return -4982;

        if (XMEMCMP(cipher, cipher3, 4))
            return -4983;

        ret = wc_AesCfbEncrypt(&enc, cipher + 4, msg3 + 4, 27);
        if (ret != 0)
            return -4984;

        if (XMEMCMP(cipher + 4, cipher3 + 4, 27))
            return -4985;

        ret = wc_AesCfbEncrypt(&enc, cipher + 31, msg3 + 31,
                (AES_BLOCK_SIZE * 4) - 31);
        if (ret != 0)
            return -4986;

        if (XMEMCMP(cipher, cipher3, AES_BLOCK_SIZE * 4))
            return -4987;

    #ifdef HAVE_AES_DECRYPT
        ret = wc_AesCfbDecrypt(&dec, plain, cipher, 4);
        if (ret != 0)
            return -4988;

        if (XMEMCMP(plain, msg3, 4))
            return -4989;

        ret = wc_AesCfbDecrypt(&dec, plain + 4, cipher + 4, 4);
        if (ret != 0)
            return -4990;

        ret = wc_AesCfbDecrypt(&dec, plain + 8, cipher + 8, 23);
        if (ret != 0)
            return -4991;

        if (XMEMCMP(plain + 4, msg3 + 4, 27))
            return -4992;

        ret = wc_AesCfbDecrypt(&dec, plain + 31, cipher + 31,
                (AES_BLOCK_SIZE * 4) - 31);
        if (ret != 0)
            return -4993;

        if (XMEMCMP(plain, msg3, AES_BLOCK_SIZE * 4))
            return -4994;
    #endif /* HAVE_AES_DECRYPT */
#endif /* WOLFSSL_AES_256 */

        return ret;
    }

#if !defined(HAVE_SELFTEST) && !defined(HAVE_FIPS)
    static int aescfb1_test(void)
    {
        Aes enc;
        byte cipher[AES_BLOCK_SIZE];
    #ifdef HAVE_AES_DECRYPT
        Aes dec;
        byte plain [AES_BLOCK_SIZE];
    #endif
        int  ret = 0;

#ifdef WOLFSSL_AES_128
        const byte iv[] = {
            0x4d,0xbb,0xdc,0xaa,0x59,0xf3,0x63,0xc9,
            0x2a,0x3b,0x98,0x43,0xad,0x20,0xe2,0xb7
        };

        const byte key1[] =
        {
            0xcd,0xef,0x9d,0x06,0x61,0xba,0xe4,0x73,
            0x8d,0x1a,0x58,0xa2,0xa6,0x22,0x8b,0x66
        };

        const byte cipher1[] =
        {
            0x00
        };

        const byte msg1[] =
        {
            0xC0
        };
#endif /* WOLFSSL_AES_128 */
#ifdef WOLFSSL_AES_192
        const byte iv2[] = {
            0x57,0xc6,0x89,0x7c,0x99,0x52,0x28,0x13,
            0xbf,0x67,0x9c,0xe1,0x13,0x70,0xaf,0x5e
        };

        const byte key2[] =
        {
            0xba,0xa1,0x58,0xa1,0x6b,0x50,0x4a,0x10,
            0x8e,0xd4,0x33,0x2e,0xe7,0xf2,0x9b,0xf6,
            0xd1,0xac,0x46,0xa8,0xde,0x5a,0xfe,0x7a
        };

        const byte cipher2[] =
        {
            0x30
        };

        const byte msg2[] =
        {
            0x80
        };
#endif /* WOLFSSL_AES_192 */
#ifdef WOLFSSL_AES_256
        const byte iv3[] = {
            0x63,0x2e,0x9f,0x83,0x1f,0xa3,0x80,0x5e,
            0x52,0x02,0xbc,0xe0,0x6d,0x04,0xf9,0xa0
        };

        const byte key3[] =
        {
            0xf6,0xfa,0xe4,0xf1,0x5d,0x91,0xfc,0x50,
            0x88,0x78,0x4f,0x84,0xa5,0x37,0x12,0x7e,
            0x32,0x63,0x55,0x9c,0x62,0x73,0x88,0x20,
            0xc2,0xcf,0x3d,0xe1,0x1c,0x2a,0x30,0x40
        };

        const byte cipher3[] =
        {
            0xF7, 0x00
        };

        const byte msg3[] =
        {
            0x41, 0xC0
        };
#endif /* WOLFSSL_AES_256 */

    if (wc_AesInit(&enc, HEAP_HINT, devId) != 0)
        return -4995;
#ifdef HAVE_AES_DECRYPT
    if (wc_AesInit(&dec, HEAP_HINT, devId) != 0)
        return -4996;
#endif

#ifdef WOLFSSL_AES_128
        /* 128 key tests */
        ret = wc_AesSetKey(&enc, key1, AES_BLOCK_SIZE, iv, AES_ENCRYPTION);
        if (ret != 0)
            return -4997;
    #ifdef HAVE_AES_DECRYPT
        /* decrypt uses AES_ENCRYPTION */
        ret = wc_AesSetKey(&dec, key1, AES_BLOCK_SIZE, iv, AES_ENCRYPTION);
        if (ret != 0)
            return -4998;
    #endif

        XMEMSET(cipher, 0, sizeof(cipher));
        ret = wc_AesCfb1Encrypt(&enc, cipher, msg1, 2);
        if (ret != 0)
            return -4999;

        if (cipher[0] != cipher1[0])
            return -5000;

    #ifdef HAVE_AES_DECRYPT
        ret = wc_AesCfb1Decrypt(&dec, plain, cipher, 2);
        if (ret != 0)
            return -5001;

        if (plain[0] != msg1[0])
            return -5002;
    #endif /* HAVE_AES_DECRYPT */

    #ifdef OPENSSL_EXTRA
        ret = wc_AesSetKey(&enc, key1, AES_BLOCK_SIZE, iv, AES_ENCRYPTION);
        if (ret != 0)
            return -5003;

        XMEMSET(cipher, 0, sizeof(cipher));
        ret = wc_AesCfb1Encrypt(&enc, cipher, msg1,
                sizeof(msg1) * WOLFSSL_BIT_SIZE);
        if (ret != 0)
            return -5004;

        ret = EVP_test(EVP_aes_128_cfb1(), key1, iv, msg1, sizeof(msg1),
                cipher, sizeof(msg1));
        if (ret != 0) {
            return ret;
        }
    #endif
#endif /* WOLFSSL_AES_128 */
#ifdef WOLFSSL_AES_192
        /* 192 key tests */
        ret = wc_AesSetKey(&enc, key2, sizeof(key2), iv2, AES_ENCRYPTION);
        if (ret != 0)
            return -5005;

        XMEMSET(cipher, 0, sizeof(cipher));
        ret = wc_AesCfb1Encrypt(&enc, cipher, msg2, 4);
        if (ret != 0)
            return -5006;
        if (XMEMCMP(cipher, cipher2, sizeof(cipher2)) != 0)
            return -5007;

    #ifdef OPENSSL_EXTRA
        ret = wc_AesSetKey(&enc, key2, sizeof(key2), iv2, AES_ENCRYPTION);
        if (ret != 0)
            return -5008;

        XMEMSET(cipher, 0, sizeof(cipher));
        ret = wc_AesCfb1Encrypt(&enc, cipher, msg2,
                sizeof(msg2) * WOLFSSL_BIT_SIZE);
        if (ret != 0)
            return -5009;

        ret = EVP_test(EVP_aes_192_cfb1(), key2, iv2, msg2, sizeof(msg2),
                cipher, sizeof(msg2));
        if (ret != 0) {
            return ret;
        }
    #endif
#endif /* WOLFSSL_AES_192 */

#ifdef WOLFSSL_AES_256
        /* 256 key tests */
        ret = wc_AesSetKey(&enc, key3, sizeof(key3), iv3, AES_ENCRYPTION);
        if (ret != 0)
            return -5010;

        XMEMSET(cipher, 0, sizeof(cipher));
        ret = wc_AesCfb1Encrypt(&enc, cipher, msg3, 10);
        if (ret != 0)
            return -5011;
        if (XMEMCMP(cipher, cipher3, sizeof(cipher3)) != 0)
            return -5012;

    #ifdef OPENSSL_EXTRA
        ret = wc_AesSetKey(&enc, key3, sizeof(key3), iv3, AES_ENCRYPTION);
        if (ret != 0)
            return -5013;

        XMEMSET(cipher, 0, sizeof(cipher));
        ret = wc_AesCfb1Encrypt(&enc, cipher, msg3,
                sizeof(msg3) * WOLFSSL_BIT_SIZE);
        if (ret != 0)
            return -5014;

        ret = EVP_test(EVP_aes_256_cfb1(), key3, iv3, msg3, sizeof(msg3),
                cipher, sizeof(msg3));
        if (ret != 0) {
            return ret;
        }
    #endif
#endif /* WOLFSSL_AES_256 */
        return ret;
    }

    static int aescfb8_test(void)
    {
        Aes enc;
        byte cipher[AES_BLOCK_SIZE];
    #ifdef HAVE_AES_DECRYPT
        Aes dec;
        byte plain [AES_BLOCK_SIZE];
    #endif
        int  ret = 0;

#ifdef WOLFSSL_AES_128
        const byte iv[] = {
            0xf4,0x75,0xc6,0x49,0x91,0xb2,0x0e,0xae,
            0xe1,0x83,0xa2,0x26,0x29,0xe2,0x1e,0x22
        };

        const byte key1[] =
        {
            0xc8,0xfe,0x9b,0xf7,0x7b,0x93,0x0f,0x46,
            0xd2,0x07,0x8b,0x8c,0x0e,0x65,0x7c,0xd4
        };

        const byte cipher1[] =
        {
            0xd2,0x76,0x91
        };

        const byte msg1[] =
        {
            0xc9,0x06,0x35
        };
#endif /* WOLFSSL_AES_128 */
#ifdef WOLFSSL_AES_192
        const byte iv2[] = {
            0x0a,0x02,0x84,0x6b,0x62,0xab,0xb6,0x93,
            0xef,0x31,0xd7,0x54,0x84,0x2e,0xed,0x29
        };

        const byte key2[] =
        {
            0xba,0xf0,0x8b,0x76,0x31,0x7a,0x65,0xc5,
            0xf0,0x7a,0xe6,0xf5,0x7e,0xb0,0xe6,0x54,
            0x88,0x65,0x93,0x24,0xd2,0x97,0x09,0xe3
        };

        const byte cipher2[] =
        {
            0x72,0x9c,0x0b,0x6d,0xeb,0x75,0xfa,0x6e,
            0xb5,0xe8
        };

        const byte msg2[] =
        {
            0x98,0x95,0x93,0x24,0x02,0x39,0x3d,0xc3,
            0x3a,0x60
        };
#endif
#ifdef WOLFSSL_AES_256
        const byte iv3[] = {
            0x33,0x8c,0x55,0x2f,0xf1,0xec,0xa1,0x44,
            0x08,0xe0,0x5d,0x8c,0xf9,0xf3,0xb3,0x1b
        };

        const byte key3[] =
        {
            0x06,0x48,0x74,0x09,0x2f,0x7a,0x13,0xcc,
            0x44,0x62,0x24,0x7a,0xd4,0x23,0xd0,0xe9,
            0x6e,0xdf,0x42,0xe8,0xb6,0x7a,0x5a,0x23,
            0xb7,0xa0,0xa6,0x47,0x7b,0x09,0x8e,0x66
        };

        const byte cipher3[] =
        {
            0x1c,0xff,0x95
        };

        const byte msg3[] =
        {
            0xb9,0x74,0xfa
        };
#endif

    if (wc_AesInit(&enc, HEAP_HINT, devId) != 0)
        return -5015;
#ifdef HAVE_AES_DECRYPT
    if (wc_AesInit(&dec, HEAP_HINT, devId) != 0)
        return -5016;
#endif

#ifdef WOLFSSL_AES_128
        /* 128 key tests */
    #ifdef OPENSSL_EXTRA
        ret = EVP_test(EVP_aes_128_cfb8(), key1, iv, msg1, sizeof(msg1),
                cipher1, sizeof(cipher1));
        if (ret != 0) {
            return ret;
        }
    #endif
        ret = wc_AesSetKey(&enc, key1, AES_BLOCK_SIZE, iv, AES_ENCRYPTION);
        if (ret != 0)
            return -5017;
    #ifdef HAVE_AES_DECRYPT
        /* decrypt uses AES_ENCRYPTION */
        ret = wc_AesSetKey(&dec, key1, AES_BLOCK_SIZE, iv, AES_ENCRYPTION);
        if (ret != 0)
            return -5018;
    #endif

        XMEMSET(cipher, 0, sizeof(cipher));
        ret = wc_AesCfb8Encrypt(&enc, cipher, msg1, sizeof(msg1));
        if (ret != 0)
            return -5019;

        if (XMEMCMP(cipher, cipher1, sizeof(cipher1)) != 0)
            return -5020;

    #ifdef HAVE_AES_DECRYPT
        ret = wc_AesCfb8Decrypt(&dec, plain, cipher, sizeof(msg1));
        if (ret != 0)
            return -5021;

        if (XMEMCMP(plain, msg1, sizeof(msg1)) != 0)
            return -5022;
    #endif /* HAVE_AES_DECRYPT */
#endif /* WOLFSSL_AES_128 */
#ifdef WOLFSSL_AES_192
        /* 192 key tests */
        ret = wc_AesSetKey(&enc, key2, sizeof(key2), iv2, AES_ENCRYPTION);
        if (ret != 0)
            return -5023;

        XMEMSET(cipher, 0, sizeof(cipher));
        ret = wc_AesCfb8Encrypt(&enc, cipher, msg2, sizeof(msg2));
        if (ret != 0)
            return -5024;
        if (XMEMCMP(cipher, cipher2, sizeof(msg2)) != 0)
            return -5025;
#ifdef OPENSSL_EXTRA
        ret = EVP_test(EVP_aes_192_cfb8(), key2, iv2, msg2, sizeof(msg2),
                cipher2, sizeof(msg2));
        if (ret != 0) {
            return ret;
        }
#endif

#endif /* WOLFSSL_AES_192 */

#ifdef WOLFSSL_AES_256
        /* 256 key tests */
        ret = wc_AesSetKey(&enc, key3, sizeof(key3), iv3, AES_ENCRYPTION);
        if (ret != 0)
            return -5026;

        XMEMSET(cipher, 0, sizeof(cipher));
        ret = wc_AesCfb8Encrypt(&enc, cipher, msg3, sizeof(msg3));
        if (ret != 0)
            return -5027;
        if (XMEMCMP(cipher, cipher3, sizeof(cipher3)) != 0)
            return -5028;

    #ifdef OPENSSL_EXTRA
        ret = EVP_test(EVP_aes_256_cfb8(), key3, iv3, msg3, sizeof(msg3),
                cipher3, sizeof(msg3));
        if (ret != 0) {
            return ret;
        }
    #endif
#endif /* WOLFSSL_AES_256 */

        return ret;
    }
#endif /* !HAVE_SELFTEST && !HAVE_FIPS */
#endif /* WOLFSSL_AES_CFB */


static int aes_key_size_test(void)
{
    int    ret;
    Aes    aes;
    byte   key16[] = { 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
                       0x38, 0x39, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66 };
    byte   key24[] = { 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
                       0x38, 0x39, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66,
                       0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37 };
    byte   key32[] = { 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
                       0x38, 0x39, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66,
                       0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
                       0x38, 0x39, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66 };
    byte   iv[]    = "1234567890abcdef";
#ifndef HAVE_FIPS
    word32 keySize;
#endif

#if !defined(HAVE_FIPS) || \
    defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2)
    /* w/ FIPS v1 (cert 2425) wc_AesInit just returns 0 always as it's not
     * supported with that FIPS version */
    ret = wc_AesInit(NULL, HEAP_HINT, devId);
    if (ret != BAD_FUNC_ARG)
        return -5100;
#endif

    ret = wc_AesInit(&aes, HEAP_HINT, devId);
    /* 0 check OK for FIPSv1 */
    if (ret != 0)
        return -5101;

#ifndef HAVE_FIPS
    /* Parameter Validation testing. */
    ret = wc_AesGetKeySize(NULL, NULL);
    if (ret != BAD_FUNC_ARG)
        return -5102;
    ret = wc_AesGetKeySize(&aes, NULL);
    if (ret != BAD_FUNC_ARG)
        return -5103;
    ret = wc_AesGetKeySize(NULL, &keySize);
    if (ret != BAD_FUNC_ARG)
        return -5104;
    /* Crashes in FIPS */
    ret = wc_AesSetKey(NULL, key16, sizeof(key16), iv, AES_ENCRYPTION);
    if (ret != BAD_FUNC_ARG)
        return -5105;
#endif
    /* NULL IV indicates to use all zeros IV. */
    ret = wc_AesSetKey(&aes, key16, sizeof(key16), NULL, AES_ENCRYPTION);
#ifdef WOLFSSL_AES_128
    if (ret != 0)
#else
    if (ret != BAD_FUNC_ARG)
#endif
        return -5106;
    ret = wc_AesSetKey(&aes, key32, sizeof(key32) - 1, iv, AES_ENCRYPTION);
    if (ret != BAD_FUNC_ARG)
        return -5107;
/* CryptoCell handles rounds internally */
#if !defined(HAVE_FIPS) && !defined(WOLFSSL_CRYPTOCELL)
    /* Force invalid rounds */
    aes.rounds = 16;
    ret = wc_AesGetKeySize(&aes, &keySize);
    if (ret != BAD_FUNC_ARG)
        return -5108;
#endif

    ret = wc_AesSetKey(&aes, key16, sizeof(key16), iv, AES_ENCRYPTION);
#ifdef WOLFSSL_AES_128
    if (ret != 0)
#else
    if (ret != BAD_FUNC_ARG)
#endif
        return -5109;
#if !defined(HAVE_FIPS) && defined(WOLFSSL_AES_128)
    ret = wc_AesGetKeySize(&aes, &keySize);
    if (ret != 0 || keySize != sizeof(key16))
        return -5110;
#endif

    ret = wc_AesSetKey(&aes, key24, sizeof(key24), iv, AES_ENCRYPTION);
#ifdef WOLFSSL_AES_192
    if (ret != 0)
#else
    if (ret != BAD_FUNC_ARG)
#endif
        return -5111;
#if !defined(HAVE_FIPS) && defined(WOLFSSL_AES_192)
    ret = wc_AesGetKeySize(&aes, &keySize);
    if (ret != 0 || keySize != sizeof(key24))
        return -5112;
#endif

    ret = wc_AesSetKey(&aes, key32, sizeof(key32), iv, AES_ENCRYPTION);
#ifdef WOLFSSL_AES_256
    if (ret != 0)
#else
    if (ret != BAD_FUNC_ARG)
#endif
        return -5113;
#if !defined(HAVE_FIPS) && defined(WOLFSSL_AES_256)
    ret = wc_AesGetKeySize(&aes, &keySize);
    if (ret != 0 || keySize != sizeof(key32))
        return -5114;
#endif

    return 0;
}

#if defined(WOLFSSL_AES_XTS)
/* test vectors from http://csrc.nist.gov/groups/STM/cavp/block-cipher-modes.html */
#ifdef WOLFSSL_AES_128
static int aes_xts_128_test(void)
{
    XtsAes aes;
    int ret = 0;
    unsigned char buf[AES_BLOCK_SIZE * 2];
    unsigned char cipher[AES_BLOCK_SIZE * 2];

    /* 128 key tests */
    static unsigned char k1[] = {
        0xa1, 0xb9, 0x0c, 0xba, 0x3f, 0x06, 0xac, 0x35,
        0x3b, 0x2c, 0x34, 0x38, 0x76, 0x08, 0x17, 0x62,
        0x09, 0x09, 0x23, 0x02, 0x6e, 0x91, 0x77, 0x18,
        0x15, 0xf2, 0x9d, 0xab, 0x01, 0x93, 0x2f, 0x2f
    };

    static unsigned char i1[] = {
        0x4f, 0xae, 0xf7, 0x11, 0x7c, 0xda, 0x59, 0xc6,
        0x6e, 0x4b, 0x92, 0x01, 0x3e, 0x76, 0x8a, 0xd5
    };

    static unsigned char p1[] = {
        0xeb, 0xab, 0xce, 0x95, 0xb1, 0x4d, 0x3c, 0x8d,
        0x6f, 0xb3, 0x50, 0x39, 0x07, 0x90, 0x31, 0x1c
    };

    /* plain text test of partial block is not from NIST test vector list */
    static unsigned char pp[] = {
        0xeb, 0xab, 0xce, 0x95, 0xb1, 0x4d, 0x3c, 0x8d,
        0x6f, 0xb3, 0x50, 0x39, 0x07, 0x90, 0x31, 0x1c,
        0x6e, 0x4b, 0x92, 0x01, 0x3e, 0x76, 0x8a, 0xd5
    };

    static unsigned char c1[] = {
        0x77, 0x8a, 0xe8, 0xb4, 0x3c, 0xb9, 0x8d, 0x5a,
        0x82, 0x50, 0x81, 0xd5, 0xbe, 0x47, 0x1c, 0x63
    };

    static unsigned char k2[] = {
        0x39, 0x25, 0x79, 0x05, 0xdf, 0xcc, 0x77, 0x76,
        0x6c, 0x87, 0x0a, 0x80, 0x6a, 0x60, 0xe3, 0xc0,
        0x93, 0xd1, 0x2a, 0xcf, 0xcb, 0x51, 0x42, 0xfa,
        0x09, 0x69, 0x89, 0x62, 0x5b, 0x60, 0xdb, 0x16
    };

    static unsigned char i2[] = {
        0x5c, 0xf7, 0x9d, 0xb6, 0xc5, 0xcd, 0x99, 0x1a,
        0x1c, 0x78, 0x81, 0x42, 0x24, 0x95, 0x1e, 0x84
    };

    static unsigned char p2[] = {
        0xbd, 0xc5, 0x46, 0x8f, 0xbc, 0x8d, 0x50, 0xa1,
        0x0d, 0x1c, 0x85, 0x7f, 0x79, 0x1c, 0x5c, 0xba,
        0xb3, 0x81, 0x0d, 0x0d, 0x73, 0xcf, 0x8f, 0x20,
        0x46, 0xb1, 0xd1, 0x9e, 0x7d, 0x5d, 0x8a, 0x56
    };

    static unsigned char c2[] = {
        0xd6, 0xbe, 0x04, 0x6d, 0x41, 0xf2, 0x3b, 0x5e,
        0xd7, 0x0b, 0x6b, 0x3d, 0x5c, 0x8e, 0x66, 0x23,
        0x2b, 0xe6, 0xb8, 0x07, 0xd4, 0xdc, 0xc6, 0x0e,
        0xff, 0x8d, 0xbc, 0x1d, 0x9f, 0x7f, 0xc8, 0x22
    };

#ifdef OPENSSL_EXTRA
    ret = EVP_test(EVP_aes_128_xts(), k2, i2, p2, sizeof(p2), c2, sizeof(c2));
    if (ret != 0) {
        printf("EVP_aes_128_xts failed!\n");
        return ret;
    }
#endif

    XMEMSET(buf, 0, sizeof(buf));
    if (wc_AesXtsSetKey(&aes, k2, sizeof(k2), AES_ENCRYPTION,
            HEAP_HINT, devId) != 0)
        return -5200;

    ret = wc_AesXtsEncrypt(&aes, buf, p2, sizeof(p2), i2, sizeof(i2));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5201;
    if (XMEMCMP(c2, buf, sizeof(c2)))
        return -5202;

    XMEMSET(buf, 0, sizeof(buf));
    if (wc_AesXtsSetKey(&aes, k1, sizeof(k1), AES_ENCRYPTION,
            HEAP_HINT, devId) != 0)
        return -5203;
    ret = wc_AesXtsEncrypt(&aes, buf, p1, sizeof(p1), i1, sizeof(i1));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5204;
    if (XMEMCMP(c1, buf, AES_BLOCK_SIZE))
        return -5205;

    /* partial block encryption test */
    XMEMSET(cipher, 0, sizeof(cipher));
    ret = wc_AesXtsEncrypt(&aes, cipher, pp, sizeof(pp), i1, sizeof(i1));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5206;
    wc_AesXtsFree(&aes);

    /* partial block decrypt test */
    XMEMSET(buf, 0, sizeof(buf));
    if (wc_AesXtsSetKey(&aes, k1, sizeof(k1), AES_DECRYPTION,
            HEAP_HINT, devId) != 0)
        return -5207;
    ret = wc_AesXtsDecrypt(&aes, buf, cipher, sizeof(pp), i1, sizeof(i1));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5208;
    if (XMEMCMP(pp, buf, sizeof(pp)))
        return -5209;

    /* NIST decrypt test vector */
    XMEMSET(buf, 0, sizeof(buf));
    ret = wc_AesXtsDecrypt(&aes, buf, c1, sizeof(c1), i1, sizeof(i1));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5210;
    if (XMEMCMP(p1, buf, AES_BLOCK_SIZE))
        return -5211;

    /* fail case with decrypting using wrong key */
    XMEMSET(buf, 0, sizeof(buf));
    ret = wc_AesXtsDecrypt(&aes, buf, c2, sizeof(c2), i2, sizeof(i2));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5212;
    if (XMEMCMP(p2, buf, sizeof(p2)) == 0) /* fail case with wrong key */
        return -5213;

    /* set correct key and retest */
    XMEMSET(buf, 0, sizeof(buf));
    if (wc_AesXtsSetKey(&aes, k2, sizeof(k2), AES_DECRYPTION,
            HEAP_HINT, devId) != 0)
        return -5214;
    ret = wc_AesXtsDecrypt(&aes, buf, c2, sizeof(c2), i2, sizeof(i2));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5215;
    if (XMEMCMP(p2, buf, sizeof(p2)))
        return -5216;
    wc_AesXtsFree(&aes);

    return ret;
}
#endif /* WOLFSSL_AES_128 */


#ifdef WOLFSSL_AES_256
static int aes_xts_256_test(void)
{
    XtsAes aes;
    int ret = 0;
    unsigned char buf[AES_BLOCK_SIZE * 3];
    unsigned char cipher[AES_BLOCK_SIZE * 3];

    /* 256 key tests */
    static unsigned char k1[] = {
        0x1e, 0xa6, 0x61, 0xc5, 0x8d, 0x94, 0x3a, 0x0e,
        0x48, 0x01, 0xe4, 0x2f, 0x4b, 0x09, 0x47, 0x14,
        0x9e, 0x7f, 0x9f, 0x8e, 0x3e, 0x68, 0xd0, 0xc7,
        0x50, 0x52, 0x10, 0xbd, 0x31, 0x1a, 0x0e, 0x7c,
        0xd6, 0xe1, 0x3f, 0xfd, 0xf2, 0x41, 0x8d, 0x8d,
        0x19, 0x11, 0xc0, 0x04, 0xcd, 0xa5, 0x8d, 0xa3,
        0xd6, 0x19, 0xb7, 0xe2, 0xb9, 0x14, 0x1e, 0x58,
        0x31, 0x8e, 0xea, 0x39, 0x2c, 0xf4, 0x1b, 0x08
    };

    static unsigned char i1[] = {
        0xad, 0xf8, 0xd9, 0x26, 0x27, 0x46, 0x4a, 0xd2,
        0xf0, 0x42, 0x8e, 0x84, 0xa9, 0xf8, 0x75, 0x64
    };

    static unsigned char p1[] = {
        0x2e, 0xed, 0xea, 0x52, 0xcd, 0x82, 0x15, 0xe1,
        0xac, 0xc6, 0x47, 0xe8, 0x10, 0xbb, 0xc3, 0x64,
        0x2e, 0x87, 0x28, 0x7f, 0x8d, 0x2e, 0x57, 0xe3,
        0x6c, 0x0a, 0x24, 0xfb, 0xc1, 0x2a, 0x20, 0x2e
    };

    /* plain text test of partial block is not from NIST test vector list */
    static unsigned char pp[] = {
        0xeb, 0xab, 0xce, 0x95, 0xb1, 0x4d, 0x3c, 0x8d,
        0x6f, 0xb3, 0x50, 0x39, 0x07, 0x90, 0x31, 0x1c,
        0x6e, 0x4b, 0x92, 0x01, 0x3e, 0x76, 0x8a, 0xd5
    };

    static unsigned char c1[] = {
        0xcb, 0xaa, 0xd0, 0xe2, 0xf6, 0xce, 0xa3, 0xf5,
        0x0b, 0x37, 0xf9, 0x34, 0xd4, 0x6a, 0x9b, 0x13,
        0x0b, 0x9d, 0x54, 0xf0, 0x7e, 0x34, 0xf3, 0x6a,
        0xf7, 0x93, 0xe8, 0x6f, 0x73, 0xc6, 0xd7, 0xdb
    };

    static unsigned char k2[] = {
        0xad, 0x50, 0x4b, 0x85, 0xd7, 0x51, 0xbf, 0xba,
        0x69, 0x13, 0xb4, 0xcc, 0x79, 0xb6, 0x5a, 0x62,
        0xf7, 0xf3, 0x9d, 0x36, 0x0f, 0x35, 0xb5, 0xec,
        0x4a, 0x7e, 0x95, 0xbd, 0x9b, 0xa5, 0xf2, 0xec,
        0xc1, 0xd7, 0x7e, 0xa3, 0xc3, 0x74, 0xbd, 0x4b,
        0x13, 0x1b, 0x07, 0x83, 0x87, 0xdd, 0x55, 0x5a,
        0xb5, 0xb0, 0xc7, 0xe5, 0x2d, 0xb5, 0x06, 0x12,
        0xd2, 0xb5, 0x3a, 0xcb, 0x47, 0x8a, 0x53, 0xb4
    };

    static unsigned char i2[] = {
        0xe6, 0x42, 0x19, 0xed, 0xe0, 0xe1, 0xc2, 0xa0,
        0x0e, 0xf5, 0x58, 0x6a, 0xc4, 0x9b, 0xeb, 0x6f
    };

    static unsigned char p2[] = {
        0x24, 0xcb, 0x76, 0x22, 0x55, 0xb5, 0xa8, 0x00,
        0xf4, 0x6e, 0x80, 0x60, 0x56, 0x9e, 0x05, 0x53,
        0xbc, 0xfe, 0x86, 0x55, 0x3b, 0xca, 0xd5, 0x89,
        0xc7, 0x54, 0x1a, 0x73, 0xac, 0xc3, 0x9a, 0xbd,
        0x53, 0xc4, 0x07, 0x76, 0xd8, 0xe8, 0x22, 0x61,
        0x9e, 0xa9, 0xad, 0x77, 0xa0, 0x13, 0x4c, 0xfc
    };

    static unsigned char c2[] = {
        0xa3, 0xc6, 0xf3, 0xf3, 0x82, 0x79, 0x5b, 0x10,
        0x87, 0xd7, 0x02, 0x50, 0xdb, 0x2c, 0xd3, 0xb1,
        0xa1, 0x62, 0xa8, 0xb6, 0xdc, 0x12, 0x60, 0x61,
        0xc1, 0x0a, 0x84, 0xa5, 0x85, 0x3f, 0x3a, 0x89,
        0xe6, 0x6c, 0xdb, 0xb7, 0x9a, 0xb4, 0x28, 0x9b,
        0xc3, 0xea, 0xd8, 0x10, 0xe9, 0xc0, 0xaf, 0x92
    };

#ifdef OPENSSL_EXTRA
    ret = EVP_test(EVP_aes_256_xts(), k2, i2, p2, sizeof(p2), c2, sizeof(c2));
    if (ret != 0) {
        printf("EVP_aes_256_xts failed\n");
        return ret;
    }
#endif

    XMEMSET(buf, 0, sizeof(buf));
    if (wc_AesXtsSetKey(&aes, k2, sizeof(k2), AES_ENCRYPTION,
            HEAP_HINT, devId) != 0)
        return -5300;
    ret = wc_AesXtsEncrypt(&aes, buf, p2, sizeof(p2), i2, sizeof(i2));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5301;
    if (XMEMCMP(c2, buf, sizeof(c2)))
        return -5302;

    XMEMSET(buf, 0, sizeof(buf));
    if (wc_AesXtsSetKey(&aes, k1, sizeof(k1), AES_ENCRYPTION,
            HEAP_HINT, devId) != 0)
        return -5303;
    ret = wc_AesXtsEncrypt(&aes, buf, p1, sizeof(p1), i1, sizeof(i1));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5304;
    if (XMEMCMP(c1, buf, AES_BLOCK_SIZE))
        return -5305;

    /* partial block encryption test */
    XMEMSET(cipher, 0, sizeof(cipher));
    ret = wc_AesXtsEncrypt(&aes, cipher, pp, sizeof(pp), i1, sizeof(i1));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5306;
    wc_AesXtsFree(&aes);

    /* partial block decrypt test */
    XMEMSET(buf, 0, sizeof(buf));
    if (wc_AesXtsSetKey(&aes, k1, sizeof(k1), AES_DECRYPTION,
            HEAP_HINT, devId) != 0)
        return -5307;
    ret = wc_AesXtsDecrypt(&aes, buf, cipher, sizeof(pp), i1, sizeof(i1));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5308;
    if (XMEMCMP(pp, buf, sizeof(pp)))
        return -5309;

    /* NIST decrypt test vector */
    XMEMSET(buf, 0, sizeof(buf));
    ret = wc_AesXtsDecrypt(&aes, buf, c1, sizeof(c1), i1, sizeof(i1));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5310;
    if (XMEMCMP(p1, buf, AES_BLOCK_SIZE))
        return -5311;

    XMEMSET(buf, 0, sizeof(buf));
    if (wc_AesXtsSetKey(&aes, k2, sizeof(k2), AES_DECRYPTION,
            HEAP_HINT, devId) != 0)
        return -5312;
    ret = wc_AesXtsDecrypt(&aes, buf, c2, sizeof(c2), i2, sizeof(i2));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5313;
    if (XMEMCMP(p2, buf, sizeof(p2)))
        return -5314;
    wc_AesXtsFree(&aes);

    return ret;
}
#endif /* WOLFSSL_AES_256 */


#if defined(WOLFSSL_AES_128) && defined(WOLFSSL_AES_256)
/* both 128 and 256 bit key test */
static int aes_xts_sector_test(void)
{
    XtsAes aes;
    int ret = 0;
    unsigned char buf[AES_BLOCK_SIZE * 2];

    /* 128 key tests */
    static unsigned char k1[] = {
        0xa3, 0xe4, 0x0d, 0x5b, 0xd4, 0xb6, 0xbb, 0xed,
        0xb2, 0xd1, 0x8c, 0x70, 0x0a, 0xd2, 0xdb, 0x22,
        0x10, 0xc8, 0x11, 0x90, 0x64, 0x6d, 0x67, 0x3c,
        0xbc, 0xa5, 0x3f, 0x13, 0x3e, 0xab, 0x37, 0x3c
    };

    static unsigned char p1[] = {
        0x20, 0xe0, 0x71, 0x94, 0x05, 0x99, 0x3f, 0x09,
        0xa6, 0x6a, 0xe5, 0xbb, 0x50, 0x0e, 0x56, 0x2c
    };

    static unsigned char c1[] = {
        0x74, 0x62, 0x35, 0x51, 0x21, 0x02, 0x16, 0xac,
        0x92, 0x6b, 0x96, 0x50, 0xb6, 0xd3, 0xfa, 0x52
    };
    word64 s1 = 141;

    /* 256 key tests */
    static unsigned char k2[] = {
        0xef, 0x01, 0x0c, 0xa1, 0xa3, 0x66, 0x3e, 0x32,
        0x53, 0x43, 0x49, 0xbc, 0x0b, 0xae, 0x62, 0x23,
        0x2a, 0x15, 0x73, 0x34, 0x85, 0x68, 0xfb, 0x9e,
        0xf4, 0x17, 0x68, 0xa7, 0x67, 0x4f, 0x50, 0x7a,
        0x72, 0x7f, 0x98, 0x75, 0x53, 0x97, 0xd0, 0xe0,
        0xaa, 0x32, 0xf8, 0x30, 0x33, 0x8c, 0xc7, 0xa9,
        0x26, 0xc7, 0x73, 0xf0, 0x9e, 0x57, 0xb3, 0x57,
        0xcd, 0x15, 0x6a, 0xfb, 0xca, 0x46, 0xe1, 0xa0
    };

    static unsigned char p2[] = {
        0xed, 0x98, 0xe0, 0x17, 0x70, 0xa8, 0x53, 0xb4,
        0x9d, 0xb9, 0xe6, 0xaa, 0xf8, 0x8f, 0x0a, 0x41,
        0xb9, 0xb5, 0x6e, 0x91, 0xa5, 0xa2, 0xb1, 0x1d,
        0x40, 0x52, 0x92, 0x54, 0xf5, 0x52, 0x3e, 0x75
    };

    static unsigned char c2[] = {
        0xca, 0x20, 0xc5, 0x5e, 0x8d, 0xc1, 0x49, 0x68,
        0x7d, 0x25, 0x41, 0xde, 0x39, 0xc3, 0xdf, 0x63,
        0x00, 0xbb, 0x5a, 0x16, 0x3c, 0x10, 0xce, 0xd3,
        0x66, 0x6b, 0x13, 0x57, 0xdb, 0x8b, 0xd3, 0x9d
    };
    word64 s2 = 187;

    XMEMSET(buf, 0, sizeof(buf));
    if (wc_AesXtsSetKey(&aes, k1, sizeof(k1), AES_ENCRYPTION,
            HEAP_HINT, devId) != 0)
        return -5400;
    ret = wc_AesXtsEncryptSector(&aes, buf, p1, sizeof(p1), s1);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5401;
    if (XMEMCMP(c1, buf, AES_BLOCK_SIZE))
        return -5402;

    /* decrypt test */
    XMEMSET(buf, 0, sizeof(buf));
    if (wc_AesXtsSetKey(&aes, k1, sizeof(k1), AES_DECRYPTION,
            HEAP_HINT, devId) != 0)
        return -5403;
    ret = wc_AesXtsDecryptSector(&aes, buf, c1, sizeof(c1), s1);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5404;
    if (XMEMCMP(p1, buf, AES_BLOCK_SIZE))
        return -5405;
    wc_AesXtsFree(&aes);

    /* 256 bit key tests */
    XMEMSET(buf, 0, sizeof(buf));
    if (wc_AesXtsSetKey(&aes, k2, sizeof(k2), AES_ENCRYPTION,
            HEAP_HINT, devId) != 0)
        return -5406;
    ret = wc_AesXtsEncryptSector(&aes, buf, p2, sizeof(p2), s2);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5407;
    if (XMEMCMP(c2, buf, sizeof(c2)))
        return -5408;

    /* decrypt test */
    XMEMSET(buf, 0, sizeof(buf));
    if (wc_AesXtsSetKey(&aes, k2, sizeof(k2), AES_DECRYPTION,
            HEAP_HINT, devId) != 0)
        return -5409;
    ret = wc_AesXtsDecryptSector(&aes, buf, c2, sizeof(c2), s2);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5410;
    if (XMEMCMP(p2, buf, sizeof(p2)))
        return -5411;
    wc_AesXtsFree(&aes);

    return ret;
}
#endif /* WOLFSSL_AES_128 && WOLFSSL_AES_256 */


#ifdef WOLFSSL_AES_128
/* testing of bad arguments */
static int aes_xts_args_test(void)
{
    XtsAes aes;
    int ret = 0;
    unsigned char buf[AES_BLOCK_SIZE * 2];

    /* 128 key tests */
    static unsigned char k1[] = {
        0xa3, 0xe4, 0x0d, 0x5b, 0xd4, 0xb6, 0xbb, 0xed,
        0xb2, 0xd1, 0x8c, 0x70, 0x0a, 0xd2, 0xdb, 0x22,
        0x10, 0xc8, 0x11, 0x90, 0x64, 0x6d, 0x67, 0x3c,
        0xbc, 0xa5, 0x3f, 0x13, 0x3e, 0xab, 0x37, 0x3c
    };

    static unsigned char p1[] = {
        0x20, 0xe0, 0x71, 0x94, 0x05, 0x99, 0x3f, 0x09,
        0xa6, 0x6a, 0xe5, 0xbb, 0x50, 0x0e, 0x56, 0x2c
    };

    static unsigned char c1[] = {
        0x74, 0x62, 0x35, 0x51, 0x21, 0x02, 0x16, 0xac,
        0x92, 0x6b, 0x96, 0x50, 0xb6, 0xd3, 0xfa, 0x52
    };
    word64 s1 = 141;

    if (wc_AesXtsSetKey(NULL, k1, sizeof(k1), AES_ENCRYPTION,
            HEAP_HINT, devId) == 0)
        return -5500;
    if (wc_AesXtsSetKey(&aes, NULL, sizeof(k1), AES_ENCRYPTION,
            HEAP_HINT, devId) == 0)
        return -5501;

    /* encryption operations */
    if (wc_AesXtsSetKey(&aes, k1, sizeof(k1), AES_ENCRYPTION,
            HEAP_HINT, devId) != 0)
        return -5502;
    ret = wc_AesXtsEncryptSector(NULL, buf, p1, sizeof(p1), s1);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret == 0)
        return -5503;

    ret = wc_AesXtsEncryptSector(&aes, NULL, p1, sizeof(p1), s1);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret == 0)
        return -5504;
    wc_AesXtsFree(&aes);

    /* decryption operations */
    if (wc_AesXtsSetKey(&aes, k1, sizeof(k1), AES_DECRYPTION,
            HEAP_HINT, devId) != 0)
        return -5505;
    ret = wc_AesXtsDecryptSector(NULL, buf, c1, sizeof(c1), s1);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret == 0)
        return -5506;

    ret = wc_AesXtsDecryptSector(&aes, NULL, c1, sizeof(c1), s1);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &aes.aes.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret == 0)
        return -5507;
    wc_AesXtsFree(&aes);

    return 0;
}
#endif /* WOLFSSL_AES_128 */
#endif /* WOLFSSL_AES_XTS */

#if defined(HAVE_AES_CBC) && defined(WOLFSSL_AES_128)
static int aes_cbc_test(void)
{
    byte cipher[AES_BLOCK_SIZE];
    byte plain[AES_BLOCK_SIZE];
    int  ret;
    const byte msg[] = { /* "Now is the time for all " w/o trailing 0 */
        0x6e,0x6f,0x77,0x20,0x69,0x73,0x20,0x74,
        0x68,0x65,0x20,0x74,0x69,0x6d,0x65,0x20,
        0x66,0x6f,0x72,0x20,0x61,0x6c,0x6c,0x20
    };
    byte key[] = "0123456789abcdef   ";  /* align */
    byte iv[]  = "1234567890abcdef   ";  /* align */

    XMEMSET(cipher, 0, AES_BLOCK_SIZE);
    XMEMSET(plain, 0, AES_BLOCK_SIZE);

    /* Parameter Validation testing. */
    ret = wc_AesCbcEncryptWithKey(cipher, msg, AES_BLOCK_SIZE, key, 17, NULL);
    if (ret != BAD_FUNC_ARG)
        return -5600;
#ifdef HAVE_AES_DECRYPT
    ret = wc_AesCbcDecryptWithKey(plain, cipher, AES_BLOCK_SIZE, key, 17, NULL);
    if (ret != BAD_FUNC_ARG)
        return -5601;
#endif

    ret = wc_AesCbcEncryptWithKey(cipher, msg, AES_BLOCK_SIZE, key,
                                  AES_BLOCK_SIZE, iv);
    if (ret != 0)
        return -5602;
#ifdef HAVE_AES_DECRYPT
    ret = wc_AesCbcDecryptWithKey(plain, cipher, AES_BLOCK_SIZE, key,
                                  AES_BLOCK_SIZE, iv);
    if (ret != 0)
        return -5603;
    if (XMEMCMP(plain, msg, AES_BLOCK_SIZE) != 0)
        return -5604;
#endif /* HAVE_AES_DECRYPT */

    (void)plain;
    return 0;
}
#endif

int aes_test(void)
{
#if defined(HAVE_AES_CBC) || defined(WOLFSSL_AES_COUNTER) || defined(WOLFSSL_AES_DIRECT)
    Aes enc;
    byte cipher[AES_BLOCK_SIZE * 4];
#if defined(HAVE_AES_DECRYPT) || defined(WOLFSSL_AES_COUNTER) || defined(WOLFSSL_AES_DIRECT)
    Aes dec;
    byte plain [AES_BLOCK_SIZE * 4];
#endif
#endif /* HAVE_AES_CBC || WOLFSSL_AES_COUNTER */
    int  ret = 0;

#ifdef HAVE_AES_CBC
#ifdef WOLFSSL_AES_128
    const byte msg[] = { /* "Now is the time for all " w/o trailing 0 */
        0x6e,0x6f,0x77,0x20,0x69,0x73,0x20,0x74,
        0x68,0x65,0x20,0x74,0x69,0x6d,0x65,0x20,
        0x66,0x6f,0x72,0x20,0x61,0x6c,0x6c,0x20
    };

    const byte verify[] =
    {
        0x95,0x94,0x92,0x57,0x5f,0x42,0x81,0x53,
        0x2c,0xcc,0x9d,0x46,0x77,0xa2,0x33,0xcb
    };

    byte key[] = "0123456789abcdef   ";  /* align */
    byte iv[]  = "1234567890abcdef   ";  /* align */

    if (wc_AesInit(&enc, HEAP_HINT, devId) != 0)
        return -5700;
#if defined(HAVE_AES_DECRYPT) || defined(WOLFSSL_AES_COUNTER)
    if (wc_AesInit(&dec, HEAP_HINT, devId) != 0)
        return -5701;
#endif
    ret = wc_AesSetKey(&enc, key, AES_BLOCK_SIZE, iv, AES_ENCRYPTION);
    if (ret != 0)
        return -5702;
#if defined(HAVE_AES_DECRYPT) || defined(WOLFSSL_AES_COUNTER)
    ret = wc_AesSetKey(&dec, key, AES_BLOCK_SIZE, iv, AES_DECRYPTION);
    if (ret != 0)
        return -5703;
#endif

    XMEMSET(cipher, 0, AES_BLOCK_SIZE * 4);
    ret = wc_AesCbcEncrypt(&enc, cipher, msg, AES_BLOCK_SIZE);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5704;
#ifdef HAVE_AES_DECRYPT
    XMEMSET(plain, 0, AES_BLOCK_SIZE * 4);
    ret = wc_AesCbcDecrypt(&dec, plain, cipher, AES_BLOCK_SIZE);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &dec.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5705;

    if (XMEMCMP(plain, msg, AES_BLOCK_SIZE))
        return -5706;
#endif /* HAVE_AES_DECRYPT */
    if (XMEMCMP(cipher, verify, AES_BLOCK_SIZE))
        return -5707;
#endif /* WOLFSSL_AES_128 */

#if defined(WOLFSSL_AESNI) && defined(HAVE_AES_DECRYPT)
    {
        const byte bigMsg[] = {
            /* "All work and no play makes Jack a dull boy. " */
            0x41,0x6c,0x6c,0x20,0x77,0x6f,0x72,0x6b,
            0x20,0x61,0x6e,0x64,0x20,0x6e,0x6f,0x20,
            0x70,0x6c,0x61,0x79,0x20,0x6d,0x61,0x6b,
            0x65,0x73,0x20,0x4a,0x61,0x63,0x6b,0x20,
            0x61,0x20,0x64,0x75,0x6c,0x6c,0x20,0x62,
            0x6f,0x79,0x2e,0x20,0x41,0x6c,0x6c,0x20,
            0x77,0x6f,0x72,0x6b,0x20,0x61,0x6e,0x64,
            0x20,0x6e,0x6f,0x20,0x70,0x6c,0x61,0x79,
            0x20,0x6d,0x61,0x6b,0x65,0x73,0x20,0x4a,
            0x61,0x63,0x6b,0x20,0x61,0x20,0x64,0x75,
            0x6c,0x6c,0x20,0x62,0x6f,0x79,0x2e,0x20,
            0x41,0x6c,0x6c,0x20,0x77,0x6f,0x72,0x6b,
            0x20,0x61,0x6e,0x64,0x20,0x6e,0x6f,0x20,
            0x70,0x6c,0x61,0x79,0x20,0x6d,0x61,0x6b,
            0x65,0x73,0x20,0x4a,0x61,0x63,0x6b,0x20,
            0x61,0x20,0x64,0x75,0x6c,0x6c,0x20,0x62,
            0x6f,0x79,0x2e,0x20,0x41,0x6c,0x6c,0x20,
            0x77,0x6f,0x72,0x6b,0x20,0x61,0x6e,0x64,
            0x20,0x6e,0x6f,0x20,0x70,0x6c,0x61,0x79,
            0x20,0x6d,0x61,0x6b,0x65,0x73,0x20,0x4a,
            0x61,0x63,0x6b,0x20,0x61,0x20,0x64,0x75,
            0x6c,0x6c,0x20,0x62,0x6f,0x79,0x2e,0x20,
            0x41,0x6c,0x6c,0x20,0x77,0x6f,0x72,0x6b,
            0x20,0x61,0x6e,0x64,0x20,0x6e,0x6f,0x20,
            0x70,0x6c,0x61,0x79,0x20,0x6d,0x61,0x6b,
            0x65,0x73,0x20,0x4a,0x61,0x63,0x6b,0x20,
            0x61,0x20,0x64,0x75,0x6c,0x6c,0x20,0x62,
            0x6f,0x79,0x2e,0x20,0x41,0x6c,0x6c,0x20,
            0x77,0x6f,0x72,0x6b,0x20,0x61,0x6e,0x64,
            0x20,0x6e,0x6f,0x20,0x70,0x6c,0x61,0x79,
            0x20,0x6d,0x61,0x6b,0x65,0x73,0x20,0x4a,
            0x61,0x63,0x6b,0x20,0x61,0x20,0x64,0x75,
            0x6c,0x6c,0x20,0x62,0x6f,0x79,0x2e,0x20,
            0x41,0x6c,0x6c,0x20,0x77,0x6f,0x72,0x6b,
            0x20,0x61,0x6e,0x64,0x20,0x6e,0x6f,0x20,
            0x70,0x6c,0x61,0x79,0x20,0x6d,0x61,0x6b,
            0x65,0x73,0x20,0x4a,0x61,0x63,0x6b,0x20,
            0x61,0x20,0x64,0x75,0x6c,0x6c,0x20,0x62,
            0x6f,0x79,0x2e,0x20,0x41,0x6c,0x6c,0x20,
            0x77,0x6f,0x72,0x6b,0x20,0x61,0x6e,0x64,
            0x20,0x6e,0x6f,0x20,0x70,0x6c,0x61,0x79,
            0x20,0x6d,0x61,0x6b,0x65,0x73,0x20,0x4a,
            0x61,0x63,0x6b,0x20,0x61,0x20,0x64,0x75,
            0x6c,0x6c,0x20,0x62,0x6f,0x79,0x2e,0x20,
            0x41,0x6c,0x6c,0x20,0x77,0x6f,0x72,0x6b,
            0x20,0x61,0x6e,0x64,0x20,0x6e,0x6f,0x20,
            0x70,0x6c,0x61,0x79,0x20,0x6d,0x61,0x6b,
            0x65,0x73,0x20,0x4a,0x61,0x63,0x6b,0x20
        };
        const byte bigKey[] = "0123456789abcdeffedcba9876543210";
        byte bigCipher[sizeof(bigMsg)];
        byte bigPlain[sizeof(bigMsg)];
        word32 keySz, msgSz;

        /* Iterate from one AES_BLOCK_SIZE of bigMsg through the whole
         * message by AES_BLOCK_SIZE for each size of AES key. */
        for (keySz = 16; keySz <= 32; keySz += 8) {
            for (msgSz = AES_BLOCK_SIZE;
                 msgSz <= sizeof(bigMsg);
                 msgSz += AES_BLOCK_SIZE) {

                XMEMSET(bigCipher, 0, sizeof(bigCipher));
                XMEMSET(bigPlain, 0, sizeof(bigPlain));
                ret = wc_AesSetKey(&enc, bigKey, keySz, iv, AES_ENCRYPTION);
                if (ret != 0)
                    return -5708;
                ret = wc_AesSetKey(&dec, bigKey, keySz, iv, AES_DECRYPTION);
                if (ret != 0)
                    return -5709;

                ret = wc_AesCbcEncrypt(&enc, bigCipher, bigMsg, msgSz);
            #if defined(WOLFSSL_ASYNC_CRYPT)
                ret = wc_AsyncWait(ret, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
            #endif
                if (ret != 0)
                    return -5710;

                ret = wc_AesCbcDecrypt(&dec, bigPlain, bigCipher, msgSz);
            #if defined(WOLFSSL_ASYNC_CRYPT)
                ret = wc_AsyncWait(ret, &dec.asyncDev, WC_ASYNC_FLAG_NONE);
            #endif
                if (ret != 0)
                    return -5711;

                if (XMEMCMP(bigPlain, bigMsg, msgSz))
                    return -5712;
            }
        }
    }
#endif /* WOLFSSL_AESNI && HAVE_AES_DECRYPT */

    /* Test of AES IV state with encrypt/decrypt */
#ifdef WOLFSSL_AES_128
    {
        /* Test Vector from "NIST Special Publication 800-38A, 2001 Edition"
         * https://nvlpubs.nist.gov/nistpubs/legacy/sp/nistspecialpublication800-38a.pdf
         */
        const byte msg2[] =
        {
            0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
            0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
            0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03, 0xac, 0x9c,
            0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51
        };

        const byte verify2[] =
        {
            0x76, 0x49, 0xab, 0xac, 0x81, 0x19, 0xb2, 0x46,
            0xce, 0xe9, 0x8e, 0x9b, 0x12, 0xe9, 0x19, 0x7d,
            0x50, 0x86, 0xcb, 0x9b, 0x50, 0x72, 0x19, 0xee,
            0x95, 0xdb, 0x11, 0x3a, 0x91, 0x76, 0x78, 0xb2
        };
        byte key2[] = {
            0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
            0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c
        };
        byte iv2[]  = {
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f
        };


        ret = wc_AesSetKey(&enc, key2, sizeof(key2), iv2, AES_ENCRYPTION);
        if (ret != 0)
            return -5713;
        XMEMSET(cipher, 0, AES_BLOCK_SIZE * 2);
        ret = wc_AesCbcEncrypt(&enc, cipher, msg2, AES_BLOCK_SIZE);
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
    #endif
        if (ret != 0)
            return -5714;
        if (XMEMCMP(cipher, verify2, AES_BLOCK_SIZE))
            return -5715;

        ret = wc_AesCbcEncrypt(&enc, cipher + AES_BLOCK_SIZE,
                msg2 + AES_BLOCK_SIZE, AES_BLOCK_SIZE);
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
    #endif
        if (ret != 0)
            return -5716;
        if (XMEMCMP(cipher + AES_BLOCK_SIZE, verify2 + AES_BLOCK_SIZE,
                    AES_BLOCK_SIZE))
            return -5717;

        #if defined(HAVE_AES_DECRYPT)
        ret = wc_AesSetKey(&dec, key2, sizeof(key2), iv2, AES_DECRYPTION);
        if (ret != 0)
            return -5718;
        XMEMSET(plain, 0, AES_BLOCK_SIZE * 2);
        ret = wc_AesCbcDecrypt(&dec, plain, verify2, AES_BLOCK_SIZE);
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &dec.asyncDev, WC_ASYNC_FLAG_NONE);
    #endif
        if (ret != 0)
            return -5719;
        if (XMEMCMP(plain, msg2, AES_BLOCK_SIZE))
            return -5720;

        ret = wc_AesCbcDecrypt(&dec, plain + AES_BLOCK_SIZE,
                verify2 + AES_BLOCK_SIZE, AES_BLOCK_SIZE);
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &dec.asyncDev, WC_ASYNC_FLAG_NONE);
    #endif
        if (ret != 0)
            return -5721;
        if (XMEMCMP(plain + AES_BLOCK_SIZE, msg2 + AES_BLOCK_SIZE,
                    AES_BLOCK_SIZE))
            return -5722;

        #endif /* HAVE_AES_DECRYPT */
    }
#endif /* WOLFSSL_AES_128 */
#endif /* HAVE_AES_CBC */

#ifdef WOLFSSL_AES_COUNTER
    {
        /* test vectors from "Recommendation for Block Cipher Modes of
         * Operation" NIST Special Publication 800-38A */

        const byte ctrIv[] =
        {
            0xf0,0xf1,0xf2,0xf3,0xf4,0xf5,0xf6,0xf7,
            0xf8,0xf9,0xfa,0xfb,0xfc,0xfd,0xfe,0xff
        };

        const byte ctrPlain[] =
        {
            0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
            0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a,
            0xae,0x2d,0x8a,0x57,0x1e,0x03,0xac,0x9c,
            0x9e,0xb7,0x6f,0xac,0x45,0xaf,0x8e,0x51,
            0x30,0xc8,0x1c,0x46,0xa3,0x5c,0xe4,0x11,
            0xe5,0xfb,0xc1,0x19,0x1a,0x0a,0x52,0xef,
            0xf6,0x9f,0x24,0x45,0xdf,0x4f,0x9b,0x17,
            0xad,0x2b,0x41,0x7b,0xe6,0x6c,0x37,0x10
        };

#ifdef WOLFSSL_AES_128
        const byte oddCipher[] =
        {
            0xb9,0xd7,0xcb,0x08,0xb0,0xe1,0x7b,0xa0,
            0xc2
        };

        const byte ctr128Key[] =
        {
            0x2b,0x7e,0x15,0x16,0x28,0xae,0xd2,0xa6,
            0xab,0xf7,0x15,0x88,0x09,0xcf,0x4f,0x3c
        };

        const byte ctr128Cipher[] =
        {
            0x87,0x4d,0x61,0x91,0xb6,0x20,0xe3,0x26,
            0x1b,0xef,0x68,0x64,0x99,0x0d,0xb6,0xce,
            0x98,0x06,0xf6,0x6b,0x79,0x70,0xfd,0xff,
            0x86,0x17,0x18,0x7b,0xb9,0xff,0xfd,0xff,
            0x5a,0xe4,0xdf,0x3e,0xdb,0xd5,0xd3,0x5e,
            0x5b,0x4f,0x09,0x02,0x0d,0xb0,0x3e,0xab,
            0x1e,0x03,0x1d,0xda,0x2f,0xbe,0x03,0xd1,
            0x79,0x21,0x70,0xa0,0xf3,0x00,0x9c,0xee
        };
#endif /* WOLFSSL_AES_128 */

#ifdef WOLFSSL_AES_192
        const byte ctr192Key[] =
        {
            0x8e,0x73,0xb0,0xf7,0xda,0x0e,0x64,0x52,
            0xc8,0x10,0xf3,0x2b,0x80,0x90,0x79,0xe5,
            0x62,0xf8,0xea,0xd2,0x52,0x2c,0x6b,0x7b
        };

        const byte ctr192Cipher[] =
        {
            0x1a,0xbc,0x93,0x24,0x17,0x52,0x1c,0xa2,
            0x4f,0x2b,0x04,0x59,0xfe,0x7e,0x6e,0x0b,
            0x09,0x03,0x39,0xec,0x0a,0xa6,0xfa,0xef,
            0xd5,0xcc,0xc2,0xc6,0xf4,0xce,0x8e,0x94,
            0x1e,0x36,0xb2,0x6b,0xd1,0xeb,0xc6,0x70,
            0xd1,0xbd,0x1d,0x66,0x56,0x20,0xab,0xf7,
            0x4f,0x78,0xa7,0xf6,0xd2,0x98,0x09,0x58,
            0x5a,0x97,0xda,0xec,0x58,0xc6,0xb0,0x50
        };
#endif
#ifdef WOLFSSL_AES_256
        const byte ctr256Key[] =
        {
            0x60,0x3d,0xeb,0x10,0x15,0xca,0x71,0xbe,
            0x2b,0x73,0xae,0xf0,0x85,0x7d,0x77,0x81,
            0x1f,0x35,0x2c,0x07,0x3b,0x61,0x08,0xd7,
            0x2d,0x98,0x10,0xa3,0x09,0x14,0xdf,0xf4
        };

        const byte ctr256Cipher[] =
        {
            0x60,0x1e,0xc3,0x13,0x77,0x57,0x89,0xa5,
            0xb7,0xa7,0xf5,0x04,0xbb,0xf3,0xd2,0x28,
            0xf4,0x43,0xe3,0xca,0x4d,0x62,0xb5,0x9a,
            0xca,0x84,0xe9,0x90,0xca,0xca,0xf5,0xc5,
            0x2b,0x09,0x30,0xda,0xa2,0x3d,0xe9,0x4c,
            0xe8,0x70,0x17,0xba,0x2d,0x84,0x98,0x8d,
            0xdf,0xc9,0xc5,0x8d,0xb6,0x7a,0xad,0xa6,
            0x13,0xc2,0xdd,0x08,0x45,0x79,0x41,0xa6
        };
#endif

#ifdef WOLFSSL_AES_128
        wc_AesSetKeyDirect(&enc, ctr128Key, sizeof(ctr128Key),
                           ctrIv, AES_ENCRYPTION);
        /* Ctr only uses encrypt, even on key setup */
        wc_AesSetKeyDirect(&dec, ctr128Key, sizeof(ctr128Key),
                           ctrIv, AES_ENCRYPTION);

        ret = wc_AesCtrEncrypt(&enc, cipher, ctrPlain, sizeof(ctrPlain));
        if (ret != 0) {
            return -5723;
        }
        ret = wc_AesCtrEncrypt(&dec, plain, cipher, sizeof(ctrPlain));
        if (ret != 0) {
            return -5724;
        }
        if (XMEMCMP(plain, ctrPlain, sizeof(ctrPlain)))
            return -5725;

        if (XMEMCMP(cipher, ctr128Cipher, sizeof(ctr128Cipher)))
            return -5726;

        /* let's try with just 9 bytes, non block size test */
        wc_AesSetKeyDirect(&enc, ctr128Key, AES_BLOCK_SIZE,
                           ctrIv, AES_ENCRYPTION);
        /* Ctr only uses encrypt, even on key setup */
        wc_AesSetKeyDirect(&dec, ctr128Key, AES_BLOCK_SIZE,
                           ctrIv, AES_ENCRYPTION);

        ret = wc_AesCtrEncrypt(&enc, cipher, ctrPlain, sizeof(oddCipher));
        if (ret != 0) {
            return -5727;
        }
        ret = wc_AesCtrEncrypt(&dec, plain, cipher, sizeof(oddCipher));
        if (ret != 0) {
            return -5728;
        }

        if (XMEMCMP(plain, ctrPlain, sizeof(oddCipher)))
            return -5729;

        if (XMEMCMP(cipher, ctr128Cipher, sizeof(oddCipher)))
            return -5730;

        /* and an additional 9 bytes to reuse tmp left buffer */
        ret = wc_AesCtrEncrypt(&enc, cipher, ctrPlain, sizeof(oddCipher));
        if (ret != 0) {
            return -5731;
        }
        ret = wc_AesCtrEncrypt(&dec, plain, cipher, sizeof(oddCipher));
        if (ret != 0) {
            return -5732;
        }

        if (XMEMCMP(plain, ctrPlain, sizeof(oddCipher)))
            return -5733;

        if (XMEMCMP(cipher, oddCipher, sizeof(oddCipher)))
            return -5734;
#endif /* WOLFSSL_AES_128 */

#ifdef WOLFSSL_AES_192
        /* 192 bit key */
        wc_AesSetKeyDirect(&enc, ctr192Key, sizeof(ctr192Key),
                           ctrIv, AES_ENCRYPTION);
        /* Ctr only uses encrypt, even on key setup */
        wc_AesSetKeyDirect(&dec, ctr192Key, sizeof(ctr192Key),
                           ctrIv, AES_ENCRYPTION);

        XMEMSET(plain, 0, sizeof(plain));
        ret = wc_AesCtrEncrypt(&enc, plain, ctr192Cipher, sizeof(ctr192Cipher));
        if (ret != 0) {
            return -5735;
        }

        if (XMEMCMP(plain, ctrPlain, sizeof(ctr192Cipher)))
            return -5736;

        ret = wc_AesCtrEncrypt(&dec, cipher, ctrPlain, sizeof(ctrPlain));
        if (ret != 0) {
            return -5737;
        }
        if (XMEMCMP(ctr192Cipher, cipher, sizeof(ctr192Cipher)))
            return -5738;
#endif /* WOLFSSL_AES_192 */

#ifdef WOLFSSL_AES_256
        /* 256 bit key */
        wc_AesSetKeyDirect(&enc, ctr256Key, sizeof(ctr256Key),
                           ctrIv, AES_ENCRYPTION);
        /* Ctr only uses encrypt, even on key setup */
        wc_AesSetKeyDirect(&dec, ctr256Key, sizeof(ctr256Key),
                           ctrIv, AES_ENCRYPTION);

        XMEMSET(plain, 0, sizeof(plain));
        ret = wc_AesCtrEncrypt(&enc, plain, ctr256Cipher, sizeof(ctr256Cipher));
        if (ret != 0) {
            return -5739;
        }

        if (XMEMCMP(plain, ctrPlain, sizeof(ctrPlain)))
            return -5740;

        ret = wc_AesCtrEncrypt(&dec, cipher, ctrPlain, sizeof(ctrPlain));
        if (ret != 0) {
            return -5741;
        }
        if (XMEMCMP(ctr256Cipher, cipher, sizeof(ctr256Cipher)))
            return -5742;
#endif /* WOLFSSL_AES_256 */
    }
#endif /* WOLFSSL_AES_COUNTER */

#if defined(WOLFSSL_AES_DIRECT) && defined(WOLFSSL_AES_256)
    {
        const byte niPlain[] =
        {
            0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
            0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a
        };

        const byte niCipher[] =
        {
            0xf3,0xee,0xd1,0xbd,0xb5,0xd2,0xa0,0x3c,
            0x06,0x4b,0x5a,0x7e,0x3d,0xb1,0x81,0xf8
        };

        const byte niKey[] =
        {
            0x60,0x3d,0xeb,0x10,0x15,0xca,0x71,0xbe,
            0x2b,0x73,0xae,0xf0,0x85,0x7d,0x77,0x81,
            0x1f,0x35,0x2c,0x07,0x3b,0x61,0x08,0xd7,
            0x2d,0x98,0x10,0xa3,0x09,0x14,0xdf,0xf4
        };

        XMEMSET(cipher, 0, AES_BLOCK_SIZE);
        ret = wc_AesSetKey(&enc, niKey, sizeof(niKey), cipher, AES_ENCRYPTION);
        if (ret != 0)
            return -5743;
        wc_AesEncryptDirect(&enc, cipher, niPlain);
        if (XMEMCMP(cipher, niCipher, AES_BLOCK_SIZE) != 0)
            return -5744;

        XMEMSET(plain, 0, AES_BLOCK_SIZE);
        ret = wc_AesSetKey(&dec, niKey, sizeof(niKey), plain, AES_DECRYPTION);
        if (ret != 0)
            return -5745;
        wc_AesDecryptDirect(&dec, plain, niCipher);
        if (XMEMCMP(plain, niPlain, AES_BLOCK_SIZE) != 0)
            return -5746;
    }
#endif /* WOLFSSL_AES_DIRECT && WOLFSSL_AES_256 */

    ret = aes_key_size_test();
    if (ret != 0)
        return ret;

#if defined(HAVE_AES_CBC) && defined(WOLFSSL_AES_128)
    ret = aes_cbc_test();
    if (ret != 0)
        return ret;
#endif

#if defined(WOLFSSL_AES_XTS)
    #ifdef WOLFSSL_AES_128
    ret = aes_xts_128_test();
    if (ret != 0)
        return ret;
    #endif
    #ifdef WOLFSSL_AES_256
    ret = aes_xts_256_test();
    if (ret != 0)
        return ret;
    #endif
    #if defined(WOLFSSL_AES_128) && defined(WOLFSSL_AES_256)
    ret = aes_xts_sector_test();
    if (ret != 0)
        return ret;
    #endif
    #ifdef WOLFSSL_AES_128
    ret = aes_xts_args_test();
    if (ret != 0)
        return ret;
    #endif
#endif

#if defined(WOLFSSL_AES_CFB)
    ret = aescfb_test();
    if (ret != 0)
        return ret;
#if !defined(HAVE_SELFTEST) && !defined(HAVE_FIPS)
    ret = aescfb1_test();
    if (ret != 0)
        return ret;

    ret = aescfb8_test();
    if (ret != 0)
        return ret;
#endif
#endif


#if defined(HAVE_AES_CBC) || defined(WOLFSSL_AES_COUNTER)
    wc_AesFree(&enc);
    (void)cipher;
#if defined(HAVE_AES_DECRYPT) || defined(WOLFSSL_AES_COUNTER)
    wc_AesFree(&dec);
    (void)plain;
#endif
#endif

    return ret;
}

#ifdef WOLFSSL_AES_192
int aes192_test(void)
{
#ifdef HAVE_AES_CBC
    Aes enc;
    byte cipher[AES_BLOCK_SIZE];
#ifdef HAVE_AES_DECRYPT
    Aes dec;
    byte plain[AES_BLOCK_SIZE];
#endif
#endif /* HAVE_AES_CBC */
    int  ret = 0;

#ifdef HAVE_AES_CBC
    /* Test vectors from NIST Special Publication 800-38A, 2001 Edition
     * Appendix F.2.3  */

    const byte msg[] = {
        0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
        0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a
    };

    const byte verify[] =
    {
        0x4f,0x02,0x1d,0xb2,0x43,0xbc,0x63,0x3d,
        0x71,0x78,0x18,0x3a,0x9f,0xa0,0x71,0xe8
    };

    byte key[] = {
        0x8e,0x73,0xb0,0xf7,0xda,0x0e,0x64,0x52,
        0xc8,0x10,0xf3,0x2b,0x80,0x90,0x79,0xe5,
        0x62,0xf8,0xea,0xd2,0x52,0x2c,0x6b,0x7b
    };
    byte iv[]  = {
        0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
        0x08,0x09,0x0A,0x0B,0x0C,0x0D,0x0E,0x0F
    };


    if (wc_AesInit(&enc, HEAP_HINT, devId) != 0)
        return -5800;
#ifdef HAVE_AES_DECRYPT
    if (wc_AesInit(&dec, HEAP_HINT, devId) != 0)
        return -5801;
#endif

    ret = wc_AesSetKey(&enc, key, (int) sizeof(key), iv, AES_ENCRYPTION);
    if (ret != 0)
        return -5802;
#ifdef HAVE_AES_DECRYPT
    ret = wc_AesSetKey(&dec, key, (int) sizeof(key), iv, AES_DECRYPTION);
    if (ret != 0)
        return -5803;
#endif

    XMEMSET(cipher, 0, AES_BLOCK_SIZE);
    ret = wc_AesCbcEncrypt(&enc, cipher, msg, (int) sizeof(msg));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5804;
#ifdef HAVE_AES_DECRYPT
    XMEMSET(plain, 0, AES_BLOCK_SIZE);
    ret = wc_AesCbcDecrypt(&dec, plain, cipher, (int) sizeof(cipher));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &dec.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5805;
    if (XMEMCMP(plain, msg, (int) sizeof(plain))) {
        return -5806;
    }
#endif

    if (XMEMCMP(cipher, verify, (int) sizeof(cipher)))
        return -5807;

    wc_AesFree(&enc);
#ifdef HAVE_AES_DECRYPT
    wc_AesFree(&dec);
#endif

#endif /* HAVE_AES_CBC */

    return ret;
}
#endif /* WOLFSSL_AES_192 */

#ifdef WOLFSSL_AES_256
int aes256_test(void)
{
#ifdef HAVE_AES_CBC
    Aes enc;
    byte cipher[AES_BLOCK_SIZE];
#ifdef HAVE_AES_DECRYPT
    Aes dec;
    byte plain[AES_BLOCK_SIZE];
#endif
#endif /* HAVE_AES_CBC */
    int  ret = 0;

#ifdef HAVE_AES_CBC
    /* Test vectors from NIST Special Publication 800-38A, 2001 Edition,
     * Appendix F.2.5  */
    const byte msg[] = {
        0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
        0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a
    };

    const byte verify[] =
    {
        0xf5,0x8c,0x4c,0x04,0xd6,0xe5,0xf1,0xba,
        0x77,0x9e,0xab,0xfb,0x5f,0x7b,0xfb,0xd6
    };

    byte key[] = {
        0x60,0x3d,0xeb,0x10,0x15,0xca,0x71,0xbe,
        0x2b,0x73,0xae,0xf0,0x85,0x7d,0x77,0x81,
        0x1f,0x35,0x2c,0x07,0x3b,0x61,0x08,0xd7,
        0x2d,0x98,0x10,0xa3,0x09,0x14,0xdf,0xf4
    };
    byte iv[]  = {
        0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
        0x08,0x09,0x0A,0x0B,0x0C,0x0D,0x0E,0x0F
    };


    if (wc_AesInit(&enc, HEAP_HINT, devId) != 0)
        return -5900;
#ifdef HAVE_AES_DECRYPT
    if (wc_AesInit(&dec, HEAP_HINT, devId) != 0)
        return -5901;
#endif

    ret = wc_AesSetKey(&enc, key, (int) sizeof(key), iv, AES_ENCRYPTION);
    if (ret != 0)
        return -5902;
#ifdef HAVE_AES_DECRYPT
    ret = wc_AesSetKey(&dec, key, (int) sizeof(key), iv, AES_DECRYPTION);
    if (ret != 0)
        return -5903;
#endif

    XMEMSET(cipher, 0, AES_BLOCK_SIZE);
    ret = wc_AesCbcEncrypt(&enc, cipher, msg, (int) sizeof(msg));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5904;
#ifdef HAVE_AES_DECRYPT
    XMEMSET(plain, 0, AES_BLOCK_SIZE);
    ret = wc_AesCbcDecrypt(&dec, plain, cipher, (int) sizeof(cipher));
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &dec.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        return -5905;
    if (XMEMCMP(plain, msg, (int) sizeof(plain))) {
        return -5906;
    }
#endif

    if (XMEMCMP(cipher, verify, (int) sizeof(cipher)))
        return -5907;

    wc_AesFree(&enc);
#ifdef HAVE_AES_DECRYPT
    wc_AesFree(&dec);
#endif

#endif /* HAVE_AES_CBC */

    return ret;
}
#endif /* WOLFSSL_AES_256 */


#ifdef HAVE_AESGCM

static int aesgcm_default_test_helper(byte* key, int keySz, byte* iv, int ivSz,
		byte* plain, int plainSz, byte* cipher, int cipherSz,
		byte* aad, int aadSz, byte* tag, int tagSz)
{
    Aes enc;
    Aes dec;

    byte resultT[AES_BLOCK_SIZE];
    byte resultP[AES_BLOCK_SIZE * 3];
    byte resultC[AES_BLOCK_SIZE * 3];
    int  result;

    XMEMSET(resultT, 0, sizeof(resultT));
    XMEMSET(resultC, 0, sizeof(resultC));
    XMEMSET(resultP, 0, sizeof(resultP));

    if (wc_AesInit(&enc, HEAP_HINT, devId) != 0) {
        return -5908;
    }
    if (wc_AesInit(&dec, HEAP_HINT, devId) != 0) {
        return -5909;
    }

    result = wc_AesGcmSetKey(&enc, key, keySz);
    if (result != 0)
        return -5910;

    /* AES-GCM encrypt and decrypt both use AES encrypt internally */
    result = wc_AesGcmEncrypt(&enc, resultC, plain, plainSz, iv, ivSz,
                                        resultT, tagSz, aad, aadSz);

#if defined(WOLFSSL_ASYNC_CRYPT)
    result = wc_AsyncWait(result, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (result != 0)
        return -5911;
    if (cipher != NULL) {
        if (XMEMCMP(cipher, resultC, cipherSz))
            return -5912;
    }
    if (XMEMCMP(tag, resultT, tagSz))
        return -5913;

    wc_AesFree(&enc);

#ifdef HAVE_AES_DECRYPT
    result = wc_AesGcmSetKey(&dec, key, keySz);
    if (result != 0)
        return -5914;

    result = wc_AesGcmDecrypt(&dec, resultP, resultC, cipherSz,
                      iv, ivSz, resultT, tagSz, aad, aadSz);
#if defined(WOLFSSL_ASYNC_CRYPT)
    result = wc_AsyncWait(result, &dec.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (result != 0)
        return -5915;
    if (plain != NULL) {
        if (XMEMCMP(plain, resultP, plainSz))
            return -5916;
    }

    wc_AesFree(&dec);
#endif /* HAVE_AES_DECRYPT */

    return 0;
}


/* tests that only use 12 byte IV and 16 or less byte AAD
 * test vectors are from NIST SP 800-38D
 * https://csrc.nist.gov/Projects/Cryptographic-Algorithm-Validation-Program/CAVP-TESTING-BLOCK-CIPHER-MODES*/
int aesgcm_default_test(void)
{
    byte key1[] = {
        0x29, 0x8e, 0xfa, 0x1c, 0xcf, 0x29, 0xcf, 0x62,
        0xae, 0x68, 0x24, 0xbf, 0xc1, 0x95, 0x57, 0xfc
    };

    byte iv1[] = {
        0x6f, 0x58, 0xa9, 0x3f, 0xe1, 0xd2, 0x07, 0xfa,
        0xe4, 0xed, 0x2f, 0x6d
    };

    ALIGN64 byte plain1[] = {
        0xcc, 0x38, 0xbc, 0xcd, 0x6b, 0xc5, 0x36, 0xad,
        0x91, 0x9b, 0x13, 0x95, 0xf5, 0xd6, 0x38, 0x01,
        0xf9, 0x9f, 0x80, 0x68, 0xd6, 0x5c, 0xa5, 0xac,
        0x63, 0x87, 0x2d, 0xaf, 0x16, 0xb9, 0x39, 0x01
    };

    byte aad1[] = {
        0x02, 0x1f, 0xaf, 0xd2, 0x38, 0x46, 0x39, 0x73,
        0xff, 0xe8, 0x02, 0x56, 0xe5, 0xb1, 0xc6, 0xb1
    };

    ALIGN64 byte cipher1[] = {
        0xdf, 0xce, 0x4e, 0x9c, 0xd2, 0x91, 0x10, 0x3d,
        0x7f, 0xe4, 0xe6, 0x33, 0x51, 0xd9, 0xe7, 0x9d,
        0x3d, 0xfd, 0x39, 0x1e, 0x32, 0x67, 0x10, 0x46,
        0x58, 0x21, 0x2d, 0xa9, 0x65, 0x21, 0xb7, 0xdb
    };

    byte tag1[] = {
        0x54, 0x24, 0x65, 0xef, 0x59, 0x93, 0x16, 0xf7,
        0x3a, 0x7a, 0x56, 0x05, 0x09, 0xa2, 0xd9, 0xf2
    };

    byte key2[] = {
        0x01, 0x6d, 0xbb, 0x38, 0xda, 0xa7, 0x6d, 0xfe,
        0x7d, 0xa3, 0x84, 0xeb, 0xf1, 0x24, 0x03, 0x64
    };

    byte iv2[] = {
        0x07, 0x93, 0xef, 0x3a, 0xda, 0x78, 0x2f, 0x78,
        0xc9, 0x8a, 0xff, 0xe3
    };

    ALIGN64 byte plain2[] = {
        0x4b, 0x34, 0xa9, 0xec, 0x57, 0x63, 0x52, 0x4b,
        0x19, 0x1d, 0x56, 0x16, 0xc5, 0x47, 0xf6, 0xb7
    };

    ALIGN64 byte cipher2[] = {
        0x60, 0x9a, 0xa3, 0xf4, 0x54, 0x1b, 0xc0, 0xfe,
        0x99, 0x31, 0xda, 0xad, 0x2e, 0xe1, 0x5d, 0x0c
    };

    byte tag2[] = {
        0x33, 0xaf, 0xec, 0x59, 0xc4, 0x5b, 0xaf, 0x68,
        0x9a, 0x5e, 0x1b, 0x13, 0xae, 0x42, 0x36, 0x19
    };

    byte key3[] = {
        0xb0, 0x1e, 0x45, 0xcc, 0x30, 0x88, 0xaa, 0xba,
        0x9f, 0xa4, 0x3d, 0x81, 0xd4, 0x81, 0x82, 0x3f
    };

    byte iv3[] = {
        0x5a, 0x2c, 0x4a, 0x66, 0x46, 0x87, 0x13, 0x45,
        0x6a, 0x4b, 0xd5, 0xe1
    };

    byte tag3[] = {
        0x01, 0x42, 0x80, 0xf9, 0x44, 0xf5, 0x3c, 0x68,
        0x11, 0x64, 0xb2, 0xff
    };

    int ret;
	ret = aesgcm_default_test_helper(key1, sizeof(key1), iv1, sizeof(iv1),
		plain1, sizeof(plain1), cipher1, sizeof(cipher1),
		aad1, sizeof(aad1), tag1, sizeof(tag1));
	if (ret != 0) {
		return ret;
	}
	ret = aesgcm_default_test_helper(key2, sizeof(key2), iv2, sizeof(iv2),
		plain2, sizeof(plain2), cipher2, sizeof(cipher2),
		NULL, 0, tag2, sizeof(tag2));
	if (ret != 0) {
		return ret;
	}
	ret = aesgcm_default_test_helper(key3, sizeof(key3), iv3, sizeof(iv3),
		NULL, 0, NULL, 0,
		NULL, 0, tag3, sizeof(tag3));
	if (ret != 0) {
		return ret;
	}

	return 0;
}

int aesgcm_test(void)
{
    Aes enc;
    Aes dec;

    /*
     * This is Test Case 16 from the document Galois/
     * Counter Mode of Operation (GCM) by McGrew and
     * Viega.
     */
    const byte p[] =
    {
        0xd9, 0x31, 0x32, 0x25, 0xf8, 0x84, 0x06, 0xe5,
        0xa5, 0x59, 0x09, 0xc5, 0xaf, 0xf5, 0x26, 0x9a,
        0x86, 0xa7, 0xa9, 0x53, 0x15, 0x34, 0xf7, 0xda,
        0x2e, 0x4c, 0x30, 0x3d, 0x8a, 0x31, 0x8a, 0x72,
        0x1c, 0x3c, 0x0c, 0x95, 0x95, 0x68, 0x09, 0x53,
        0x2f, 0xcf, 0x0e, 0x24, 0x49, 0xa6, 0xb5, 0x25,
        0xb1, 0x6a, 0xed, 0xf5, 0xaa, 0x0d, 0xe6, 0x57,
        0xba, 0x63, 0x7b, 0x39
    };

#if defined(WOLFSSL_AES_256)
    const byte a[] =
    {
        0xfe, 0xed, 0xfa, 0xce, 0xde, 0xad, 0xbe, 0xef,
        0xfe, 0xed, 0xfa, 0xce, 0xde, 0xad, 0xbe, 0xef,
        0xab, 0xad, 0xda, 0xd2
    };
#endif

#ifdef WOLFSSL_AES_256
    const byte k1[] =
    {
        0xfe, 0xff, 0xe9, 0x92, 0x86, 0x65, 0x73, 0x1c,
        0x6d, 0x6a, 0x8f, 0x94, 0x67, 0x30, 0x83, 0x08,
        0xfe, 0xff, 0xe9, 0x92, 0x86, 0x65, 0x73, 0x1c,
        0x6d, 0x6a, 0x8f, 0x94, 0x67, 0x30, 0x83, 0x08
    };

    const byte iv1[] =
    {
        0xca, 0xfe, 0xba, 0xbe, 0xfa, 0xce, 0xdb, 0xad,
        0xde, 0xca, 0xf8, 0x88
    };

    const byte c1[] =
    {
        0x52, 0x2d, 0xc1, 0xf0, 0x99, 0x56, 0x7d, 0x07,
        0xf4, 0x7f, 0x37, 0xa3, 0x2a, 0x84, 0x42, 0x7d,
        0x64, 0x3a, 0x8c, 0xdc, 0xbf, 0xe5, 0xc0, 0xc9,
        0x75, 0x98, 0xa2, 0xbd, 0x25, 0x55, 0xd1, 0xaa,
        0x8c, 0xb0, 0x8e, 0x48, 0x59, 0x0d, 0xbb, 0x3d,
        0xa7, 0xb0, 0x8b, 0x10, 0x56, 0x82, 0x88, 0x38,
        0xc5, 0xf6, 0x1e, 0x63, 0x93, 0xba, 0x7a, 0x0a,
        0xbc, 0xc9, 0xf6, 0x62
    };
#endif /* WOLFSSL_AES_256 */

    const byte t1[] =
    {
        0x76, 0xfc, 0x6e, 0xce, 0x0f, 0x4e, 0x17, 0x68,
        0xcd, 0xdf, 0x88, 0x53, 0xbb, 0x2d, 0x55, 0x1b
    };

    /* FIPS, QAT and PIC32MZ HW Crypto only support 12-byte IV */
#if !defined(HAVE_FIPS) && \
        !defined(WOLFSSL_PIC32MZ_CRYPT) && \
        !defined(FREESCALE_LTC) && !defined(FREESCALE_MMCAU) && \
        !defined(WOLFSSL_XILINX_CRYPT) && !defined(WOLFSSL_AFALG_XILINX_AES) && \
        !(defined(WOLF_CRYPTO_CB) && \
            (defined(HAVE_INTEL_QA_SYNC) || defined(HAVE_CAVIUM_OCTEON_SYNC)))

    #define ENABLE_NON_12BYTE_IV_TEST
#ifdef WOLFSSL_AES_192
    /* Test Case 12, uses same plaintext and AAD data. */
    const byte k2[] =
    {
        0xfe, 0xff, 0xe9, 0x92, 0x86, 0x65, 0x73, 0x1c,
        0x6d, 0x6a, 0x8f, 0x94, 0x67, 0x30, 0x83, 0x08,
        0xfe, 0xff, 0xe9, 0x92, 0x86, 0x65, 0x73, 0x1c
    };

    const byte iv2[] =
    {
        0x93, 0x13, 0x22, 0x5d, 0xf8, 0x84, 0x06, 0xe5,
        0x55, 0x90, 0x9c, 0x5a, 0xff, 0x52, 0x69, 0xaa,
        0x6a, 0x7a, 0x95, 0x38, 0x53, 0x4f, 0x7d, 0xa1,
        0xe4, 0xc3, 0x03, 0xd2, 0xa3, 0x18, 0xa7, 0x28,
        0xc3, 0xc0, 0xc9, 0x51, 0x56, 0x80, 0x95, 0x39,
        0xfc, 0xf0, 0xe2, 0x42, 0x9a, 0x6b, 0x52, 0x54,
        0x16, 0xae, 0xdb, 0xf5, 0xa0, 0xde, 0x6a, 0x57,
        0xa6, 0x37, 0xb3, 0x9b
    };

    const byte c2[] =
    {
        0xd2, 0x7e, 0x88, 0x68, 0x1c, 0xe3, 0x24, 0x3c,
        0x48, 0x30, 0x16, 0x5a, 0x8f, 0xdc, 0xf9, 0xff,
        0x1d, 0xe9, 0xa1, 0xd8, 0xe6, 0xb4, 0x47, 0xef,
        0x6e, 0xf7, 0xb7, 0x98, 0x28, 0x66, 0x6e, 0x45,
        0x81, 0xe7, 0x90, 0x12, 0xaf, 0x34, 0xdd, 0xd9,
        0xe2, 0xf0, 0x37, 0x58, 0x9b, 0x29, 0x2d, 0xb3,
        0xe6, 0x7c, 0x03, 0x67, 0x45, 0xfa, 0x22, 0xe7,
        0xe9, 0xb7, 0x37, 0x3b
    };

    const byte t2[] =
    {
        0xdc, 0xf5, 0x66, 0xff, 0x29, 0x1c, 0x25, 0xbb,
        0xb8, 0x56, 0x8f, 0xc3, 0xd3, 0x76, 0xa6, 0xd9
    };
#endif /* WOLFSSL_AES_192 */
#ifdef WOLFSSL_AES_128
    /* The following is an interesting test case from the example
     * FIPS test vectors for AES-GCM. IVlen = 1 byte */
    const byte p3[] =
    {
        0x57, 0xce, 0x45, 0x1f, 0xa5, 0xe2, 0x35, 0xa5,
        0x8e, 0x1a, 0xa2, 0x3b, 0x77, 0xcb, 0xaf, 0xe2
    };

    const byte k3[] =
    {
        0xbb, 0x01, 0xd7, 0x03, 0x81, 0x1c, 0x10, 0x1a,
        0x35, 0xe0, 0xff, 0xd2, 0x91, 0xba, 0xf2, 0x4b
    };

    const byte iv3[] =
    {
        0xca
    };

    const byte c3[] =
    {
        0x6b, 0x5f, 0xb3, 0x9d, 0xc1, 0xc5, 0x7a, 0x4f,
        0xf3, 0x51, 0x4d, 0xc2, 0xd5, 0xf0, 0xd0, 0x07
    };

    const byte a3[] =
    {
        0x40, 0xfc, 0xdc, 0xd7, 0x4a, 0xd7, 0x8b, 0xf1,
        0x3e, 0x7c, 0x60, 0x55, 0x50, 0x51, 0xdd, 0x54
    };

    const byte t3[] =
    {
        0x06, 0x90, 0xed, 0x01, 0x34, 0xdd, 0xc6, 0x95,
        0x31, 0x2e, 0x2a, 0xf9, 0x57, 0x7a, 0x1e, 0xa6
    };
#endif /* WOLFSSL_AES_128 */
#ifdef WOLFSSL_AES_256
    int ivlen;
#endif
#endif

    byte resultT[sizeof(t1)];
    byte resultP[sizeof(p) + AES_BLOCK_SIZE];
    byte resultC[sizeof(p) + AES_BLOCK_SIZE];
    int  result = 0;
#ifdef WOLFSSL_AES_256
    int  alen;
    #if !defined(WOLFSSL_AFALG_XILINX_AES) && !defined(WOLFSSL_XILINX_CRYPT)
    int  plen;
    #endif
#endif

#if !defined(BENCH_EMBEDDED)
    #ifndef BENCH_AESGCM_LARGE
        #define BENCH_AESGCM_LARGE 1024
    #endif
    byte large_input[BENCH_AESGCM_LARGE];
    byte large_output[BENCH_AESGCM_LARGE + AES_BLOCK_SIZE];
    byte large_outdec[BENCH_AESGCM_LARGE];

    XMEMSET(large_input, 0, sizeof(large_input));
    XMEMSET(large_output, 0, sizeof(large_output));
    XMEMSET(large_outdec, 0, sizeof(large_outdec));
#endif

    (void)result;

    XMEMSET(resultT, 0, sizeof(resultT));
    XMEMSET(resultC, 0, sizeof(resultC));
    XMEMSET(resultP, 0, sizeof(resultP));

    if (wc_AesInit(&enc, HEAP_HINT, devId) != 0) {
        return -6100;
    }
    if (wc_AesInit(&dec, HEAP_HINT, devId) != 0) {
        return -6101;
    }

#ifdef WOLFSSL_AES_256
    result = wc_AesGcmSetKey(&enc, k1, sizeof(k1));
    if (result != 0)
        return -6102;

    /* AES-GCM encrypt and decrypt both use AES encrypt internally */
    result = wc_AesGcmEncrypt(&enc, resultC, p, sizeof(p), iv1, sizeof(iv1),
                                        resultT, sizeof(resultT), a, sizeof(a));
#if defined(WOLFSSL_ASYNC_CRYPT)
    result = wc_AsyncWait(result, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (result != 0)
        return -6103;
    if (XMEMCMP(c1, resultC, sizeof(c1)))
        return -6104;
    if (XMEMCMP(t1, resultT, sizeof(resultT)))
        return -6105;

#ifdef HAVE_AES_DECRYPT
    result = wc_AesGcmSetKey(&dec, k1, sizeof(k1));
    if (result != 0)
        return -6106;

    result = wc_AesGcmDecrypt(&dec, resultP, resultC, sizeof(c1),
                      iv1, sizeof(iv1), resultT, sizeof(resultT), a, sizeof(a));
#if defined(WOLFSSL_ASYNC_CRYPT)
    result = wc_AsyncWait(result, &dec.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (result != 0)
        return -6107;
    if (XMEMCMP(p, resultP, sizeof(p)))
        return -6108;
#endif /* HAVE_AES_DECRYPT */

    /* Large buffer test */
#ifdef BENCH_AESGCM_LARGE
    /* setup test buffer */
    for (alen=0; alen<BENCH_AESGCM_LARGE; alen++)
        large_input[alen] = (byte)alen;

    /* AES-GCM encrypt and decrypt both use AES encrypt internally */
    result = wc_AesGcmEncrypt(&enc, large_output, large_input,
                              BENCH_AESGCM_LARGE, iv1, sizeof(iv1),
                              resultT, sizeof(resultT), a, sizeof(a));
#if defined(WOLFSSL_ASYNC_CRYPT)
    result = wc_AsyncWait(result, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (result != 0)
        return -6109;

#ifdef HAVE_AES_DECRYPT
    result = wc_AesGcmDecrypt(&dec, large_outdec, large_output,
                              BENCH_AESGCM_LARGE, iv1, sizeof(iv1), resultT,
                              sizeof(resultT), a, sizeof(a));
#if defined(WOLFSSL_ASYNC_CRYPT)
    result = wc_AsyncWait(result, &dec.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (result != 0)
        return -6110;
    if (XMEMCMP(large_input, large_outdec, BENCH_AESGCM_LARGE))
        return -6111;
#endif /* HAVE_AES_DECRYPT */
#endif /* BENCH_AESGCM_LARGE */
#if defined(ENABLE_NON_12BYTE_IV_TEST) && defined(WOLFSSL_AES_256)
    /* Variable IV length test */
    for (ivlen=1; ivlen<(int)sizeof(k1); ivlen++) {
         /* AES-GCM encrypt and decrypt both use AES encrypt internally */
         result = wc_AesGcmEncrypt(&enc, resultC, p, sizeof(p), k1,
                         (word32)ivlen, resultT, sizeof(resultT), a, sizeof(a));
#if defined(WOLFSSL_ASYNC_CRYPT)
        result = wc_AsyncWait(result, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
        if (result != 0)
            return -6112;
#ifdef HAVE_AES_DECRYPT
        result = wc_AesGcmDecrypt(&dec, resultP, resultC, sizeof(c1), k1,
                         (word32)ivlen, resultT, sizeof(resultT), a, sizeof(a));
#if defined(WOLFSSL_ASYNC_CRYPT)
        result = wc_AsyncWait(result, &dec.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
        if (result != 0)
            return -6113;
#endif /* HAVE_AES_DECRYPT */
    }
#endif

#if !(defined(WOLF_CRYPTO_CB) && defined(HAVE_INTEL_QA_SYNC))
    /* Variable authenticated data length test */
    for (alen=0; alen<(int)sizeof(p); alen++) {
         /* AES-GCM encrypt and decrypt both use AES encrypt internally */
         result = wc_AesGcmEncrypt(&enc, resultC, p, sizeof(p), iv1,
                        sizeof(iv1), resultT, sizeof(resultT), p, (word32)alen);
#if defined(WOLFSSL_ASYNC_CRYPT)
        result = wc_AsyncWait(result, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
        if (result != 0)
            return -6114;
#ifdef HAVE_AES_DECRYPT
        result = wc_AesGcmDecrypt(&dec, resultP, resultC, sizeof(c1), iv1,
                        sizeof(iv1), resultT, sizeof(resultT), p, (word32)alen);
#if defined(WOLFSSL_ASYNC_CRYPT)
        result = wc_AsyncWait(result, &dec.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
        if (result != 0)
            return -6115;
#endif /* HAVE_AES_DECRYPT */
    }
#endif

#if !defined(WOLFSSL_AFALG_XILINX_AES) && !defined(WOLFSSL_XILINX_CRYPT)
#ifdef BENCH_AESGCM_LARGE
    /* Variable plain text length test */
    for (plen=1; plen<BENCH_AESGCM_LARGE; plen++) {
        /* AES-GCM encrypt and decrypt both use AES encrypt internally */
        result = wc_AesGcmEncrypt(&enc, large_output, large_input,
                                  plen, iv1, sizeof(iv1), resultT,
                                  sizeof(resultT), a, sizeof(a));
#if defined(WOLFSSL_ASYNC_CRYPT)
        result = wc_AsyncWait(result, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
        if (result != 0)
            return -6116;

#ifdef HAVE_AES_DECRYPT
        result = wc_AesGcmDecrypt(&dec, large_outdec, large_output,
                                  plen, iv1, sizeof(iv1), resultT,
                                  sizeof(resultT), a, sizeof(a));
#if defined(WOLFSSL_ASYNC_CRYPT)
        result = wc_AsyncWait(result, &dec.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
        if (result != 0)
            return -6117;
#endif /* HAVE_AES_DECRYPT */
    }
#else /* BENCH_AESGCM_LARGE */
    /* Variable plain text length test */
    for (plen=1; plen<(int)sizeof(p); plen++) {
         /* AES-GCM encrypt and decrypt both use AES encrypt internally */
         result = wc_AesGcmEncrypt(&enc, resultC, p, (word32)plen, iv1,
                           sizeof(iv1), resultT, sizeof(resultT), a, sizeof(a));
#if defined(WOLFSSL_ASYNC_CRYPT)
        result = wc_AsyncWait(result, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
        if (result != 0)
            return -6118;
#ifdef HAVE_AES_DECRYPT
        result = wc_AesGcmDecrypt(&dec, resultP, resultC, (word32)plen, iv1,
                           sizeof(iv1), resultT, sizeof(resultT), a, sizeof(a));
#if defined(WOLFSSL_ASYNC_CRYPT)
        result = wc_AsyncWait(result, &dec.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
        if (result != 0)
            return -6119;
#endif /* HAVE_AES_DECRYPT */
    }
#endif /* BENCH_AESGCM_LARGE */
#endif
#endif /* WOLFSSL_AES_256 */

    /* test with IV != 12 bytes */
#ifdef ENABLE_NON_12BYTE_IV_TEST
    XMEMSET(resultT, 0, sizeof(resultT));
    XMEMSET(resultC, 0, sizeof(resultC));
    XMEMSET(resultP, 0, sizeof(resultP));

#ifdef WOLFSSL_AES_192
    wc_AesGcmSetKey(&enc, k2, sizeof(k2));
    /* AES-GCM encrypt and decrypt both use AES encrypt internally */
    result = wc_AesGcmEncrypt(&enc, resultC, p, sizeof(p), iv2, sizeof(iv2),
                                        resultT, sizeof(resultT), a, sizeof(a));
#if defined(WOLFSSL_ASYNC_CRYPT)
    result = wc_AsyncWait(result, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (result != 0)
        return -6120;
    if (XMEMCMP(c2, resultC, sizeof(c2)))
        return -6121;
    if (XMEMCMP(t2, resultT, sizeof(resultT)))
        return -6122;

#ifdef HAVE_AES_DECRYPT
    result = wc_AesGcmDecrypt(&enc, resultP, resultC, sizeof(c1),
                      iv2, sizeof(iv2), resultT, sizeof(resultT), a, sizeof(a));
#if defined(WOLFSSL_ASYNC_CRYPT)
    result = wc_AsyncWait(result, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (result != 0)
        return -6123;
    if (XMEMCMP(p, resultP, sizeof(p)))
        return -6124;
#endif /* HAVE_AES_DECRYPT */

    XMEMSET(resultT, 0, sizeof(resultT));
    XMEMSET(resultC, 0, sizeof(resultC));
    XMEMSET(resultP, 0, sizeof(resultP));
#endif /* WOLFSSL_AES_192 */
#ifdef WOLFSSL_AES_128
    wc_AesGcmSetKey(&enc, k3, sizeof(k3));
    /* AES-GCM encrypt and decrypt both use AES encrypt internally */
    result = wc_AesGcmEncrypt(&enc, resultC, p3, sizeof(p3), iv3, sizeof(iv3),
                                        resultT, sizeof(t3), a3, sizeof(a3));
#if defined(WOLFSSL_ASYNC_CRYPT)
    result = wc_AsyncWait(result, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (result != 0)
        return -6125;
    if (XMEMCMP(c3, resultC, sizeof(c3)))
        return -6126;
    if (XMEMCMP(t3, resultT, sizeof(t3)))
        return -6127;

#ifdef HAVE_AES_DECRYPT
    result = wc_AesGcmDecrypt(&enc, resultP, resultC, sizeof(c3),
                      iv3, sizeof(iv3), resultT, sizeof(t3), a3, sizeof(a3));
#if defined(WOLFSSL_ASYNC_CRYPT)
    result = wc_AsyncWait(result, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (result != 0)
        return -6128;
    if (XMEMCMP(p3, resultP, sizeof(p3)))
        return -6129;
#endif /* HAVE_AES_DECRYPT */
#endif /* WOLFSSL_AES_128 */
#endif /* ENABLE_NON_12BYTE_IV_TEST */

#if defined(WOLFSSL_AES_256) && !defined(WOLFSSL_AFALG_XILINX_AES) && \
    !defined(WOLFSSL_XILINX_CRYPT) && \
    !(defined(WOLF_CRYPTO_CB) && \
        defined(HAVE_INTEL_QA_SYNC) || defined(HAVE_CAVIUM_OCTEON_SYNC))
    XMEMSET(resultT, 0, sizeof(resultT));
    XMEMSET(resultC, 0, sizeof(resultC));
    XMEMSET(resultP, 0, sizeof(resultP));

    wc_AesGcmSetKey(&enc, k1, sizeof(k1));
    /* AES-GCM encrypt and decrypt both use AES encrypt internally */
    result = wc_AesGcmEncrypt(&enc, resultC, p, sizeof(p), iv1, sizeof(iv1),
                                resultT + 1, sizeof(resultT) - 1, a, sizeof(a));
#if defined(WOLFSSL_ASYNC_CRYPT)
    result = wc_AsyncWait(result, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (result != 0)
        return -6130;
    if (XMEMCMP(c1, resultC, sizeof(c1)))
        return -6131;
    if (XMEMCMP(t1, resultT + 1, sizeof(resultT) - 1))
        return -6132;

#ifdef HAVE_AES_DECRYPT
    result = wc_AesGcmDecrypt(&enc, resultP, resultC, sizeof(p),
              iv1, sizeof(iv1), resultT + 1, sizeof(resultT) - 1, a, sizeof(a));
#if defined(WOLFSSL_ASYNC_CRYPT)
    result = wc_AsyncWait(result, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (result != 0)
        return -6133;
    if (XMEMCMP(p, resultP, sizeof(p)))
        return -6134;
#endif /* HAVE_AES_DECRYPT */
#endif /* WOLFSSL_AES_256 */

#if !defined(HAVE_FIPS) || \
    (defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2))
    /* Test encrypt with internally generated IV */
#if defined(WOLFSSL_AES_256) && !(defined(WC_NO_RNG) || defined(HAVE_SELFTEST)) \
    && !(defined(WOLF_CRYPTO_CB) && defined(HAVE_CAVIUM_OCTEON_SYNC))
    {
        WC_RNG rng;
        byte randIV[12];

        result = wc_InitRng_ex(&rng, HEAP_HINT, devId);
        if (result != 0)
            return -6135;

        XMEMSET(randIV, 0, sizeof(randIV));
        XMEMSET(resultT, 0, sizeof(resultT));
        XMEMSET(resultC, 0, sizeof(resultC));
        XMEMSET(resultP, 0, sizeof(resultP));

        wc_AesGcmSetKey(&enc, k1, sizeof(k1));
        result = wc_AesGcmSetIV(&enc, sizeof(randIV), NULL, 0, &rng);
        if (result != 0)
            return -6136;

        result = wc_AesGcmEncrypt_ex(&enc,
                        resultC, p, sizeof(p),
                        randIV, sizeof(randIV),
                        resultT, sizeof(resultT),
                        a, sizeof(a));
    #if defined(WOLFSSL_ASYNC_CRYPT)
        result = wc_AsyncWait(result, &enc.asyncDev, WC_ASYNC_FLAG_NONE);
    #endif
        if (result != 0)
            return -6137;

        /* Check the IV has been set. */
        {
            word32 i, ivSum = 0;

            for (i = 0; i < sizeof(randIV); i++)
                ivSum += randIV[i];
            if (ivSum == 0)
                return -6138;
        }

#ifdef HAVE_AES_DECRYPT
        wc_AesGcmSetKey(&dec, k1, sizeof(k1));
        result = wc_AesGcmSetIV(&dec, sizeof(randIV), NULL, 0, &rng);
        if (result != 0)
            return -6139;

        result = wc_AesGcmDecrypt(&dec,
                          resultP, resultC, sizeof(c1),
                          randIV, sizeof(randIV),
                          resultT, sizeof(resultT),
                          a, sizeof(a));
#if defined(WOLFSSL_ASYNC_CRYPT)
        result = wc_AsyncWait(result, &dec.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
        if (result != 0)
            return -6140;
        if (XMEMCMP(p, resultP, sizeof(p)))
            return -6141;
#endif /* HAVE_AES_DECRYPT */

        wc_FreeRng(&rng);
    }
#endif /* WOLFSSL_AES_256 && !(WC_NO_RNG || HAVE_SELFTEST) */
#endif /* HAVE_FIPS_VERSION >= 2 */

    wc_AesFree(&enc);
    wc_AesFree(&dec);

    return 0;
}

#ifdef WOLFSSL_AES_128
int gmac_test(void)
{
    Gmac gmac;

    const byte k1[] =
    {
        0x89, 0xc9, 0x49, 0xe9, 0xc8, 0x04, 0xaf, 0x01,
        0x4d, 0x56, 0x04, 0xb3, 0x94, 0x59, 0xf2, 0xc8
    };
    const byte iv1[] =
    {
        0xd1, 0xb1, 0x04, 0xc8, 0x15, 0xbf, 0x1e, 0x94,
        0xe2, 0x8c, 0x8f, 0x16
    };
    const byte a1[] =
    {
       0x82, 0xad, 0xcd, 0x63, 0x8d, 0x3f, 0xa9, 0xd9,
       0xf3, 0xe8, 0x41, 0x00, 0xd6, 0x1e, 0x07, 0x77
    };
    const byte t1[] =
    {
        0x88, 0xdb, 0x9d, 0x62, 0x17, 0x2e, 0xd0, 0x43,
        0xaa, 0x10, 0xf1, 0x6d, 0x22, 0x7d, 0xc4, 0x1b
    };

#if !defined(HAVE_FIPS) || \
    (defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2))
	/* FIPS builds only allow 16-byte auth tags. */
	/* This sample uses a 15-byte auth tag. */
    const byte k2[] =
    {
        0x40, 0xf7, 0xec, 0xb2, 0x52, 0x6d, 0xaa, 0xd4,
        0x74, 0x25, 0x1d, 0xf4, 0x88, 0x9e, 0xf6, 0x5b
    };
    const byte iv2[] =
    {
        0xee, 0x9c, 0x6e, 0x06, 0x15, 0x45, 0x45, 0x03,
        0x1a, 0x60, 0x24, 0xa7
    };
    const byte a2[] =
    {
        0x94, 0x81, 0x2c, 0x87, 0x07, 0x4e, 0x15, 0x18,
        0x34, 0xb8, 0x35, 0xaf, 0x1c, 0xa5, 0x7e, 0x56
    };
    const byte t2[] =
    {
        0xc6, 0x81, 0x79, 0x8e, 0x3d, 0xda, 0xb0, 0x9f,
        0x8d, 0x83, 0xb0, 0xbb, 0x14, 0xb6, 0x91
    };
#endif

    byte tag[16];

    XMEMSET(&gmac, 0, sizeof(Gmac)); /* clear context */
    (void)wc_AesInit((Aes*)&gmac, HEAP_HINT, INVALID_DEVID); /* Make sure devId updated */
    XMEMSET(tag, 0, sizeof(tag));
    wc_GmacSetKey(&gmac, k1, sizeof(k1));
    wc_GmacUpdate(&gmac, iv1, sizeof(iv1), a1, sizeof(a1), tag, sizeof(t1));
    if (XMEMCMP(t1, tag, sizeof(t1)) != 0)
        return -6200;

#if !defined(HAVE_FIPS) || \
    (defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2))
    XMEMSET(tag, 0, sizeof(tag));
    wc_GmacSetKey(&gmac, k2, sizeof(k2));
    wc_GmacUpdate(&gmac, iv2, sizeof(iv2), a2, sizeof(a2), tag, sizeof(t2));
    if (XMEMCMP(t2, tag, sizeof(t2)) != 0)
        return -6201;

#if !defined(WC_NO_RNG) && !defined(HAVE_SELFTEST) && !defined(NO_AES_DECRYPT)
    {
        const byte badT[] =
        {
            0xde, 0xad, 0xbe, 0xef, 0x17, 0x2e, 0xd0, 0x43,
            0xaa, 0x10, 0xf1, 0x6d, 0x22, 0x7d, 0xc4, 0x1b
        };

        WC_RNG rng;
        byte iv[12];

        #ifndef HAVE_FIPS
            if (wc_InitRng_ex(&rng, HEAP_HINT, devId) != 0)
                return -6202;
        #else
            if (wc_InitRng(&rng) != 0)
                return -6203;
        #endif

        if (wc_GmacVerify(k1, sizeof(k1), iv1, sizeof(iv1), a1, sizeof(a1),
                    t1, sizeof(t1)) != 0)
            return -6204;
        if (wc_GmacVerify(k1, sizeof(k1), iv1, sizeof(iv1), a1, sizeof(a1),
                    badT, sizeof(badT)) != AES_GCM_AUTH_E)
            return -6205;
        if (wc_GmacVerify(k2, sizeof(k2), iv2, sizeof(iv2), a2, sizeof(a2),
                    t2, sizeof(t2)) != 0)
            return -6206;

        XMEMSET(tag, 0, sizeof(tag));
        XMEMSET(iv, 0, sizeof(iv));
        if (wc_Gmac(k1, sizeof(k1), iv, sizeof(iv), a1, sizeof(a1),
                    tag, sizeof(tag), &rng) != 0)
            return -6207;
        if (wc_GmacVerify(k1, sizeof(k1), iv, sizeof(iv), a1, sizeof(a1),
                    tag, sizeof(tag)) != 0)
            return -6208;
        wc_FreeRng(&rng);
    }
#endif /* !WC_NO_RNG && !HAVE_SELFTEST && !NO_AES_DECRYPT */
#endif /* HAVE_FIPS */

    return 0;
}
#endif /* WOLFSSL_AES_128 */
#endif /* HAVE_AESGCM */

#if defined(HAVE_AESCCM) && defined(WOLFSSL_AES_128)
int aesccm_test(void)
{
    Aes enc;

    /* key */
    const byte k[] =
    {
        0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7,
        0xc8, 0xc9, 0xca, 0xcb, 0xcc, 0xcd, 0xce, 0xcf
    };

    /* nonce */
    const byte iv[] =
    {
        0x00, 0x00, 0x00, 0x03, 0x02, 0x01, 0x00, 0xa0,
        0xa1, 0xa2, 0xa3, 0xa4, 0xa5
    };

    /* plaintext */
    const byte p[] =
    {
        0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
        0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e
    };
    /* plaintext - long */
    const byte pl[] =
    {
        0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
        0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
        0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27,
        0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f,
        0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
        0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f,
        0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47,
        0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f,
        0x50
    };


    const byte a[] =
    {
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07
    };

    /* ciphertext */
    const byte c[] =
    {
        0x58, 0x8c, 0x97, 0x9a, 0x61, 0xc6, 0x63, 0xd2,
        0xf0, 0x66, 0xd0, 0xc2, 0xc0, 0xf9, 0x89, 0x80,
        0x6d, 0x5f, 0x6b, 0x61, 0xda, 0xc3, 0x84
    };
    /* tag - authentication */
    const byte t[] =
    {
        0x17, 0xe8, 0xd1, 0x2c, 0xfd, 0xf9, 0x26, 0xe0
    };
    /* ciphertext - long */
    const byte cl[] =
    {
        0x58, 0x8c, 0x97, 0x9a, 0x61, 0xc6, 0x63, 0xd2,
        0xf0, 0x66, 0xd0, 0xc2, 0xc0, 0xf9, 0x89, 0x80,
        0x6d, 0x5f, 0x6b, 0x61, 0xda, 0xc3, 0x84, 0xe0,
        0x44, 0x2d, 0xbe, 0x25, 0xfa, 0x48, 0x2b, 0xa8,
        0x36, 0x0b, 0xbf, 0x01, 0xc0, 0x12, 0x45, 0xa4,
        0x82, 0x9f, 0x20, 0x6c, 0xc3, 0xd6, 0xae, 0x5b,
        0x54, 0x8d, 0xd0, 0xb1, 0x69, 0x2c, 0xec, 0x5e,
        0x95, 0xa5, 0x6b, 0x48, 0xc3, 0xc6, 0xc8, 0x9e,
        0xc7, 0x92, 0x98, 0x9d, 0x26, 0x7d, 0x2a, 0x10,
        0x0b
    };
    /* tag - authentication - long */
    const byte tl[] =
    {
        0x89, 0xd8, 0xd2, 0x02, 0xc5, 0xcf, 0xae, 0xf4
    };

    byte t2[sizeof(t)];
    byte p2[sizeof(p)];
    byte c2[sizeof(c)];
    byte iv2[sizeof(iv)];
    byte pl2[sizeof(pl)];
    byte cl2[sizeof(cl)];
    byte tl2[sizeof(tl)];

    int result;

    XMEMSET(&enc, 0, sizeof(Aes)); /* clear context */
    XMEMSET(t2, 0, sizeof(t2));
    XMEMSET(c2, 0, sizeof(c2));
    XMEMSET(p2, 0, sizeof(p2));

    result = wc_AesCcmSetKey(&enc, k, sizeof(k));
    if (result != 0)
        return -6300;

    /* AES-CCM encrypt and decrypt both use AES encrypt internally */
    result = wc_AesCcmEncrypt(&enc, c2, p, sizeof(c2), iv, sizeof(iv),
                                                 t2, sizeof(t2), a, sizeof(a));
    if (result != 0)
        return -6301;
    if (XMEMCMP(c, c2, sizeof(c2)))
        return -6302;
    if (XMEMCMP(t, t2, sizeof(t2)))
        return -6303;

    result = wc_AesCcmDecrypt(&enc, p2, c2, sizeof(p2), iv, sizeof(iv),
                                                 t2, sizeof(t2), a, sizeof(a));
    if (result != 0)
        return -6304;
    if (XMEMCMP(p, p2, sizeof(p2)))
        return -6305;

    /* Test the authentication failure */
    t2[0]++; /* Corrupt the authentication tag. */
    result = wc_AesCcmDecrypt(&enc, p2, c, sizeof(p2), iv, sizeof(iv),
                                                 t2, sizeof(t2), a, sizeof(a));
    if (result == 0)
        return -6306;

    /* Clear c2 to compare against p2. p2 should be set to zero in case of
     * authentication fail. */
    XMEMSET(c2, 0, sizeof(c2));
    if (XMEMCMP(p2, c2, sizeof(p2)))
        return -6307;

    XMEMSET(&enc, 0, sizeof(Aes)); /* clear context */
    XMEMSET(t2, 0, sizeof(t2));
    XMEMSET(c2, 0, sizeof(c2));
    XMEMSET(p2, 0, sizeof(p2));
    XMEMSET(iv2, 0, sizeof(iv2));

#ifndef HAVE_SELFTEST
    /* selftest build does not have wc_AesCcmSetNonce() or
     * wc_AesCcmEncrypt_ex() */
    if (wc_AesCcmSetKey(&enc, k, sizeof(k)) != 0)
        return -6308;

    if (wc_AesCcmSetNonce(&enc, iv, sizeof(iv)) != 0)
        return -6309;
    if (wc_AesCcmEncrypt_ex(&enc, c2, p, sizeof(c2), iv2, sizeof(iv2),
                            t2, sizeof(t2), a, sizeof(a)) != 0)
        return -6310;
    if (XMEMCMP(iv, iv2, sizeof(iv2)))
        return -6311;
    if (XMEMCMP(c, c2, sizeof(c2)))
        return -6312;
    if (XMEMCMP(t, t2, sizeof(t2)))
        return -6313;
#endif

#if !defined(HAVE_FIPS) && !defined(HAVE_SELFTEST)
    /* test fail on invalid IV sizes */
    result = wc_AesCcmSetKey(&enc, k, sizeof(k));
    if (result != 0)
        return -6314;

    /* AES-CCM encrypt and decrypt both use AES encrypt internally */
    result = wc_AesCcmEncrypt(&enc, c2, p, sizeof(c2), iv, sizeof(iv),
            t2, 1, a, sizeof(a));
    if (result == 0) {
        return -6315;
    }
#endif

    /* AES-CCM encrypt and decrypt both use AES encrypt internally */
    result = wc_AesCcmEncrypt(&enc, cl2, pl, sizeof(cl2), iv, sizeof(iv),
                                                tl2, sizeof(tl2), a, sizeof(a));
    if (result != 0)
        return -6301;
    if (XMEMCMP(cl, cl2, sizeof(cl2)))
        return -6302;
    if (XMEMCMP(tl, tl2, sizeof(tl2)))
        return -6303;

    result = wc_AesCcmDecrypt(&enc, pl2, cl2, sizeof(pl2), iv, sizeof(iv),
                                                tl2, sizeof(tl2), a, sizeof(a));
    if (result != 0)
        return -6304;
    if (XMEMCMP(pl, pl2, sizeof(pl2)))
        return -6305;

    return 0;
}
#endif /* HAVE_AESCCM WOLFSSL_AES_128 */


#ifdef HAVE_AES_KEYWRAP

#define MAX_KEYWRAP_TEST_OUTLEN 40
#define MAX_KEYWRAP_TEST_PLAINLEN 32

typedef struct keywrapVector {
    const byte* kek;
    const byte* data;
    const byte* verify;
    word32 kekLen;
    word32 dataLen;
    word32 verifyLen;
} keywrapVector;

int aeskeywrap_test(void)
{
    int wrapSz, plainSz, testSz, i;

    /* test vectors from RFC 3394 (kek, data, verify) */

#ifdef WOLFSSL_AES_128
    /* Wrap 128 bits of Key Data with a 128-bit KEK */
    const byte k1[] = {
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
        0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F
    };

    const byte d1[] = {
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
        0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF
    };

    const byte v1[] = {
        0x1F, 0xA6, 0x8B, 0x0A, 0x81, 0x12, 0xB4, 0x47,
        0xAE, 0xF3, 0x4B, 0xD8, 0xFB, 0x5A, 0x7B, 0x82,
        0x9D, 0x3E, 0x86, 0x23, 0x71, 0xD2, 0xCF, 0xE5
    };
#endif /* WOLFSSL_AES_128 */

#ifdef WOLFSSL_AES_192
    /* Wrap 128 bits of Key Data with a 192-bit KEK */
    const byte k2[] = {
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
        0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17
    };

    const byte d2[] = {
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
        0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF
    };

    const byte v2[] = {
        0x96, 0x77, 0x8B, 0x25, 0xAE, 0x6C, 0xA4, 0x35,
        0xF9, 0x2B, 0x5B, 0x97, 0xC0, 0x50, 0xAE, 0xD2,
        0x46, 0x8A, 0xB8, 0xA1, 0x7A, 0xD8, 0x4E, 0x5D
    };
#endif

#ifdef WOLFSSL_AES_256
    /* Wrap 128 bits of Key Data with a 256-bit KEK */
    const byte k3[] = {
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
        0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
        0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F
    };

    const byte d3[] = {
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
        0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF
    };

    const byte v3[] = {
        0x64, 0xE8, 0xC3, 0xF9, 0xCE, 0x0F, 0x5B, 0xA2,
        0x63, 0xE9, 0x77, 0x79, 0x05, 0x81, 0x8A, 0x2A,
        0x93, 0xC8, 0x19, 0x1E, 0x7D, 0x6E, 0x8A, 0xE7
    };
#endif

#ifdef WOLFSSL_AES_192
    /* Wrap 192 bits of Key Data with a 192-bit KEK */
    const byte k4[] = {
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
        0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17
    };

    const byte d4[] = {
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
        0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF,
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07
    };

    const byte v4[] = {
        0x03, 0x1D, 0x33, 0x26, 0x4E, 0x15, 0xD3, 0x32,
        0x68, 0xF2, 0x4E, 0xC2, 0x60, 0x74, 0x3E, 0xDC,
        0xE1, 0xC6, 0xC7, 0xDD, 0xEE, 0x72, 0x5A, 0x93,
        0x6B, 0xA8, 0x14, 0x91, 0x5C, 0x67, 0x62, 0xD2
    };
#endif

#ifdef WOLFSSL_AES_256
    /* Wrap 192 bits of Key Data with a 256-bit KEK */
    const byte k5[] = {
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
        0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
        0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F
    };

    const byte d5[] = {
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
        0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF,
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07
    };

    const byte v5[] = {
        0xA8, 0xF9, 0xBC, 0x16, 0x12, 0xC6, 0x8B, 0x3F,
        0xF6, 0xE6, 0xF4, 0xFB, 0xE3, 0x0E, 0x71, 0xE4,
        0x76, 0x9C, 0x8B, 0x80, 0xA3, 0x2C, 0xB8, 0x95,
        0x8C, 0xD5, 0xD1, 0x7D, 0x6B, 0x25, 0x4D, 0xA1
    };

    /* Wrap 256 bits of Key Data with a 256-bit KEK */
    const byte k6[] = {
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
        0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
        0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F
    };

    const byte d6[] = {
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
        0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF,
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
        0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F
    };

    const byte v6[] = {
        0x28, 0xC9, 0xF4, 0x04, 0xC4, 0xB8, 0x10, 0xF4,
        0xCB, 0xCC, 0xB3, 0x5C, 0xFB, 0x87, 0xF8, 0x26,
        0x3F, 0x57, 0x86, 0xE2, 0xD8, 0x0E, 0xD3, 0x26,
        0xCB, 0xC7, 0xF0, 0xE7, 0x1A, 0x99, 0xF4, 0x3B,
        0xFB, 0x98, 0x8B, 0x9B, 0x7A, 0x02, 0xDD, 0x21
    };
#endif /* WOLFSSL_AES_256 */

    byte output[MAX_KEYWRAP_TEST_OUTLEN];
    byte plain [MAX_KEYWRAP_TEST_PLAINLEN];

    const keywrapVector test_wrap[] =
    {
    #ifdef WOLFSSL_AES_128
        {k1, d1, v1, sizeof(k1), sizeof(d1), sizeof(v1)},
    #endif
    #ifdef WOLFSSL_AES_192
        {k2, d2, v2, sizeof(k2), sizeof(d2), sizeof(v2)},
    #endif
    #ifdef WOLFSSL_AES_256
        {k3, d3, v3, sizeof(k3), sizeof(d3), sizeof(v3)},
    #endif
    #ifdef WOLFSSL_AES_192
        {k4, d4, v4, sizeof(k4), sizeof(d4), sizeof(v4)},
    #endif
    #ifdef WOLFSSL_AES_256
        {k5, d5, v5, sizeof(k5), sizeof(d5), sizeof(v5)},
        {k6, d6, v6, sizeof(k6), sizeof(d6), sizeof(v6)}
    #endif
    };
    testSz = sizeof(test_wrap) / sizeof(keywrapVector);

    XMEMSET(output, 0, sizeof(output));
    XMEMSET(plain,  0, sizeof(plain));

    for (i = 0; i < testSz; i++) {

        wrapSz = wc_AesKeyWrap(test_wrap[i].kek, test_wrap[i].kekLen,
                               test_wrap[i].data, test_wrap[i].dataLen,
                               output, sizeof(output), NULL);

        if ( (wrapSz < 0) || (wrapSz != (int)test_wrap[i].verifyLen) )
            return -6400;

        if (XMEMCMP(output, test_wrap[i].verify, test_wrap[i].verifyLen) != 0)
            return -6401;

        plainSz = wc_AesKeyUnWrap((byte*)test_wrap[i].kek, test_wrap[i].kekLen,
                                  output, wrapSz,
                                  plain, sizeof(plain), NULL);

        if ( (plainSz < 0) || (plainSz != (int)test_wrap[i].dataLen) )
            return -6402;

        if (XMEMCMP(plain, test_wrap[i].data, test_wrap[i].dataLen) != 0)
            return -6403 - i;
    }

    return 0;
}
#endif /* HAVE_AES_KEYWRAP */


#endif /* NO_AES */


#ifdef HAVE_CAMELLIA

enum {
    CAM_ECB_ENC, CAM_ECB_DEC, CAM_CBC_ENC, CAM_CBC_DEC
};

typedef struct {
    int type;
    const byte* plaintext;
    const byte* iv;
    const byte* ciphertext;
    const byte* key;
    word32 keySz;
    int errorCode;
} test_vector_t;

int camellia_test(void)
{
    /* Camellia ECB Test Plaintext */
    static const byte pte[] =
    {
        0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef,
        0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10
    };

    /* Camellia ECB Test Initialization Vector */
    static const byte ive[] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};

    /* Test 1: Camellia ECB 128-bit key */
    static const byte k1[] =
    {
        0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef,
        0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10
    };
    static const byte c1[] =
    {
        0x67, 0x67, 0x31, 0x38, 0x54, 0x96, 0x69, 0x73,
        0x08, 0x57, 0x06, 0x56, 0x48, 0xea, 0xbe, 0x43
    };

    /* Test 2: Camellia ECB 192-bit key */
    static const byte k2[] =
    {
        0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef,
        0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10,
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77
    };
    static const byte c2[] =
    {
        0xb4, 0x99, 0x34, 0x01, 0xb3, 0xe9, 0x96, 0xf8,
        0x4e, 0xe5, 0xce, 0xe7, 0xd7, 0x9b, 0x09, 0xb9
    };

    /* Test 3: Camellia ECB 256-bit key */
    static const byte k3[] =
    {
        0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef,
        0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10,
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
        0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff
    };
    static const byte c3[] =
    {
        0x9a, 0xcc, 0x23, 0x7d, 0xff, 0x16, 0xd7, 0x6c,
        0x20, 0xef, 0x7c, 0x91, 0x9e, 0x3a, 0x75, 0x09
    };

    /* Camellia CBC Test Plaintext */
    static const byte ptc[] =
    {
        0x6B, 0xC1, 0xBE, 0xE2, 0x2E, 0x40, 0x9F, 0x96,
        0xE9, 0x3D, 0x7E, 0x11, 0x73, 0x93, 0x17, 0x2A
    };

    /* Camellia CBC Test Initialization Vector */
    static const byte ivc[] =
    {
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
        0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F
    };

    /* Test 4: Camellia-CBC 128-bit key */
    static const byte k4[] =
    {
        0x2B, 0x7E, 0x15, 0x16, 0x28, 0xAE, 0xD2, 0xA6,
        0xAB, 0xF7, 0x15, 0x88, 0x09, 0xCF, 0x4F, 0x3C
    };
    static const byte c4[] =
    {
        0x16, 0x07, 0xCF, 0x49, 0x4B, 0x36, 0xBB, 0xF0,
        0x0D, 0xAE, 0xB0, 0xB5, 0x03, 0xC8, 0x31, 0xAB
    };

    /* Test 5: Camellia-CBC 192-bit key */
    static const byte k5[] =
    {
        0x8E, 0x73, 0xB0, 0xF7, 0xDA, 0x0E, 0x64, 0x52,
        0xC8, 0x10, 0xF3, 0x2B, 0x80, 0x90, 0x79, 0xE5,
        0x62, 0xF8, 0xEA, 0xD2, 0x52, 0x2C, 0x6B, 0x7B
    };
    static const byte c5[] =
    {
        0x2A, 0x48, 0x30, 0xAB, 0x5A, 0xC4, 0xA1, 0xA2,
        0x40, 0x59, 0x55, 0xFD, 0x21, 0x95, 0xCF, 0x93
    };

    /* Test 6: CBC 256-bit key */
    static const byte k6[] =
    {
        0x60, 0x3D, 0xEB, 0x10, 0x15, 0xCA, 0x71, 0xBE,
        0x2B, 0x73, 0xAE, 0xF0, 0x85, 0x7D, 0x77, 0x81,
        0x1F, 0x35, 0x2C, 0x07, 0x3B, 0x61, 0x08, 0xD7,
        0x2D, 0x98, 0x10, 0xA3, 0x09, 0x14, 0xDF, 0xF4
    };
    static const byte c6[] =
    {
        0xE6, 0xCF, 0xA3, 0x5F, 0xC0, 0x2B, 0x13, 0x4A,
        0x4D, 0x2C, 0x0B, 0x67, 0x37, 0xAC, 0x3E, 0xDA
    };

    byte out[CAMELLIA_BLOCK_SIZE];
    Camellia cam;
    int i, testsSz, ret;
    const test_vector_t testVectors[] =
    {
        {CAM_ECB_ENC, pte, ive, c1, k1, sizeof(k1), -114},
        {CAM_ECB_ENC, pte, ive, c2, k2, sizeof(k2), -115},
        {CAM_ECB_ENC, pte, ive, c3, k3, sizeof(k3), -116},
        {CAM_ECB_DEC, pte, ive, c1, k1, sizeof(k1), -117},
        {CAM_ECB_DEC, pte, ive, c2, k2, sizeof(k2), -118},
        {CAM_ECB_DEC, pte, ive, c3, k3, sizeof(k3), -119},
        {CAM_CBC_ENC, ptc, ivc, c4, k4, sizeof(k4), -120},
        {CAM_CBC_ENC, ptc, ivc, c5, k5, sizeof(k5), -121},
        {CAM_CBC_ENC, ptc, ivc, c6, k6, sizeof(k6), -122},
        {CAM_CBC_DEC, ptc, ivc, c4, k4, sizeof(k4), -123},
        {CAM_CBC_DEC, ptc, ivc, c5, k5, sizeof(k5), -124},
        {CAM_CBC_DEC, ptc, ivc, c6, k6, sizeof(k6), -125}
    };

    testsSz = sizeof(testVectors)/sizeof(test_vector_t);
    for (i = 0; i < testsSz; i++) {
        if (wc_CamelliaSetKey(&cam, testVectors[i].key, testVectors[i].keySz,
                                                        testVectors[i].iv) != 0)
            return testVectors[i].errorCode;

        switch (testVectors[i].type) {
            case CAM_ECB_ENC:
                ret = wc_CamelliaEncryptDirect(&cam, out,
                                                testVectors[i].plaintext);
                if (ret != 0 || XMEMCMP(out, testVectors[i].ciphertext,
                                                        CAMELLIA_BLOCK_SIZE))
                    return testVectors[i].errorCode;
                break;
            case CAM_ECB_DEC:
                ret = wc_CamelliaDecryptDirect(&cam, out,
                                                    testVectors[i].ciphertext);
                if (ret != 0 || XMEMCMP(out, testVectors[i].plaintext,
                                                        CAMELLIA_BLOCK_SIZE))
                    return testVectors[i].errorCode;
                break;
            case CAM_CBC_ENC:
                ret = wc_CamelliaCbcEncrypt(&cam, out, testVectors[i].plaintext,
                                                           CAMELLIA_BLOCK_SIZE);
                if (ret != 0 || XMEMCMP(out, testVectors[i].ciphertext,
                                                        CAMELLIA_BLOCK_SIZE))
                    return testVectors[i].errorCode;
                break;
            case CAM_CBC_DEC:
                ret = wc_CamelliaCbcDecrypt(&cam, out,
                                testVectors[i].ciphertext, CAMELLIA_BLOCK_SIZE);
                if (ret != 0 || XMEMCMP(out, testVectors[i].plaintext,
                                                           CAMELLIA_BLOCK_SIZE))
                    return testVectors[i].errorCode;
                break;
            default:
                break;
        }
    }

    /* Setting the IV and checking it was actually set. */
    ret = wc_CamelliaSetIV(&cam, ivc);
    if (ret != 0 || XMEMCMP(cam.reg, ivc, CAMELLIA_BLOCK_SIZE))
        return -6500;

    /* Setting the IV to NULL should be same as all zeros IV */
    if (wc_CamelliaSetIV(&cam, NULL) != 0 ||
                                    XMEMCMP(cam.reg, ive, CAMELLIA_BLOCK_SIZE))
        return -6501;

    /* First parameter should never be null */
    if (wc_CamelliaSetIV(NULL, NULL) == 0)
        return -6502;

    /* First parameter should never be null, check it fails */
    if (wc_CamelliaSetKey(NULL, k1, sizeof(k1), NULL) == 0)
        return -6503;

    /* Key should have a size of 16, 24, or 32 */
    if (wc_CamelliaSetKey(&cam, k1, 0, NULL) == 0)
        return -6504;

    return 0;
}
#endif /* HAVE_CAMELLIA */

#ifdef HAVE_IDEA
int idea_test(void)
{
    int ret;
    word16 i, j;

    Idea idea;
    byte data[IDEA_BLOCK_SIZE];

    /* Project NESSIE test vectors */
#define IDEA_NB_TESTS   6
#define IDEA_NB_TESTS_EXTRA 4

    const byte v_key[IDEA_NB_TESTS][IDEA_KEY_SIZE] = {
        { 0x37, 0x37, 0x37, 0x37, 0x37, 0x37, 0x37, 0x37,
            0x37, 0x37, 0x37, 0x37, 0x37, 0x37, 0x37, 0x37 },
        { 0x57, 0x57, 0x57, 0x57, 0x57, 0x57, 0x57, 0x57,
            0x57, 0x57, 0x57, 0x57, 0x57, 0x57, 0x57, 0x57 },
        { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F },
        { 0x2B, 0xD6, 0x45, 0x9F, 0x82, 0xC5, 0xB3, 0x00,
            0x95, 0x2C, 0x49, 0x10, 0x48, 0x81, 0xFF, 0x48 },
        { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F },
        { 0x2B, 0xD6, 0x45, 0x9F, 0x82, 0xC5, 0xB3, 0x00,
            0x95, 0x2C, 0x49, 0x10, 0x48, 0x81, 0xFF, 0x48 },
    };

    const byte v1_plain[IDEA_NB_TESTS][IDEA_BLOCK_SIZE] = {
        { 0x37, 0x37, 0x37, 0x37, 0x37, 0x37, 0x37, 0x37 },
        { 0x57, 0x57, 0x57, 0x57, 0x57, 0x57, 0x57, 0x57 },
        { 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77 },
        { 0xEA, 0x02, 0x47, 0x14, 0xAD, 0x5C, 0x4D, 0x84 },
        { 0xDB, 0x2D, 0x4A, 0x92, 0xAA, 0x68, 0x27, 0x3F },
        { 0xF1, 0x29, 0xA6, 0x60, 0x1E, 0xF6, 0x2A, 0x47 },
    };

    byte v1_cipher[IDEA_NB_TESTS][IDEA_BLOCK_SIZE] = {
        { 0x54, 0xCF, 0x21, 0xE3, 0x89, 0xD8, 0x73, 0xEC },
        { 0x85, 0x52, 0x4D, 0x41, 0x0E, 0xB4, 0x28, 0xAE },
        { 0xF5, 0x26, 0xAB, 0x9A, 0x62, 0xC0, 0xD2, 0x58 },
        { 0xC8, 0xFB, 0x51, 0xD3, 0x51, 0x66, 0x27, 0xA8 },
        { 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77 },
        { 0xEA, 0x02, 0x47, 0x14, 0xAD, 0x5C, 0x4D, 0x84 },
    };

    byte v1_cipher_100[IDEA_NB_TESTS_EXTRA][IDEA_BLOCK_SIZE]  = {
        { 0x12, 0x46, 0x2F, 0xD0, 0xFB, 0x3A, 0x63, 0x39 },
        { 0x15, 0x61, 0xE8, 0xC9, 0x04, 0x54, 0x8B, 0xE9 },
        { 0x42, 0x12, 0x2A, 0x94, 0xB0, 0xF6, 0xD2, 0x43 },
        { 0x53, 0x4D, 0xCD, 0x48, 0xDD, 0xD5, 0xF5, 0x9C },
    };

    byte v1_cipher_1000[IDEA_NB_TESTS_EXTRA][IDEA_BLOCK_SIZE] = {
        { 0x44, 0x1B, 0x38, 0x5C, 0x77, 0x29, 0x75, 0x34 },
        { 0xF0, 0x4E, 0x58, 0x88, 0x44, 0x99, 0x22, 0x2D },
        { 0xB3, 0x5F, 0x93, 0x7F, 0x6A, 0xA0, 0xCD, 0x1F },
        { 0x9A, 0xEA, 0x46, 0x8F, 0x42, 0x9B, 0xBA, 0x15 },
    };

    /* CBC test */
    const char *message = "International Data Encryption Algorithm";
    byte msg_enc[40], msg_dec[40];

    for (i = 0; i < IDEA_NB_TESTS; i++) {
        /* Set encryption key */
        XMEMSET(&idea, 0, sizeof(Idea));
        ret = wc_IdeaSetKey(&idea, v_key[i], IDEA_KEY_SIZE,
                            NULL, IDEA_ENCRYPTION);
        if (ret != 0) {
            printf("wc_IdeaSetKey (enc) failed\n");
            return -6600;
        }

        /* Data encryption */
        ret = wc_IdeaCipher(&idea, data, v1_plain[i]);
        if (ret != 0 || XMEMCMP(&v1_cipher[i], data, IDEA_BLOCK_SIZE)) {
            printf("Bad encryption\n");
            return -6601;
        }

        /* Set decryption key */
        XMEMSET(&idea, 0, sizeof(Idea));
        ret = wc_IdeaSetKey(&idea, v_key[i], IDEA_KEY_SIZE,
                            NULL, IDEA_DECRYPTION);
        if (ret != 0) {
            printf("wc_IdeaSetKey (dec) failed\n");
            return -6602;
        }

        /* Data decryption */
        ret = wc_IdeaCipher(&idea, data, data);
        if (ret != 0 || XMEMCMP(v1_plain[i], data, IDEA_BLOCK_SIZE)) {
            printf("Bad decryption\n");
            return -6603;
        }

        /* Set encryption key */
        XMEMSET(&idea, 0, sizeof(Idea));
        ret = wc_IdeaSetKey(&idea, v_key[i], IDEA_KEY_SIZE,
                            v_key[i], IDEA_ENCRYPTION);
        if (ret != 0) {
            printf("wc_IdeaSetKey (enc) failed\n");
            return -6604;
        }

        XMEMSET(msg_enc, 0, sizeof(msg_enc));
        ret = wc_IdeaCbcEncrypt(&idea, msg_enc, (byte *)message,
                                (word32)XSTRLEN(message)+1);
        if (ret != 0) {
            printf("wc_IdeaCbcEncrypt failed\n");
            return -6605;
        }

        /* Set decryption key */
        XMEMSET(&idea, 0, sizeof(Idea));
        ret = wc_IdeaSetKey(&idea, v_key[i], IDEA_KEY_SIZE,
                            v_key[i], IDEA_DECRYPTION);
        if (ret != 0) {
            printf("wc_IdeaSetKey (dec) failed\n");
            return -6606;
        }

        XMEMSET(msg_dec, 0, sizeof(msg_dec));
        ret = wc_IdeaCbcDecrypt(&idea, msg_dec, msg_enc,
                                (word32)XSTRLEN(message)+1);
        if (ret != 0) {
            printf("wc_IdeaCbcDecrypt failed\n");
            return -6607;
        }

        if (XMEMCMP(message, msg_dec, (word32)XSTRLEN(message))) {
            printf("Bad CBC decryption\n");
            return -6608;
        }
    }

    for (i = 0; i < IDEA_NB_TESTS_EXTRA; i++) {
        /* Set encryption key */
        XMEMSET(&idea, 0, sizeof(Idea));
        ret = wc_IdeaSetKey(&idea, v_key[i], IDEA_KEY_SIZE,
                            NULL, IDEA_ENCRYPTION);
        if (ret != 0) {
            printf("wc_IdeaSetKey (enc) failed\n");
            return -6609;
        }

        /* 100 times data encryption */
        XMEMCPY(data, v1_plain[i], IDEA_BLOCK_SIZE);
        for (j = 0; j < 100; j++) {
            ret = wc_IdeaCipher(&idea, data, data);
            if (ret != 0) {
                return -6610;
            }
        }

        if (XMEMCMP(v1_cipher_100[i], data, IDEA_BLOCK_SIZE)) {
            printf("Bad encryption (100 times)\n");
            return -6611;
        }

        /* 1000 times data encryption */
        XMEMCPY(data, v1_plain[i], IDEA_BLOCK_SIZE);
        for (j = 0; j < 1000; j++) {
            ret = wc_IdeaCipher(&idea, data, data);
            if (ret != 0) {
                return -6612;
            }
        }

        if (XMEMCMP(v1_cipher_1000[i], data, IDEA_BLOCK_SIZE)) {
            printf("Bad encryption (100 times)\n");
            return -6613;
        }
    }

#ifndef WC_NO_RNG
    /* random test for CBC */
    {
        WC_RNG rng;
        byte key[IDEA_KEY_SIZE], iv[IDEA_BLOCK_SIZE],
        rnd[1000], enc[1000], dec[1000];

        /* random values */
    #ifndef HAVE_FIPS
        ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
    #else
        ret = wc_InitRng(&rng);
    #endif
        if (ret != 0)
            return -6614;

        for (i = 0; i < 1000; i++) {
            /* random key */
            ret = wc_RNG_GenerateBlock(&rng, key, sizeof(key));
            if (ret != 0)
                return -6615;

            /* random iv */
            ret = wc_RNG_GenerateBlock(&rng, iv, sizeof(iv));
            if (ret != 0)
                return -6616;

            /* random data */
            ret = wc_RNG_GenerateBlock(&rng, rnd, sizeof(rnd));
            if (ret != 0)
                return -6617;

            /* Set encryption key */
            XMEMSET(&idea, 0, sizeof(Idea));
            ret = wc_IdeaSetKey(&idea, key, IDEA_KEY_SIZE, iv, IDEA_ENCRYPTION);
            if (ret != 0) {
                printf("wc_IdeaSetKey (enc) failed\n");
                return -6618;
            }

            /* Data encryption */
            XMEMSET(enc, 0, sizeof(enc));
            ret = wc_IdeaCbcEncrypt(&idea, enc, rnd, sizeof(rnd));
            if (ret != 0) {
                printf("wc_IdeaCbcEncrypt failed\n");
                return -6619;
            }

            /* Set decryption key */
            XMEMSET(&idea, 0, sizeof(Idea));
            ret = wc_IdeaSetKey(&idea, key, IDEA_KEY_SIZE, iv, IDEA_DECRYPTION);
            if (ret != 0) {
                printf("wc_IdeaSetKey (enc) failed\n");
                return -6620;
            }

            /* Data decryption */
            XMEMSET(dec, 0, sizeof(dec));
            ret = wc_IdeaCbcDecrypt(&idea, dec, enc, sizeof(enc));
            if (ret != 0) {
                printf("wc_IdeaCbcDecrypt failed\n");
                return -6621;
            }

            if (XMEMCMP(rnd, dec, sizeof(rnd))) {
                printf("Bad CBC decryption\n");
                return -6622;
            }
        }

        wc_FreeRng(&rng);
    }
#endif /* WC_NO_RNG */

    return 0;
}
#endif /* HAVE_IDEA */


#ifndef WC_NO_RNG
static int _rng_test(WC_RNG* rng, int errorOffset)
{
    byte block[32];
    int ret, i;

    XMEMSET(block, 0, sizeof(block));

    ret = wc_RNG_GenerateBlock(rng, block, sizeof(block));
    if (ret != 0) {
        ret = -6623;
        goto exit;
    }

    /* Check for 0's */
    for (i=0; i<(int)sizeof(block); i++) {
        if (block[i] == 0) {
            ret++;
        }
    }
    /* All zeros count check */
    if (ret >= (int)sizeof(block)) {
        ret = -6624;
        goto exit;
    }

    ret = wc_RNG_GenerateByte(rng, block);
    if (ret != 0) {
        ret = -6625;
        goto exit;
    }

    /* Parameter validation testing. */
    ret = wc_RNG_GenerateBlock(NULL, block, sizeof(block));
    if (ret != BAD_FUNC_ARG) {
        ret = -6626;
        goto exit;
    }
    ret = wc_RNG_GenerateBlock(rng, NULL, sizeof(block));
    if (ret != BAD_FUNC_ARG) {
        ret = -6627;
        goto exit;
    }

    ret = wc_RNG_GenerateByte(NULL, block);
    if (ret != BAD_FUNC_ARG) {
        ret = -6628;
        goto exit;
    }
    ret = wc_RNG_GenerateByte(rng, NULL);
    if (ret != BAD_FUNC_ARG) {
        ret = -6629;
        goto exit;
    }

    ret = 0;

exit:
    if (ret != 0)
        ret += errorOffset;

    return ret;
}


static int random_rng_test(void)
{
    WC_RNG localRng;
    WC_RNG* rng;
    int ret;

    rng = &localRng;
    /* Test stack based RNG. */
#ifndef HAVE_FIPS
    ret = wc_InitRng_ex(rng, HEAP_HINT, devId);
#else
    ret = wc_InitRng(rng);
#endif
    if (ret != 0) return -6700;

    ret = _rng_test(rng, -6300);

    /* Make sure and free RNG */
    wc_FreeRng(rng);

    if (ret != 0) return ret;

#if !defined(HAVE_FIPS) && !defined(HAVE_SELFTEST)
    {
        byte nonce[8] = { 0 };
        /* Test dynamic RNG. */
        rng = wc_rng_new(nonce, (word32)sizeof(nonce), HEAP_HINT);
        if (rng == NULL) return -6701;

        ret = _rng_test(rng, -6310);

        wc_rng_free(rng);
    }
#endif

    return ret;
}

#if defined(HAVE_HASHDRBG) && !defined(CUSTOM_RAND_GENERATE_BLOCK)

int random_test(void)
{
    const byte test1Entropy[] =
    {
        0xa6, 0x5a, 0xd0, 0xf3, 0x45, 0xdb, 0x4e, 0x0e, 0xff, 0xe8, 0x75, 0xc3,
        0xa2, 0xe7, 0x1f, 0x42, 0xc7, 0x12, 0x9d, 0x62, 0x0f, 0xf5, 0xc1, 0x19,
        0xa9, 0xef, 0x55, 0xf0, 0x51, 0x85, 0xe0, 0xfb, 0x85, 0x81, 0xf9, 0x31,
        0x75, 0x17, 0x27, 0x6e, 0x06, 0xe9, 0x60, 0x7d, 0xdb, 0xcb, 0xcc, 0x2e
    };
    const byte test1Output[] =
    {
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
    const byte test2EntropyA[] =
    {
        0x63, 0x36, 0x33, 0x77, 0xe4, 0x1e, 0x86, 0x46, 0x8d, 0xeb, 0x0a, 0xb4,
        0xa8, 0xed, 0x68, 0x3f, 0x6a, 0x13, 0x4e, 0x47, 0xe0, 0x14, 0xc7, 0x00,
        0x45, 0x4e, 0x81, 0xe9, 0x53, 0x58, 0xa5, 0x69, 0x80, 0x8a, 0xa3, 0x8f,
        0x2a, 0x72, 0xa6, 0x23, 0x59, 0x91, 0x5a, 0x9f, 0x8a, 0x04, 0xca, 0x68
    };
    const byte test2EntropyB[] =
    {
        0xe6, 0x2b, 0x8a, 0x8e, 0xe8, 0xf1, 0x41, 0xb6, 0x98, 0x05, 0x66, 0xe3,
        0xbf, 0xe3, 0xc0, 0x49, 0x03, 0xda, 0xd4, 0xac, 0x2c, 0xdf, 0x9f, 0x22,
        0x80, 0x01, 0x0a, 0x67, 0x39, 0xbc, 0x83, 0xd3
    };
    const byte test2Output[] =
    {
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

    byte output[WC_SHA256_DIGEST_SIZE * 4];
    int ret;

    ret = wc_RNG_HealthTest(0, test1Entropy, sizeof(test1Entropy), NULL, 0,
                            output, sizeof(output));
    if (ret != 0)
        return -6800;

    if (XMEMCMP(test1Output, output, sizeof(output)) != 0)
        return -6801;

    ret = wc_RNG_HealthTest(1, test2EntropyA, sizeof(test2EntropyA),
                            test2EntropyB, sizeof(test2EntropyB),
                            output, sizeof(output));
    if (ret != 0)
        return -6802;

    if (XMEMCMP(test2Output, output, sizeof(output)) != 0)
        return -6803;

    /* Basic RNG generate block test */
    if ((ret = random_rng_test()) != 0)
        return ret;

    /* Test the seed check function. */
#if !(defined(HAVE_FIPS) || defined(HAVE_SELFTEST)) || \
    (defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2))
    {
        word32 i, outputSz;

        /* Repeat the same byte over and over. Should fail. */
        outputSz = sizeof(output);
        XMEMSET(output, 1, outputSz);
        ret = wc_RNG_TestSeed(output, outputSz);
        if (ret == 0)
            return -6804;

        /* Every byte of the entropy scratch is different,
         * entropy is a single byte that shouldn't match. */
        outputSz = (sizeof(word32) * 2) + 1;
        for (i = 0; i < outputSz; i++)
            output[i] = (byte)i;
        ret = wc_RNG_TestSeed(output, outputSz);
        if (ret != 0)
            return -6805;

        outputSz = sizeof(output);
        for (i = 0; i < outputSz; i++)
            output[i] = (byte)i;
        ret = wc_RNG_TestSeed(output, outputSz);
        if (ret != 0)
            return -6806;
    }
#endif
    return 0;
}

#else

int random_test(void)
{
    /* Basic RNG generate block test */
    return random_rng_test();
}

#endif /* HAVE_HASHDRBG && !CUSTOM_RAND_GENERATE_BLOCK */
#endif /* WC_NO_RNG */

#ifndef MEM_TEST_SZ
    #define MEM_TEST_SZ 1024
#endif

#if defined(WOLFSSL_STATIC_MEMORY) || !defined(WOLFSSL_NO_MALLOC)
static int simple_mem_test(int sz)
{
    int ret = 0;
    byte* b;
    int i;

    b = (byte*)XMALLOC(sz, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (b == NULL) {
        return -6900;
    }
    /* utilize memory */
    for (i = 0; i < sz; i++) {
        b[i] = (byte)i;
    }
    /* read back and verify */
    for (i = 0; i < sz; i++) {
        if (b[i] != (byte)i) {
            ret = -6901;
            break;
        }
    }
    XFREE(b, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    return ret;
}
#endif

int memory_test(void)
{
    int ret = 0;
#ifndef USE_FAST_MATH
    byte* b = NULL;
#endif
#if defined(COMPLEX_MEM_TEST) || defined(WOLFSSL_STATIC_MEMORY)
    int i;
#endif
#ifdef WOLFSSL_STATIC_MEMORY
    word32 size[] = { WOLFMEM_BUCKETS };
    word32 dist[] = { WOLFMEM_DIST };
    byte buffer[30000]; /* make large enough to involve many bucket sizes */
    int pad = -(int)((wolfssl_word)buffer) & (WOLFSSL_STATIC_ALIGN - 1);
              /* pad to account for if head of buffer is not at set memory
               * alignment when tests are ran */
#endif

#ifdef WOLFSSL_STATIC_MEMORY
    /* check macro settings */
    if (sizeof(size)/sizeof(word32) != WOLFMEM_MAX_BUCKETS) {
        return -7000;
    }

    if (sizeof(dist)/sizeof(word32) != WOLFMEM_MAX_BUCKETS) {
        return -7001;
    }

    for (i = 0; i < WOLFMEM_MAX_BUCKETS; i++) {
        if ((size[i] % WOLFSSL_STATIC_ALIGN) != 0) {
            /* each element in array should be divisible by alignment size */
            return -7002;
        }
    }

    for (i = 1; i < WOLFMEM_MAX_BUCKETS; i++) {
        if (size[i - 1] >= size[i]) {
            return -7003; /* sizes should be in increasing order  */
        }
    }

    /* check that padding size returned is possible */
    if (wolfSSL_MemoryPaddingSz() < WOLFSSL_STATIC_ALIGN) {
        return -7004; /* no room for wc_Memory struct */
    }

    if (wolfSSL_MemoryPaddingSz() < 0) {
        return -7005;
    }

    if (wolfSSL_MemoryPaddingSz() % WOLFSSL_STATIC_ALIGN != 0) {
        return -7006; /* not aligned! */
    }

    /* check function to return optimum buffer size (rounded down) */
    ret = wolfSSL_StaticBufferSz(buffer, sizeof(buffer), WOLFMEM_GENERAL);
    if ((ret - pad) % WOLFSSL_STATIC_ALIGN != 0) {
        return -7007; /* not aligned! */
    }

    if (ret < 0) {
        return -7008;
    }

    if ((unsigned int)ret > sizeof(buffer)) {
        return -7009; /* did not round down as expected */
    }

    if (ret != wolfSSL_StaticBufferSz(buffer, ret, WOLFMEM_GENERAL)) {
        return -7010; /* return value changed when using suggested value */
    }

    ret = wolfSSL_MemoryPaddingSz();
    ret += pad; /* add space that is going to be needed if buffer not aligned */
    if (wolfSSL_StaticBufferSz(buffer, size[0] + ret + 1, WOLFMEM_GENERAL) !=
            (ret + (int)size[0])) {
        return -7011; /* did not round down to nearest bucket value */
    }

    ret = wolfSSL_StaticBufferSz(buffer, sizeof(buffer), WOLFMEM_IO_POOL);
    if ((ret - pad) < 0) {
        return -7012;
    }

    if (((ret - pad) % (WOLFMEM_IO_SZ + wolfSSL_MemoryPaddingSz())) != 0) {
        return -7013; /* not even chunks of memory for IO size */
    }

    if (((ret - pad) % WOLFSSL_STATIC_ALIGN) != 0) {
        return -7014; /* memory not aligned */
    }

    /* check for passing bad or unknown arguments to functions */
    if (wolfSSL_StaticBufferSz(NULL, 1, WOLFMEM_GENERAL) > 0) {
        return -7015;
    }

    if (wolfSSL_StaticBufferSz(buffer, 1, WOLFMEM_GENERAL) != 0) {
        return -7016; /* should round to 0 since struct + bucket will not fit */
    }

    (void)dist; /* avoid static analysis warning of variable not used */
#endif

#if defined(WOLFSSL_STATIC_MEMORY) || !defined(WOLFSSL_NO_MALLOC)
    /* simple test */
    ret = simple_mem_test(MEM_TEST_SZ);
    if (ret != 0)
        return ret;
#endif

#ifdef COMPLEX_MEM_TEST
    /* test various size blocks */
    for (i = 1; i < MEM_TEST_SZ; i*=2) {
        ret = simple_mem_test(i);
        if (ret != 0)
            return ret;
    }
#endif

#ifndef USE_FAST_MATH
    /* realloc test */
    b = (byte*)XMALLOC(MEM_TEST_SZ, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (b) {
        b = (byte*)XREALLOC(b, MEM_TEST_SZ+sizeof(word32), HEAP_HINT,
            DYNAMIC_TYPE_TMP_BUFFER);
    }
    if (b == NULL) {
        return -7017;
    }
    XFREE(b, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}


#ifdef HAVE_NTRU

byte GetEntropy(ENTROPY_CMD cmd, byte* out);

byte GetEntropy(ENTROPY_CMD cmd, byte* out)
{
    static WC_RNG rng;

    if (cmd == INIT)
        return (wc_InitRng(&rng) == 0) ? 1 : 0;

    if (out == NULL)
        return 0;

    if (cmd == GET_BYTE_OF_ENTROPY)
        return (wc_RNG_GenerateBlock(&rng, out, 1) == 0) ? 1 : 0;

    if (cmd == GET_NUM_BYTES_PER_BYTE_OF_ENTROPY) {
        *out = 1;
        return 1;
    }

    return 0;
}

#endif /* HAVE_NTRU */


#ifndef NO_FILESYSTEM

/* Cert Paths */
#ifdef FREESCALE_MQX
    #define CERT_PREFIX "a:\\"
    #define CERT_PATH_SEP "\\"
#elif defined(WOLFSSL_uTKERNEL2)
    #define CERT_PREFIX "/uda/"
    #define CERT_PATH_SEP "/"
#else
    #define CERT_PREFIX "./"
    #define CERT_PATH_SEP "/"
#endif
#define CERT_ROOT CERT_PREFIX "certs" CERT_PATH_SEP

/* Generated Test Certs */
#if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048) && \
    !defined(USE_CERT_BUFFERS_3072) && !defined(USE_CERT_BUFFERS_4096)
    #if !defined(NO_RSA) && !defined(NO_ASN)
        static const char* clientKey  = CERT_ROOT "client-key.der";
        static const char* clientCert = CERT_ROOT "client-cert.der";
        #ifdef WOLFSSL_CERT_EXT
            static const char* clientKeyPub  = CERT_ROOT "client-keyPub.der";
        #endif
    #endif /* !NO_RSA && !NO_ASN */
#endif
#if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048)
    #if !defined(NO_RSA) && !defined(NO_ASN)
        #if defined(WOLFSSL_CERT_GEN) || defined(HAVE_PKCS7)
            static const char* rsaCaKeyFile  = CERT_ROOT "ca-key.der";
            #ifdef WOLFSSL_CERT_GEN
            static const char* rsaCaCertFile = CERT_ROOT "ca-cert.pem";
            #endif
            #if defined(WOLFSSL_ALT_NAMES) || defined(HAVE_PKCS7)
            static const char* rsaCaCertDerFile = CERT_ROOT "ca-cert.der";
            #endif
            #ifdef HAVE_PKCS7
                static const char* rsaServerCertDerFile =
                                               CERT_ROOT "server-cert.der";
                static const char* rsaServerKeyDerFile =
                                               CERT_ROOT "server-key.der";
            #endif
        #endif
    #endif /* !NO_RSA && !NO_ASN */
#endif /* !USE_CERT_BUFFER_* */
#if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048) && \
    !defined(USE_CERT_BUFFERS_3072) && !defined(USE_CERT_BUFFERS_4096) && \
    !defined(NO_ASN)
    #ifndef NO_DH
        static const char* dhParamsFile = CERT_ROOT "dh2048.der";
        #ifdef WOLFSSL_DH_EXTRA
            static const char* dhKeyFile = CERT_ROOT "statickeys/dh-ffdhe2048.der";
        #endif
    #endif
    #ifndef NO_DSA
        static const char* dsaKey = CERT_ROOT "dsa2048.der";
    #endif
#endif /* !USE_CERT_BUFFER_* */
#if !defined(USE_CERT_BUFFERS_256)
    #ifdef HAVE_ECC
        /* cert files to be used in rsa cert gen test, check if RSA enabled */
        #ifdef HAVE_ECC_KEY_IMPORT
            static const char* eccKeyDerFile = CERT_ROOT "ecc-key.der";
        #endif
#endif
#if !defined(USE_CERT_BUFFERS_256) && !defined(NO_ASN)
        #if defined(HAVE_ECC) && defined(WOLFSSL_CERT_GEN)
            #ifndef NO_RSA
                /* eccKeyPubFile is used in a test that requires RSA. */
                static const char* eccKeyPubFile = CERT_ROOT "ecc-keyPub.der";
            #endif
            static const char* eccCaKeyFile  = CERT_ROOT "ca-ecc-key.der";
            static const char* eccCaCertFile = CERT_ROOT "ca-ecc-cert.pem";
            #ifdef ENABLE_ECC384_CERT_GEN_TEST
                static const char* eccCaKey384File =
                                               CERT_ROOT "ca-ecc384-key.der";
                static const char* eccCaCert384File =
                                               CERT_ROOT "ca-ecc384-cert.pem";
            #endif
        #endif
        #if defined(HAVE_PKCS7) && defined(HAVE_ECC)
            static const char* eccClientKey  = CERT_ROOT "ecc-client-key.der";
            static const char* eccClientCert = CERT_ROOT "client-ecc-cert.der";
        #endif
    #endif /* HAVE_ECC */
    #ifdef HAVE_ED25519
        #ifdef WOLFSSL_TEST_CERT
            static const char* serverEd25519Cert =
                                         CERT_ROOT "ed25519/server-ed25519.der";
            static const char* caEd25519Cert     =
                                             CERT_ROOT "ed25519/ca-ed25519.der";
        #endif
    #endif
    #ifdef HAVE_ED448
        #ifdef WOLFSSL_TEST_CERT
            static const char* serverEd448Cert =
                                             CERT_ROOT "ed448/server-ed448.der";
            static const char* caEd448Cert     = CERT_ROOT "ed448/ca-ed448.der";
        #endif
    #endif
#endif /* !USE_CERT_BUFFER_* */

#ifndef NO_WRITE_TEMP_FILES
#ifdef HAVE_ECC
    #ifdef WOLFSSL_CERT_GEN
         static const char* certEccPemFile =   CERT_PREFIX "certecc.pem";
    #endif
    #if defined(WOLFSSL_CERT_GEN) && !defined(NO_RSA)
        static const char* certEccRsaPemFile = CERT_PREFIX "certeccrsa.pem";
        static const char* certEccRsaDerFile = CERT_PREFIX "certeccrsa.der";
    #endif
        static const char* eccCaKeyPemFile  = CERT_PREFIX "ecc-key.pem";
        static const char* eccPubKeyDerFile = CERT_PREFIX "ecc-public-key.der";
        static const char* eccCaKeyTempFile = CERT_PREFIX "ecc-key.der";
    #ifdef HAVE_PKCS8
        static const char* eccPkcs8KeyDerFile = CERT_PREFIX "ecc-key-pkcs8.der";
    #endif
    #if defined(WOLFSSL_CERT_GEN) || \
            (defined(WOLFSSL_CERT_EXT) && defined(WOLFSSL_TEST_CERT))
        static const char* certEccDerFile = CERT_PREFIX "certecc.der";
    #endif
#endif /* HAVE_ECC */

#ifndef NO_RSA
    #if defined(WOLFSSL_CERT_GEN) || \
        (defined(WOLFSSL_CERT_EXT) && defined(WOLFSSL_TEST_CERT))
        static const char* otherCertDerFile = CERT_PREFIX "othercert.der";
        static const char* certDerFile = CERT_PREFIX "cert.der";
    #endif
    #ifdef WOLFSSL_CERT_GEN
        static const char* otherCertPemFile = CERT_PREFIX "othercert.pem";
        static const char* certPemFile = CERT_PREFIX "cert.pem";
    #endif
    #ifdef WOLFSSL_CERT_REQ
        static const char* certReqDerFile = CERT_PREFIX "certreq.der";
        static const char* certReqPemFile = CERT_PREFIX "certreq.pem";
    #endif
#endif /* !NO_RSA */

#if !defined(NO_RSA) || !defined(NO_DSA)
    #ifdef WOLFSSL_KEY_GEN
        static const char* keyDerFile = CERT_PREFIX "key.der";
        static const char* keyPemFile = CERT_PREFIX "key.pem";
    #endif
#endif

#endif /* !NO_WRITE_TEMP_FILES */
#endif /* !NO_FILESYSTEM */


#if defined(WOLFSSL_CERT_GEN) && (!defined(NO_RSA) || defined(HAVE_ECC)) || \
  (defined(WOLFSSL_TEST_CERT) && (defined(HAVE_ED25519) || defined(HAVE_ED448)))
#ifdef WOLFSSL_MULTI_ATTRIB
static CertName certDefaultName;
static void initDefaultName(void)
{
    XMEMCPY(certDefaultName.country, "US", sizeof("US"));
    certDefaultName.countryEnc = CTC_PRINTABLE;
    XMEMCPY(certDefaultName.state, "Oregon", sizeof("Oregon"));
    certDefaultName.stateEnc = CTC_UTF8;
    XMEMCPY(certDefaultName.locality, "Portland", sizeof("Portland"));
    certDefaultName.localityEnc = CTC_UTF8;
    XMEMCPY(certDefaultName.sur, "Test", sizeof("Test"));
    certDefaultName.surEnc = CTC_UTF8;
    XMEMCPY(certDefaultName.org, "wolfSSL", sizeof("wolfSSL"));
    certDefaultName.orgEnc = CTC_UTF8;
    XMEMCPY(certDefaultName.unit, "Development", sizeof("Development"));
    certDefaultName.unitEnc = CTC_UTF8;
    XMEMCPY(certDefaultName.commonName, "www.wolfssl.com", sizeof("www.wolfssl.com"));
    certDefaultName.commonNameEnc = CTC_UTF8;
    XMEMCPY(certDefaultName.serialDev, "wolfSSL12345", sizeof("wolfSSL12345"));
    certDefaultName.serialDevEnc = CTC_PRINTABLE;
#ifdef WOLFSSL_CERT_EXT
    XMEMCPY(certDefaultName.busCat, "Private Organization", sizeof("Private Organization"));
    certDefaultName.busCatEnc = CTC_UTF8;
#endif
    XMEMCPY(certDefaultName.email, "info@wolfssl.com", sizeof("info@wolfssl.com"));

#ifdef WOLFSSL_TEST_CERT
    {
        NameAttrib* n;
        /* test having additional OUs and setting DC */
        n = &certDefaultName.name[0];
        n->id   = ASN_ORGUNIT_NAME;
        n->type = CTC_UTF8;
        n->sz   = sizeof("Development-2");
        XMEMCPY(n->value, "Development-2", sizeof("Development-2"));

    #if CTC_MAX_ATTRIB > 3
        n = &certDefaultName.name[1];
        n->id   = ASN_DOMAIN_COMPONENT;
        n->type = CTC_UTF8;
        n->sz   = sizeof("com");
        XMEMCPY(n->value, "com", sizeof("com"));

        n = &certDefaultName.name[2];
        n->id   = ASN_DOMAIN_COMPONENT;
        n->type = CTC_UTF8;
        n->sz   = sizeof("wolfssl");
        XMEMCPY(n->value, "wolfssl", sizeof("wolfssl"));

    #endif
    }
#endif /* WOLFSSL_TEST_CERT */
}
#else
static const CertName certDefaultName = {
    "US",               CTC_PRINTABLE,  /* country */
    "Oregon",           CTC_UTF8,       /* state */
    "Portland",         CTC_UTF8,       /* locality */
    "Test",             CTC_UTF8,       /* sur */
    "wolfSSL",          CTC_UTF8,       /* org */
    "Development",      CTC_UTF8,       /* unit */
    "www.wolfssl.com",  CTC_UTF8,       /* commonName */
    "wolfSSL12345",     CTC_PRINTABLE,  /* serial number of device */
#ifdef WOLFSSL_CERT_EXT
    "Private Organization", CTC_UTF8,   /* businessCategory */
    "US",               CTC_PRINTABLE,  /* jurisdiction country */
    "Oregon",           CTC_PRINTABLE,  /* jurisdiction state */
#endif
    "info@wolfssl.com"                  /* email */
};
#endif /* WOLFSSL_MULTI_ATTRIB */

#ifdef WOLFSSL_CERT_EXT
    #if ((defined(HAVE_ED25519) || defined(HAVE_ED448)) && \
                                defined(WOLFSSL_TEST_CERT)) || defined(HAVE_ECC)
    static const char certKeyUsage[] =
        "digitalSignature,nonRepudiation";
    #endif
    #if (defined(WOLFSSL_CERT_REQ) || defined(HAVE_NTRU)) && !defined(NO_RSA)
        static const char certKeyUsage2[] =
        "digitalSignature,nonRepudiation,keyEncipherment,keyAgreement";
    #endif
#endif /* WOLFSSL_CERT_EXT */
#endif /* WOLFSSL_CERT_GEN */

#ifndef NO_RSA

#if !defined(NO_ASN_TIME) && !defined(NO_RSA) && defined(WOLFSSL_TEST_CERT) && \
    !defined(NO_FILESYSTEM)
static byte minSerial[] = { 0x02, 0x01, 0x01 };
static byte minName[] = { 0x30, 0x00 };
static byte nameBad[] = {
    0x30, 0x08,
          0x31, 0x06,
                0x30, 0x04,
                      0x06, 0x02,
                            0x55, 0x04,
};
static byte minDates[] = {
    0x30, 0x1e,
          0x17, 0x0d,
                0x31, 0x38, 0x30, 0x34, 0x31, 0x33, 0x31, 0x35,
                0x32, 0x33, 0x31, 0x30, 0x5a,
          0x17, 0x0d,
                0x32, 0x31, 0x30, 0x31, 0x30, 0x37, 0x31, 0x35,
                0x32, 0x33, 0x31, 0x30, 0x5a
};
static byte minPubKey[] = {
    0x30, 0x1b,
          0x30, 0x0d,
                0x06, 0x09,
                      0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01,
                      0x01,
                0x05, 0x00,
          0x03, 0x0b,
                0x00, 0x30, 0x08,
                            0x02, 0x01,
                                  0x03,
                            0x02, 0x03,
                                  0x01, 0x00, 0x01
};
static byte minSigAlg[] = {
    0x30, 0x0d,
          0x06, 0x09,
                0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01,
                0x0b,
          0x05, 0x00
};
static byte minSig[] = {
    0x03, 0x01,
          0x00
};

static int add_seq(byte* certData, int offset, byte* data, byte length)
{
    XMEMMOVE(certData + offset + 2, data, length);
    certData[offset++] = 0x30;
    certData[offset++] = length;
    return offset + length;
}
static int add_data(byte* certData, int offset, byte* data, byte length)
{
    XMEMCPY(certData + offset, data, length);
    return offset + length;
}

static int cert_asn1_test(void)
{
    int ret;
    int len[3];
    DecodedCert cert;
    byte certData[106];
    byte* badCert = NULL;

    len[2] = add_data(certData, 0, minSerial, (byte)sizeof(minSerial));
    len[2] = add_data(certData, len[2], minSigAlg, (byte)sizeof(minSigAlg));
    len[2] = add_data(certData, len[2], minName, (byte)sizeof(minName));
    len[2] = add_data(certData, len[2], minDates, (byte)sizeof(minDates));
    len[2] = add_data(certData, len[2], minName, (byte)sizeof(minName));
    len[2] = add_data(certData, len[2], minPubKey, (byte)sizeof(minPubKey));
    len[1] = add_seq(certData, 0, certData, len[2]);
    len[1] = add_data(certData, len[1], minSigAlg, (byte)sizeof(minSigAlg));
    len[1] = add_data(certData, len[1], minSig, (byte)sizeof(minSig));
    len[0] = add_seq(certData, 0, certData, len[1]);

    /* Minimal good certificate */
    InitDecodedCert(&cert, certData, len[0], 0);
    ret = ParseCert(&cert, CERT_TYPE, NO_VERIFY, NULL);
    FreeDecodedCert(&cert);
    if (ret != 0) {
        ERROR_OUT(-7100, done);
    }

    /* Bad issuer name */
    len[2] = add_data(certData, 0, minSerial, (byte)sizeof(minSerial));
    len[2] = add_data(certData, len[2], minSigAlg, (byte)sizeof(minSigAlg));
    len[2] = add_data(certData, len[2], nameBad, (byte)sizeof(nameBad));
    len[1] = add_seq(certData, 0, certData, len[2]);
    len[0] = add_seq(certData, 0, certData, len[1]);
    /* Put data into allocated buffer to allow access error checking. */
    badCert = (byte*)XMALLOC(len[0], HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    XMEMCPY(badCert, certData, len[0]);
    InitDecodedCert(&cert, badCert, len[0], 0);
    ret = ParseCert(&cert, CERT_TYPE, NO_VERIFY, NULL);
    FreeDecodedCert(&cert);
    if (ret != ASN_PARSE_E) {
        ERROR_OUT(-7101, done);
    }
    XFREE(badCert, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    badCert = NULL;
    ret = 0;

done:
    if (badCert != NULL)
        XFREE(badCert, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    return ret;
}

int cert_test(void)
{
#if !defined(NO_FILESYSTEM)
    DecodedCert cert;
    byte*       tmp;
    size_t      bytes;
    XFILE       file;
    int         ret;

    tmp = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (tmp == NULL)
        return -7200;

    /* Certificate with Name Constraints extension. */
#ifdef FREESCALE_MQX
    file = XFOPEN(".\\certs\\test\\cert-ext-nc.der", "rb");
#else
    file = XFOPEN("./certs/test/cert-ext-nc.der", "rb");
#endif
    if (!file) {
        ERROR_OUT(-7201, done);
    }
    bytes = XFREAD(tmp, 1, FOURK_BUF, file);
    XFCLOSE(file);
    InitDecodedCert(&cert, tmp, (word32)bytes, 0);
    ret = ParseCert(&cert, CERT_TYPE, NO_VERIFY, NULL);
    if (ret != 0) {
        ERROR_OUT(-7202, done);
    }
    FreeDecodedCert(&cert);

    /* Certificate with Inhibit Any Policy extension. */
#ifdef FREESCALE_MQX
    file = XFOPEN(".\\certs\\test\\cert-ext-ia.der", "rb");
#else
    file = XFOPEN("./certs/test/cert-ext-ia.der", "rb");
#endif
    if (!file) {
        ERROR_OUT(-7203, done);
    }
    bytes = XFREAD(tmp, 1, FOURK_BUF, file);
    XFCLOSE(file);
    InitDecodedCert(&cert, tmp, (word32)bytes, 0);
    ret = ParseCert(&cert, CERT_TYPE, NO_VERIFY, NULL);
    if (ret != 0) {
        ERROR_OUT(-7204, done);
    }
    FreeDecodedCert(&cert);

    /* Certificate with Netscape Certificate Type extension. */
#ifdef FREESCALE_MQX
    file = XFOPEN(".\\certs\\test\\cert-ext-nct.der", "rb");
#else
    file = XFOPEN("./certs/test/cert-ext-nct.der", "rb");
#endif
    if (!file) {
        ERROR_OUT(-7203, done);
    }
    bytes = XFREAD(tmp, 1, FOURK_BUF, file);
    XFCLOSE(file);
    InitDecodedCert(&cert, tmp, (word32)bytes, 0);
    ret = ParseCert(&cert, CERT_TYPE, NO_VERIFY, NULL);
#ifndef IGNORE_NETSCAPE_CERT_TYPE
    if (ret != 0) {
        ERROR_OUT(-7204, done);
    }
#else
    if (ret != ASN_CRIT_EXT_E) {
        ERROR_OUT(-7205, done);
    }
    ret = 0;
#endif

done:
    FreeDecodedCert(&cert);
    XFREE(tmp, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
#endif /* !NO_FILESYSTEM */

    if (ret == 0)
        ret = cert_asn1_test();

    return ret;
}
#endif /* WOLFSSL_TEST_CERT */

#if defined(WOLFSSL_CERT_EXT) && defined(WOLFSSL_TEST_CERT) && \
   !defined(NO_FILESYSTEM)
int certext_test(void)
{
    DecodedCert cert;
    byte*       tmp;
    size_t      bytes;
    XFILE       file;
    int         ret;

    /* created from rsa_test : othercert.der */
    byte skid_rsa[]   = "\x33\xD8\x45\x66\xD7\x68\x87\x18\x7E\x54"
                        "\x0D\x70\x27\x91\xC7\x26\xD7\x85\x65\xC0";

    /* created from rsa_test : othercert.der */
    byte akid_rsa[] = "\x27\x8E\x67\x11\x74\xC3\x26\x1D\x3F\xED"
                      "\x33\x63\xB3\xA4\xD8\x1D\x30\xE5\xE8\xD5";

#ifdef HAVE_ECC
   /* created from ecc_test_cert_gen : certecc.der */
#ifdef ENABLE_ECC384_CERT_GEN_TEST
    /* Authority key id from ./certs/ca-ecc384-cert.pem */
    byte akid_ecc[] = "\xAB\xE0\xC3\x26\x4C\x18\xD4\x72\xBB\xD2"
                      "\x84\x8C\x9C\x0A\x05\x92\x80\x12\x53\x52";
#else
    /* Authority key id from ./certs/ca-ecc-cert.pem */
    byte akid_ecc[] = "\x56\x8E\x9A\xC3\xF0\x42\xDE\x18\xB9\x45"
                      "\x55\x6E\xF9\x93\xCF\xEA\xC3\xF3\xA5\x21";
#endif
#endif /* HAVE_ECC */

    /* created from rsa_test : cert.der */
    byte kid_ca[] = "\x33\xD8\x45\x66\xD7\x68\x87\x18\x7E\x54"
                    "\x0D\x70\x27\x91\xC7\x26\xD7\x85\x65\xC0";

    tmp = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (tmp == NULL)
        return -7300;

    /* load othercert.der (Cert signed by an authority) */
    file = XFOPEN(otherCertDerFile, "rb");
    if (!file) {
        XFREE(tmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        return -7301;
    }

    bytes = XFREAD(tmp, 1, FOURK_BUF, file);
    XFCLOSE(file);

    InitDecodedCert(&cert, tmp, (word32)bytes, 0);

    ret = ParseCert(&cert, CERT_TYPE, NO_VERIFY, 0);
    if (ret != 0)
        return -7302;

    /* check the SKID from a RSA certificate */
    if (XMEMCMP(skid_rsa, cert.extSubjKeyId, sizeof(cert.extSubjKeyId)))
        return -7303;

    /* check the AKID from an RSA certificate */
    if (XMEMCMP(akid_rsa, cert.extAuthKeyId, sizeof(cert.extAuthKeyId)))
        return -7304;

    /* check the Key Usage from an RSA certificate */
    if (!cert.extKeyUsageSet)
        return -7305;

    if (cert.extKeyUsage != (KEYUSE_KEY_ENCIPHER|KEYUSE_KEY_AGREE))
        return -7306;

    /* check the CA Basic Constraints from an RSA certificate */
    if (cert.isCA)
        return -7307;

#ifndef WOLFSSL_SEP /* test only if not using SEP policies */
    /* check the Certificate Policies Id */
    if (cert.extCertPoliciesNb != 1)
        return -7308;

    if (strncmp(cert.extCertPolicies[0], "2.16.840.1.101.3.4.1.42", 23))
        return -7309;
#endif

    FreeDecodedCert(&cert);

#ifdef HAVE_ECC
    /* load certecc.der (Cert signed by our ECC CA test in ecc_test_cert_gen) */
    file = XFOPEN(certEccDerFile, "rb");
    if (!file) {
        XFREE(tmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        return -7310;
    }

    bytes = XFREAD(tmp, 1, FOURK_BUF, file);
    XFCLOSE(file);

    InitDecodedCert(&cert, tmp, (word32)bytes, 0);

    ret = ParseCert(&cert, CERT_TYPE, NO_VERIFY, 0);
    if (ret != 0)
        return -7311;

    /* check the SKID from a ECC certificate - generated dynamically */

    /* check the AKID from an ECC certificate */
    if (XMEMCMP(akid_ecc, cert.extAuthKeyId, sizeof(cert.extAuthKeyId)))
        return -7312;

    /* check the Key Usage from an ECC certificate */
    if (!cert.extKeyUsageSet)
        return -7313;

    if (cert.extKeyUsage != (KEYUSE_DIGITAL_SIG|KEYUSE_CONTENT_COMMIT))
        return -7314;

    /* check the CA Basic Constraints from an ECC certificate */
    if (cert.isCA)
        return -7315;

#ifndef WOLFSSL_SEP /* test only if not using SEP policies */
    /* check the Certificate Policies Id */
    if (cert.extCertPoliciesNb != 2)
        return -7316;

    if (strncmp(cert.extCertPolicies[0], "2.4.589440.587.101.2.1.9632587.1", 32))
        return -7317;

    if (strncmp(cert.extCertPolicies[1], "1.2.13025.489.1.113549", 22))
        return -7318;
#endif

    FreeDecodedCert(&cert);
#endif /* HAVE_ECC */

    /* load cert.der (self signed certificate) */
    file = XFOPEN(certDerFile, "rb");
    if (!file) {
        XFREE(tmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        return -7319;
    }

    bytes = XFREAD(tmp, 1, FOURK_BUF, file);
    XFCLOSE(file);

    InitDecodedCert(&cert, tmp, (word32)bytes, 0);

    ret = ParseCert(&cert, CERT_TYPE, NO_VERIFY, 0);
    if (ret != 0)
        return -7320;

    /* check the SKID from a CA certificate */
    if (XMEMCMP(kid_ca, cert.extSubjKeyId, sizeof(cert.extSubjKeyId)))
        return -7321;

    /* check the AKID from an CA certificate */
    if (XMEMCMP(kid_ca, cert.extAuthKeyId, sizeof(cert.extAuthKeyId)))
        return -7322;

    /* check the Key Usage from CA certificate */
    if (!cert.extKeyUsageSet)
        return -7323;

    if (cert.extKeyUsage != (KEYUSE_KEY_CERT_SIGN|KEYUSE_CRL_SIGN))
        return -7324;

    /* check the CA Basic Constraints CA certificate */
    if (!cert.isCA)
        return -7325;

#ifndef WOLFSSL_SEP /* test only if not using SEP policies */
    /* check the Certificate Policies Id */
    if (cert.extCertPoliciesNb != 2)
        return -7326;

    if (strncmp(cert.extCertPolicies[0], "2.16.840.1.101.3.4.1.42", 23))
        return -7327;

    if (strncmp(cert.extCertPolicies[1], "1.2.840.113549.1.9.16.6.5", 25))
        return -7328;
#endif

    FreeDecodedCert(&cert);
    XFREE(tmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);

    return 0;
}
#endif /* WOLFSSL_CERT_EXT && WOLFSSL_TEST_CERT */

#if defined(WOLFSSL_CERT_GEN_CACHE) && defined(WOLFSSL_TEST_CERT) && \
    defined(WOLFSSL_CERT_EXT) && defined(WOLFSSL_CERT_GEN)
int decodedCertCache_test(void)
{
    int ret = 0;
    Cert cert;
    FILE* file;
    byte* der;
    word32 derSz;

    derSz = FOURK_BUF;
    der = XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (der == NULL)
        ret = -7400;

    if (ret == 0) {
        /* load cert.der */
        file = XFOPEN(certDerFile, "rb");
        if (file != NULL) {
            derSz = XFREAD(der, 1, FOURK_BUF, file);
            XFCLOSE(file);
        }
        else
            ret = -7401;
    }

    if (ret == 0) {
        if (wc_InitCert(&cert)) {
            ret = -7402;
        }
    }

    if (ret == 0) {
        ret = wc_SetSubjectBuffer(&cert, der, derSz);
    }

    if (ret == 0) {
        if(wc_SetSubjectBuffer(NULL, der, derSz) != BAD_FUNC_ARG)
            ret = -7403;
    }

    if (ret == 0) {
        if (wc_SetSubjectRaw(&cert, der, derSz) != 0)
            ret = -7404;
    }

    if (ret == 0) {
        if(wc_SetSubjectRaw(NULL, der, derSz) != BAD_FUNC_ARG)
            ret = -7405;
    }

    if (ret == 0) {
        if(wc_SetIssuerBuffer(&cert, der, derSz) != 0)
            ret = -7406;
    }

    if (ret == 0) {
        if(wc_SetIssuerBuffer(NULL, der, derSz) != BAD_FUNC_ARG)
            ret = -7407;
    }

    if (ret == 0) {
        if(wc_SetIssuerRaw(&cert, der, derSz) != 0)
            ret = -7408;
    }

    if (ret == 0) {
        if(wc_SetIssuerRaw(NULL, der, derSz) != BAD_FUNC_ARG)
            ret = -7409;
    }

#ifdef WOLFSSL_ALT_NAMES
    if (ret == 0) {
        if(wc_SetAltNamesBuffer(&cert, der, derSz) != 0)
            ret = -7410;
    }

    if (ret == 0) {
        if(wc_SetAltNamesBuffer(NULL, der, derSz) != BAD_FUNC_ARG)
            ret = -7411;
    }

    if (ret == 0) {
        if(wc_SetDatesBuffer(&cert, der, derSz) != 0)
            ret = -7412;
    }

    if (ret == 0) {
        if(wc_SetDatesBuffer(NULL, der, derSz) != BAD_FUNC_ARG)
            ret = -7413;
    }
#endif

    if (ret == 0) {
        if(wc_SetAuthKeyIdFromCert(&cert, der, derSz) != 0)
            ret = -7414;
    }

    if (ret == 0) {
        if(wc_SetAuthKeyIdFromCert(NULL, der, derSz) != BAD_FUNC_ARG)
            ret = -7415;
    }

    wc_SetCert_Free(&cert);
    if (ret == 0) {
        if(cert.decodedCert != NULL)
            ret = -7416;
    }

    XFREE(der, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);

    return ret;
}
#endif /* defined(WOLFSSL_CERT_GEN_CACHE) && defined(WOLFSSL_TEST_CERT) &&
          defined(WOLFSSL_CERT_EXT) && defined(WOLFSSL_CERT_GEN) */

#define RSA_TEST_BYTES 512 /* up to 4096-bit key */

#if !defined(NO_ASN) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)
static int rsa_flatten_test(RsaKey* key)
{
    int    ret;
    byte   e[RSA_TEST_BYTES];
    byte   n[RSA_TEST_BYTES];
    word32 eSz = sizeof(e);
    word32 nSz = sizeof(n);

    /* Parameter Validation testing. */
    ret = wc_RsaFlattenPublicKey(NULL, e, &eSz, n, &nSz);
#ifdef HAVE_USER_RSA
    /* Implementation using IPP Libraries returns:
     *     -101 = USER_CRYPTO_ERROR
     */
    if (ret == 0)
#else
    if (ret != BAD_FUNC_ARG)
#endif
        return -7417;
    ret = wc_RsaFlattenPublicKey(key, NULL, &eSz, n, &nSz);
#ifdef HAVE_USER_RSA
    /* Implementation using IPP Libraries returns:
     *     -101 = USER_CRYPTO_ERROR
     */
    if (ret == 0)
#else
    if (ret != BAD_FUNC_ARG)
#endif
        return -7418;
    ret = wc_RsaFlattenPublicKey(key, e, NULL, n, &nSz);
#ifdef HAVE_USER_RSA
    /* Implementation using IPP Libraries returns:
     *     -101 = USER_CRYPTO_ERROR
     */
    if (ret == 0)
#else
    if (ret != BAD_FUNC_ARG)
#endif
        return -7419;
    ret = wc_RsaFlattenPublicKey(key, e, &eSz, NULL, &nSz);
#ifdef HAVE_USER_RSA
    /* Implementation using IPP Libraries returns:
     *     -101 = USER_CRYPTO_ERROR
     */
    if (ret == 0)
#else
    if (ret != BAD_FUNC_ARG)
#endif
        return -7420;
    ret = wc_RsaFlattenPublicKey(key, e, &eSz, n, NULL);
#ifdef HAVE_USER_RSA
    /* Implementation using IPP Libraries returns:
     *     -101 = USER_CRYPTO_ERROR
     */
    if (ret == 0)
#else
    if (ret != BAD_FUNC_ARG)
#endif
        return -7421;
    ret = wc_RsaFlattenPublicKey(key, e, &eSz, n, &nSz);
    if (ret != 0)
        return -7422;
    eSz = 0;
    ret = wc_RsaFlattenPublicKey(key, e, &eSz, n, &nSz);
#ifdef HAVE_USER_RSA
    /* Implementation using IPP Libraries returns:
     *     -101 = USER_CRYPTO_ERROR
     */
    if (ret == 0)
#elif defined(HAVE_FIPS) && \
      (!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION < 2))
    if (ret != 0)
#else
    if (ret != RSA_BUFFER_E)
#endif
        return -7423;
    eSz = sizeof(e);
    nSz = 0;
    ret = wc_RsaFlattenPublicKey(key, e, &eSz, n, &nSz);
#ifdef HAVE_USER_RSA
    /* Implementation using IPP Libraries returns:
     *     -101 = USER_CRYPTO_ERROR
     */
    if (ret == 0)
#else
    if (ret != RSA_BUFFER_E)
#endif
        return -7424;

    return 0;
}
#endif /* NO_ASN */

#if !defined(HAVE_FIPS) && !defined(HAVE_USER_RSA) && !defined(NO_ASN) \
    && !defined(WOLFSSL_RSA_VERIFY_ONLY)
static int rsa_export_key_test(RsaKey* key)
{
    int ret;
    byte e[3];
    word32 eSz = sizeof(e);
    byte n[RSA_TEST_BYTES];
    word32 nSz = sizeof(n);
    byte d[RSA_TEST_BYTES];
    word32 dSz = sizeof(d);
    byte p[RSA_TEST_BYTES/2];
    word32 pSz = sizeof(p);
    byte q[RSA_TEST_BYTES/2];
    word32 qSz = sizeof(q);
    word32 zero = 0;

    ret = wc_RsaExportKey(NULL, e, &eSz, n, &nSz, d, &dSz, p, &pSz, q, &qSz);
    if (ret != BAD_FUNC_ARG)
        return -7425;
    ret = wc_RsaExportKey(key, NULL, &eSz, n, &nSz, d, &dSz, p, &pSz, q, &qSz);
    if (ret != BAD_FUNC_ARG)
        return -7426;
    ret = wc_RsaExportKey(key, e, NULL, n, &nSz, d, &dSz, p, &pSz, q, &qSz);
    if (ret != BAD_FUNC_ARG)
        return -7427;
    ret = wc_RsaExportKey(key, e, &eSz, NULL, &nSz, d, &dSz, p, &pSz, q, &qSz);
    if (ret != BAD_FUNC_ARG)
        return -7428;
    ret = wc_RsaExportKey(key, e, &eSz, n, NULL, d, &dSz, p, &pSz, q, &qSz);
    if (ret != BAD_FUNC_ARG)
        return -7429;
    ret = wc_RsaExportKey(key, e, &eSz, n, &nSz, NULL, &dSz, p, &pSz, q, &qSz);
    if (ret != BAD_FUNC_ARG)
        return -7430;
    ret = wc_RsaExportKey(key, e, &eSz, n, &nSz, d, NULL, p, &pSz, q, &qSz);
    if (ret != BAD_FUNC_ARG)
        return -7431;
    ret = wc_RsaExportKey(key, e, &eSz, n, &nSz, d, &dSz, NULL, &pSz, q, &qSz);
    if (ret != BAD_FUNC_ARG)
        return -7432;
    ret = wc_RsaExportKey(key, e, &eSz, n, &nSz, d, &dSz, p, NULL, q, &qSz);
    if (ret != BAD_FUNC_ARG)
        return -7433;
    ret = wc_RsaExportKey(key, e, &eSz, n, &nSz, d, &dSz, p, &pSz, NULL, &qSz);
    if (ret != BAD_FUNC_ARG)
        return -7434;
    ret = wc_RsaExportKey(key, e, &eSz, n, &nSz, d, &dSz, p, &pSz, q, NULL);
    if (ret != BAD_FUNC_ARG)
        return -7435;

    ret = wc_RsaExportKey(key, e, &zero, n, &nSz, d, &dSz, p, &pSz, q, &qSz);
    if (ret != RSA_BUFFER_E)
        return -7436;
    ret = wc_RsaExportKey(key, e, &eSz, n, &zero, d, &dSz, p, &pSz, q, &qSz);
    if (ret != RSA_BUFFER_E)
        return -7437;
#ifndef WOLFSSL_RSA_PUBLIC_ONLY
    ret = wc_RsaExportKey(key, e, &eSz, n, &nSz, d, &zero, p, &pSz, q, &qSz);
    if (ret != RSA_BUFFER_E)
        return -7438;
    ret = wc_RsaExportKey(key, e, &eSz, n, &nSz, d, &dSz, p, &zero, q, &qSz);
    if (ret != RSA_BUFFER_E)
        return -7439;
    ret = wc_RsaExportKey(key, e, &eSz, n, &nSz, d, &dSz, p, &pSz, q, &zero);
    if (ret != RSA_BUFFER_E)
        return -7440;
#endif /* WOLFSSL_RSA_PUBLIC_ONLY */

    ret = wc_RsaExportKey(key, e, &eSz, n, &nSz, d, &dSz, p, &pSz, q, &qSz);
    if (ret != 0)
        return -7441;

    return 0;
}
#endif /* !HAVE_FIPS && !USER_RSA && !NO_ASN */

#ifndef NO_SIG_WRAPPER
static int rsa_sig_test(RsaKey* key, word32 keyLen, int modLen, WC_RNG* rng)
{
    int ret;
    word32 sigSz;
    const byte in[] = "Everyone gets Friday off.";
    const byte hash[] = {
        0xf2, 0x02, 0x95, 0x65, 0xcb, 0xf6, 0x2a, 0x59,
        0x39, 0x2c, 0x05, 0xff, 0x0e, 0x29, 0xaf, 0xfe,
        0x47, 0x33, 0x8c, 0x99, 0x8d, 0x58, 0x64, 0x83,
        0xa6, 0x58, 0x0a, 0x33, 0x0b, 0x84, 0x5f, 0x5f
    };
    const byte hashEnc[] = {
        0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86,
        0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05,
        0x00, 0x04, 0x20,

        0xf2, 0x02, 0x95, 0x65, 0xcb, 0xf6, 0x2a, 0x59,
        0x39, 0x2c, 0x05, 0xff, 0x0e, 0x29, 0xaf, 0xfe,
        0x47, 0x33, 0x8c, 0x99, 0x8d, 0x58, 0x64, 0x83,
        0xa6, 0x58, 0x0a, 0x33, 0x0b, 0x84, 0x5f, 0x5f
    };
    word32 inLen = (word32)XSTRLEN((char*)in);
    byte   out[RSA_TEST_BYTES];

    /* Parameter Validation testing. */
    ret = wc_SignatureGetSize(WC_SIGNATURE_TYPE_NONE, key, keyLen);
    if (ret != BAD_FUNC_ARG)
        return -7442;
    ret = wc_SignatureGetSize(WC_SIGNATURE_TYPE_RSA, key, 0);
    if (ret != BAD_FUNC_ARG)
        return -7443;

    sigSz = (word32)modLen;
    ret = wc_SignatureGenerate(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA, NULL,
                               inLen, out, &sigSz, key, keyLen, rng);
    if (ret != BAD_FUNC_ARG)
        return -7444;
    ret = wc_SignatureGenerate(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA, in,
                               0, out, &sigSz, key, keyLen, rng);
    if (ret != BAD_FUNC_ARG)
        return -7445;
    ret = wc_SignatureGenerate(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA, in,
                               inLen, NULL, &sigSz, key, keyLen, rng);
    if (ret != BAD_FUNC_ARG)
        return -7446;
    ret = wc_SignatureGenerate(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA, in,
                               inLen, out, NULL, key, keyLen, rng);
    if (ret != BAD_FUNC_ARG)
        return -7447;
    ret = wc_SignatureGenerate(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA, in,
                               inLen, out, &sigSz, NULL, keyLen, rng);
    if (ret != BAD_FUNC_ARG)
        return -7448;
    ret = wc_SignatureGenerate(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA, in,
                               inLen, out, &sigSz, key, 0, rng);
    if (ret != BAD_FUNC_ARG)
        return -7449;
    ret = wc_SignatureGenerate(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA, in,
                               inLen, out, &sigSz, key, keyLen, NULL);
#ifdef HAVE_USER_RSA
    /* Implementation using IPP Libraries returns:
     *     -101 = USER_CRYPTO_ERROR
     */
    if (ret == 0)
#elif defined(WOLFSSL_AFALG_XILINX_RSA) || defined(WOLFSSL_XILINX_CRYPT)
    /* blinding / rng handled with hardware acceleration */
    if (ret != 0)
#elif defined(WOLFSSL_ASYNC_CRYPT) || defined(WOLF_CRYPTO_CB)
    /* async may not require RNG */
    if (ret != 0 && ret != MISSING_RNG_E)
#elif defined(HAVE_FIPS) || defined(WOLFSSL_ASYNC_CRYPT) || \
     !defined(WC_RSA_BLINDING)
    /* FIPS140 implementation does not do blinding */
    if (ret != 0)
#elif defined(WOLFSSL_RSA_PUBLIC_ONLY)
    if (ret != SIG_TYPE_E)
#elif defined(WOLFSSL_CRYPTOCELL)
    /* RNG is handled with the cryptocell */
    if (ret != 0)
#else
    if (ret != MISSING_RNG_E)
#endif
        return -7450;
    sigSz = 0;
    ret = wc_SignatureGenerate(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA, in,
                               inLen, out, &sigSz, key, keyLen, rng);
    if (ret != BAD_FUNC_ARG)
        return -7451;

    ret = wc_SignatureVerify(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA, NULL,
                             inLen, out, (word32)modLen, key, keyLen);
    if (ret != BAD_FUNC_ARG)
        return -7452;
    ret = wc_SignatureVerify(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA, in,
                             0, out, (word32)modLen, key, keyLen);
    if (ret != BAD_FUNC_ARG)
        return -7453;
    ret = wc_SignatureVerify(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA, in,
                             inLen, NULL, (word32)modLen, key, keyLen);
    if (ret != BAD_FUNC_ARG)
        return -7454;
    ret = wc_SignatureVerify(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA, in,
                             inLen, out, 0, key, keyLen);
    if (ret != BAD_FUNC_ARG)
        return -7455;
    ret = wc_SignatureVerify(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA, in,
                             inLen, out, (word32)modLen, NULL, keyLen);
    if (ret != BAD_FUNC_ARG)
        return -7456;
    ret = wc_SignatureVerify(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA, in,
                             inLen, out, (word32)modLen, key, 0);
    if (ret != BAD_FUNC_ARG)
        return -7457;

#ifndef HAVE_ECC
    ret = wc_SignatureGetSize(WC_SIGNATURE_TYPE_ECC, key, keyLen);
    if (ret != SIG_TYPE_E)
        return -7458;
#endif

    /* Use APIs. */
    ret = wc_SignatureGetSize(WC_SIGNATURE_TYPE_RSA, key, keyLen);
    if (ret != modLen)
        return -7459;
    ret = wc_SignatureGetSize(WC_SIGNATURE_TYPE_RSA_W_ENC, key, keyLen);
    if (ret != modLen)
        return -7460;

    sigSz = (word32)ret;
#ifndef WOLFSSL_RSA_PUBLIC_ONLY
    XMEMSET(out, 0, sizeof(out));
    ret = wc_SignatureGenerate(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA, in,
                               inLen, out, &sigSz, key, keyLen, rng);
    if (ret != 0)
        return -7461;

    ret = wc_SignatureVerify(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA, in,
                             inLen, out, (word32)modLen, key, keyLen);
    if (ret != 0)
        return -7462;

    sigSz = (word32)sizeof(out);
    ret = wc_SignatureGenerate(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA_W_ENC,
                               in, inLen, out, &sigSz, key, keyLen, rng);
    if (ret != 0)
        return -7463;

    ret = wc_SignatureVerify(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA_W_ENC,
                             in, inLen, out, (word32)modLen, key, keyLen);
    if (ret != 0)
        return -7464;

    /* Wrong signature type. */
    ret = wc_SignatureVerify(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA, in,
                             inLen, out, (word32)modLen, key, keyLen);
    if (ret == 0)
        return -7465;

    /* check hash functions */
    sigSz = (word32)sizeof(out);
    ret = wc_SignatureGenerateHash(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA,
        hash, (int)sizeof(hash), out, &sigSz, key, keyLen, rng);
    if (ret != 0)
        return -7466;

    ret = wc_SignatureVerifyHash(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA,
        hash, (int)sizeof(hash), out, (word32)modLen, key, keyLen);
    if (ret != 0)
        return -7467;

    sigSz = (word32)sizeof(out);
    ret = wc_SignatureGenerateHash(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA_W_ENC,
        hashEnc, (int)sizeof(hashEnc), out, &sigSz, key, keyLen, rng);
    if (ret != 0)
        return -7468;

    ret = wc_SignatureVerifyHash(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_RSA_W_ENC,
        hashEnc, (int)sizeof(hashEnc), out, (word32)modLen, key, keyLen);
    if (ret != 0)
        return -7469;
#else
    (void)hash;
    (void)hashEnc;
#endif /* WOLFSSL_RSA_PUBLIC_ONLY */

    return 0;
}
#endif /* !NO_SIG_WRAPPER */

#ifdef WC_RSA_NONBLOCK
static int rsa_nb_test(RsaKey* key, const byte* in, word32 inLen, byte* out,
    word32 outSz, byte* plain, word32 plainSz, WC_RNG* rng)
{
    int ret = 0, count;
    int signSz = 0;
    RsaNb nb;
    byte* inlinePlain = NULL;

    /* Enable non-blocking RSA mode - provide context */
    ret = wc_RsaSetNonBlock(key, &nb);
    if (ret != 0)
        return ret;

#ifdef WC_RSA_NONBLOCK_TIME
    /* Enable time based RSA blocking. 8 microseconds max (3.1GHz) */
    ret = wc_RsaSetNonBlockTime(key, 8, 3100);
    if (ret != 0)
        return ret;
#endif

    count = 0;
    do {
        ret = wc_RsaSSL_Sign(in, inLen, out, outSz, key, rng);
        count++; /* track number of would blocks */
        if (ret == FP_WOULDBLOCK) {
            /* do "other" work here */
        }
    } while (ret == FP_WOULDBLOCK);
    if (ret < 0) {
        return ret;
    }
#ifdef DEBUG_WOLFSSL
    printf("RSA non-block sign: %d times\n", count);
#endif
    signSz = ret;

    /* Test non-blocking verify */
    XMEMSET(plain, 0, plainSz);
    count = 0;
    do {
        ret = wc_RsaSSL_Verify(out, (word32)signSz, plain, plainSz, key);
        count++; /* track number of would blocks */
        if (ret == FP_WOULDBLOCK) {
            /* do "other" work here */
        }
    } while (ret == FP_WOULDBLOCK);
    if (ret < 0) {
        return ret;
    }
#ifdef DEBUG_WOLFSSL
    printf("RSA non-block verify: %d times\n", count);
#endif

    if (signSz == ret && XMEMCMP(plain, in, (size_t)ret)) {
        return SIG_VERIFY_E;
    }

    /* Test inline non-blocking verify */
    count = 0;
    do {
        ret = wc_RsaSSL_VerifyInline(out, (word32)signSz, &inlinePlain, key);
        count++; /* track number of would blocks */
        if (ret == FP_WOULDBLOCK) {
            /* do "other" work here */
        }
    } while (ret == FP_WOULDBLOCK);
    if (ret < 0) {
        return ret;
    }
#ifdef DEBUG_WOLFSSL
    printf("RSA non-block inline verify: %d times\n", count);
#endif

    if (signSz == ret && XMEMCMP(inlinePlain, in, (size_t)ret)) {
        return SIG_VERIFY_E;
    }

    /* Disabling non-block RSA mode */
    ret = wc_RsaSetNonBlock(key, NULL);

    (void)count;

    return 0;
}
#endif

#if !defined(HAVE_USER_RSA) && !defined(NO_ASN)
static int rsa_decode_test(RsaKey* keyPub)
{
    int        ret;
    word32     inSz;
    word32     inOutIdx;
    static const byte n[2] = { 0x00, 0x23 };
    static const byte e[2] = { 0x00, 0x03 };
    static const byte good[] = { 0x30, 0x06, 0x02, 0x01, 0x23, 0x02, 0x1,
           0x03 };
    static const byte goodAlgId[] = { 0x30, 0x0f, 0x30, 0x0d, 0x06, 0x00,
            0x03, 0x09, 0x00, 0x30, 0x06, 0x02, 0x01, 0x23, 0x02, 0x1, 0x03 };
    static const byte goodAlgIdNull[] = { 0x30, 0x11, 0x30, 0x0f, 0x06, 0x00,
            0x05, 0x00, 0x03, 0x09, 0x00, 0x30, 0x06, 0x02, 0x01, 0x23,
            0x02, 0x1, 0x03 };
    static const byte badAlgIdNull[] = { 0x30, 0x12, 0x30, 0x10, 0x06, 0x00,
            0x05, 0x01, 0x00, 0x03, 0x09, 0x00, 0x30, 0x06, 0x02, 0x01, 0x23,
            0x02, 0x1, 0x03 };
    static const byte badNotBitString[] = { 0x30, 0x0f, 0x30, 0x0d, 0x06, 0x00,
            0x04, 0x09, 0x00, 0x30, 0x06, 0x02, 0x01, 0x23, 0x02, 0x1, 0x03 };
    static const byte badBitStringLen[] = { 0x30, 0x0f, 0x30, 0x0d, 0x06, 0x00,
            0x03, 0x0a, 0x00, 0x30, 0x06, 0x02, 0x01, 0x23, 0x02, 0x1, 0x03 };
    static const byte badNoSeq[] = { 0x30, 0x0d, 0x30, 0x0b, 0x06, 0x00, 0x03,
            0x07, 0x00, 0x02, 0x01, 0x23, 0x02, 0x1, 0x03 };
    static const byte badNoObj[] = {
            0x30, 0x0f, 0x30, 0x0d, 0x05, 0x00, 0x03, 0x09, 0x00, 0x30, 0x06,
            0x02, 0x01, 0x23, 0x02, 0x1, 0x03 };
    static const byte badIntN[] = { 0x30, 0x06, 0x02, 0x05, 0x23, 0x02, 0x1,
            0x03 };
    static const byte badNotIntE[] = { 0x30, 0x06, 0x02, 0x01, 0x23, 0x04, 0x1,
            0x03 };
    static const byte badLength[] = { 0x30, 0x04, 0x02, 0x01, 0x23, 0x02, 0x1,
            0x03 };
    static const byte badBitStrNoZero[] = { 0x30, 0x0e, 0x30, 0x0c, 0x06, 0x00,
            0x03, 0x08, 0x30, 0x06, 0x02, 0x01, 0x23, 0x02, 0x1, 0x03 };

    ret = wc_InitRsaKey(keyPub, NULL);
    if (ret != 0)
        return -7470;

    /* Parameter Validation testing. */
    ret = wc_RsaPublicKeyDecodeRaw(NULL, sizeof(n), e, sizeof(e), keyPub);
    if (ret != BAD_FUNC_ARG) {
        ret = -7471;
        goto done;
    }
    ret = wc_RsaPublicKeyDecodeRaw(n, sizeof(n), NULL, sizeof(e), keyPub);
    if (ret != BAD_FUNC_ARG) {
        ret = -7472;
        goto done;
    }
    ret = wc_RsaPublicKeyDecodeRaw(n, sizeof(n), e, sizeof(e), NULL);
    if (ret != BAD_FUNC_ARG) {
        ret = -7473;
        goto done;
    }
    ret = wc_RsaPublicKeyDecodeRaw(n, (word32)-1, e, sizeof(e), keyPub);
#ifndef WOLFSSL_SP_MATH
    if (ret != 0) {
#else
    if (ret != ASN_GETINT_E) {
#endif
        ret = -7474;
        goto done;
    }
    wc_FreeRsaKey(keyPub);
    ret = wc_InitRsaKey(keyPub, NULL);
    if (ret != 0)
        return -7475;
    ret = wc_RsaPublicKeyDecodeRaw(n, sizeof(n), e, (word32)-1, keyPub);
#ifndef WOLFSSL_SP_MATH
    if (ret != 0) {
#else
    if (ret != ASN_GETINT_E) {
#endif
        ret = -7476;
        goto done;
    }
    wc_FreeRsaKey(keyPub);
    ret = wc_InitRsaKey(keyPub, NULL);
    if (ret != 0)
        return -7477;

    /* Use API. */
    ret = wc_RsaPublicKeyDecodeRaw(n, sizeof(n), e, sizeof(e), keyPub);
    if (ret != 0) {
        ret = -7478;
        goto done;
    }
    wc_FreeRsaKey(keyPub);
    ret = wc_InitRsaKey(keyPub, NULL);
    if (ret != 0)
        return -7479;

    /* Parameter Validation testing. */
    inSz = sizeof(good);
    ret = wc_RsaPublicKeyDecode(NULL, &inOutIdx, keyPub, inSz);
    if (ret != BAD_FUNC_ARG) {
        ret = -7480;
        goto done;
    }
    ret = wc_RsaPublicKeyDecode(good, NULL, keyPub, inSz);
    if (ret != BAD_FUNC_ARG) {
        ret = -7481;
        goto done;
    }
    ret = wc_RsaPublicKeyDecode(good, &inOutIdx, NULL, inSz);
    if (ret != BAD_FUNC_ARG) {
        ret = -7482;
        goto done;
    }

    /* Use good data and offset to bad data. */
    inOutIdx = 2;
    inSz = sizeof(good) - inOutIdx;
    ret = wc_RsaPublicKeyDecode(good, &inOutIdx, keyPub, inSz);
    if (ret != ASN_PARSE_E) {
        ret = -7483;
        goto done;
    }
    inOutIdx = 2;
    inSz = sizeof(goodAlgId) - inOutIdx;
    ret = wc_RsaPublicKeyDecode(goodAlgId, &inOutIdx, keyPub, inSz);
    if (ret != ASN_PARSE_E) {
        ret = -7484;
        goto done;
    }
    inOutIdx = 2;
    inSz = sizeof(goodAlgId);
    ret = wc_RsaPublicKeyDecode(goodAlgId, &inOutIdx, keyPub, inSz);
#ifndef WOLFSSL_NO_DECODE_EXTRA
    if (ret != ASN_PARSE_E)
#else
    if (ret != ASN_RSA_KEY_E)
#endif
    {
        ret = -7485;
        goto done;
    }
    /* Try different bad data. */
    inSz = sizeof(badAlgIdNull);
    inOutIdx = 0;
    ret = wc_RsaPublicKeyDecode(badAlgIdNull, &inOutIdx, keyPub, inSz);
    if (ret != ASN_EXPECT_0_E) {
        ret = -7486;
        goto done;
    }
    inSz = sizeof(badNotBitString);
    inOutIdx = 0;
    ret = wc_RsaPublicKeyDecode(badNotBitString, &inOutIdx, keyPub, inSz);
    if (ret != ASN_BITSTR_E) {
        ret = -7487;
        goto done;
    }
    inSz = sizeof(badBitStringLen);
    inOutIdx = 0;
    ret = wc_RsaPublicKeyDecode(badBitStringLen, &inOutIdx, keyPub, inSz);
    if (ret != ASN_PARSE_E) {
        ret = -7488;
        goto done;
    }
    inSz = sizeof(badNoSeq);
    inOutIdx = 0;
    ret = wc_RsaPublicKeyDecode(badNoSeq, &inOutIdx, keyPub, inSz);
    if (ret != ASN_PARSE_E) {
        ret = -7489;
        goto done;
    }
    inSz = sizeof(badNoObj);
    inOutIdx = 0;
    ret = wc_RsaPublicKeyDecode(badNoObj, &inOutIdx, keyPub, inSz);
    if (ret != ASN_PARSE_E) {
        ret = -7490;
        goto done;
    }
    inSz = sizeof(badIntN);
    inOutIdx = 0;
    ret = wc_RsaPublicKeyDecode(badIntN, &inOutIdx, keyPub, inSz);
    if (ret != ASN_RSA_KEY_E) {
        ret = -7491;
        goto done;
    }
    inSz = sizeof(badNotIntE);
    inOutIdx = 0;
    ret = wc_RsaPublicKeyDecode(badNotIntE, &inOutIdx, keyPub, inSz);
    if (ret != ASN_RSA_KEY_E) {
        ret = -7492;
        goto done;
    }
    /* TODO: Shouldn't pass as the sequence length is too small. */
    inSz = sizeof(badLength);
    inOutIdx = 0;
    ret = wc_RsaPublicKeyDecode(badLength, &inOutIdx, keyPub, inSz);
    if (ret != 0) {
        ret = -7493;
        goto done;
    }
    /* TODO: Shouldn't ignore object id's data. */
    wc_FreeRsaKey(keyPub);
    ret = wc_InitRsaKey(keyPub, NULL);
    if (ret != 0)
        return -7494;

    inSz = sizeof(badBitStrNoZero);
    inOutIdx = 0;
    ret = wc_RsaPublicKeyDecode(badBitStrNoZero, &inOutIdx, keyPub, inSz);
    if (ret != ASN_EXPECT_0_E) {
        ret = -7495;
        goto done;
    }
    wc_FreeRsaKey(keyPub);
    ret = wc_InitRsaKey(keyPub, NULL);
    if (ret != 0)
        return -7496;

    /* Valid data cases. */
    inSz = sizeof(good);
    inOutIdx = 0;
    ret = wc_RsaPublicKeyDecode(good, &inOutIdx, keyPub, inSz);
    if (ret != 0) {
        ret = -7497;
        goto done;
    }
    if (inOutIdx != inSz) {
        ret = -7498;
        goto done;
    }
    wc_FreeRsaKey(keyPub);
    ret = wc_InitRsaKey(keyPub, NULL);
    if (ret != 0)
        return -7499;

    inSz = sizeof(goodAlgId);
    inOutIdx = 0;
    ret = wc_RsaPublicKeyDecode(goodAlgId, &inOutIdx, keyPub, inSz);
    if (ret != 0) {
        ret = -7500;
        goto done;
    }
    if (inOutIdx != inSz) {
        ret = -7501;
        goto done;
    }
    wc_FreeRsaKey(keyPub);
    ret = wc_InitRsaKey(keyPub, NULL);
    if (ret != 0)
        return -7502;

    inSz = sizeof(goodAlgIdNull);
    inOutIdx = 0;
    ret = wc_RsaPublicKeyDecode(goodAlgIdNull, &inOutIdx, keyPub, inSz);
    if (ret != 0) {
        ret = -7503;
        goto done;
    }
    if (inOutIdx != inSz) {
        ret = -7504;
        goto done;
    }

done:
    wc_FreeRsaKey(keyPub);
    return ret;
}
#endif

#if defined(WC_RSA_PSS) && !defined(HAVE_FIPS_VERSION) /* not supported with FIPSv1 */
/* Need to create known good signatures to test with this. */
#ifndef WOLFSSL_RSA_VERIFY_ONLY
static int rsa_pss_test(WC_RNG* rng, RsaKey* key)
{
    byte             digest[WC_MAX_DIGEST_SIZE];
    int              ret     = 0;
    const char*      inStr   = "Everyone gets Friday off.";
    word32           inLen   = (word32)XSTRLEN((char*)inStr);
    word32           outSz;
    word32           plainSz;
    word32           digestSz;
    int              i, j;
#ifdef RSA_PSS_TEST_WRONG_PARAMS
    int              k, l;
#endif
    int              len;
    byte*            plain;
    int              mgf[]   = {
#ifndef NO_SHA
                                 WC_MGF1SHA1,
#endif
#ifdef WOLFSSL_SHA224
                                 WC_MGF1SHA224,
#endif
                                 WC_MGF1SHA256,
#ifdef WOLFSSL_SHA384
                                 WC_MGF1SHA384,
#endif
#ifdef WOLFSSL_SHA512
                                 WC_MGF1SHA512
#endif
                               };
    enum wc_HashType hash[]  = {
#ifndef NO_SHA
                                 WC_HASH_TYPE_SHA,
#endif
#ifdef WOLFSSL_SHA224
                                 WC_HASH_TYPE_SHA224,
#endif
                                 WC_HASH_TYPE_SHA256,
#ifdef WOLFSSL_SHA384
                                 WC_HASH_TYPE_SHA384,
#endif
#ifdef WOLFSSL_SHA512
                                 WC_HASH_TYPE_SHA512,
#endif
                               };

    DECLARE_VAR_INIT(in, byte, inLen, inStr, HEAP_HINT);
    DECLARE_VAR(out, byte, RSA_TEST_BYTES, HEAP_HINT);
    DECLARE_VAR(sig, byte, RSA_TEST_BYTES, HEAP_HINT);

    /* Test all combinations of hash and MGF. */
    for (j = 0; j < (int)(sizeof(hash)/sizeof(*hash)); j++) {
        /* Calculate hash of message. */
        ret = wc_Hash(hash[j], in, inLen, digest, sizeof(digest));
        if (ret != 0)
            ERROR_OUT(-7505, exit_rsa_pss);
        digestSz = wc_HashGetDigestSize(hash[j]);

        for (i = 0; i < (int)(sizeof(mgf)/sizeof(*mgf)); i++) {
            outSz = RSA_TEST_BYTES;
            do {
            #if defined(WOLFSSL_ASYNC_CRYPT)
                ret = wc_AsyncWait(ret, &key->asyncDev,
                    WC_ASYNC_FLAG_CALL_AGAIN);
            #endif
                if (ret >= 0) {
                    ret = wc_RsaPSS_Sign_ex(digest, digestSz, out, outSz,
                        hash[j], mgf[i], -1, key, rng);
                }
            } while (ret == WC_PENDING_E);
            if (ret <= 0)
                ERROR_OUT(-7506, exit_rsa_pss);
            outSz = ret;

            XMEMCPY(sig, out, outSz);
            plain = NULL;
            TEST_SLEEP();

            do {
            #if defined(WOLFSSL_ASYNC_CRYPT)
                ret = wc_AsyncWait(ret, &key->asyncDev,
                    WC_ASYNC_FLAG_CALL_AGAIN);
            #endif
                if (ret >= 0) {
                    ret = wc_RsaPSS_VerifyInline_ex(sig, outSz, &plain, hash[j],
                        mgf[i], -1, key);
                }
            } while (ret == WC_PENDING_E);
            if (ret <= 0)
                ERROR_OUT(-7507, exit_rsa_pss);
            plainSz = ret;
            TEST_SLEEP();

#if defined(HAVE_SELFTEST) && \
    (!defined(HAVE_SELFTEST_VERSION) || (HAVE_SELFTEST_VERSION < 2))
            ret = wc_RsaPSS_CheckPadding_ex(digest, digestSz, plain, plainSz,
                                         hash[j], -1);
#else
            ret = wc_RsaPSS_CheckPadding_ex(digest, digestSz, plain, plainSz,
                                         hash[j], -1, wc_RsaEncryptSize(key)*8);
#endif
            if (ret != 0)
                ERROR_OUT(-7508, exit_rsa_pss);

#ifdef RSA_PSS_TEST_WRONG_PARAMS
            for (k = 0; k < (int)(sizeof(mgf)/sizeof(*mgf)); k++) {
                for (l = 0; l < (int)(sizeof(hash)/sizeof(*hash)); l++) {
                    if (i == k && j == l)
                        continue;

                    XMEMCPY(sig, out, outSz);

                    do {
                    #if defined(WOLFSSL_ASYNC_CRYPT)
                        ret = wc_AsyncWait(ret, &key->asyncDev,
                            WC_ASYNC_FLAG_CALL_AGAIN);
                    #endif
                        if (ret >= 0) {
                            ret = wc_RsaPSS_VerifyInline_ex(sig, outSz,
                                (byte**)&plain, hash[l], mgf[k], -1, key);
                        }
                    } while (ret == WC_PENDING_E);
                    if (ret >= 0)
                        ERROR_OUT(-7509, exit_rsa_pss);
                }
            }
#endif
        }
    }

    /* Test that a salt length of zero works. */
    digestSz = wc_HashGetDigestSize(hash[0]);
    outSz = RSA_TEST_BYTES;
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key->asyncDev,
            WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret >= 0) {
            ret = wc_RsaPSS_Sign_ex(digest, digestSz, out, outSz, hash[0],
                mgf[0], 0, key, rng);
        }
    } while (ret == WC_PENDING_E);
    if (ret <= 0)
        ERROR_OUT(-7510, exit_rsa_pss);
    outSz = ret;
    TEST_SLEEP();

    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key->asyncDev,
            WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret >= 0) {
            ret = wc_RsaPSS_Verify_ex(out, outSz, sig, outSz, hash[0], mgf[0],
                0, key);
        }
    } while (ret == WC_PENDING_E);
    if (ret <= 0)
        ERROR_OUT(-7511, exit_rsa_pss);
    plainSz = ret;
    TEST_SLEEP();

    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key->asyncDev,
            WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret >= 0) {
#if defined(HAVE_SELFTEST) && \
    (!defined(HAVE_SELFTEST_VERSION) || (HAVE_SELFTEST_VERSION < 2))
            ret = wc_RsaPSS_CheckPadding_ex(digest, digestSz, sig, plainSz,
                hash[0], 0);
#else
            ret = wc_RsaPSS_CheckPadding_ex(digest, digestSz, sig, plainSz,
                hash[0], 0, 0);
#endif
        }
    } while (ret == WC_PENDING_E);
    if (ret != 0)
        ERROR_OUT(-7512, exit_rsa_pss);

    XMEMCPY(sig, out, outSz);
    plain = NULL;
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key->asyncDev,
            WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret >= 0) {
            ret = wc_RsaPSS_VerifyInline_ex(sig, outSz, &plain, hash[0], mgf[0],
                0, key);
        }
    } while (ret == WC_PENDING_E);
    if (ret <= 0)
        ERROR_OUT(-7513, exit_rsa_pss);
    plainSz = ret;
    TEST_SLEEP();

#if defined(HAVE_SELFTEST) && \
    (!defined(HAVE_SELFTEST_VERSION) || (HAVE_SELFTEST_VERSION < 2))
    ret = wc_RsaPSS_CheckPadding_ex(digest, digestSz, plain, plainSz, hash[0],
                                    0);
#else
    ret = wc_RsaPSS_CheckPadding_ex(digest, digestSz, plain, plainSz, hash[0],
                                    0, 0);
#endif
    if (ret != 0)
        ERROR_OUT(-7514, exit_rsa_pss);

    /* Test bad salt lengths in various APIs. */
    digestSz = wc_HashGetDigestSize(hash[0]);
    outSz = RSA_TEST_BYTES;
#ifndef WOLFSSL_PSS_SALT_LEN_DISCOVER
    len = -2;
#else
    len = -3;
#endif
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key->asyncDev,
            WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret >= 0) {
            ret = wc_RsaPSS_Sign_ex(digest, digestSz, out, outSz, hash[0],
                mgf[0], len, key, rng);
        }
    } while (ret == WC_PENDING_E);
    if (ret != PSS_SALTLEN_E)
        ERROR_OUT(-7515, exit_rsa_pss);

    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key->asyncDev,
            WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret >= 0) {
            ret = wc_RsaPSS_Sign_ex(digest, digestSz, out, outSz, hash[0],
                mgf[0], digestSz + 1, key, rng);
        }
    } while (ret == WC_PENDING_E);
    if (ret != PSS_SALTLEN_E)
        ERROR_OUT(-7516, exit_rsa_pss);
    TEST_SLEEP();

    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key->asyncDev,
            WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret >= 0) {
            ret = wc_RsaPSS_VerifyInline_ex(sig, outSz, &plain, hash[0],
                mgf[0], -2, key);
        }
    } while (ret == WC_PENDING_E);
    if (ret != PSS_SALTLEN_E)
        ERROR_OUT(-7517, exit_rsa_pss);
    TEST_SLEEP();

    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key->asyncDev,
            WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret >= 0) {
            ret = wc_RsaPSS_VerifyInline_ex(sig, outSz, &plain, hash[0], mgf[0],
                digestSz + 1, key);
        }
    } while (ret == WC_PENDING_E);
    if (ret != PSS_SALTLEN_E)
        ERROR_OUT(-7518, exit_rsa_pss);
    TEST_SLEEP();

#ifndef WOLFSSL_PSS_SALT_LEN_DISCOVER
    len = -2;
#else
    len = -3;
#endif
#if defined(HAVE_SELFTEST) && \
    (!defined(HAVE_SELFTEST_VERSION) || (HAVE_SELFTEST_VERSION < 2))
    ret = wc_RsaPSS_CheckPadding_ex(digest, digestSz, plain, plainSz, hash[0],
                                    len);
#else
    ret = wc_RsaPSS_CheckPadding_ex(digest, digestSz, plain, plainSz, hash[0],
                                    len, 0);
#endif
    if (ret != PSS_SALTLEN_E)
        ERROR_OUT(-7519, exit_rsa_pss);
#ifndef WOLFSSL_PSS_LONG_SALT
    len = digestSz + 1;
#else
    len = plainSz - digestSz - 1;
#endif
#if defined(HAVE_SELFTEST) && \
    (!defined(HAVE_SELFTEST_VERSION) || (HAVE_SELFTEST_VERSION < 2))
    ret = wc_RsaPSS_CheckPadding_ex(digest, digestSz, plain, plainSz, hash[0],
                                    len);
#else
    ret = wc_RsaPSS_CheckPadding_ex(digest, digestSz, plain, plainSz, hash[0],
                                    len, 0);
#endif
    if (ret != PSS_SALTLEN_E)
        ERROR_OUT(-7520, exit_rsa_pss);

    ret = 0;
exit_rsa_pss:
    FREE_VAR(sig, HEAP_HINT);
    FREE_VAR(in, HEAP_HINT);
    FREE_VAR(out, HEAP_HINT);

    return ret;
}
#endif /* WOLFSSL_RSA_VERIFY_ONLY */
#endif

#ifdef WC_RSA_NO_PADDING
int rsa_no_pad_test(void)
{
    WC_RNG rng;
    RsaKey key;
    byte*  tmp;
    size_t bytes;
    int    ret;
    word32 inLen   = 0;
    word32 idx     = 0;
    word32 outSz   = RSA_TEST_BYTES;
    word32 plainSz = RSA_TEST_BYTES;
#if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048) && \
    !defined(USE_CERT_BUFFERS_3072) && !defined(USE_CERT_BUFFERS_4096) && \
    !defined(NO_FILESYSTEM)
    XFILE  file;
#endif
    DECLARE_VAR(out, byte, RSA_TEST_BYTES, HEAP_HINT);
    DECLARE_VAR(plain, byte, RSA_TEST_BYTES, HEAP_HINT);

    /* initialize stack structures */
    XMEMSET(&rng, 0, sizeof(rng));
    XMEMSET(&key, 0, sizeof(key));
#ifdef USE_CERT_BUFFERS_1024
    bytes = (size_t)sizeof_client_key_der_1024;
	if (bytes < (size_t)sizeof_client_cert_der_1024)
		bytes = (size_t)sizeof_client_cert_der_1024;
#elif defined(USE_CERT_BUFFERS_2048)
    bytes = (size_t)sizeof_client_key_der_2048;
	if (bytes < (size_t)sizeof_client_cert_der_2048)
		bytes = (size_t)sizeof_client_cert_der_2048;
#else
	bytes = FOURK_BUF;
#endif

    tmp = (byte*)XMALLOC(bytes, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (tmp == NULL
    #ifdef WOLFSSL_ASYNC_CRYPT
        || out == NULL || plain == NULL
    #endif
    ) {
        ERROR_OUT(-7600, exit_rsa_nopadding);
    }

#ifdef USE_CERT_BUFFERS_1024
    XMEMCPY(tmp, client_key_der_1024, (size_t)sizeof_client_key_der_1024);
#elif defined(USE_CERT_BUFFERS_2048)
    XMEMCPY(tmp, client_key_der_2048, (size_t)sizeof_client_key_der_2048);
#elif defined(USE_CERT_BUFFERS_3072)
    XMEMCPY(tmp, client_key_der_3072, (size_t)sizeof_client_key_der_3072);
#elif defined(USE_CERT_BUFFERS_4096)
    XMEMCPY(tmp, client_key_der_4096, (size_t)sizeof_client_key_der_4096);
#elif !defined(NO_FILESYSTEM)
    file = XFOPEN(clientKey, "rb");
    if (!file) {
        err_sys("can't open ./certs/client-key.der, "
                "Please run from wolfSSL home dir", -40);
        ERROR_OUT(-7601, exit_rsa_nopadding);
    }

    bytes = XFREAD(tmp, 1, FOURK_BUF, file);
    XFCLOSE(file);
#else
    /* No key to use. */
    ERROR_OUT(-7602, exit_rsa_nopadding);
#endif /* USE_CERT_BUFFERS */

    ret = wc_InitRsaKey_ex(&key, HEAP_HINT, devId);
    if (ret != 0) {
        ERROR_OUT(-7603, exit_rsa_nopadding);
    }
    ret = wc_RsaPrivateKeyDecode(tmp, &idx, &key, (word32)bytes);
    if (ret != 0) {
        ERROR_OUT(-7604, exit_rsa_nopadding);
    }

    /* after loading in key use tmp as the test buffer */

#ifndef HAVE_FIPS
    ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
    ret = wc_InitRng(&rng);
#endif
    if (ret != 0) {
        ERROR_OUT(-7605, exit_rsa_nopadding);
    }

#ifndef WOLFSSL_RSA_VERIFY_ONLY
    inLen = wc_RsaEncryptSize(&key);
    outSz   = inLen;
    plainSz = inLen;
    XMEMSET(tmp, 7, inLen);
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret >= 0) {
            ret = wc_RsaDirect(tmp, inLen, out, &outSz, &key,
                    RSA_PRIVATE_ENCRYPT, &rng);
        }
    } while (ret == WC_PENDING_E);
    if (ret <= 0) {
        ERROR_OUT(-7606, exit_rsa_nopadding);
    }

    /* encrypted result should not be the same as input */
    if (XMEMCMP(out, tmp, inLen) == 0) {
        ERROR_OUT(-7607, exit_rsa_nopadding);
    }
    TEST_SLEEP();

    /* decrypt with public key and compare result */
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret >= 0) {
            ret = wc_RsaDirect(out, outSz, plain, &plainSz, &key,
                    RSA_PUBLIC_DECRYPT, &rng);
        }
    } while (ret == WC_PENDING_E);
    if (ret <= 0) {
        ERROR_OUT(-7608, exit_rsa_nopadding);
    }

    if (XMEMCMP(plain, tmp, inLen) != 0) {
        ERROR_OUT(-7609, exit_rsa_nopadding);
    }
    TEST_SLEEP();
#endif

#ifdef WC_RSA_BLINDING
    ret = wc_RsaSetRNG(NULL, &rng);
    if (ret != BAD_FUNC_ARG) {
        ERROR_OUT(-7610, exit_rsa_nopadding);
    }

    ret = wc_RsaSetRNG(&key, &rng);
    if (ret < 0) {
        ERROR_OUT(-7611, exit_rsa_nopadding);
    }
#endif

    /* test encrypt and decrypt using WC_RSA_NO_PAD */
#ifndef WOLFSSL_RSA_VERIFY_ONLY
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret >= 0) {
            ret = wc_RsaPublicEncrypt_ex(tmp, inLen, out, (int)outSz, &key, &rng,
                WC_RSA_NO_PAD, WC_HASH_TYPE_NONE, WC_MGF1NONE, NULL, 0);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7612, exit_rsa_nopadding);
    }
    TEST_SLEEP();
#endif /* WOLFSSL_RSA_VERIFY_ONLY */

#ifndef WOLFSSL_RSA_PUBLIC_ONLY
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret >= 0) {
            ret = wc_RsaPrivateDecrypt_ex(out, outSz, plain, (int)plainSz, &key,
                WC_RSA_NO_PAD, WC_HASH_TYPE_NONE, WC_MGF1NONE, NULL, 0);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7613, exit_rsa_nopadding);
    }

    if (XMEMCMP(plain, tmp, inLen) != 0) {
        ERROR_OUT(-7614, exit_rsa_nopadding);
    }
    TEST_SLEEP();
#endif /* WOLFSSL_RSA_PUBLIC_ONLY */

    /* test some bad arguments */
    ret = wc_RsaDirect(out, outSz, plain, &plainSz, &key, -1,
            &rng);
    if (ret != BAD_FUNC_ARG) {
        ERROR_OUT(-7615, exit_rsa_nopadding);
    }

    ret = wc_RsaDirect(out, outSz, plain, &plainSz, NULL, RSA_PUBLIC_DECRYPT,
            &rng);
    if (ret != BAD_FUNC_ARG) {
        ERROR_OUT(-7616, exit_rsa_nopadding);
    }

    ret = wc_RsaDirect(out, outSz, NULL, &plainSz, &key, RSA_PUBLIC_DECRYPT,
            &rng);
    if (ret != LENGTH_ONLY_E || plainSz != inLen) {
        ERROR_OUT(-7617, exit_rsa_nopadding);
    }

    ret = wc_RsaDirect(out, outSz - 10, plain, &plainSz, &key,
            RSA_PUBLIC_DECRYPT, &rng);
    if (ret != BAD_FUNC_ARG) {
        ERROR_OUT(-7618, exit_rsa_nopadding);
    }

    /* if making it to this point of code without hitting an ERROR_OUT then
     * all tests have passed */
    ret = 0;

exit_rsa_nopadding:
    XFREE(tmp, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    FREE_VAR(out, HEAP_HINT);
    FREE_VAR(plain, HEAP_HINT);
    wc_FreeRsaKey(&key);
    wc_FreeRng(&rng);

    return ret;
}
#endif /* WC_RSA_NO_PADDING */

#ifdef WOLFSSL_CERT_GEN
static int rsa_certgen_test(RsaKey* key, RsaKey* keypub, WC_RNG* rng, byte* tmp)
{
    RsaKey      caKey;
    byte*       der;
    int         ret;
    Cert*       myCert = NULL;
    int         certSz;
    size_t      bytes3;
    word32      idx3 = 0;
#if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048)
    XFILE       file3;
#endif
#ifdef WOLFSSL_TEST_CERT
    DecodedCert decode;
#endif
#if defined(WOLFSSL_ALT_NAMES) && !defined(NO_ASN_TIME)
    struct tm beforeTime;
    struct tm afterTime;
#endif
    const byte  mySerial[8] = {1,2,3,4,5,6,7,8};

    (void)keypub;

    XMEMSET(&caKey, 0, sizeof(caKey));

    der = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (der == NULL) {
        ERROR_OUT(-7619, exit_rsa);
    }
    myCert = (Cert*)XMALLOC(sizeof(Cert), HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (myCert == NULL) {
        ERROR_OUT(-7621, exit_rsa);
    }

    /* self signed */
    if (wc_InitCert(myCert)) {
        ERROR_OUT(-7622, exit_rsa);
    }

    XMEMCPY(&myCert->subject, &certDefaultName, sizeof(CertName));
    XMEMCPY(myCert->serial, mySerial, sizeof(mySerial));
    myCert->serialSz = (int)sizeof(mySerial);
    myCert->isCA    = 1;
#ifndef NO_SHA256
    myCert->sigType = CTC_SHA256wRSA;
#else
    myCert->sigType = CTC_SHAwRSA;
#endif


#ifdef WOLFSSL_CERT_EXT
    /* add Policies */
    XSTRNCPY(myCert->certPolicies[0], "2.16.840.1.101.3.4.1.42",
            CTC_MAX_CERTPOL_SZ);
    XSTRNCPY(myCert->certPolicies[1], "1.2.840.113549.1.9.16.6.5",
            CTC_MAX_CERTPOL_SZ);
    myCert->certPoliciesNb = 2;

    /* add SKID from the Public Key */
    if (wc_SetSubjectKeyIdFromPublicKey(myCert, keypub, NULL) != 0) {
        ERROR_OUT(-7623, exit_rsa);
    }

     /* add AKID from the Public Key */
     if (wc_SetAuthKeyIdFromPublicKey(myCert, keypub, NULL) != 0) {
        ERROR_OUT(-7624, exit_rsa);
    }

    /* add Key Usage */
    if (wc_SetKeyUsage(myCert,"cRLSign,keyCertSign") != 0) {
        ERROR_OUT(-7625, exit_rsa);
    }
#ifdef WOLFSSL_EKU_OID
    {
        const char unique[] = "2.16.840.1.111111.100.1.10.1";
        if (wc_SetExtKeyUsageOID(myCert, unique, sizeof(unique), 0,
                    HEAP_HINT) != 0) {
            ERROR_OUT(-7626, exit_rsa);
        }
    }
#endif /* WOLFSSL_EKU_OID */
#endif /* WOLFSSL_CERT_EXT */

    ret = 0;
    do {
#if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key->asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
#endif
        if (ret >= 0) {
            ret = wc_MakeSelfCert(myCert, der, FOURK_BUF, key, rng);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7627, exit_rsa);
    }
    certSz = ret;

#ifdef WOLFSSL_TEST_CERT
    InitDecodedCert(&decode, der, certSz, HEAP_HINT);
    ret = ParseCert(&decode, CERT_TYPE, NO_VERIFY, 0);
    if (ret != 0) {
        FreeDecodedCert(&decode);
        ERROR_OUT(-7628, exit_rsa);
    }
    FreeDecodedCert(&decode);
#endif

    ret = SaveDerAndPem(der, certSz, certDerFile, certPemFile,
        CERT_TYPE, -5578);
    if (ret != 0) {
        goto exit_rsa;
    }

    /* Setup Certificate */
    if (wc_InitCert(myCert)) {
        ERROR_OUT(-7629, exit_rsa);
    }

#ifdef WOLFSSL_ALT_NAMES
        /* Get CA Cert for testing */
    #ifdef USE_CERT_BUFFERS_1024
        XMEMCPY(tmp, ca_cert_der_1024, sizeof_ca_cert_der_1024);
        bytes3 = sizeof_ca_cert_der_1024;
    #elif defined(USE_CERT_BUFFERS_2048)
        XMEMCPY(tmp, ca_cert_der_2048, sizeof_ca_cert_der_2048);
        bytes3 = sizeof_ca_cert_der_2048;
    #else
        file3 = XFOPEN(rsaCaCertDerFile, "rb");
        if (!file3) {
            ERROR_OUT(-7630, exit_rsa);
        }
        bytes3 = XFREAD(tmp, 1, FOURK_BUF, file3);
        XFCLOSE(file3);
    #endif /* USE_CERT_BUFFERS */

    #if !defined(NO_FILESYSTEM) && !defined(USE_CERT_BUFFERS_1024) && \
        !defined(USE_CERT_BUFFERS_2048) && !defined(NO_ASN)
        ret = wc_SetAltNames(myCert, rsaCaCertFile);
        if (ret != 0) {
            ERROR_OUT(-7631, exit_rsa);
        }
    #endif
        /* get alt names from der */
        ret = wc_SetAltNamesBuffer(myCert, tmp, (int)bytes3);
        if (ret != 0) {
            ERROR_OUT(-7632, exit_rsa);
        }

        /* get dates from der */
        ret = wc_SetDatesBuffer(myCert, tmp, (int)bytes3);
        if (ret != 0) {
            ERROR_OUT(-7633, exit_rsa);
        }

    #ifndef NO_ASN_TIME
        ret = wc_GetCertDates(myCert, &beforeTime, &afterTime);
        if (ret < 0) {
            ERROR_OUT(-7634, exit_rsa);
        }
    #endif
#endif /* WOLFSSL_ALT_NAMES */

    /* Get CA Key */
#ifdef USE_CERT_BUFFERS_1024
    XMEMCPY(tmp, ca_key_der_1024, sizeof_ca_key_der_1024);
    bytes3 = sizeof_ca_key_der_1024;
#elif defined(USE_CERT_BUFFERS_2048)
    XMEMCPY(tmp, ca_key_der_2048, sizeof_ca_key_der_2048);
    bytes3 = sizeof_ca_key_der_2048;
#else
    file3 = XFOPEN(rsaCaKeyFile, "rb");
    if (!file3) {
        ERROR_OUT(-7635, exit_rsa);
    }

    bytes3 = XFREAD(tmp, 1, FOURK_BUF, file3);
    XFCLOSE(file3);
#endif /* USE_CERT_BUFFERS */

    ret = wc_InitRsaKey(&caKey, HEAP_HINT);
    if (ret != 0) {
        ERROR_OUT(-7636, exit_rsa);
    }
    ret = wc_RsaPrivateKeyDecode(tmp, &idx3, &caKey, (word32)bytes3);
    if (ret != 0) {
        ERROR_OUT(-7637, exit_rsa);
    }

#ifndef NO_SHA256
    myCert->sigType = CTC_SHA256wRSA;
#else
    myCert->sigType = CTC_SHAwRSA;
#endif

    XMEMCPY(&myCert->subject, &certDefaultName, sizeof(CertName));

#ifdef WOLFSSL_CERT_EXT
    /* add Policies */
    XSTRNCPY(myCert->certPolicies[0], "2.16.840.1.101.3.4.1.42",
            CTC_MAX_CERTPOL_SZ);
    myCert->certPoliciesNb =1;

    /* add SKID from the Public Key */
    if (wc_SetSubjectKeyIdFromPublicKey(myCert, key, NULL) != 0) {
        ERROR_OUT(-7638, exit_rsa);
    }

    /* add AKID from the CA certificate */
#if defined(USE_CERT_BUFFERS_2048)
    ret = wc_SetAuthKeyIdFromCert(myCert, ca_cert_der_2048,
                                        sizeof_ca_cert_der_2048);
#elif defined(USE_CERT_BUFFERS_1024)
    ret = wc_SetAuthKeyIdFromCert(myCert, ca_cert_der_1024,
                                        sizeof_ca_cert_der_1024);
#else
    ret = wc_SetAuthKeyId(myCert, rsaCaCertFile);
#endif
    if (ret != 0) {
        ERROR_OUT(-7639, exit_rsa);
    }

    /* add Key Usage */
    if (wc_SetKeyUsage(myCert,"keyEncipherment,keyAgreement") != 0) {
        ERROR_OUT(-7640, exit_rsa);
    }
#endif /* WOLFSSL_CERT_EXT */

#if defined(USE_CERT_BUFFERS_2048)
    ret = wc_SetIssuerBuffer(myCert, ca_cert_der_2048,
                                      sizeof_ca_cert_der_2048);
#elif defined(USE_CERT_BUFFERS_1024)
    ret = wc_SetIssuerBuffer(myCert, ca_cert_der_1024,
                                      sizeof_ca_cert_der_1024);
#else
    ret = wc_SetIssuer(myCert, rsaCaCertFile);
#endif
    if (ret < 0) {
        ERROR_OUT(-7641, exit_rsa);
    }

    certSz = wc_MakeCert(myCert, der, FOURK_BUF, key, NULL, rng);
    if (certSz < 0) {
        ERROR_OUT(-7642, exit_rsa);
    }

    ret = 0;
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &caKey.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret >= 0) {
            ret = wc_SignCert(myCert->bodySz, myCert->sigType, der, FOURK_BUF,
                      &caKey, NULL, rng);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7643, exit_rsa);
    }
    certSz = ret;

#ifdef WOLFSSL_TEST_CERT
    InitDecodedCert(&decode, der, certSz, HEAP_HINT);
    ret = ParseCert(&decode, CERT_TYPE, NO_VERIFY, 0);
    if (ret != 0) {
        FreeDecodedCert(&decode);
        ERROR_OUT(-7644, exit_rsa);
    }
    FreeDecodedCert(&decode);
#endif

    ret = SaveDerAndPem(der, certSz, otherCertDerFile, otherCertPemFile,
        CERT_TYPE, -5598);
    if (ret != 0) {
        goto exit_rsa;
    }

exit_rsa:
    wc_FreeRsaKey(&caKey);

    XFREE(myCert, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(der, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);

    return ret;
}
#endif

#if !defined(NO_RSA) && defined(HAVE_ECC) && defined(WOLFSSL_CERT_GEN)
/* Make Cert / Sign example for ECC cert and RSA CA */
static int rsa_ecc_certgen_test(WC_RNG* rng, byte* tmp)
{
    RsaKey      caKey;
    ecc_key     caEccKey;
    ecc_key     caEccKeyPub;
    byte*       der;
    Cert*       myCert = NULL;
    int         certSz;
    size_t      bytes3;
    word32      idx3 = 0;
#if (!defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048)) \
    || !defined(USE_CERT_BUFFERS_256)
    XFILE       file3;
#endif
#ifdef WOLFSSL_TEST_CERT
    DecodedCert decode;
#endif
    int ret;

    XMEMSET(&caKey, 0, sizeof(caKey));
    XMEMSET(&caEccKey, 0, sizeof(caEccKey));
    XMEMSET(&caEccKeyPub, 0, sizeof(caEccKeyPub));

    der = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (der == NULL) {
        ERROR_OUT(-7645, exit_rsa);
    }
    myCert = (Cert*)XMALLOC(sizeof(Cert), HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (myCert == NULL) {
        ERROR_OUT(-7647, exit_rsa);
    }

    /* Get CA Key */
#ifdef USE_CERT_BUFFERS_1024
    XMEMCPY(tmp, ca_key_der_1024, sizeof_ca_key_der_1024);
    bytes3 = sizeof_ca_key_der_1024;
#elif defined(USE_CERT_BUFFERS_2048)
    XMEMCPY(tmp, ca_key_der_2048, sizeof_ca_key_der_2048);
    bytes3 = sizeof_ca_key_der_2048;
#else
    file3 = XFOPEN(rsaCaKeyFile, "rb");
    if (!file3) {
        ERROR_OUT(-7648, exit_rsa);
    }

    bytes3 = XFREAD(tmp, 1, FOURK_BUF, file3);
    XFCLOSE(file3);
#endif /* USE_CERT_BUFFERS */

    ret = wc_InitRsaKey(&caKey, HEAP_HINT);
    if (ret != 0) {
        ERROR_OUT(-7649, exit_rsa);
    }
    ret = wc_RsaPrivateKeyDecode(tmp, &idx3, &caKey, (word32)bytes3);
    if (ret != 0) {
        ERROR_OUT(-7650, exit_rsa);
    }

    /* Get Cert Key */
#ifdef USE_CERT_BUFFERS_256
    XMEMCPY(tmp, ecc_key_pub_der_256, sizeof_ecc_key_pub_der_256);
    bytes3 = sizeof_ecc_key_pub_der_256;
#else
    file3 = XFOPEN(eccKeyPubFile, "rb");
    if (!file3) {
        ERROR_OUT(-7651, exit_rsa);
    }

    bytes3 = XFREAD(tmp, 1, FOURK_BUF, file3);
    XFCLOSE(file3);
#endif

    ret = wc_ecc_init_ex(&caEccKeyPub, HEAP_HINT, devId);
    if (ret != 0) {
        ERROR_OUT(-7652, exit_rsa);
    }

    idx3 = 0;
    ret = wc_EccPublicKeyDecode(tmp, &idx3, &caEccKeyPub, (word32)bytes3);
    if (ret != 0) {
        ERROR_OUT(-7653, exit_rsa);
    }

    /* Setup Certificate */
    if (wc_InitCert(myCert)) {
        ERROR_OUT(-7654, exit_rsa);
    }

#ifndef NO_SHA256
    myCert->sigType = CTC_SHA256wRSA;
#else
    myCert->sigType = CTC_SHAwRSA;
#endif

    XMEMCPY(&myCert->subject, &certDefaultName, sizeof(CertName));

#ifdef WOLFSSL_CERT_EXT
    /* add Policies */
    XSTRNCPY(myCert->certPolicies[0], "2.4.589440.587.101.2.1.9632587.1",
            CTC_MAX_CERTPOL_SZ);
    XSTRNCPY(myCert->certPolicies[1], "1.2.13025.489.1.113549",
            CTC_MAX_CERTPOL_SZ);
    myCert->certPoliciesNb = 2;

    /* add SKID from the Public Key */
    if (wc_SetSubjectKeyIdFromPublicKey(myCert, NULL, &caEccKeyPub) != 0) {
        ERROR_OUT(-7655, exit_rsa);
    }

    /* add AKID from the CA certificate */
#if defined(USE_CERT_BUFFERS_2048)
    ret = wc_SetAuthKeyIdFromCert(myCert, ca_cert_der_2048,
                                           sizeof_ca_cert_der_2048);
#elif defined(USE_CERT_BUFFERS_1024)
    ret = wc_SetAuthKeyIdFromCert(myCert, ca_cert_der_1024,
                                           sizeof_ca_cert_der_1024);
#else
    ret = wc_SetAuthKeyId(myCert, rsaCaCertFile);
#endif
    if (ret != 0) {
        ERROR_OUT(-7656, exit_rsa);
    }

    /* add Key Usage */
    if (wc_SetKeyUsage(myCert, certKeyUsage) != 0) {
        ERROR_OUT(-7657, exit_rsa);
    }
#endif /* WOLFSSL_CERT_EXT */

#if defined(USE_CERT_BUFFERS_2048)
    ret = wc_SetIssuerBuffer(myCert, ca_cert_der_2048,
                                      sizeof_ca_cert_der_2048);
#elif defined(USE_CERT_BUFFERS_1024)
    ret = wc_SetIssuerBuffer(myCert, ca_cert_der_1024,
                                      sizeof_ca_cert_der_1024);
#else
    ret = wc_SetIssuer(myCert, rsaCaCertFile);
#endif
    if (ret < 0) {
        ERROR_OUT(-7658, exit_rsa);
    }

    certSz = wc_MakeCert(myCert, der, FOURK_BUF, NULL, &caEccKeyPub, rng);
    if (certSz < 0) {
        ERROR_OUT(-7659, exit_rsa);
    }

    ret = 0;
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &caEccKey.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret >= 0) {
            ret = wc_SignCert(myCert->bodySz, myCert->sigType, der,
                              FOURK_BUF, &caKey, NULL, rng);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7660, exit_rsa);
    }
    certSz = ret;

#ifdef WOLFSSL_TEST_CERT
    InitDecodedCert(&decode, der, certSz, 0);
    ret = ParseCert(&decode, CERT_TYPE, NO_VERIFY, 0);
    if (ret != 0) {
        FreeDecodedCert(&decode);
        ERROR_OUT(-7661, exit_rsa);

    }
    FreeDecodedCert(&decode);
#endif

    ret = SaveDerAndPem(der, certSz, certEccRsaDerFile, certEccRsaPemFile,
        CERT_TYPE, -5616);
    if (ret != 0) {
        goto exit_rsa;
    }

exit_rsa:
    wc_FreeRsaKey(&caKey);
    wc_ecc_free(&caEccKey);
    wc_ecc_free(&caEccKeyPub);

    XFREE(myCert, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    myCert = NULL;
    XFREE(der, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    der = NULL;

    if (ret >= 0)
        ret = 0;
    return ret;
}
#endif /* !NO_RSA && HAVE_ECC && WOLFSSL_CERT_GEN */

#ifdef WOLFSSL_KEY_GEN
static int rsa_keygen_test(WC_RNG* rng)
{
    RsaKey genKey;
    int    ret;
    byte*  der = NULL;
    word32 idx = 0;
    int    derSz = 0;
#if !defined(WOLFSSL_SP_MATH) && !defined(HAVE_FIPS)
    int    keySz = 1024;
#else
    int    keySz = 2048;
#endif

    XMEMSET(&genKey, 0, sizeof(genKey));

    ret = wc_InitRsaKey_ex(&genKey, HEAP_HINT, devId);
    if (ret != 0) {
        ERROR_OUT(-7662, exit_rsa);
    }

    ret = wc_MakeRsaKey(&genKey, keySz, WC_RSA_EXPONENT, rng);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &genKey.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0) {
        ERROR_OUT(-7663, exit_rsa);
    }
    TEST_SLEEP();

    /* If not using old FIPS, or not using FAST or USER RSA... */
    #if !defined(HAVE_FAST_RSA) && !defined(HAVE_USER_RSA) && \
        (!defined(HAVE_FIPS) || \
         (defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2))) && \
        !defined(HAVE_SELFTEST) && !defined(HAVE_INTEL_QA)
    ret = wc_CheckRsaKey(&genKey);
    if (ret != 0) {
        ERROR_OUT(-7664, exit_rsa);
    }
    #endif
    der = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (der == NULL) {
        ERROR_OUT(-7665, exit_rsa);
    }

    derSz = wc_RsaKeyToDer(&genKey, der, FOURK_BUF);
    if (derSz < 0) {
        ERROR_OUT(-7667, exit_rsa);
    }

    ret = SaveDerAndPem(der, derSz, keyDerFile, keyPemFile,
        PRIVATEKEY_TYPE, -5555);
    if (ret != 0) {
        goto exit_rsa;
    }

    wc_FreeRsaKey(&genKey);
    ret = wc_InitRsaKey(&genKey, HEAP_HINT);
    if (ret != 0) {
        ERROR_OUT(-7668, exit_rsa);
    }
    idx = 0;
#if !defined(WOLFSSL_CRYPTOCELL)
    /* The private key part of the key gen pairs from cryptocell can't be exported */
    ret = wc_RsaPrivateKeyDecode(der, &idx, &genKey, derSz);
    if (ret != 0) {
        ERROR_OUT(-7669, exit_rsa);
    }
#endif /* WOLFSSL_CRYPTOCELL */

exit_rsa:
    wc_FreeRsaKey(&genKey);
    if (der != NULL) {
        XFREE(der, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        der = NULL;
    }

    return ret;
}
#endif

int rsa_test(void)
{
    int    ret;
    byte*  tmp;
    byte*  der = NULL;
    size_t bytes;
    WC_RNG rng;
    RsaKey key;
#if defined(WOLFSSL_CERT_EXT) || defined(WOLFSSL_CERT_GEN)
    RsaKey keypub;
#endif
#if defined(HAVE_NTRU)
    RsaKey caKey;
#endif
#if !defined(NO_ASN) || !defined(WOLFSSL_RSA_PUBLIC_ONLY) \
                     || defined(WOLFSSL_PUBLIC_MP)
    word32 idx = 0;
#endif
#if (!defined(WOLFSSL_RSA_VERIFY_ONLY) || defined(WOLFSSL_PUBLIC_MP)) && \
                                 !defined(WC_NO_RSA_OAEP) && !defined(WC_NO_RNG)
    const char* inStr = "Everyone gets Friday off.";
    word32      inLen = (word32)XSTRLEN((char*)inStr);
    const word32 outSz   = RSA_TEST_BYTES;
    const word32 plainSz = RSA_TEST_BYTES;
#endif
#if !defined(WOLFSSL_RSA_PUBLIC_ONLY) || defined(WOLFSSL_PUBLIC_MP)
    byte*  res;
#endif
#ifndef NO_SIG_WRAPPER
    int modLen;
#endif
#if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048) && \
    !defined(USE_CERT_BUFFERS_3072) && !defined(USE_CERT_BUFFERS_4096) && \
    !defined(NO_FILESYSTEM)
    XFILE   file;
    XFILE   file2;
#endif
#ifdef WOLFSSL_TEST_CERT
    DecodedCert cert;
#endif

#if (!defined(WOLFSSL_RSA_VERIFY_ONLY) || defined(WOLFSSL_PUBLIC_MP)) && \
                                 !defined(WC_NO_RSA_OAEP) && !defined(WC_NO_RNG)
    DECLARE_VAR_INIT(in, byte, inLen, inStr, HEAP_HINT);
    DECLARE_VAR(out, byte, RSA_TEST_BYTES, HEAP_HINT);
    DECLARE_VAR(plain, byte, RSA_TEST_BYTES, HEAP_HINT);
#endif

#ifdef WOLFSSL_ASYNC_CRYPT
    if (in == NULL)
        return MEMORY_E;
#endif

    /* initialize stack structures */
    XMEMSET(&rng, 0, sizeof(rng));
    XMEMSET(&key, 0, sizeof(key));
#ifdef WOLFSSL_CERT_EXT
    XMEMSET(&keypub, 0, sizeof(keypub));
#endif
#if defined(HAVE_NTRU)
    XMEMSET(&caKey, 0, sizeof(caKey));
#endif

#if !defined(HAVE_USER_RSA) && !defined(NO_ASN)
    ret = rsa_decode_test(&key);
    if (ret != 0)
        return ret;
#endif

#ifdef USE_CERT_BUFFERS_1024
    bytes = (size_t)sizeof_client_key_der_1024;
    if (bytes < (size_t)sizeof_client_cert_der_1024)
        bytes = (size_t)sizeof_client_cert_der_1024;
#elif defined(USE_CERT_BUFFERS_2048)
    bytes = (size_t)sizeof_client_key_der_2048;
    if (bytes < (size_t)sizeof_client_cert_der_2048)
        bytes = (size_t)sizeof_client_cert_der_2048;
#elif defined(USE_CERT_BUFFERS_3072)
    bytes = (size_t)sizeof_client_key_der_3072;
    if (bytes < (size_t)sizeof_client_cert_der_3072)
        bytes = (size_t)sizeof_client_cert_der_3072;
#elif defined(USE_CERT_BUFFERS_4096)
    bytes = (size_t)sizeof_client_key_der_4096;
    if (bytes < (size_t)sizeof_client_cert_der_4096)
        bytes = (size_t)sizeof_client_cert_der_4096;
#else
	bytes = FOURK_BUF;
#endif

    tmp = (byte*)XMALLOC(bytes, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (tmp == NULL
    #ifdef WOLFSSL_ASYNC_CRYPT
        || out == NULL || plain == NULL
    #endif
    ) {
        return -7700;
    }

#ifdef USE_CERT_BUFFERS_1024
    XMEMCPY(tmp, client_key_der_1024, (size_t)sizeof_client_key_der_1024);
#elif defined(USE_CERT_BUFFERS_2048)
    XMEMCPY(tmp, client_key_der_2048, (size_t)sizeof_client_key_der_2048);
#elif defined(USE_CERT_BUFFERS_3072)
    XMEMCPY(tmp, client_key_der_3072, (size_t)sizeof_client_key_der_3072);
#elif defined(USE_CERT_BUFFERS_4096)
    XMEMCPY(tmp, client_key_der_4096, (size_t)sizeof_client_key_der_4096);
#elif !defined(NO_FILESYSTEM)
    file = XFOPEN(clientKey, "rb");
    if (!file) {
        err_sys("can't open ./certs/client-key.der, "
                "Please run from wolfSSL home dir", -40);
        ERROR_OUT(-7701, exit_rsa);
    }

    bytes = XFREAD(tmp, 1, FOURK_BUF, file);
    XFCLOSE(file);
#else
    /* No key to use. */
    ERROR_OUT(-7702, exit_rsa);
#endif /* USE_CERT_BUFFERS */

    ret = wc_InitRsaKey_ex(&key, HEAP_HINT, devId);
    if (ret != 0) {
        ERROR_OUT(-7703, exit_rsa);
    }
#ifndef NO_ASN
    ret = wc_RsaPrivateKeyDecode(tmp, &idx, &key, (word32)bytes);
    if (ret != 0) {
        ERROR_OUT(-7704, exit_rsa);
    }
#ifndef NO_SIG_WRAPPER
    modLen = wc_RsaEncryptSize(&key);
#endif
#else
    #ifdef USE_CERT_BUFFERS_2048
        ret = mp_read_unsigned_bin(&key.n, &tmp[12], 256);
        if (ret != 0) {
            ERROR_OUT(-7705, exit_rsa);
        }
        ret = mp_set_int(&key.e, WC_RSA_EXPONENT);
        if (ret != 0) {
            ERROR_OUT(-7706, exit_rsa);
        }
#ifndef NO_SIG_WRAPPER
        modLen = 2048;
#endif
    #else
        #error Not supported yet!
    #endif
#endif

#ifndef WC_NO_RNG
#ifndef HAVE_FIPS
    ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
    ret = wc_InitRng(&rng);
#endif
    if (ret != 0) {
        ERROR_OUT(-7707, exit_rsa);
    }
#endif

#ifndef NO_SIG_WRAPPER
    ret = rsa_sig_test(&key, sizeof(RsaKey), modLen, &rng);
    if (ret != 0)
        goto exit_rsa;
#endif

#ifdef WC_RSA_NONBLOCK
    ret = rsa_nb_test(&key, in, inLen, out, outSz, plain, plainSz, &rng);
    if (ret != 0)
        goto exit_rsa;
#endif

#if !defined(WOLFSSL_RSA_VERIFY_ONLY) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)
    do {
#if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
#endif
        if (ret >= 0) {
            ret = wc_RsaPublicEncrypt(in, inLen, out, outSz, &key, &rng);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7708, exit_rsa);
    }
    TEST_SLEEP();

#ifdef WC_RSA_BLINDING
    {
        int tmpret = ret;
        ret = wc_RsaSetRNG(&key, &rng);
        if (ret < 0) {
            ERROR_OUT(-7709, exit_rsa);
        }
        ret = tmpret;
    }
#endif

    idx = (word32)ret; /* save off encrypted length */
    do {
#if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
#endif
        if (ret >= 0) {
            ret = wc_RsaPrivateDecrypt(out, idx, plain, plainSz, &key);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7710, exit_rsa);
    }

    if (XMEMCMP(plain, in, inLen)) {
        ERROR_OUT(-7711, exit_rsa);
    }
    TEST_SLEEP();

    do {
#if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
#endif
        if (ret >= 0) {
            ret = wc_RsaPrivateDecryptInline(out, idx, &res, &key);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7712, exit_rsa);
    }
    if (ret != (int)inLen) {
        ERROR_OUT(-7713, exit_rsa);
    }
    if (XMEMCMP(res, in, inLen)) {
        ERROR_OUT(-7714, exit_rsa);
    }
    TEST_SLEEP();

    do {
#if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
#endif
        if (ret >= 0) {
            ret = wc_RsaSSL_Sign(in, inLen, out, outSz, &key, &rng);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7715, exit_rsa);
    }
    TEST_SLEEP();

#elif defined(WOLFSSL_PUBLIC_MP)
    (void)outSz;
    (void)inLen;
    (void)res;
    {
        byte signature_2048[] = {
            0x07, 0x6f, 0xc9, 0x85, 0x73, 0x9e, 0x21, 0x79,
            0x47, 0xf1, 0xa3, 0xd7, 0xf4, 0x27, 0x29, 0xbe,
            0x99, 0x5d, 0xac, 0xb2, 0x10, 0x3f, 0x95, 0xda,
            0x89, 0x23, 0xb8, 0x96, 0x13, 0x57, 0x72, 0x30,
            0xa1, 0xfe, 0x5a, 0x68, 0x9c, 0x99, 0x9d, 0x1e,
            0x05, 0xa4, 0x80, 0xb0, 0xbb, 0xd9, 0xd9, 0xa1,
            0x69, 0x97, 0x74, 0xb3, 0x41, 0x21, 0x3b, 0x47,
            0xf5, 0x51, 0xb1, 0xfb, 0xc7, 0xaa, 0xcc, 0xdc,
            0xcd, 0x76, 0xa0, 0x28, 0x4d, 0x27, 0x14, 0xa4,
            0xb9, 0x41, 0x68, 0x7c, 0xb3, 0x66, 0xe6, 0x6f,
            0x40, 0x76, 0xe4, 0x12, 0xfd, 0xae, 0x29, 0xb5,
            0x63, 0x60, 0x87, 0xce, 0x49, 0x6b, 0xf3, 0x05,
            0x9a, 0x14, 0xb5, 0xcc, 0xcd, 0xf7, 0x30, 0x95,
            0xd2, 0x72, 0x52, 0x1d, 0x5b, 0x7e, 0xef, 0x4a,
            0x02, 0x96, 0x21, 0x6c, 0x55, 0xa5, 0x15, 0xb1,
            0x57, 0x63, 0x2c, 0xa3, 0x8e, 0x9d, 0x3d, 0x45,
            0xcc, 0xb8, 0xe6, 0xa1, 0xc8, 0x59, 0xcd, 0xf5,
            0xdc, 0x0a, 0x51, 0xb6, 0x9d, 0xfb, 0xf4, 0x6b,
            0xfd, 0x32, 0x71, 0x6e, 0xcf, 0xcb, 0xb3, 0xd9,
            0xe0, 0x4a, 0x77, 0x34, 0xd6, 0x61, 0xf5, 0x7c,
            0xf9, 0xa9, 0xa4, 0xb0, 0x8e, 0x3b, 0xd6, 0x04,
            0xe0, 0xde, 0x2b, 0x5b, 0x5a, 0xbf, 0xd9, 0xef,
            0x8d, 0xa3, 0xf5, 0xb1, 0x67, 0xf3, 0xb9, 0x72,
            0x0a, 0x37, 0x12, 0x35, 0x6c, 0x8e, 0x10, 0x8b,
            0x38, 0x06, 0x16, 0x4b, 0x20, 0x20, 0x13, 0x00,
            0x2e, 0x6d, 0xc2, 0x59, 0x23, 0x67, 0x4a, 0x6d,
            0xa1, 0x46, 0x8b, 0xee, 0xcf, 0x44, 0xb4, 0x3e,
            0x56, 0x75, 0x00, 0x68, 0xb5, 0x7d, 0x0f, 0x20,
            0x79, 0x5d, 0x7f, 0x12, 0x15, 0x32, 0x89, 0x61,
            0x6b, 0x29, 0xb7, 0x52, 0xf5, 0x25, 0xd8, 0x98,
            0xe8, 0x6f, 0xf9, 0x22, 0xb4, 0xbb, 0xe5, 0xff,
            0xd0, 0x92, 0x86, 0x9a, 0x88, 0xa2, 0xaf, 0x6b
        };
        ret = sizeof(signature_2048);
        XMEMCPY(out, signature_2048, ret);
    }
#endif

#if !defined(WOLFSSL_RSA_PUBLIC_ONLY) || defined(WOLFSSL_PUBLIC_MP)
    idx = (word32)ret;
    XMEMSET(plain, 0, plainSz);
    do {
#if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
#endif
        if (ret >= 0) {
#ifndef WOLFSSL_RSA_VERIFY_INLINE

#if defined(WOLFSSL_CRYPTOCELL)
        /*
        Cryptocell requires the input data and signature byte array to verify.

        first argument must be the input data
        second argument must be the length of input data
        third argument must be the signature byte array or the output from
                                                                wc_RsaSSL_Sign()
        fourth argument must be the length of the signature byte array
        */

        ret = wc_RsaSSL_Verify(in, inLen, out, outSz, &key);
#else
        ret = wc_RsaSSL_Verify(out, idx, plain, plainSz, &key);
#endif /* WOLFSSL_CRYPTOCELL */
#else
            byte* dec = NULL;
            ret = wc_RsaSSL_VerifyInline(out, idx, &dec, &key);
            if (ret > 0) {
                XMEMCPY(plain, dec, ret);
            }
#endif
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7716, exit_rsa);
    }

    if (XMEMCMP(plain, in, (size_t)ret)) {
        ERROR_OUT(-7717, exit_rsa);
    }
    TEST_SLEEP();
#endif

#ifndef WOLFSSL_RSA_VERIFY_ONLY
    #if !defined(WC_NO_RSA_OAEP) && !defined(WC_NO_RNG)
    /* OAEP padding testing */
    #if !defined(HAVE_FAST_RSA) && !defined(HAVE_USER_RSA) && \
        (!defined(HAVE_FIPS) || \
         (defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2)))
    #ifndef NO_SHA
    XMEMSET(plain, 0, plainSz);

    do {
#if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
#endif
        if (ret >= 0) {
            ret = wc_RsaPublicEncrypt_ex(in, inLen, out, outSz, &key, &rng,
                       WC_RSA_OAEP_PAD, WC_HASH_TYPE_SHA, WC_MGF1SHA1, NULL, 0);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7718, exit_rsa);
    }
    TEST_SLEEP();

#ifndef WOLFSSL_RSA_PUBLIC_ONLY
    idx = (word32)ret;
    do {
#if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
#endif
        if (ret >= 0) {
            ret = wc_RsaPrivateDecrypt_ex(out, idx, plain, plainSz, &key,
                       WC_RSA_OAEP_PAD, WC_HASH_TYPE_SHA, WC_MGF1SHA1, NULL, 0);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7719, exit_rsa);
    }

    if (XMEMCMP(plain, in, inLen)) {
        ERROR_OUT(-7720, exit_rsa);
    }
    TEST_SLEEP();
    #endif /* NO_SHA */
#endif

    #ifndef NO_SHA256
    XMEMSET(plain, 0, plainSz);
#ifndef WOLFSSL_RSA_VERIFY_ONLY
    do {
#if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
#endif
        if (ret >= 0) {
            ret = wc_RsaPublicEncrypt_ex(in, inLen, out, outSz, &key, &rng,
                  WC_RSA_OAEP_PAD, WC_HASH_TYPE_SHA256, WC_MGF1SHA256, NULL, 0);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7721, exit_rsa);
    }
    TEST_SLEEP();
#endif /* WOLFSSL_RSA_VERIFY_ONLY */

    idx = (word32)ret;
#ifndef WOLFSSL_RSA_PUBLIC_ONLY
    do {
#if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
#endif
        if (ret >= 0) {
            ret = wc_RsaPrivateDecrypt_ex(out, idx, plain, plainSz, &key,
                  WC_RSA_OAEP_PAD, WC_HASH_TYPE_SHA256, WC_MGF1SHA256, NULL, 0);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7722, exit_rsa);
    }

    if (XMEMCMP(plain, in, inLen)) {
        ERROR_OUT(-7723, exit_rsa);
    }
    TEST_SLEEP();
#endif /* WOLFSSL_RSA_PUBLIC_ONLY */

#ifndef WOLFSSL_RSA_PUBLIC_ONLY
    do {
#if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
#endif
        if (ret >= 0) {
            ret = wc_RsaPrivateDecryptInline_ex(out, idx, &res, &key,
                WC_RSA_OAEP_PAD, WC_HASH_TYPE_SHA256, WC_MGF1SHA256, NULL, 0);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7724, exit_rsa);
    }
    if (ret != (int)inLen) {
        ERROR_OUT(-7725, exit_rsa);
    }
    if (XMEMCMP(res, in, inLen)) {
        ERROR_OUT(-7726, exit_rsa);
    }
    TEST_SLEEP();
#endif /* WOLFSSL_RSA_PUBLIC_ONLY */

    /* check fails if not using the same optional label */
    XMEMSET(plain, 0, plainSz);
#ifndef WOLFSSL_RSA_VERIFY_ONLY
    do {
#if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
#endif
        if (ret >= 0) {
            ret = wc_RsaPublicEncrypt_ex(in, inLen, out, outSz, &key, &rng,
                  WC_RSA_OAEP_PAD, WC_HASH_TYPE_SHA256, WC_MGF1SHA256, NULL, 0);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7727, exit_rsa);
    }
    TEST_SLEEP();
#endif /* WOLFSSL_RSA_VERIFY_ONLY */

/* TODO: investigate why Cavium Nitrox doesn't detect decrypt error here */
#if !defined(HAVE_CAVIUM) && !defined(WOLFSSL_RSA_PUBLIC_ONLY) && \
    !defined(WOLFSSL_CRYPTOCELL)
/* label is unused in cryptocell so it won't detect decrypt error due to label */
    idx = (word32)ret;
    do {
#if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
#endif
        if (ret >= 0) {
            ret = wc_RsaPrivateDecrypt_ex(out, idx, plain, plainSz, &key,
               WC_RSA_OAEP_PAD, WC_HASH_TYPE_SHA256, WC_MGF1SHA256, in, inLen);
        }
    } while (ret == WC_PENDING_E);
    if (ret > 0) { /* in this case decrypt should fail */
        ERROR_OUT(-7728, exit_rsa);
    }
    ret = 0;
    TEST_SLEEP();
#endif /* !HAVE_CAVIUM */

    /* check using optional label with encrypt/decrypt */
    XMEMSET(plain, 0, plainSz);
#ifndef WOLFSSL_RSA_VERIFY_ONLY
    do {
#if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
#endif
        if (ret >= 0) {
            ret = wc_RsaPublicEncrypt_ex(in, inLen, out, outSz, &key, &rng,
               WC_RSA_OAEP_PAD, WC_HASH_TYPE_SHA256, WC_MGF1SHA256, in, inLen);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7729, exit_rsa);
    }
    TEST_SLEEP();
#endif /* WOLFSSL_RSA_VERIFY_ONLY */

    idx = (word32)ret;
#ifndef WOLFSSL_RSA_PUBLIC_ONLY
    do {
#if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
#endif
        if (ret >= 0) {
            ret = wc_RsaPrivateDecrypt_ex(out, idx, plain, plainSz, &key,
               WC_RSA_OAEP_PAD, WC_HASH_TYPE_SHA256, WC_MGF1SHA256, in, inLen);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7730, exit_rsa);
    }

    if (XMEMCMP(plain, in, inLen)) {
        ERROR_OUT(-7731, exit_rsa);
    }
    TEST_SLEEP();
#endif /* WOLFSSL_RSA_PUBLIC_ONLY */

#ifndef WOLFSSL_RSA_VERIFY_ONLY
    #ifndef NO_SHA
        /* check fail using mismatch hash algorithms */
        XMEMSET(plain, 0, plainSz);
        do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
            ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
            if (ret >= 0) {
                ret = wc_RsaPublicEncrypt_ex(in, inLen, out, outSz, &key, &rng,
                    WC_RSA_OAEP_PAD, WC_HASH_TYPE_SHA, WC_MGF1SHA1, in, inLen);
            }
        } while (ret == WC_PENDING_E);
        if (ret < 0) {
            ERROR_OUT(-7732, exit_rsa);
        }
        TEST_SLEEP();

/* TODO: investigate why Cavium Nitrox doesn't detect decrypt error here */
#if !defined(HAVE_CAVIUM) && !defined(WOLFSSL_RSA_PUBLIC_ONLY) && \
    !defined(WOLFSSL_CRYPTOCELL)
        idx = (word32)ret;
        do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
            ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
            if (ret >= 0) {
                ret = wc_RsaPrivateDecrypt_ex(out, idx, plain, plainSz, &key,
                    WC_RSA_OAEP_PAD, WC_HASH_TYPE_SHA256, WC_MGF1SHA256,
                    in, inLen);
            }
        } while (ret == WC_PENDING_E);
        if (ret > 0) { /* should fail */
            ERROR_OUT(-7733, exit_rsa);
        }
        ret = 0;
        TEST_SLEEP();
    #endif /* !HAVE_CAVIUM */
    #endif /* NO_SHA */
#endif /* WOLFSSL_RSA_VERIFY_ONLY */
#endif /* NO_SHA256 */

#ifdef WOLFSSL_SHA512
    /* Check valid RSA key size is used while using hash length of SHA512
       If key size is less than (hash length * 2) + 2 then is invalid use
       and test, since OAEP padding requires this.
       BAD_FUNC_ARG is returned when this case is not met */
    if (wc_RsaEncryptSize(&key) > ((int)WC_SHA512_DIGEST_SIZE * 2) + 2) {
        XMEMSET(plain, 0, plainSz);
        do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
            ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
            if (ret >= 0) {
                ret = wc_RsaPublicEncrypt_ex(in, inLen, out, outSz, &key, &rng,
                  WC_RSA_OAEP_PAD, WC_HASH_TYPE_SHA512, WC_MGF1SHA512, NULL, 0);
            }
        } while (ret == WC_PENDING_E);
        if (ret < 0) {
            ERROR_OUT(-7734, exit_rsa);
        }
        TEST_SLEEP();

        idx = ret;
#ifndef WOLFSSL_RSA_PUBLIC_ONLY
        do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
            ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
            if (ret >= 0) {
                ret = wc_RsaPrivateDecrypt_ex(out, idx, plain, plainSz, &key,
                  WC_RSA_OAEP_PAD, WC_HASH_TYPE_SHA512, WC_MGF1SHA512, NULL, 0);
            }
        } while (ret == WC_PENDING_E);
        if (ret < 0) {
            ERROR_OUT(-7735, exit_rsa);
        }

        if (XMEMCMP(plain, in, inLen)) {
            ERROR_OUT(-7736, exit_rsa);
        }
        TEST_SLEEP();
#endif /* WOLFSSL_RSA_PUBLIC_ONLY */
    }
#endif /* WOLFSSL_SHA512 */

    /* check using pkcsv15 padding with _ex API */
    XMEMSET(plain, 0, plainSz);
    do {
#if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
#endif
        if (ret >= 0) {
            ret = wc_RsaPublicEncrypt_ex(in, inLen, out, outSz, &key, &rng,
                  WC_RSA_PKCSV15_PAD, WC_HASH_TYPE_NONE, 0, NULL, 0);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7737, exit_rsa);
    }
    TEST_SLEEP();

    idx = (word32)ret;
#ifndef WOLFSSL_RSA_PUBLIC_ONLY
    do {
#if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
#endif
        if (ret >= 0) {
            ret = wc_RsaPrivateDecrypt_ex(out, idx, plain, plainSz, &key,
                  WC_RSA_PKCSV15_PAD, WC_HASH_TYPE_NONE, 0, NULL, 0);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-7738, exit_rsa);
    }

    if (XMEMCMP(plain, in, inLen)) {
        ERROR_OUT(-7739, exit_rsa);
    }
    TEST_SLEEP();
#endif /* WOLFSSL_RSA_PUBLIC_ONLY */
    #endif /* !HAVE_FAST_RSA && !HAVE_FIPS */
    #endif /* WC_NO_RSA_OAEP && !WC_NO_RNG */
#endif /* WOLFSSL_RSA_VERIFY_ONLY */

#if !defined(HAVE_FIPS) && !defined(HAVE_USER_RSA) && !defined(NO_ASN) \
    && !defined(WOLFSSL_RSA_VERIFY_ONLY)
    ret = rsa_export_key_test(&key);
    if (ret != 0)
        return ret;
#endif

#if !defined(NO_ASN) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)
    ret = rsa_flatten_test(&key);
    if (ret != 0)
        return ret;
#endif

#if defined(WOLFSSL_MDK_ARM)
    #define sizeof(s) XSTRLEN((char *)(s))
#endif

#ifdef USE_CERT_BUFFERS_1024
    XMEMCPY(tmp, client_cert_der_1024, (size_t)sizeof_client_cert_der_1024);
    bytes = (size_t)sizeof_client_cert_der_1024;
#elif defined(USE_CERT_BUFFERS_2048)
    XMEMCPY(tmp, client_cert_der_2048, (size_t)sizeof_client_cert_der_2048);
    bytes = (size_t)sizeof_client_cert_der_2048;
#elif defined(USE_CERT_BUFFERS_3072)
    XMEMCPY(tmp, client_cert_der_3072, (size_t)sizeof_client_cert_der_3072);
    bytes = (size_t)sizeof_client_cert_der_3072;
#elif defined(USE_CERT_BUFFERS_4096)
    XMEMCPY(tmp, client_cert_der_4096, (size_t)sizeof_client_cert_der_4096);
    bytes = (size_t)sizeof_client_cert_der_4096;
#elif !defined(NO_FILESYSTEM)
    file2 = XFOPEN(clientCert, "rb");
    if (!file2) {
        ERROR_OUT(-7740, exit_rsa);
    }

    bytes = XFREAD(tmp, 1, FOURK_BUF, file2);
    XFCLOSE(file2);
#else
    /* No certificate to use. */
    ERROR_OUT(-7741, exit_rsa);
#endif

#ifdef sizeof
    #undef sizeof
#endif

#ifdef WOLFSSL_TEST_CERT
    InitDecodedCert(&cert, tmp, (word32)bytes, 0);

    ret = ParseCert(&cert, CERT_TYPE, NO_VERIFY, 0);
    if (ret != 0) {
        FreeDecodedCert(&cert);
        ERROR_OUT(-7742, exit_rsa);
    }

    FreeDecodedCert(&cert);
#else
    (void)bytes;
#endif

#ifdef WOLFSSL_CERT_EXT

#ifdef USE_CERT_BUFFERS_1024
    XMEMCPY(tmp, client_keypub_der_1024, sizeof_client_keypub_der_1024);
    bytes = sizeof_client_keypub_der_1024;
#elif defined(USE_CERT_BUFFERS_2048)
    XMEMCPY(tmp, client_keypub_der_2048, sizeof_client_keypub_der_2048);
    bytes = sizeof_client_keypub_der_2048;
#elif defined(USE_CERT_BUFFERS_3072)
    XMEMCPY(tmp, client_keypub_der_3072, sizeof_client_keypub_der_3072);
    bytes = sizeof_client_keypub_der_3072;
#elif defined(USE_CERT_BUFFERS_4096)
    XMEMCPY(tmp, client_keypub_der_4096, sizeof_client_keypub_der_4096);
    bytes = sizeof_client_keypub_der_4096;
#else
    file = XFOPEN(clientKeyPub, "rb");
    if (!file) {
        err_sys("can't open ./certs/client-keyPub.der, "
                "Please run from wolfSSL home dir", -40);
        ERROR_OUT(-7743, exit_rsa);
    }

    bytes = XFREAD(tmp, 1, FOURK_BUF, file);
    XFCLOSE(file);
#endif /* USE_CERT_BUFFERS */

    ret = wc_InitRsaKey(&keypub, HEAP_HINT);
    if (ret != 0) {
        ERROR_OUT(-7744, exit_rsa);
    }
    idx = 0;

    ret = wc_RsaPublicKeyDecode(tmp, &idx, &keypub, (word32)bytes);
    if (ret != 0) {
        ERROR_OUT(-7745, exit_rsa);
    }
#endif /* WOLFSSL_CERT_EXT */

#ifdef WOLFSSL_KEY_GEN
    ret = rsa_keygen_test(&rng);
    if (ret != 0)
        goto exit_rsa;
#endif

#ifdef WOLFSSL_CERT_GEN
    /* Make Cert / Sign example for RSA cert and RSA CA */
    ret = rsa_certgen_test(&key, &keypub, &rng, tmp);
    if (ret != 0)
        goto exit_rsa;

#if !defined(NO_RSA) && defined(HAVE_ECC)
    ret = rsa_ecc_certgen_test(&rng, tmp);
    if (ret != 0)
        goto exit_rsa;
#endif

#ifdef HAVE_NTRU
    {
        Cert        myCert;
    #if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048)
        XFILE       caFile;
    #endif
    #if !defined(NO_FILESYSTEM) && !defined(NO_WRITE_TEMP_FILES)
        XFILE       ntruPrivFile;
    #endif
        int         certSz;
        word32      idx3 = 0;
    #ifdef WOLFSSL_TEST_CERT
        DecodedCert decode;
    #endif
        byte   public_key[557];          /* sized for EES401EP2 */
        word16 public_key_len;           /* no. of octets in public key */
        byte   private_key[607];         /* sized for EES401EP2 */
        word16 private_key_len;          /* no. of octets in private key */
        DRBG_HANDLE drbg;
        static uint8_t const pers_str[] = {
                'C', 'y', 'a', 'S', 'S', 'L', ' ', 't', 'e', 's', 't'
        };
        word32 rc = ntru_crypto_drbg_instantiate(112, pers_str,
                          sizeof(pers_str), GetEntropy, &drbg);
        if (rc != DRBG_OK) {
            ERROR_OUT(-7746, exit_rsa);
        }

        rc = ntru_crypto_ntru_encrypt_keygen(drbg, NTRU_EES401EP2,
                                             &public_key_len, NULL,
                                             &private_key_len, NULL);
        if (rc != NTRU_OK) {
            ERROR_OUT(-7747, exit_rsa);
        }

        rc = ntru_crypto_ntru_encrypt_keygen(drbg, NTRU_EES401EP2,
                                             &public_key_len, public_key,
                                             &private_key_len, private_key);
        if (rc != NTRU_OK) {
            ERROR_OUT(-7748, exit_rsa);
        }

        rc = ntru_crypto_drbg_uninstantiate(drbg);
        if (rc != NTRU_OK) {
            ERROR_OUT(-7749, exit_rsa);
        }

    #ifdef USE_CERT_BUFFERS_1024
        XMEMCPY(tmp, ca_key_der_1024, sizeof_ca_key_der_1024);
        bytes = sizeof_ca_key_der_1024;
    #elif defined(USE_CERT_BUFFERS_2048)
        XMEMCPY(tmp, ca_key_der_2048, sizeof_ca_key_der_2048);
        bytes = sizeof_ca_key_der_2048;
    #else
        caFile = XFOPEN(rsaCaKeyFile, "rb");
        if (!caFile) {
            ERROR_OUT(-7750, exit_rsa);
        }

        bytes = XFREAD(tmp, 1, FOURK_BUF, caFile);
        XFCLOSE(caFile);
    #endif /* USE_CERT_BUFFERS */

        ret = wc_InitRsaKey(&caKey, HEAP_HINT);
        if (ret != 0) {
            ERROR_OUT(-7751, exit_rsa);
        }
        ret = wc_RsaPrivateKeyDecode(tmp, &idx3, &caKey, (word32)bytes);
        if (ret != 0) {
            ERROR_OUT(-7752, exit_rsa);
        }

        if (wc_InitCert(&myCert)) {
            ERROR_OUT(-7753, exit_rsa);
        }

        XMEMCPY(&myCert.subject, &certDefaultName, sizeof(CertName));
        myCert.daysValid = 1000;

    #ifdef WOLFSSL_CERT_EXT
        /* add SKID from the Public Key */
        if (wc_SetSubjectKeyIdFromNtruPublicKey(&myCert, public_key,
                                                public_key_len) != 0) {
            ERROR_OUT(-7754, exit_rsa);
        }

        /* add AKID from the CA certificate */
    #if defined(USE_CERT_BUFFERS_2048)
        ret = wc_SetAuthKeyIdFromCert(&myCert, ca_cert_der_2048,
                                            sizeof_ca_cert_der_2048);
    #elif defined(USE_CERT_BUFFERS_1024)
        ret = wc_SetAuthKeyIdFromCert(&myCert, ca_cert_der_1024,
                                            sizeof_ca_cert_der_1024);
    #else
        ret = wc_SetAuthKeyId(&myCert, rsaCaCertFile);
    #endif
        if (ret != 0) {
            ERROR_OUT(-7755, exit_rsa);
        }

        /* add Key Usage */
        if (wc_SetKeyUsage(&myCert, certKeyUsage2) != 0) {
            ERROR_OUT(-7756, exit_rsa);
        }
    #endif /* WOLFSSL_CERT_EXT */

    #if defined(USE_CERT_BUFFERS_2048)
        ret = wc_SetIssuerBuffer(&myCert, ca_cert_der_2048,
                                          sizeof_ca_cert_der_2048);
    #elif defined(USE_CERT_BUFFERS_1024)
        ret = wc_SetIssuerBuffer(&myCert, ca_cert_der_1024,
                                          sizeof_ca_cert_der_1024);
    #else
        ret = wc_SetIssuer(&myCert, rsaCaCertFile);
    #endif
        if (ret < 0) {
            ERROR_OUT(-7757, exit_rsa);
        }

        der = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        if (der == NULL) {
            ERROR_OUT(-7758, exit_rsa);
        }

        certSz = wc_MakeNtruCert(&myCert, der, FOURK_BUF, public_key,
                              public_key_len, &rng);
        if (certSz < 0) {
            ERROR_OUT(-7760, exit_rsa);
        }

        ret = 0;
        do {
        #if defined(WOLFSSL_ASYNC_CRYPT)
            ret = wc_AsyncWait(ret, &caKey.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
        #endif
            if (ret >= 0) {
                ret = wc_SignCert(myCert.bodySz, myCert.sigType, der, FOURK_BUF,
                          &caKey, NULL, &rng);
            }
        } while (ret == WC_PENDING_E);
        wc_FreeRsaKey(&caKey);
        if (ret < 0) {
            ERROR_OUT(-7761, exit_rsa);
        }
        certSz = ret;

    #ifdef WOLFSSL_TEST_CERT
        InitDecodedCert(&decode, der, certSz, HEAP_HINT);
        ret = ParseCert(&decode, CERT_TYPE, NO_VERIFY, 0);
        if (ret != 0) {
            FreeDecodedCert(&decode);
            ERROR_OUT(-7762, exit_rsa);
        }
        FreeDecodedCert(&decode);
    #endif

        ret = SaveDerAndPem(der, certSz, "./ntru-cert.der", "./ntru-cert.pem",
            CERT_TYPE, -5637);
        if (ret != 0) {
            goto exit_rsa;
        }

    #if !defined(NO_FILESYSTEM) && !defined(NO_WRITE_TEMP_FILES)
        ntruPrivFile = XFOPEN("./ntru-key.raw", "wb");
        if (!ntruPrivFile) {
            ERROR_OUT(-7763, exit_rsa);
        }
        ret = (int)XFWRITE(private_key, 1, private_key_len, ntruPrivFile);
        XFCLOSE(ntruPrivFile);
        if (ret != private_key_len) {
            ERROR_OUT(-7764, exit_rsa);
        }
    #endif

        XFREE(der, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        der = NULL;
    }
#endif /* HAVE_NTRU */
#ifdef WOLFSSL_CERT_REQ
    {
        Cert        req;
        int         derSz;

        der = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT,DYNAMIC_TYPE_TMP_BUFFER);
        if (der == NULL) {
            ERROR_OUT(-7765, exit_rsa);
        }

        if (wc_InitCert(&req)) {
            ERROR_OUT(-7767, exit_rsa);
        }

        req.version = 0;
        req.isCA    = 1;
        XSTRNCPY(req.challengePw, "wolf123", CTC_NAME_SIZE);
        XMEMCPY(&req.subject, &certDefaultName, sizeof(CertName));

    #ifndef NO_SHA256
        req.sigType = CTC_SHA256wRSA;
    #else
        req.sigType = CTC_SHAwRSA;
    #endif

    #ifdef WOLFSSL_CERT_EXT
        /* add SKID from the Public Key */
        if (wc_SetSubjectKeyIdFromPublicKey(&req, &keypub, NULL) != 0) {
            ERROR_OUT(-7768, exit_rsa);
        }

        /* add Key Usage */
        if (wc_SetKeyUsage(&req, certKeyUsage2) != 0) {
            ERROR_OUT(-7769, exit_rsa);
        }

        /* add Extended Key Usage */
        if (wc_SetExtKeyUsage(&req, "serverAuth,clientAuth,codeSigning,"
                            "emailProtection,timeStamping,OCSPSigning") != 0) {
            ERROR_OUT(-7770, exit_rsa);
        }
    #ifdef WOLFSSL_EKU_OID
        {
            const char unique[] = "2.16.840.1.111111.100.1.10.1";
            if (wc_SetExtKeyUsageOID(&req, unique, sizeof(unique), 0,
                        HEAP_HINT) != 0) {
                ERROR_OUT(-7771, exit_rsa);
            }
        }
    #endif /* WOLFSSL_EKU_OID */
    #endif /* WOLFSSL_CERT_EXT */

        derSz = wc_MakeCertReq(&req, der, FOURK_BUF, &key, NULL);
        if (derSz < 0) {
            ERROR_OUT(-7772, exit_rsa);
        }

    #ifdef WOLFSSL_CERT_EXT
        /* Try again with "any" flag set, will override all others */
        if (wc_SetExtKeyUsage(&req, "any") != 0) {
            ERROR_OUT(-7773, exit_rsa);
        }
        derSz = wc_MakeCertReq(&req, der, FOURK_BUF, &key, NULL);
        if (derSz < 0) {
            ERROR_OUT(-7774, exit_rsa);
        }
    #endif /* WOLFSSL_CERT_EXT */

        ret = 0;
        do {
        #if defined(WOLFSSL_ASYNC_CRYPT)
            ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
        #endif
            if (ret >= 0) {
                ret = wc_SignCert(req.bodySz, req.sigType, der, FOURK_BUF,
                          &key, NULL, &rng);
            }
        } while (ret == WC_PENDING_E);
        if (ret < 0) {
            ERROR_OUT(-7775, exit_rsa);
        }
        derSz = ret;

        ret = SaveDerAndPem(der, derSz, certReqDerFile, certReqPemFile,
            CERTREQ_TYPE, -5650);
        if (ret != 0) {
            goto exit_rsa;
        }

        derSz = wc_MakeCertReq_ex(&req, der, FOURK_BUF, RSA_TYPE, &key);
        if (derSz < 0) {
            ERROR_OUT(-7776, exit_rsa);
        }

        XFREE(der, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        der = NULL;
    }
#endif /* WOLFSSL_CERT_REQ */
#endif /* WOLFSSL_CERT_GEN */

#if defined(WC_RSA_PSS) && !defined(HAVE_FIPS_VERSION) /* not supported with FIPSv1 */
/* Need to create known good signatures to test with this. */
#ifndef WOLFSSL_RSA_VERIFY_ONLY
    ret = rsa_pss_test(&rng, &key);
#endif
#endif

exit_rsa:
    wc_FreeRsaKey(&key);
#ifdef WOLFSSL_CERT_EXT
    wc_FreeRsaKey(&keypub);
#endif
#if defined(HAVE_NTRU)
    wc_FreeRsaKey(&caKey);
#endif

    XFREE(der, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(tmp, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    wc_FreeRng(&rng);

    FREE_VAR(in, HEAP_HINT);
    FREE_VAR(out, HEAP_HINT);
    FREE_VAR(plain, HEAP_HINT);

    /* ret can be greater then 0 with certgen but all negative values should
     * be returned and treated as an error */
    if (ret >= 0) {
        return 0;
    }
    else {
        return ret;
    }
}

#endif /* !NO_RSA */


#ifndef NO_DH

static int dh_fips_generate_test(WC_RNG *rng)
{
    int    ret = 0;
    DhKey  key;
    static byte p[] = {
        0xc5, 0x7c, 0xa2, 0x4f, 0x4b, 0xd6, 0x8c, 0x3c,
        0xda, 0xc7, 0xba, 0xaa, 0xea, 0x2e, 0x5c, 0x1e,
        0x18, 0xb2, 0x7b, 0x8c, 0x55, 0x65, 0x9f, 0xea,
        0xe0, 0xa1, 0x36, 0x53, 0x2b, 0x36, 0xe0, 0x4e,
        0x3e, 0x64, 0xa9, 0xe4, 0xfc, 0x8f, 0x32, 0x62,
        0x97, 0xe4, 0xbe, 0xf7, 0xc1, 0xde, 0x07, 0x5a,
        0x89, 0x28, 0xf3, 0xfe, 0x4f, 0xfe, 0x68, 0xbc,
        0xfb, 0x0a, 0x7c, 0xa4, 0xb3, 0x14, 0x48, 0x89,
        0x9f, 0xaf, 0xb8, 0x43, 0xe2, 0xa0, 0x62, 0x5c,
        0xb4, 0x88, 0x3f, 0x06, 0x50, 0x11, 0xfe, 0x65,
        0x8d, 0x49, 0xd2, 0xf5, 0x4b, 0x74, 0x79, 0xdb,
        0x06, 0x62, 0x92, 0x89, 0xed, 0xda, 0xcb, 0x87,
        0x37, 0x16, 0xd2, 0xa1, 0x7a, 0xe8, 0xde, 0x92,
        0xee, 0x3e, 0x41, 0x4a, 0x91, 0x5e, 0xed, 0xf3,
        0x6c, 0x6b, 0x7e, 0xfd, 0x15, 0x92, 0x18, 0xfc,
        0xa7, 0xac, 0x42, 0x85, 0x57, 0xe9, 0xdc, 0xda,
        0x55, 0xc9, 0x8b, 0x28, 0x9e, 0xc1, 0xc4, 0x46,
        0x4d, 0x88, 0xed, 0x62, 0x8e, 0xdb, 0x3f, 0xb9,
        0xd7, 0xc8, 0xe3, 0xcf, 0xb8, 0x34, 0x2c, 0xd2,
        0x6f, 0x28, 0x06, 0x41, 0xe3, 0x66, 0x8c, 0xfc,
        0x72, 0xff, 0x26, 0x3b, 0x6b, 0x6c, 0x6f, 0x73,
        0xde, 0xf2, 0x90, 0x29, 0xe0, 0x61, 0x32, 0xc4,
        0x12, 0x74, 0x09, 0x52, 0xec, 0xf3, 0x1b, 0xa6,
        0x45, 0x98, 0xac, 0xf9, 0x1c, 0x65, 0x8e, 0x3a,
        0x91, 0x84, 0x4b, 0x23, 0x8a, 0xb2, 0x3c, 0xc9,
        0xfa, 0xea, 0xf1, 0x38, 0xce, 0xd8, 0x05, 0xe0,
        0xfa, 0x44, 0x68, 0x1f, 0xeb, 0xd9, 0x57, 0xb8,
        0x4a, 0x97, 0x5b, 0x88, 0xc5, 0xf1, 0xbb, 0xb0,
        0x49, 0xc3, 0x91, 0x7c, 0xd3, 0x13, 0xb9, 0x47,
        0xbb, 0x91, 0x8f, 0xe5, 0x26, 0x07, 0xab, 0xa9,
        0xc5, 0xd0, 0x3d, 0x95, 0x41, 0x26, 0x92, 0x9d,
        0x13, 0x67, 0xf2, 0x7e, 0x11, 0x88, 0xdc, 0x2d
    };
    static byte g[] = {
        0x4a, 0x1a, 0xf3, 0xa4, 0x92, 0xe9, 0xee, 0x74,
        0x6e, 0x57, 0xd5, 0x8c, 0x2c, 0x5b, 0x41, 0x41,
        0x5e, 0xd4, 0x55, 0x19, 0xdc, 0xd9, 0x32, 0x91,
        0xf7, 0xfd, 0xc2, 0x57, 0xff, 0x03, 0x14, 0xdb,
        0xf1, 0xb7, 0x60, 0x0c, 0x43, 0x59, 0x3f, 0xff,
        0xac, 0xf1, 0x80, 0x9a, 0x15, 0x6f, 0xd8, 0x6e,
        0xb7, 0x85, 0x18, 0xc8, 0xec, 0x4e, 0x59, 0x4a,
        0xe2, 0x91, 0x43, 0x4c, 0xeb, 0x95, 0xb6, 0x2e,
        0x9a, 0xea, 0x53, 0x68, 0x80, 0x64, 0x69, 0x40,
        0xf9, 0xec, 0xbd, 0x85, 0x89, 0x26, 0x97, 0x67,
        0xaf, 0xb0, 0xad, 0x00, 0x1b, 0xd4, 0xfd, 0x94,
        0xd3, 0xe9, 0x92, 0xb1, 0xb4, 0xbc, 0x5a, 0xaa,
        0x92, 0x80, 0x89, 0x3b, 0x39, 0x05, 0x6c, 0x22,
        0x26, 0xfe, 0x5a, 0x28, 0x6c, 0x37, 0x50, 0x5a,
        0x38, 0x99, 0xcf, 0xf3, 0xc1, 0x96, 0x45, 0xdc,
        0x01, 0xcb, 0x20, 0x87, 0xa5, 0x00, 0x8c, 0xf5,
        0x4d, 0xc2, 0xef, 0xb8, 0x9b, 0xd1, 0x87, 0xbe,
        0xed, 0xd5, 0x0a, 0x29, 0x15, 0x34, 0x59, 0x4c,
        0x3a, 0x05, 0x22, 0x05, 0x44, 0x4f, 0x9f, 0xc8,
        0x47, 0x12, 0x24, 0x8e, 0xa8, 0x79, 0xe4, 0x67,
        0xba, 0x4d, 0x5b, 0x75, 0x56, 0x95, 0xeb, 0xe8,
        0x8a, 0xfa, 0x8e, 0x01, 0x8c, 0x1b, 0x74, 0x63,
        0xd9, 0x2f, 0xf7, 0xd3, 0x44, 0x8f, 0xa8, 0xf5,
        0xaf, 0x6c, 0x4f, 0xdb, 0xe7, 0xc9, 0x6c, 0x71,
        0x22, 0xa3, 0x1d, 0xf1, 0x40, 0xb2, 0xe0, 0x9a,
        0xb6, 0x72, 0xc9, 0xc0, 0x13, 0x16, 0xa2, 0x4a,
        0xe1, 0x92, 0xc7, 0x54, 0x23, 0xab, 0x9d, 0xa1,
        0xa1, 0xe5, 0x0b, 0xed, 0xba, 0xe8, 0x84, 0x37,
        0xb2, 0xe7, 0xfe, 0x32, 0x8d, 0xfa, 0x1c, 0x53,
        0x77, 0x97, 0xc7, 0xf3, 0x48, 0xc9, 0xdb, 0x2d,
        0x75, 0x52, 0x9d, 0x42, 0x51, 0x78, 0x62, 0x68,
        0x05, 0x45, 0x15, 0xf8, 0xa2, 0x4e, 0xf3, 0x0b
    };
    static byte q[] = {
        0xe0, 0x35, 0x37, 0xaf, 0xb2, 0x50, 0x91, 0x8e,
        0xf2, 0x62, 0x2b, 0xd9, 0x9f, 0x6c, 0x11, 0x75,
        0xec, 0x24, 0x5d, 0x78, 0x59, 0xe7, 0x8d, 0xb5,
        0x40, 0x52, 0xed, 0x41
    };
    static byte q0[] = {
                                                  0x00,
        0xe0, 0x35, 0x37, 0xaf, 0xb2, 0x50, 0x91, 0x8e,
        0xf2, 0x62, 0x2b, 0xd9, 0x9f, 0x6c, 0x11, 0x75,
        0xec, 0x24, 0x5d, 0x78, 0x59, 0xe7, 0x8d, 0xb5,
        0x40, 0x52, 0xed, 0x41
    };
    byte   priv[256];
    byte   pub[256];
    word32 privSz = sizeof(priv);
    word32 pubSz = sizeof(pub);

    /* Parameter Validation testing. */
    ret = wc_DhGenerateKeyPair(NULL, rng, priv, &privSz, pub, &pubSz);
    if (ret != BAD_FUNC_ARG)
        return -7777;
    ret = wc_DhGenerateKeyPair(&key, NULL, priv, &privSz, pub, &pubSz);
    if (ret != BAD_FUNC_ARG)
        return -7778;
    ret = wc_DhGenerateKeyPair(&key, rng, NULL, &privSz, pub, &pubSz);
    if (ret != BAD_FUNC_ARG)
        return -7779;
    ret = wc_DhGenerateKeyPair(&key, rng, priv, NULL, pub, &pubSz);
    if (ret != BAD_FUNC_ARG)
        return -7780;
    ret = wc_DhGenerateKeyPair(&key, rng, priv, &privSz, NULL, &pubSz);
    if (ret != BAD_FUNC_ARG)
        return -7781;
    ret = wc_DhGenerateKeyPair(&key, rng, priv, &privSz, pub, NULL);
    if (ret != BAD_FUNC_ARG)
        return -7782;

    ret = wc_InitDhKey_ex(&key, HEAP_HINT, devId);
    if (ret != 0)
        return -7783;

    ret = wc_DhSetKey_ex(&key, p, sizeof(p), g, sizeof(g), q0, sizeof(q0));
    if (ret != 0) {
        ERROR_OUT(-7784, exit_gen_test);
    }

    wc_FreeDhKey(&key);

    ret = wc_InitDhKey_ex(&key, HEAP_HINT, devId);
    if (ret != 0)
        return -7785;

    ret = wc_DhSetKey_ex(&key, p, sizeof(p), g, sizeof(g), q, sizeof(q));
    if (ret != 0) {
        ERROR_OUT(-7786, exit_gen_test);
    }

    /* Use API. */
    ret = wc_DhGenerateKeyPair(&key, rng, priv, &privSz, pub, &pubSz);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0) {
        ERROR_OUT(-7787, exit_gen_test);
    }

    ret = wc_DhCheckPubKey_ex(&key, pub, pubSz, q0, sizeof(q0));
    if (ret != 0) {
        ERROR_OUT(-7788, exit_gen_test);
    }

    wc_FreeDhKey(&key);
    ret = wc_InitDhKey_ex(&key, HEAP_HINT, devId);
    if (ret != 0)
        return -7789;

    ret = wc_DhSetKey(&key, p, sizeof(p), g, sizeof(g));
    if (ret != 0) {
        ERROR_OUT(-7790, exit_gen_test);
    }

    ret = wc_DhCheckPubKey_ex(&key, pub, pubSz, q, sizeof(q));
    if (ret != 0) {
        ERROR_OUT(-7791, exit_gen_test);
    }

#ifndef HAVE_SELFTEST
    ret = wc_DhCheckKeyPair(&key, pub, pubSz, priv, privSz);
    if (ret != 0) {
        ERROR_OUT(-7792, exit_gen_test);
    }

    /* Taint the public key so the check fails. */
    pub[0]++;
    ret = wc_DhCheckKeyPair(&key, pub, pubSz, priv, privSz);
    if (ret != MP_CMP_E) {
        ERROR_OUT(-7793, exit_gen_test);
    }

#ifdef WOLFSSL_KEY_GEN
    wc_FreeDhKey(&key);
    ret = wc_InitDhKey_ex(&key, HEAP_HINT, devId);
    if (ret != 0)
        return -7794;

    ret = wc_DhGenerateParams(rng, 2048, &key);
    if (ret != 0) {
        ERROR_OUT(-7795, exit_gen_test);
    }

    privSz = sizeof(priv);
    pubSz = sizeof(pub);

    ret = wc_DhGenerateKeyPair(&key, rng, priv, &privSz, pub, &pubSz);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0) {
        ERROR_OUT(-7796, exit_gen_test);
    }
#endif /* WOLFSSL_KEY_GEN */
#endif /* HAVE_SELFTEST */

    ret = 0;

exit_gen_test:
    wc_FreeDhKey(&key);

    return ret;
}

static int dh_generate_test(WC_RNG *rng)
{
    int    ret = 0;
    DhKey  smallKey;
    byte   p[2] = { 0, 5 };
    byte   g[2] = { 0, 2 };
#ifndef WOLFSSL_SP_MATH
#ifdef WOLFSSL_DH_CONST
    /* the table for constant DH lookup will round to the lowest byte size 21 */
    byte   priv[21];
    byte   pub[21];
#else
    byte   priv[2];
    byte   pub[2];
#endif
    word32 privSz = sizeof(priv);
    word32 pubSz = sizeof(pub);
#endif

    ret = wc_InitDhKey_ex(&smallKey, HEAP_HINT, devId);
    if (ret != 0)
        return -7797;

    /* Parameter Validation testing. */
    ret = wc_InitDhKey_ex(NULL, HEAP_HINT, devId);
    if (ret != BAD_FUNC_ARG)
        return -7798;
    wc_FreeDhKey(NULL);

    ret = wc_DhSetKey(NULL, p, sizeof(p), g, sizeof(g));
    if (ret != BAD_FUNC_ARG) {
        ERROR_OUT(-7799, exit_gen_test);
    }
    ret = wc_DhSetKey(&smallKey, NULL, sizeof(p), g, sizeof(g));
    if (ret != BAD_FUNC_ARG) {
        ERROR_OUT(-7800, exit_gen_test);
    }
    ret = wc_DhSetKey(&smallKey, p, 0, g, sizeof(g));
    if (ret != BAD_FUNC_ARG) {
        ERROR_OUT(-7801, exit_gen_test);
    }
    ret = wc_DhSetKey(&smallKey, p, sizeof(p), NULL, sizeof(g));
    if (ret != BAD_FUNC_ARG) {
        ERROR_OUT(-7802, exit_gen_test);
    }
    ret = wc_DhSetKey(&smallKey, p, sizeof(p), g, 0);
    if (ret != BAD_FUNC_ARG) {
        ERROR_OUT(-7803, exit_gen_test);
    }
    ret = wc_DhSetKey(&smallKey, p, sizeof(p), g, sizeof(g));
    if (ret != 0) {
        ERROR_OUT(-7804, exit_gen_test);
    }

#ifndef WOLFSSL_SP_MATH
    /* Use API. */
    ret = wc_DhGenerateKeyPair(&smallKey, rng, priv, &privSz, pub, &pubSz);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &smallKey.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0) {
        ret = -7805;
    }
#else
    (void)rng;
    ret = 0;
#endif

exit_gen_test:
    wc_FreeDhKey(&smallKey);

    return ret;
}

#if !defined(HAVE_FIPS) && !defined(HAVE_SELFTEST)
typedef struct dh_pubvalue_test {
    const byte* data;
    word32 len;
} dh_pubvalue_test;

static int dh_test_check_pubvalue(void)
{
    int ret;
    word32 i;
    const byte prime[] = {0x01, 0x00, 0x01};
    const byte pubValZero[] = { 0x00 };
    const byte pubValZeroLong[] = { 0x00, 0x00, 0x00 };
    const byte pubValOne[] = { 0x01 };
    const byte pubValOneLong[] = { 0x00, 0x00, 0x01 };
    const byte pubValPrimeMinusOne[] = { 0x01, 0x00, 0x00 };
    const byte pubValPrimeLong[] = {0x00, 0x01, 0x00, 0x01};
    const byte pubValPrimePlusOne[] = { 0x01, 0x00, 0x02 };
    const byte pubValTooBig0[] = { 0x02, 0x00, 0x01 };
    const byte pubValTooBig1[] = { 0x01, 0x01, 0x01 };
    const byte pubValTooLong[] = { 0x01, 0x00, 0x00, 0x01 };
    const dh_pubvalue_test dh_pubval_fail[] = {
        { prime, sizeof(prime) },
        { pubValZero, sizeof(pubValZero) },
        { pubValZeroLong, sizeof(pubValZeroLong) },
        { pubValOne, sizeof(pubValOne) },
        { pubValOneLong, sizeof(pubValOneLong) },
        { pubValPrimeMinusOne, sizeof(pubValPrimeMinusOne) },
        { pubValPrimeLong, sizeof(pubValPrimeLong) },
        { pubValPrimePlusOne, sizeof(pubValPrimePlusOne) },
        { pubValTooBig0, sizeof(pubValTooBig0) },
        { pubValTooBig1, sizeof(pubValTooBig1) },
        { pubValTooLong, sizeof(pubValTooLong) },
    };
    const byte pubValTwo[] = { 0x02 };
    const byte pubValTwoLong[] = { 0x00, 0x00, 0x02 };
    const byte pubValGood[] = { 0x12, 0x34 };
    const byte pubValGoodLen[] = { 0x00, 0x12, 0x34 };
    const byte pubValGoodLong[] = { 0x00, 0x00, 0x12, 0x34 };
    const dh_pubvalue_test dh_pubval_pass[] = {
        { pubValTwo, sizeof(pubValTwo) },
        { pubValTwoLong, sizeof(pubValTwoLong) },
        { pubValGood, sizeof(pubValGood) },
        { pubValGoodLen, sizeof(pubValGoodLen) },
        { pubValGoodLong, sizeof(pubValGoodLong) },
    };

    for (i = 0; i < sizeof(dh_pubval_fail) / sizeof(*dh_pubval_fail); i++) {
        ret = wc_DhCheckPubValue(prime, sizeof(prime), dh_pubval_fail[i].data,
                                                         dh_pubval_fail[i].len);
        if (ret != MP_VAL)
            return -7806 - (int)i;
    }

    for (i = 0; i < sizeof(dh_pubval_pass) / sizeof(*dh_pubval_pass); i++) {
        ret = wc_DhCheckPubValue(prime, sizeof(prime), dh_pubval_pass[i].data,
                                                         dh_pubval_pass[i].len);
        if (ret != 0)
            return -7816 - (int)i;
    }

    return 0;
}
#endif

#if defined(HAVE_FFDHE)

#ifdef HAVE_FFDHE_3072
    #define FFDHE_KEY_SIZE      (3072/8)
#else
    #define FFDHE_KEY_SIZE      (2048/8)
#endif

static int dh_test_ffdhe(WC_RNG *rng, const DhParams* params)
{
    int    ret;
    word32 privSz, pubSz, privSz2, pubSz2;
    byte   priv[FFDHE_KEY_SIZE];
    byte   pub[FFDHE_KEY_SIZE];
    byte   priv2[FFDHE_KEY_SIZE];
    byte   pub2[FFDHE_KEY_SIZE];
    byte   agree[FFDHE_KEY_SIZE];
    byte   agree2[FFDHE_KEY_SIZE];
    word32 agreeSz = (word32)sizeof(agree);
    word32 agreeSz2 = (word32)sizeof(agree2);
    DhKey  key;
    DhKey  key2;

    XMEMSET(&key, 0, sizeof(DhKey));
    XMEMSET(&key2, 0, sizeof(DhKey));

    ret = wc_InitDhKey_ex(&key, HEAP_HINT, devId);
    if (ret != 0) {
        ERROR_OUT(-7826, done);
    }
    ret = wc_InitDhKey_ex(&key2, HEAP_HINT, devId);
    if (ret != 0) {
        ERROR_OUT(-7827, done);
    }

    ret = wc_DhSetKey(&key, params->p, params->p_len, params->g, params->g_len);
    if (ret != 0) {
        ERROR_OUT(-7828, done);
    }

    ret = wc_DhSetKey(&key2, params->p, params->p_len, params->g,
                                                                 params->g_len);
    if (ret != 0) {
        ERROR_OUT(-7829, done);
    }

    ret = wc_DhGenerateKeyPair(&key, rng, priv, &privSz, pub, &pubSz);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0) {
        ERROR_OUT(-7830, done);
    }

    ret = wc_DhGenerateKeyPair(&key2, rng, priv2, &privSz2, pub2, &pubSz2);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &key2.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0) {
        ERROR_OUT(-7831, done);
    }

    ret = wc_DhAgree(&key, agree, &agreeSz, priv, privSz, pub2, pubSz2);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0) {
        ERROR_OUT(-7832, done);
    }

    ret = wc_DhAgree(&key2, agree2, &agreeSz2, priv2, privSz2, pub, pubSz);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &key2.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0) {
        ERROR_OUT(-7833, done);
    }

    if (agreeSz != agreeSz2 || XMEMCMP(agree, agree2, agreeSz)) {
        ERROR_OUT(-7834, done);
    }

done:
    wc_FreeDhKey(&key);
    wc_FreeDhKey(&key2);
    return ret;
}

#endif /* HAVE_FFDHE */

int dh_test(void)
{
    int    ret;
    word32 bytes;
    word32 idx = 0, privSz, pubSz, privSz2, pubSz2;
    byte   tmp[1024];
#if !defined(USE_CERT_BUFFERS_3072) && !defined(USE_CERT_BUFFERS_4096)
    byte   priv[256];
    byte   pub[256];
    byte   priv2[256];
    byte   pub2[256];
    byte   agree[256];
    byte   agree2[256];
#else
    byte   priv[512];
    byte   pub[512];
    byte   priv2[512];
    byte   pub2[512];
    byte   agree[512];
    byte   agree2[512];
#endif
    word32 agreeSz = (word32)sizeof(agree);
    word32 agreeSz2 = (word32)sizeof(agree2);
    DhKey  key;
    DhKey  key2;
    WC_RNG rng;
    int keyInit = 0;

#ifdef USE_CERT_BUFFERS_1024
    XMEMCPY(tmp, dh_key_der_1024, (size_t)sizeof_dh_key_der_1024);
    bytes = (size_t)sizeof_dh_key_der_1024;
#elif defined(USE_CERT_BUFFERS_2048)
    XMEMCPY(tmp, dh_key_der_2048, (size_t)sizeof_dh_key_der_2048);
    bytes = (size_t)sizeof_dh_key_der_2048;
#elif defined(USE_CERT_BUFFERS_3072)
    XMEMCPY(tmp, dh_key_der_3072, (size_t)sizeof_dh_key_der_3072);
    bytes = (size_t)sizeof_dh_key_der_3072;
#elif defined(USE_CERT_BUFFERS_4096)
    XMEMCPY(tmp, dh_key_der_4096, (size_t)sizeof_dh_key_der_4096);
    bytes = (size_t)sizeof_dh_key_der_4096;
#elif defined(NO_ASN)
    /* don't use file, no DER parsing */
#elif !defined(NO_FILESYSTEM)
    XFILE  file = XFOPEN(dhParamsFile, "rb");
    if (!file)
        return -7900;

    bytes = (word32) XFREAD(tmp, 1, sizeof(tmp), file);
    XFCLOSE(file);
#else
    /* No DH key to use. */
    return -7901;
#endif /* USE_CERT_BUFFERS */

    (void)idx;
    (void)tmp;
    (void)bytes;

    XMEMSET(&rng, 0, sizeof(rng));
    /* Use API for coverage. */
    ret = wc_InitDhKey(&key);
    if (ret != 0) {
        ERROR_OUT(-7902, done);
    }
    wc_FreeDhKey(&key);

    ret = wc_InitDhKey_ex(&key, HEAP_HINT, devId);
    if (ret != 0) {
        ERROR_OUT(-7903, done);
    }
    keyInit = 1;
    ret = wc_InitDhKey_ex(&key2, HEAP_HINT, devId);
    if (ret != 0) {
        ERROR_OUT(-7904, done);
    }

#ifdef NO_ASN
    ret = wc_DhSetKey(&key, dh_p, sizeof(dh_p), dh_g, sizeof(dh_g));
    if (ret != 0) {
        ERROR_OUT(-7905, done);
    }

    ret = wc_DhSetKey(&key2, dh_p, sizeof(dh_p), dh_g, sizeof(dh_g));
    if (ret != 0) {
        ERROR_OUT(-7906, done);
    }
#else
    ret = wc_DhKeyDecode(tmp, &idx, &key, bytes);
    if (ret != 0) {
        ERROR_OUT(-7907, done);
    }

    idx = 0;
    ret = wc_DhKeyDecode(tmp, &idx, &key2, bytes);
    if (ret != 0) {
        ERROR_OUT(-7908, done);
    }
#endif

#ifndef HAVE_FIPS
    ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
    ret = wc_InitRng(&rng);
#endif
    if (ret != 0) {
        ERROR_OUT(-7909, done);
    }

    ret = wc_DhGenerateKeyPair(&key, &rng, priv, &privSz, pub, &pubSz);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0) {
        ERROR_OUT(-7910, done);
    }

    ret = wc_DhGenerateKeyPair(&key2, &rng, priv2, &privSz2, pub2, &pubSz2);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &key2.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0) {
        ERROR_OUT(-7911, done);
    }

    ret = wc_DhAgree(&key, agree, &agreeSz, priv, privSz, pub2, pubSz2);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0) {
        ERROR_OUT(-7912, done);
    }

    ret = wc_DhAgree(&key2, agree2, &agreeSz2, priv2, privSz2, pub, pubSz);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &key2.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0) {
        ERROR_OUT(-7913, done);
    }

    if (agreeSz != agreeSz2 || XMEMCMP(agree, agree2, agreeSz)) {
        ERROR_OUT(-7914, done);
    }

#if defined(WOLFSSL_KEY_GEN) && !defined(HAVE_FIPS) && !defined(HAVE_SELFTEST)
    if (wc_DhCheckPrivKey(NULL, NULL, 0) != BAD_FUNC_ARG)
        return -7915;

    if (wc_DhCheckPrivKey(&key, priv, privSz) != 0)
        return -7916;

    if (wc_DhExportParamsRaw(NULL, NULL, NULL, NULL, NULL, NULL, NULL) != BAD_FUNC_ARG)
        return -7917;
    {
        word32 pSz, qSz, gSz;
        if (wc_DhExportParamsRaw(&key, NULL, &pSz, NULL, &qSz, NULL, &gSz) != LENGTH_ONLY_E)
            return -7918;
    }
#endif

    

    /* Test DH key import / export */
#ifdef WOLFSSL_DH_EXTRA
#if !defined(NO_ASN) && !defined(NO_FILESYSTEM)
    file = XFOPEN(dhKeyFile, "rb");
    if (!file)
        return -7950;
    bytes = (word32)XFREAD(tmp, 1, sizeof(tmp), file);
    XFCLOSE(file);

    idx = 0;
    ret = wc_DhKeyDecode(tmp, &idx, &key, bytes);
    if (ret != 0) {
        return -7951;
    }
#endif

    privSz = sizeof(priv);
    pubSz = sizeof(pub);
    ret = wc_DhExportKeyPair(&key, priv, &privSz, pub, &pubSz);
    if (ret != 0) {
        return -7952;
    }
    ret = wc_DhImportKeyPair(&key2, priv, privSz, pub, pubSz);
    if (ret != 0) {
        return -7953;
    }
#endif /* WOLFSSL_DH_EXTRA */

    ret = dh_generate_test(&rng);
    if (ret == 0)
        ret = dh_fips_generate_test(&rng);
#if !defined(HAVE_FIPS) && !defined(HAVE_SELFTEST)
    if (ret == 0)
        ret = dh_test_check_pubvalue();
#endif

    /* Specialized code for key gen when using FFDHE-2048 and FFDHE-3072. */
    #ifdef HAVE_FFDHE_2048
    if (ret == 0) {
        ret = dh_test_ffdhe(&rng, wc_Dh_ffdhe2048_Get());
        if (ret != 0)
            printf("error with FFDHE 2048\n");
    }
    #endif
    #ifdef HAVE_FFDHE_3072
    if (ret == 0) {
        ret = dh_test_ffdhe(&rng, wc_Dh_ffdhe3072_Get());
        if (ret != 0)
            printf("error with FFDHE 3072\n");
    }
    #endif

    wc_FreeDhKey(&key);
    keyInit = 0;

#if !defined(HAVE_FIPS) && !defined(HAVE_SELFTEST) && \
    !defined(WOLFSSL_OLD_PRIME_CHECK)
    if (ret == 0) {
        /* Test Check Key */
        ret = wc_DhSetCheckKey(&key, dh_p, sizeof(dh_p), dh_g, sizeof(dh_g),
            NULL, 0, 0, &rng);
        keyInit = 1; /* DhSetCheckKey also initializes the key, free it */
    }
#endif

done:

    if (keyInit)
        wc_FreeDhKey(&key);
    wc_FreeDhKey(&key2);
    wc_FreeRng(&rng);

    return ret;
}

#endif /* NO_DH */


#ifndef NO_DSA

int dsa_test(void)
{
    int    ret, answer;
    word32 bytes;
    word32 idx = 0;
    byte   tmp[1024];
    DsaKey key;
    WC_RNG rng;
    wc_Sha sha;
    byte   hash[WC_SHA_DIGEST_SIZE];
    byte   signature[40];

#ifdef USE_CERT_BUFFERS_1024
    XMEMCPY(tmp, dsa_key_der_1024, sizeof_dsa_key_der_1024);
    bytes = sizeof_dsa_key_der_1024;
#elif defined(USE_CERT_BUFFERS_2048)
    XMEMCPY(tmp, dsa_key_der_2048, sizeof_dsa_key_der_2048);
    bytes = sizeof_dsa_key_der_2048;
#else
    XFILE  file = XFOPEN(dsaKey, "rb");
    if (!file)
        return -8000;

    bytes = (word32) XFREAD(tmp, 1, sizeof(tmp), file);
    XFCLOSE(file);
#endif /* USE_CERT_BUFFERS */

    ret = wc_InitSha_ex(&sha, HEAP_HINT, devId);
    if (ret != 0)
        return -8001;
    wc_ShaUpdate(&sha, tmp, bytes);
    wc_ShaFinal(&sha, hash);
    wc_ShaFree(&sha);

    ret = wc_InitDsaKey(&key);
    if (ret != 0) return -8002;

    ret = wc_DsaPrivateKeyDecode(tmp, &idx, &key, bytes);
    if (ret != 0) return -8003;

#ifndef HAVE_FIPS
    ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
    ret = wc_InitRng(&rng);
#endif
    if (ret != 0) return -8004;

    ret = wc_DsaSign(hash, signature, &key, &rng);
    if (ret != 0) return -8005;

    ret = wc_DsaVerify(hash, signature, &key, &answer);
    if (ret != 0) return -8006;
    if (answer != 1) return -8007;

    wc_FreeDsaKey(&key);

#ifdef WOLFSSL_KEY_GEN
    {
    byte*  der;
    int    derSz = 0;
    DsaKey derIn;
    DsaKey genKey;

    ret = wc_InitDsaKey(&genKey);
    if (ret != 0) return -8008;

    ret = wc_MakeDsaParameters(&rng, 1024, &genKey);
    if (ret != 0) {
        wc_FreeDsaKey(&genKey);
        return -8009;
    }

    ret = wc_MakeDsaKey(&rng, &genKey);
    if (ret != 0) {
        wc_FreeDsaKey(&genKey);
        return -8010;
    }

    der = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (der == NULL) {
        wc_FreeDsaKey(&genKey);
        return -8011;
    }

    derSz = wc_DsaKeyToDer(&genKey, der, FOURK_BUF);
    if (derSz < 0) {
        XFREE(der, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        return -8013;
    }

    ret = SaveDerAndPem(der, derSz, keyDerFile, keyPemFile,
        DSA_PRIVATEKEY_TYPE, -5814);
    if (ret != 0) {
        XFREE(der, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        wc_FreeDsaKey(&genKey);
        return ret;
    }

    ret = wc_InitDsaKey(&derIn);
    if (ret != 0) {
        XFREE(der, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        wc_FreeDsaKey(&genKey);
        return -8014;
    }

    idx = 0;
    ret = wc_DsaPrivateKeyDecode(der, &idx, &derIn, derSz);
    if (ret != 0) {
        XFREE(der, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        wc_FreeDsaKey(&derIn);
        wc_FreeDsaKey(&genKey);
        return -8015;
    }

    wc_FreeDsaKey(&derIn);
    wc_FreeDsaKey(&genKey);
    XFREE(der, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif /* WOLFSSL_KEY_GEN */

    if (wc_InitDsaKey_h(&key, NULL) != 0)
        return -8016;

    wc_FreeRng(&rng);
    return 0;
}

#endif /* NO_DSA */

#ifdef WOLFCRYPT_HAVE_SRP

static int generate_random_salt(byte *buf, word32 size)
{
    int ret = -8017;
    WC_RNG rng;

    if(NULL == buf || !size)
        return -8018;

    if (buf && size && wc_InitRng_ex(&rng, HEAP_HINT, devId) == 0) {
        ret = wc_RNG_GenerateBlock(&rng, (byte *)buf, size);

        wc_FreeRng(&rng);
    }

    return ret;
}

int srp_test(void)
{
    Srp cli, srv;
    int r;

    byte clientPubKey[80]; /* A */
    byte serverPubKey[80]; /* B */
    word32 clientPubKeySz = 80;
    word32 serverPubKeySz = 80;
    byte clientProof[SRP_MAX_DIGEST_SIZE]; /* M1 */
    byte serverProof[SRP_MAX_DIGEST_SIZE]; /* M2 */
    word32 clientProofSz = SRP_MAX_DIGEST_SIZE;
    word32 serverProofSz = SRP_MAX_DIGEST_SIZE;

    byte username[] = "user";
    word32 usernameSz = 4;

    byte password[] = "password";
    word32 passwordSz = 8;

    byte N[] = {
        0xC9, 0x4D, 0x67, 0xEB, 0x5B, 0x1A, 0x23, 0x46, 0xE8, 0xAB, 0x42, 0x2F,
        0xC6, 0xA0, 0xED, 0xAE, 0xDA, 0x8C, 0x7F, 0x89, 0x4C, 0x9E, 0xEE, 0xC4,
        0x2F, 0x9E, 0xD2, 0x50, 0xFD, 0x7F, 0x00, 0x46, 0xE5, 0xAF, 0x2C, 0xF7,
        0x3D, 0x6B, 0x2F, 0xA2, 0x6B, 0xB0, 0x80, 0x33, 0xDA, 0x4D, 0xE3, 0x22,
        0xE1, 0x44, 0xE7, 0xA8, 0xE9, 0xB1, 0x2A, 0x0E, 0x46, 0x37, 0xF6, 0x37,
        0x1F, 0x34, 0xA2, 0x07, 0x1C, 0x4B, 0x38, 0x36, 0xCB, 0xEE, 0xAB, 0x15,
        0x03, 0x44, 0x60, 0xFA, 0xA7, 0xAD, 0xF4, 0x83
    };

    byte g[] = {
        0x02
    };

    byte salt[10];

    byte verifier[80];
    word32 v_size = sizeof(verifier);

    /* set as 0's so if second init on srv not called SrpTerm is not on
     * garbage values */
    XMEMSET(&srv, 0, sizeof(Srp));
    XMEMSET(&cli, 0, sizeof(Srp));

    /* generating random salt */

    r = generate_random_salt(salt, sizeof(salt));

    /* client knows username and password.   */
    /* server knows N, g, salt and verifier. */

    if (!r) r = wc_SrpInit(&cli, SRP_TYPE_SHA, SRP_CLIENT_SIDE);
    if (!r) r = wc_SrpSetUsername(&cli, username, usernameSz);

    /* loading N, g and salt in advance to generate the verifier. */

    if (!r) r = wc_SrpSetParams(&cli, N,    sizeof(N),
                                      g,    sizeof(g),
                                      salt, sizeof(salt));
    if (!r) r = wc_SrpSetPassword(&cli, password, passwordSz);
    if (!r) r = wc_SrpGetVerifier(&cli, verifier, &v_size);

    /* client sends username to server */

    if (!r) r = wc_SrpInit(&srv, SRP_TYPE_SHA, SRP_SERVER_SIDE);
    if (!r) r = wc_SrpSetUsername(&srv, username, usernameSz);
    if (!r) r = wc_SrpSetParams(&srv, N,    sizeof(N),
                                      g,    sizeof(g),
                                      salt, sizeof(salt));
    if (!r) r = wc_SrpSetVerifier(&srv, verifier, v_size);
    if (!r) r = wc_SrpGetPublic(&srv, serverPubKey, &serverPubKeySz);

    /* server sends N, g, salt and B to client */

    if (!r) r = wc_SrpGetPublic(&cli, clientPubKey, &clientPubKeySz);
    if (!r) r = wc_SrpComputeKey(&cli, clientPubKey, clientPubKeySz,
                                       serverPubKey, serverPubKeySz);
    if (!r) r = wc_SrpGetProof(&cli, clientProof, &clientProofSz);

    /* client sends A and M1 to server */

    if (!r) r = wc_SrpComputeKey(&srv, clientPubKey, clientPubKeySz,
                                       serverPubKey, serverPubKeySz);
    if (!r) r = wc_SrpVerifyPeersProof(&srv, clientProof, clientProofSz);
    if (!r) r = wc_SrpGetProof(&srv, serverProof, &serverProofSz);

    /* server sends M2 to client */

    if (!r) r = wc_SrpVerifyPeersProof(&cli, serverProof, serverProofSz);

    wc_SrpTerm(&cli);
    wc_SrpTerm(&srv);

    return r;
}

#endif /* WOLFCRYPT_HAVE_SRP */

#if defined(OPENSSL_EXTRA) && !defined(WOLFCRYPT_ONLY)

#if !defined(NO_AES) && !defined(WOLFCRYPT_ONLY)
static int openssl_aes_test(void)
{
#ifdef HAVE_AES_CBC
#ifdef WOLFSSL_AES_128
    {
        /* EVP_CipherUpdate test */
        const byte cbcPlain[] =
        {
            0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
            0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a,
            0xae,0x2d,0x8a,0x57,0x1e,0x03,0xac,0x9c,
            0x9e,0xb7,0x6f,0xac,0x45,0xaf,0x8e,0x51,
            0x30,0xc8,0x1c,0x46,0xa3,0x5c,0xe4,0x11,
            0xe5,0xfb,0xc1,0x19,0x1a,0x0a,0x52,0xef,
            0xf6,0x9f,0x24,0x45,0xdf,0x4f,0x9b,0x17,
            0xad,0x2b,0x41,0x7b,0xe6,0x6c,0x37,0x10
        };

        byte key[] = "0123456789abcdef   ";  /* align */
        byte iv[]  = "1234567890abcdef   ";  /* align */

        byte cipher[AES_BLOCK_SIZE * 4];
        byte plain [AES_BLOCK_SIZE * 4];
        EVP_CIPHER_CTX en;
        EVP_CIPHER_CTX de;
        int outlen ;
        int total = 0;
        int i;

        EVP_CIPHER_CTX_init(&en);
        if (EVP_CipherInit(&en, EVP_aes_128_cbc(),
            (unsigned char*)key, (unsigned char*)iv, 1) == 0)
            return -8200;
        if (EVP_CipherUpdate(&en, (byte*)cipher, &outlen,
                    (byte*)cbcPlain, 9) == 0)
            return -8201;
        if (outlen != 0)
            return -8202;
        total += outlen;

        if (EVP_CipherUpdate(&en, (byte*)&cipher[total], &outlen,
                    (byte*)&cbcPlain[9]  , 9) == 0)
            return -8203;
        if (outlen != 16)
            return -8204;
        total += outlen;

        if (EVP_CipherFinal(&en, (byte*)&cipher[total], &outlen) == 0)
            return -8205;
        if (outlen != 16)
            return -8206;
        total += outlen;
        if (total != 32)
            return 3408;

        total = 0;
        EVP_CIPHER_CTX_init(&de);
        if (EVP_CipherInit(&de, EVP_aes_128_cbc(),
            (unsigned char*)key, (unsigned char*)iv, 0) == 0)
            return -8207;

        if (EVP_CipherUpdate(&de, (byte*)plain, &outlen, (byte*)cipher, 6) == 0)
            return -8208;
        if (outlen != 0)
            return -8209;
        total += outlen;

        if (EVP_CipherUpdate(&de, (byte*)&plain[total], &outlen,
                    (byte*)&cipher[6], 12) == 0)
            return -8210;
        if (outlen != 0)
        total += outlen;

        if (EVP_CipherUpdate(&de, (byte*)&plain[total], &outlen,
                    (byte*)&cipher[6+12], 14) == 0)
            return -8211;
        if (outlen != 16)
            return -8212;
        total += outlen;

        if (EVP_CipherFinal(&de, (byte*)&plain[total], &outlen) == 0)
            return -8213;
        if (outlen != 2)
            return -8214;
        total += outlen;

        if (total != 18)
            return 3427;

        if (XMEMCMP(plain, cbcPlain, 18))
            return -8215;

        /* test with encrypting/decrypting more than 16 bytes at once */
        total = 0;
        EVP_CIPHER_CTX_init(&en);
        if (EVP_CipherInit(&en, EVP_aes_128_cbc(),
            (unsigned char*)key, (unsigned char*)iv, 1) == 0)
            return -8216;
        if (EVP_CipherUpdate(&en, (byte*)cipher, &outlen,
                    (byte*)cbcPlain, 17) == 0)
            return -8217;
        if (outlen != 16)
            return -8218;
        total += outlen;

        if (EVP_CipherUpdate(&en, (byte*)&cipher[total], &outlen,
                    (byte*)&cbcPlain[17]  , 1) == 0)
            return -8219;
        if (outlen != 0)
            return -8220;
        total += outlen;

        if (EVP_CipherFinal(&en, (byte*)&cipher[total], &outlen) == 0)
            return -8221;
        if (outlen != 16)
            return -8222;
        total += outlen;
        if (total != 32)
            return -8223;

        total = 0;
        EVP_CIPHER_CTX_init(&de);
        if (EVP_CipherInit(&de, EVP_aes_128_cbc(),
            (unsigned char*)key, (unsigned char*)iv, 0) == 0)
            return -8224;

        if (EVP_CipherUpdate(&de, (byte*)plain, &outlen, (byte*)cipher, 17) == 0)
            return -8225;
        if (outlen != 16)
            return -8226;
        total += outlen;

        /* final call on non block size should fail */
        if (EVP_CipherFinal(&de, (byte*)&plain[total], &outlen) != 0)
            return -8227;

        if (EVP_CipherUpdate(&de, (byte*)&plain[total], &outlen,
                    (byte*)&cipher[17], 1) == 0)
            return -8228;
        if (outlen != 0)
        total += outlen;

        if (EVP_CipherUpdate(&de, (byte*)&plain[total], &outlen,
                    (byte*)&cipher[17+1], 14) == 0)
            return -8229;
        if (outlen != 0)
            return -8230;
        total += outlen;

        if (EVP_CipherFinal(&de, (byte*)&plain[total], &outlen) == 0)
            return -8231;
        if (outlen != 2)
            return -8232;
        total += outlen;

        if (total != 18)
            return -8233;

        if (XMEMCMP(plain, cbcPlain, 18))
            return -8234;

        /* test byte by byte decrypt */
        for (i = 0; i < AES_BLOCK_SIZE * 3; i++) {
            plain[i] = i;
        }

        total = 0;
        EVP_CIPHER_CTX_init(&en);
        if (EVP_CipherInit(&en, EVP_aes_128_cbc(),
            (unsigned char*)key, (unsigned char*)iv, 1) == 0)
            return -8235;
        if (EVP_CipherUpdate(&en, (byte*)cipher, &outlen,
                    (byte*)plain, AES_BLOCK_SIZE * 3) == 0)
            return -8236;
        if (outlen != AES_BLOCK_SIZE * 3)
            return -8237;
        total += outlen;

        if (EVP_CipherFinal(&en, (byte*)&cipher[total], &outlen) == 0)
            return -8238;
        if (outlen != AES_BLOCK_SIZE)
            return -8239;
        total += outlen;
        if (total != sizeof(plain))
            return -8240;

        total = 0;
        EVP_CIPHER_CTX_init(&de);
        if (EVP_CipherInit(&de, EVP_aes_128_cbc(),
            (unsigned char*)key, (unsigned char*)iv, 0) == 0)
            return -8241;

        for (i = 0; i < AES_BLOCK_SIZE * 4; i++) {
            if (EVP_CipherUpdate(&de, (byte*)plain + total, &outlen,
                        (byte*)cipher + i, 1) == 0)
                return -8242;

            if (outlen > 0) {
                int j;

                total += outlen;
                for (j = 0; j < total; j++) {
                    if (plain[j] != j) {
                        return -8243;
                    }
                }
            }
        }

        if (EVP_CipherFinal(&de, (byte*)&plain[total], &outlen) == 0)
            return -8244;
        total += outlen;
        if (total != AES_BLOCK_SIZE * 3) {
            return -8245;
        }
        for (i = 0; i < AES_BLOCK_SIZE * 3; i++) {
            if (plain[i] != i) {
                return -8246;
            }
        }
    }

    /* set buffers to be exact size to catch potential over read/write */
    {
        /* EVP_CipherUpdate test */
        const byte cbcPlain[] =
        {
            0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
            0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a,
            0xae,0x2d,0x8a,0x57,0x1e,0x03,0xac,0x9c,
            0x9e,0xb7,0x6f,0xac,0x45,0xaf,0x8e,0x51,
            0x30,0xc8,0x1c,0x46,0xa3,0x5c,0xe4,0x11,
            0xe5,0xfb,0xc1,0x19,0x1a,0x0a,0x52,0xef,
            0xf6,0x9f,0x24,0x45,0xdf,0x4f,0x9b,0x17,
            0xad,0x2b,0x41,0x7b,0xe6,0x6c,0x37,0x10
        };

        byte key[] = "0123456789abcdef   ";  /* align */
        byte iv[]  = "1234567890abcdef   ";  /* align */

        #define EVP_TEST_BUF_SZ 18
        #define EVP_TEST_BUF_PAD 32
        byte cipher[EVP_TEST_BUF_SZ];
        byte plain [EVP_TEST_BUF_SZ];
        byte padded[EVP_TEST_BUF_PAD];
        EVP_CIPHER_CTX en;
        EVP_CIPHER_CTX de;
        int outlen ;
        int total = 0;

        EVP_CIPHER_CTX_init(&en);
        if (EVP_CipherInit(&en, EVP_aes_128_cbc(),
            (unsigned char*)key, (unsigned char*)iv, 1) == 0)
            return -8247;
        if (EVP_CIPHER_CTX_set_padding(&en, 0) != 1)
            return -8248;
        if (EVP_CipherUpdate(&en, (byte*)cipher, &outlen,
                    (byte*)cbcPlain, EVP_TEST_BUF_SZ) == 0)
            return -8249;
        if (outlen != 16)
            return -8250;
        total += outlen;

        /* should fail here */
        if (EVP_CipherFinal(&en, (byte*)&cipher[total], &outlen) != 0)
            return -8251;

        /* turn padding back on and do successful encrypt */
        total = 0;
        EVP_CIPHER_CTX_init(&en);
        if (EVP_CipherInit(&en, EVP_aes_128_cbc(),
            (unsigned char*)key, (unsigned char*)iv, 1) == 0)
            return -8252;
        if (EVP_CIPHER_CTX_set_padding(&en, 1) != 1)
            return -8253;
        if (EVP_CipherUpdate(&en, (byte*)padded, &outlen,
                    (byte*)cbcPlain, EVP_TEST_BUF_SZ) == 0)
            return -8254;
        if (outlen != 16)
            return -8255;
        total += outlen;

        if (EVP_CipherFinal(&en, (byte*)&padded[total], &outlen) == 0)
            return -8256;
        total += outlen;
        if (total != 32)
            return -8257;
        XMEMCPY(cipher, padded, EVP_TEST_BUF_SZ);

        /* test out of bounds read on buffers w/o padding during decryption */
        total = 0;
        EVP_CIPHER_CTX_init(&de);
        if (EVP_CipherInit(&de, EVP_aes_128_cbc(),
            (unsigned char*)key, (unsigned char*)iv, 0) == 0)
            return -8258;

        if (EVP_CIPHER_CTX_set_padding(&de, 0) != 1)
            return -8259;
        if (EVP_CipherUpdate(&de, (byte*)plain, &outlen, (byte*)cipher,
                    EVP_TEST_BUF_SZ) == 0)
            return -8260;
        if (outlen != 16)
            return -8261;
        total += outlen;

        /* should fail since not using padding */
        if (EVP_CipherFinal(&de, (byte*)&plain[total], &outlen) != 0)
            return -8262;

        total = 0;
        EVP_CIPHER_CTX_init(&de);
        if (EVP_CipherInit(&de, EVP_aes_128_cbc(),
            (unsigned char*)key, (unsigned char*)iv, 0) == 0)
            return -8263;
        if (EVP_CIPHER_CTX_set_padding(&de, 1) != 1)
            return -8264;
        if (EVP_CipherUpdate(&de, (byte*)padded, &outlen, (byte*)padded,
                    EVP_TEST_BUF_PAD) == 0)
            return -8265;
        if (outlen != 16)
            return -8266;
        total += outlen;

        if (EVP_CipherFinal(&de, (byte*)&padded[total], &outlen) == 0)
            return -8267;
        if (XMEMCMP(padded, cbcPlain, EVP_TEST_BUF_SZ))
            return -8268;
    }

    {  /* evp_cipher test: EVP_aes_128_cbc */
        EVP_CIPHER_CTX ctx;

        const byte msg[] = { /* "Now is the time for all " w/o trailing 0 */
            0x6e,0x6f,0x77,0x20,0x69,0x73,0x20,0x74,
            0x68,0x65,0x20,0x74,0x69,0x6d,0x65,0x20,
            0x66,0x6f,0x72,0x20,0x61,0x6c,0x6c,0x20
        };

        const byte verify[] =
        {
            0x95,0x94,0x92,0x57,0x5f,0x42,0x81,0x53,
            0x2c,0xcc,0x9d,0x46,0x77,0xa2,0x33,0xcb
        };

        byte key[] = "0123456789abcdef   ";  /* align */
        byte iv[]  = "1234567890abcdef   ";  /* align */

        byte cipher[AES_BLOCK_SIZE * 4];
        byte plain [AES_BLOCK_SIZE * 4];

        EVP_CIPHER_CTX_init(&ctx);
        if (EVP_CipherInit(&ctx, EVP_aes_128_cbc(), key, iv, 1) == 0)
            return -8269;

        if (EVP_Cipher(&ctx, cipher, (byte*)msg, 16) == 0)
            return -8270;

        if (XMEMCMP(cipher, verify, AES_BLOCK_SIZE))
            return -8271;

        EVP_CIPHER_CTX_init(&ctx);
        if (EVP_CipherInit(&ctx, EVP_aes_128_cbc(), key, iv, 0) == 0)
            return -8272;

        if (EVP_Cipher(&ctx, plain, cipher, 16) == 0)
            return -8273;

        if (XMEMCMP(plain, msg, AES_BLOCK_SIZE))
            return -8274;


    }  /* end evp_cipher test: EVP_aes_128_cbc*/
#endif /* WOLFSSL_AES_128 */
#endif /* HAVE_AES_CBC */

#if defined(HAVE_AES_ECB) && defined(WOLFSSL_AES_256)
    {  /* evp_cipher test: EVP_aes_256_ecb*/
        EVP_CIPHER_CTX ctx;
        const byte msg[] =
        {
          0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
          0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a
        };

        const byte verify[] =
        {
            0xf3,0xee,0xd1,0xbd,0xb5,0xd2,0xa0,0x3c,
            0x06,0x4b,0x5a,0x7e,0x3d,0xb1,0x81,0xf8
        };

        const byte key[] =
        {
          0x60,0x3d,0xeb,0x10,0x15,0xca,0x71,0xbe,
          0x2b,0x73,0xae,0xf0,0x85,0x7d,0x77,0x81,
          0x1f,0x35,0x2c,0x07,0x3b,0x61,0x08,0xd7,
          0x2d,0x98,0x10,0xa3,0x09,0x14,0xdf,0xf4
        };


        byte cipher[AES_BLOCK_SIZE * 4];
        byte plain [AES_BLOCK_SIZE * 4];

        EVP_CIPHER_CTX_init(&ctx);
        if (EVP_CipherInit(&ctx, EVP_aes_256_ecb(), (unsigned char*)key, NULL, 1) == 0)
            return -8275;

        if (EVP_Cipher(&ctx, cipher, (byte*)msg, 16) == 0)
            return -8276;

        if (XMEMCMP(cipher, verify, AES_BLOCK_SIZE))
            return -8277;

        EVP_CIPHER_CTX_init(&ctx);
        if (EVP_CipherInit(&ctx, EVP_aes_256_ecb(), (unsigned char*)key, NULL, 0) == 0)
            return -8278;

        if (EVP_Cipher(&ctx, plain, cipher, 16) == 0)
            return -8279;

        if (XMEMCMP(plain, msg, AES_BLOCK_SIZE))
            return -8280;

    }  /* end evp_cipher test */
#endif /* HAVE_AES_ECB && WOLFSSL_AES_256 */

#if defined(WOLFSSL_AES_DIRECT) && defined(WOLFSSL_AES_256)
    /* enable HAVE_AES_DECRYPT for AES_encrypt/decrypt */
    {
        /* Test: AES_encrypt/decrypt/set Key */
        AES_KEY enc;
        #ifdef HAVE_AES_DECRYPT
        AES_KEY dec;
        #endif

        const byte msg[] =
        {
            0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
            0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a
        };

        const byte verify[] =
        {
            0xf3,0xee,0xd1,0xbd,0xb5,0xd2,0xa0,0x3c,
            0x06,0x4b,0x5a,0x7e,0x3d,0xb1,0x81,0xf8
        };

        const byte key[] =
        {
            0x60,0x3d,0xeb,0x10,0x15,0xca,0x71,0xbe,
            0x2b,0x73,0xae,0xf0,0x85,0x7d,0x77,0x81,
            0x1f,0x35,0x2c,0x07,0x3b,0x61,0x08,0xd7,
            0x2d,0x98,0x10,0xa3,0x09,0x14,0xdf,0xf4
        };

        byte plain[sizeof(msg)];
        byte cipher[sizeof(msg)];

        AES_set_encrypt_key(key, sizeof(key)*8, &enc);
        AES_set_decrypt_key(key,  sizeof(key)*8, &dec);

        AES_encrypt(msg, cipher, &enc);

        #ifdef HAVE_AES_DECRYPT
        AES_decrypt(cipher, plain, &dec);
        if (XMEMCMP(plain, msg, AES_BLOCK_SIZE))
            return -8281;
        #endif /* HAVE_AES_DECRYPT */

        if (XMEMCMP(cipher, verify, AES_BLOCK_SIZE))
            return -8282;
    }
#endif /* WOLFSSL_AES_DIRECT && WOLFSSL_AES_256 */

/* EVP_Cipher with EVP_aes_xxx_ctr() */
#ifdef WOLFSSL_AES_COUNTER
    {
        byte plainBuff [64];
        byte cipherBuff[64];

#ifdef WOLFSSL_AES_128
        const byte ctrKey[] =
        {
            0x2b,0x7e,0x15,0x16,0x28,0xae,0xd2,0xa6,
            0xab,0xf7,0x15,0x88,0x09,0xcf,0x4f,0x3c
        };

        const byte ctrIv[] =
        {
            0xf0,0xf1,0xf2,0xf3,0xf4,0xf5,0xf6,0xf7,
            0xf8,0xf9,0xfa,0xfb,0xfc,0xfd,0xfe,0xff
        };


        const byte ctrPlain[] =
        {
            0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
            0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a,
            0xae,0x2d,0x8a,0x57,0x1e,0x03,0xac,0x9c,
            0x9e,0xb7,0x6f,0xac,0x45,0xaf,0x8e,0x51,
            0x30,0xc8,0x1c,0x46,0xa3,0x5c,0xe4,0x11,
            0xe5,0xfb,0xc1,0x19,0x1a,0x0a,0x52,0xef,
            0xf6,0x9f,0x24,0x45,0xdf,0x4f,0x9b,0x17,
            0xad,0x2b,0x41,0x7b,0xe6,0x6c,0x37,0x10
        };

        const byte ctrCipher[] =
        {
            0x87,0x4d,0x61,0x91,0xb6,0x20,0xe3,0x26,
            0x1b,0xef,0x68,0x64,0x99,0x0d,0xb6,0xce,
            0x98,0x06,0xf6,0x6b,0x79,0x70,0xfd,0xff,
            0x86,0x17,0x18,0x7b,0xb9,0xff,0xfd,0xff,
            0x5a,0xe4,0xdf,0x3e,0xdb,0xd5,0xd3,0x5e,
            0x5b,0x4f,0x09,0x02,0x0d,0xb0,0x3e,0xab,
            0x1e,0x03,0x1d,0xda,0x2f,0xbe,0x03,0xd1,
            0x79,0x21,0x70,0xa0,0xf3,0x00,0x9c,0xee
        };

        const byte oddCipher[] =
        {
            0xb9,0xd7,0xcb,0x08,0xb0,0xe1,0x7b,0xa0,
            0xc2
        };
#endif

        /* test vector from "Recommendation for Block Cipher Modes of Operation"
         * NIST Special Publication 800-38A */
#ifdef WOLFSSL_AES_192
        const byte ctr192Key[] =
        {
            0x8e,0x73,0xb0,0xf7,0xda,0x0e,0x64,0x52,
            0xc8,0x10,0xf3,0x2b,0x80,0x90,0x79,0xe5,
            0x62,0xf8,0xea,0xd2,0x52,0x2c,0x6b,0x7b
        };

        const byte ctr192Iv[] =
        {
            0xf0,0xf1,0xf2,0xf3,0xf4,0xf5,0xf6,0xf7,
            0xf8,0xf9,0xfa,0xfb,0xfc,0xfd,0xfe,0xff
        };


        const byte ctr192Plain[] =
        {
            0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
            0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a
        };

        const byte ctr192Cipher[] =
        {
            0x1a,0xbc,0x93,0x24,0x17,0x52,0x1c,0xa2,
            0x4f,0x2b,0x04,0x59,0xfe,0x7e,0x6e,0x0b
        };
#endif /* WOLFSSL_AES_192 */

#ifdef WOLFSSL_AES_256
        /* test vector from "Recommendation for Block Cipher Modes of Operation"
         * NIST Special Publication 800-38A */
        const byte ctr256Key[] =
        {
            0x60,0x3d,0xeb,0x10,0x15,0xca,0x71,0xbe,
            0x2b,0x73,0xae,0xf0,0x85,0x7d,0x77,0x81,
            0x1f,0x35,0x2c,0x07,0x3b,0x61,0x08,0xd7,
            0x2d,0x98,0x10,0xa3,0x09,0x14,0xdf,0xf4
        };

        const byte ctr256Iv[] =
        {
            0xf0,0xf1,0xf2,0xf3,0xf4,0xf5,0xf6,0xf7,
            0xf8,0xf9,0xfa,0xfb,0xfc,0xfd,0xfe,0xff
        };


        const byte ctr256Plain[] =
        {
            0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
            0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a
        };

        const byte ctr256Cipher[] =
        {
            0x60,0x1e,0xc3,0x13,0x77,0x57,0x89,0xa5,
            0xb7,0xa7,0xf5,0x04,0xbb,0xf3,0xd2,0x28
        };
#endif /* WOLFSSL_AES_256 */

        EVP_CIPHER_CTX en;
        EVP_CIPHER_CTX de;
#ifdef WOLFSSL_AES_128
        EVP_CIPHER_CTX *p_en;
        EVP_CIPHER_CTX *p_de;

        EVP_CIPHER_CTX_init(&en);
        if (EVP_CipherInit(&en, EVP_aes_128_ctr(),
                (unsigned char*)ctrKey, (unsigned char*)ctrIv, 0) == 0)
            return -8283;
        if (EVP_Cipher(&en, (byte*)cipherBuff, (byte*)ctrPlain,
                    AES_BLOCK_SIZE*4) == 0)
            return -8284;
        EVP_CIPHER_CTX_init(&de);
        if (EVP_CipherInit(&de, EVP_aes_128_ctr(),
                (unsigned char*)ctrKey, (unsigned char*)ctrIv, 0) == 0)
            return -8285;

        if (EVP_Cipher(&de, (byte*)plainBuff, (byte*)cipherBuff,
                    AES_BLOCK_SIZE*4) == 0)
            return -8286;

        if (XMEMCMP(cipherBuff, ctrCipher, AES_BLOCK_SIZE*4))
            return -8287;
        if (XMEMCMP(plainBuff, ctrPlain, AES_BLOCK_SIZE*4))
            return -8288;

        p_en = wolfSSL_EVP_CIPHER_CTX_new();
        if (p_en == NULL)
            return -8289;
        p_de = wolfSSL_EVP_CIPHER_CTX_new();
        if (p_de == NULL)
            return -8290;

        if (EVP_CipherInit(p_en, EVP_aes_128_ctr(),
                (unsigned char*)ctrKey, (unsigned char*)ctrIv, 0) == 0)
            return -8291;
        if (EVP_Cipher(p_en, (byte*)cipherBuff, (byte*)ctrPlain,
                    AES_BLOCK_SIZE*4) == 0)
            return -8292;
        if (EVP_CipherInit(p_de, EVP_aes_128_ctr(),
                (unsigned char*)ctrKey, (unsigned char*)ctrIv, 0) == 0)
            return -8293;

        if (EVP_Cipher(p_de, (byte*)plainBuff, (byte*)cipherBuff,
                    AES_BLOCK_SIZE*4) == 0)
            return -8294;

        wolfSSL_EVP_CIPHER_CTX_free(p_en);
        wolfSSL_EVP_CIPHER_CTX_free(p_de);

        if (XMEMCMP(cipherBuff, ctrCipher, AES_BLOCK_SIZE*4))
            return -8295;
        if (XMEMCMP(plainBuff, ctrPlain, AES_BLOCK_SIZE*4))
            return -8296;

        EVP_CIPHER_CTX_init(&en);
        if (EVP_CipherInit(&en, EVP_aes_128_ctr(),
            (unsigned char*)ctrKey, (unsigned char*)ctrIv, 0) == 0)
            return -8297;
        if (EVP_Cipher(&en, (byte*)cipherBuff, (byte*)ctrPlain, 9) == 0)
            return -8298;

        EVP_CIPHER_CTX_init(&de);
        if (EVP_CipherInit(&de, EVP_aes_128_ctr(),
            (unsigned char*)ctrKey, (unsigned char*)ctrIv, 0) == 0)
            return -8299;

        if (EVP_Cipher(&de, (byte*)plainBuff, (byte*)cipherBuff, 9) == 0)
            return -8300;

        if (XMEMCMP(plainBuff, ctrPlain, 9))
            return -8301;
        if (XMEMCMP(cipherBuff, ctrCipher, 9))
            return -8302;

        if (EVP_Cipher(&en, (byte*)cipherBuff, (byte*)ctrPlain, 9) == 0)
            return -8303;
        if (EVP_Cipher(&de, (byte*)plainBuff, (byte*)cipherBuff, 9) == 0)
            return -8304;

        if (XMEMCMP(plainBuff, ctrPlain, 9))
            return -8305;
        if (XMEMCMP(cipherBuff, oddCipher, 9))
            return -8306;
#endif /* WOLFSSL_AES_128 */

#ifdef WOLFSSL_AES_192
        EVP_CIPHER_CTX_init(&en);
        if (EVP_CipherInit(&en, EVP_aes_192_ctr(),
                (unsigned char*)ctr192Key, (unsigned char*)ctr192Iv, 0) == 0)
            return -8307;
        if (EVP_Cipher(&en, (byte*)cipherBuff, (byte*)ctr192Plain,
                    AES_BLOCK_SIZE) == 0)
            return -8308;
        EVP_CIPHER_CTX_init(&de);
        if (EVP_CipherInit(&de, EVP_aes_192_ctr(),
            (unsigned char*)ctr192Key, (unsigned char*)ctr192Iv, 0) == 0)
            return -8309;

        XMEMSET(plainBuff, 0, sizeof(plainBuff));
        if (EVP_Cipher(&de, (byte*)plainBuff, (byte*)cipherBuff,
                    AES_BLOCK_SIZE) == 0)
            return -8310;

        if (XMEMCMP(plainBuff, ctr192Plain, sizeof(ctr192Plain)))
            return -8311;
        if (XMEMCMP(ctr192Cipher, cipherBuff, sizeof(ctr192Cipher)))
            return -8312;
#endif /* WOLFSSL_AES_192 */

#ifdef WOLFSSL_AES_256
        EVP_CIPHER_CTX_init(&en);
        if (EVP_CipherInit(&en, EVP_aes_256_ctr(),
            (unsigned char*)ctr256Key, (unsigned char*)ctr256Iv, 0) == 0)
            return -8313;
        if (EVP_Cipher(&en, (byte*)cipherBuff, (byte*)ctr256Plain,
                    AES_BLOCK_SIZE) == 0)
            return -8314;
        EVP_CIPHER_CTX_init(&de);
        if (EVP_CipherInit(&de, EVP_aes_256_ctr(),
            (unsigned char*)ctr256Key, (unsigned char*)ctr256Iv, 0) == 0)
            return -8315;

        XMEMSET(plainBuff, 0, sizeof(plainBuff));
        if (EVP_Cipher(&de, (byte*)plainBuff, (byte*)cipherBuff,
                    AES_BLOCK_SIZE) == 0)
            return -8316;

        if (XMEMCMP(plainBuff, ctr256Plain, sizeof(ctr256Plain)))
            return -8317;
        if (XMEMCMP(ctr256Cipher, cipherBuff, sizeof(ctr256Cipher)))
            return -8318;
#endif /* WOLFSSL_AES_256 */
    }
#endif /* HAVE_AES_COUNTER */

#if defined(WOLFSSL_AES_CFB) && defined(WOLFSSL_AES_128)
    {
        AES_KEY enc;
        AES_KEY dec;

        const byte setIv[] = {
            0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
            0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f
        };

        const byte key[] =
        {
            0x2b,0x7e,0x15,0x16,0x28,0xae,0xd2,0xa6,
            0xab,0xf7,0x15,0x88,0x09,0xcf,0x4f,0x3c
        };

        const byte cipher1[] =
        {
            0x3b,0x3f,0xd9,0x2e,0xb7,0x2d,0xad,0x20,
            0x33,0x34,0x49,0xf8,0xe8,0x3c,0xfb,0x4a,
            0xc8,0xa6,0x45,0x37,0xa0,0xb3,0xa9,0x3f,
            0xcd,0xe3,0xcd,0xad,0x9f,0x1c,0xe5,0x8b
        };

        const byte msg[] =
        {
            0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
            0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a,
            0xae,0x2d,0x8a,0x57,0x1e,0x03,0xac,0x9c,
            0x9e,0xb7,0x6f,0xac,0x45,0xaf,0x8e,0x51
        };

        byte cipher[AES_BLOCK_SIZE * 2];
        byte iv[AES_BLOCK_SIZE]; /* iv buffer is updeated by API */
        int  num = 0;

        XMEMCPY(iv, setIv, sizeof(setIv));
        wolfSSL_AES_set_encrypt_key(key, sizeof(key) * 8, &enc);
        wolfSSL_AES_set_encrypt_key(key, sizeof(key) * 8, &dec);

        wolfSSL_AES_cfb128_encrypt(msg, cipher, AES_BLOCK_SIZE - 1, &enc, iv,
                &num, AES_ENCRYPT);

        if (XMEMCMP(cipher, cipher1, AES_BLOCK_SIZE - 1))
            return -8319;

        if (num != 15) /* should have used 15 of the 16 bytes */
            return -8320;

        wolfSSL_AES_cfb128_encrypt(msg + AES_BLOCK_SIZE - 1,
                cipher + AES_BLOCK_SIZE - 1, AES_BLOCK_SIZE + 1, &enc, iv,
                &num, AES_ENCRYPT);

        if (XMEMCMP(cipher, cipher1, AES_BLOCK_SIZE * 2))
            return -8321;

        if (num != 0)
            return -8322;
    }
#endif /* WOLFSSL_AES_CFB && WOLFSSL_AES_128 */
    return 0;
}


#endif /* !defined(NO_AES) && !defined(WOLFCRYPT_ONLY) */

int openssl_test(void)
{
    EVP_MD_CTX md_ctx;
    testVector a, b, c, d, e, f;
    byte       hash[WC_SHA256_DIGEST_SIZE*2];  /* max size */

    a.inLen = 0;
    b.inLen = c.inLen = d.inLen = e.inLen = f.inLen = a.inLen;

    (void)a;
    (void)b;
    (void)c;
    (void)d;
    (void)e;
    (void)f;

    /* test malloc / free , 10 is an arbitrary amount of memory chosen */
    {
        byte* p;
        p = (byte*)CRYPTO_malloc(10);
        if (p == NULL) {
            return -8400;
        }
        XMEMSET(p, 0, 10);
        CRYPTO_free(p);
    }

#ifndef NO_MD5

    a.input  = "1234567890123456789012345678901234567890123456789012345678"
               "9012345678901234567890";
    a.output = "\x57\xed\xf4\xa2\x2b\xe3\xc9\x55\xac\x49\xda\x2e\x21\x07\xb6"
               "\x7a";
    a.inLen  = XSTRLEN(a.input);
    a.outLen = WC_MD5_DIGEST_SIZE;

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_md5());

    EVP_DigestUpdate(&md_ctx, a.input, (unsigned long)a.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (XMEMCMP(hash, a.output, WC_MD5_DIGEST_SIZE) != 0)
        return -8401;

#endif /* NO_MD5 */

#ifndef NO_SHA

    b.input  = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
               "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
               "aaaaaaaaaa";
    b.output = "\xAD\x5B\x3F\xDB\xCB\x52\x67\x78\xC2\x83\x9D\x2F\x15\x1E\xA7"
               "\x53\x99\x5E\x26\xA0";
    b.inLen  = XSTRLEN(b.input);
    b.outLen = WC_SHA_DIGEST_SIZE;

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_sha1());

    EVP_DigestUpdate(&md_ctx, b.input, (unsigned long)b.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (XMEMCMP(hash, b.output, WC_SHA_DIGEST_SIZE) != 0)
        return -8402;

#endif /* NO_SHA */

#ifdef WOLFSSL_SHA224

    e.input  = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhi"
               "jklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    e.output = "\xc9\x7c\xa9\xa5\x59\x85\x0c\xe9\x7a\x04\xa9\x6d\xef\x6d\x99"
               "\xa9\xe0\xe0\xe2\xab\x14\xe6\xb8\xdf\x26\x5f\xc0\xb3";
    e.inLen  = XSTRLEN(e.input);
    e.outLen = WC_SHA224_DIGEST_SIZE;

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_sha224());

    EVP_DigestUpdate(&md_ctx, e.input, (unsigned long)e.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (XMEMCMP(hash, e.output, WC_SHA224_DIGEST_SIZE) != 0)
        return -8403;

#endif /* WOLFSSL_SHA224 */


    d.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    d.output = "\x24\x8D\x6A\x61\xD2\x06\x38\xB8\xE5\xC0\x26\x93\x0C\x3E\x60"
               "\x39\xA3\x3C\xE4\x59\x64\xFF\x21\x67\xF6\xEC\xED\xD4\x19\xDB"
               "\x06\xC1";
    d.inLen  = XSTRLEN(d.input);
    d.outLen = WC_SHA256_DIGEST_SIZE;

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_sha256());

    EVP_DigestUpdate(&md_ctx, d.input, (unsigned long)d.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (XMEMCMP(hash, d.output, WC_SHA256_DIGEST_SIZE) != 0)
        return -8404;

#ifdef WOLFSSL_SHA384

    e.input  = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhi"
               "jklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    e.output = "\x09\x33\x0c\x33\xf7\x11\x47\xe8\x3d\x19\x2f\xc7\x82\xcd\x1b"
               "\x47\x53\x11\x1b\x17\x3b\x3b\x05\xd2\x2f\xa0\x80\x86\xe3\xb0"
               "\xf7\x12\xfc\xc7\xc7\x1a\x55\x7e\x2d\xb9\x66\xc3\xe9\xfa\x91"
               "\x74\x60\x39";
    e.inLen  = XSTRLEN(e.input);
    e.outLen = WC_SHA384_DIGEST_SIZE;

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_sha384());

    EVP_DigestUpdate(&md_ctx, e.input, (unsigned long)e.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (XMEMCMP(hash, e.output, WC_SHA384_DIGEST_SIZE) != 0)
        return -8405;

#endif /* WOLFSSL_SHA384 */


#ifdef WOLFSSL_SHA512

    f.input  = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhi"
               "jklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    f.output = "\x8e\x95\x9b\x75\xda\xe3\x13\xda\x8c\xf4\xf7\x28\x14\xfc\x14"
               "\x3f\x8f\x77\x79\xc6\xeb\x9f\x7f\xa1\x72\x99\xae\xad\xb6\x88"
               "\x90\x18\x50\x1d\x28\x9e\x49\x00\xf7\xe4\x33\x1b\x99\xde\xc4"
               "\xb5\x43\x3a\xc7\xd3\x29\xee\xb6\xdd\x26\x54\x5e\x96\xe5\x5b"
               "\x87\x4b\xe9\x09";
    f.inLen  = XSTRLEN(f.input);
    f.outLen = WC_SHA512_DIGEST_SIZE;

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_sha512());

    EVP_DigestUpdate(&md_ctx, f.input, (unsigned long)f.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (XMEMCMP(hash, f.output, WC_SHA512_DIGEST_SIZE) != 0)
        return -8406;

#endif /* WOLFSSL_SHA512 */
#ifdef WOLFSSL_SHA3
#ifndef WOLFSSL_NOSHA3_224

    e.input  = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhi"
               "jklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    e.output = "\x54\x3e\x68\x68\xe1\x66\x6c\x1a\x64\x36\x30\xdf\x77\x36\x7a\xe5\xa6\x2a\x85\x07\x0a\x51\xc1\x4c\xbf\x66\x5c\xbc";
    e.inLen  = XSTRLEN(e.input);
    e.outLen = WC_SHA3_224_DIGEST_SIZE;

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_sha3_224());

    EVP_DigestUpdate(&md_ctx, e.input, (unsigned long)e.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (XMEMCMP(hash, e.output, WC_SHA3_224_DIGEST_SIZE) != 0)
        return -8407;

#endif /* WOLFSSL_NOSHA3_224 */


#ifndef WOLFSSL_NOSHA3_256
    d.input  = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhi"
               "jklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    d.output = "\x91\x6f\x60\x61\xfe\x87\x97\x41\xca\x64\x69\xb4\x39\x71\xdf"
               "\xdb\x28\xb1\xa3\x2d\xc3\x6c\xb3\x25\x4e\x81\x2b\xe2\x7a\xad"
               "\x1d\x18";
    d.inLen  = XSTRLEN(d.input);
    d.outLen = WC_SHA3_256_DIGEST_SIZE;

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_sha3_256());

    EVP_DigestUpdate(&md_ctx, d.input, (unsigned long)d.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (XMEMCMP(hash, d.output, WC_SHA3_256_DIGEST_SIZE) != 0)
        return -8408;
#endif /* WOLFSSL_NOSHA3_256 */


    e.input  = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhi"
               "jklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    e.output = "\x79\x40\x7d\x3b\x59\x16\xb5\x9c\x3e\x30\xb0\x98\x22\x97\x47\x91\xc3\x13\xfb\x9e\xcc\x84\x9e\x40\x6f\x23\x59\x2d\x04\xf6\x25\xdc\x8c\x70\x9b\x98\xb4\x3b\x38\x52\xb3\x37\x21\x61\x79\xaa\x7f\xc7";
    e.inLen  = XSTRLEN(e.input);
    e.outLen = WC_SHA3_384_DIGEST_SIZE;

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_sha3_384());

    EVP_DigestUpdate(&md_ctx, e.input, (unsigned long)e.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (XMEMCMP(hash, e.output, WC_SHA3_384_DIGEST_SIZE) != 0)
        return -8409;



#ifndef WOLFSSL_NOSHA3_512

    f.input  = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhi"
               "jklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    f.output = "\xaf\xeb\xb2\xef\x54\x2e\x65\x79\xc5\x0c\xad\x06\xd2\xe5\x78\xf9\xf8\xdd\x68\x81\xd7\xdc\x82\x4d\x26\x36\x0f\xee\xbf\x18\xa4\xfa\x73\xe3\x26\x11\x22\x94\x8e\xfc\xfd\x49\x2e\x74\xe8\x2e\x21\x89\xed\x0f\xb4\x40\xd1\x87\xf3\x82\x27\x0c\xb4\x55\xf2\x1d\xd1\x85";
    f.inLen  = XSTRLEN(f.input);
    f.outLen = WC_SHA3_512_DIGEST_SIZE;

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_sha3_512());

    EVP_DigestUpdate(&md_ctx, f.input, (unsigned long)f.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (XMEMCMP(hash, f.output, WC_SHA3_512_DIGEST_SIZE) != 0)
        return -8410;

#endif /* WOLFSSL_NOSHA3_512 */
#endif /* WOLFSSL_SHA3 */

#ifndef NO_MD5
    if (RAND_bytes(hash, sizeof(hash)) != 1)
        return -8411;

    c.input  = "what do ya want for nothing?";
    c.output = "\x55\x78\xe8\x48\x4b\xcc\x93\x80\x93\xec\x53\xaf\x22\xd6\x14"
               "\x76";
    c.inLen  = XSTRLEN(c.input);
    c.outLen = WC_MD5_DIGEST_SIZE;

    HMAC(EVP_md5(),
                 "JefeJefeJefeJefe", 16, (byte*)c.input, (int)c.inLen, hash, 0);

    if (XMEMCMP(hash, c.output, WC_MD5_DIGEST_SIZE) != 0)
        return -8412;

#endif /* NO_MD5 */

#ifndef NO_DES3
    { /* des test */
    const byte vector[] = { /* "now is the time for all " w/o trailing 0 */
        0x6e,0x6f,0x77,0x20,0x69,0x73,0x20,0x74,
        0x68,0x65,0x20,0x74,0x69,0x6d,0x65,0x20,
        0x66,0x6f,0x72,0x20,0x61,0x6c,0x6c,0x20
    };

    byte plain[24];
    byte cipher[24];

    const_DES_cblock key =
    {
        0x01,0x23,0x45,0x67,0x89,0xab,0xcd,0xef
    };

    DES_cblock iv =
    {
        0x12,0x34,0x56,0x78,0x90,0xab,0xcd,0xef
    };

    DES_key_schedule sched;

    const byte verify[] =
    {
        0x8b,0x7c,0x52,0xb0,0x01,0x2b,0x6c,0xb8,
        0x4f,0x0f,0xeb,0xf3,0xfb,0x5f,0x86,0x73,
        0x15,0x85,0xb3,0x22,0x4b,0x86,0x2b,0x4b
    };

    DES_key_sched(&key, &sched);

    DES_cbc_encrypt(vector, cipher, sizeof(vector), &sched, &iv, DES_ENCRYPT);
    DES_cbc_encrypt(cipher, plain, sizeof(vector), &sched, &iv, DES_DECRYPT);

    if (XMEMCMP(plain, vector, sizeof(vector)) != 0)
        return -8413;

    if (XMEMCMP(cipher, verify, sizeof(verify)) != 0)
        return -8414;

        /* test changing iv */
    DES_ncbc_encrypt(vector, cipher, 8, &sched, &iv, DES_ENCRYPT);
    DES_ncbc_encrypt(vector + 8, cipher + 8, 16, &sched, &iv, DES_ENCRYPT);

    if (XMEMCMP(cipher, verify, sizeof(verify)) != 0)
        return -8415;

    }  /* end des test */

#endif /* NO_DES3 */

#if !defined(NO_AES) && !defined(WOLFCRYPT_ONLY)
        if (openssl_aes_test() != 0) {
            return -8416;
        }

#if defined(WOLFSSL_AES_128) && defined(HAVE_AES_CBC)
    {  /* evp_cipher test: EVP_aes_128_cbc */
        EVP_CIPHER_CTX ctx;
        int idx, cipherSz, plainSz;

        const byte msg[] = { /* "Now is the time for all " w/o trailing 0 */
            0x6e,0x6f,0x77,0x20,0x69,0x73,0x20,0x74,
            0x68,0x65,0x20,0x74,0x69,0x6d,0x65,0x20,
            0x66,0x6f,0x72,0x20,0x61,0x6c,0x6c,0x20
        };

        const byte verify[] =
        {
            0x95,0x94,0x92,0x57,0x5f,0x42,0x81,0x53,
            0x2c,0xcc,0x9d,0x46,0x77,0xa2,0x33,0xcb,
            0x3b,0x5d,0x41,0x97,0x94,0x25,0xa4,0xb4,
            0xae,0x7b,0x34,0xd0,0x3f,0x0c,0xbc,0x06
        };

        const byte verify2[] =
        {
            0x95,0x94,0x92,0x57,0x5f,0x42,0x81,0x53,
            0x2c,0xcc,0x9d,0x46,0x77,0xa2,0x33,0xcb,
            0x7d,0x37,0x7b,0x0b,0x44,0xaa,0xb5,0xf0,
            0x5f,0x34,0xb4,0xde,0xb5,0xbd,0x2a,0xbb
        };

        byte key[] = "0123456789abcdef   ";  /* align */
        byte iv[]  = "1234567890abcdef   ";  /* align */

        byte cipher[AES_BLOCK_SIZE * 4];
        byte plain [AES_BLOCK_SIZE * 4];

        EVP_CIPHER_CTX_init(&ctx);
        if (EVP_CipherInit(&ctx, EVP_aes_128_cbc(), key, iv, 1) == 0)
            return -8417;

        if (EVP_CipherUpdate(&ctx, cipher, &idx, (byte*)msg, sizeof(msg)) == 0)
            return -8418;

        cipherSz = idx;
        if (EVP_CipherFinal(&ctx, cipher + cipherSz, &idx) == 0)
            return -8419;
        cipherSz += idx;

        if ((cipherSz != (int)sizeof(verify)) &&
                                             XMEMCMP(cipher, verify, cipherSz))
            return -8420;

        EVP_CIPHER_CTX_init(&ctx);
        if (EVP_CipherInit(&ctx, EVP_aes_128_cbc(), key, iv, 0) == 0)
            return -8421;

        /* check partial decrypt (not enough padding for full block) */
        if (EVP_CipherUpdate(&ctx, plain, &idx, cipher, 1) == 0)
            return -8422;

        plainSz = idx;
        if (EVP_CipherFinal(&ctx, plain + plainSz, &idx) != 0)
            return -8423;

        EVP_CIPHER_CTX_init(&ctx);
        if (EVP_CipherInit(&ctx, EVP_aes_128_cbc(), key, iv, 0) == 0)
            return -8424;

        if (EVP_CipherUpdate(&ctx, plain, &idx, cipher, cipherSz) == 0)
            return -8425;

        plainSz = idx;
        if (EVP_CipherFinal(&ctx, plain + plainSz, &idx) == 0)
            return -8426;
        plainSz += idx;

        if ((plainSz != sizeof(msg)) || XMEMCMP(plain, msg, sizeof(msg)))
            return -8427;

        EVP_CIPHER_CTX_init(&ctx);
        if (EVP_CipherInit(&ctx, EVP_aes_128_cbc(), key, iv, 1) == 0)
            return -8428;

        if (EVP_CipherUpdate(&ctx, cipher, &idx, msg, AES_BLOCK_SIZE) == 0)
            return -8429;

        cipherSz = idx;
        if (EVP_CipherFinal(&ctx, cipher + cipherSz, &idx) == 0)
            return -8430;
        cipherSz += idx;

        if ((cipherSz != (int)sizeof(verify2)) ||
                                            XMEMCMP(cipher, verify2, cipherSz))
            return -8431;

    }  /* end evp_cipher test: EVP_aes_128_cbc*/
#endif /* WOLFSSL_AES_128 && HAVE_AES_CBC */

#if defined(HAVE_AES_ECB) && defined(WOLFSSL_AES_256)
    {  /* evp_cipher test: EVP_aes_256_ecb*/
        EVP_CIPHER_CTX ctx;
        const byte msg[] =
        {
          0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
          0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a
        };

        const byte verify[] =
        {
            0xf3,0xee,0xd1,0xbd,0xb5,0xd2,0xa0,0x3c,
            0x06,0x4b,0x5a,0x7e,0x3d,0xb1,0x81,0xf8
        };

        const byte key[] =
        {
          0x60,0x3d,0xeb,0x10,0x15,0xca,0x71,0xbe,
          0x2b,0x73,0xae,0xf0,0x85,0x7d,0x77,0x81,
          0x1f,0x35,0x2c,0x07,0x3b,0x61,0x08,0xd7,
          0x2d,0x98,0x10,0xa3,0x09,0x14,0xdf,0xf4
        };


        byte cipher[AES_BLOCK_SIZE * 4];
        byte plain [AES_BLOCK_SIZE * 4];

        EVP_CIPHER_CTX_init(&ctx);
        if (EVP_CipherInit(&ctx, EVP_aes_256_ecb(), (unsigned char*)key,
                                                                NULL, 1) == 0)
            return -8432;

        if (EVP_Cipher(&ctx, cipher, (byte*)msg, 16) == 0)
            return -8433;

        if (XMEMCMP(cipher, verify, AES_BLOCK_SIZE))
            return -8434;

        EVP_CIPHER_CTX_init(&ctx);
        if (EVP_CipherInit(&ctx, EVP_aes_256_ecb(), (unsigned char*)key,
                                                                NULL, 0) == 0)
            return -8435;

        if (EVP_Cipher(&ctx, plain, cipher, 16) == 0)
            return -8436;

        if (XMEMCMP(plain, msg, AES_BLOCK_SIZE))
            return -8437;

    }  /* end evp_cipher test */
#endif /* HAVE_AES_ECB && WOLFSSL_AES_128 */

#define OPENSSL_TEST_ERROR (-10000)


#if defined(WOLFSSL_AES_DIRECT) && defined(WOLFSSL_AES_256)
  /* enable HAVE_AES_DECRYPT for AES_encrypt/decrypt */
{

  /* Test: AES_encrypt/decrypt/set Key */
  AES_KEY enc;
#ifdef HAVE_AES_DECRYPT
  AES_KEY dec;
#endif

  const byte msg[] =
  {
      0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
      0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a
  };

  const byte verify[] =
  {
      0xf3,0xee,0xd1,0xbd,0xb5,0xd2,0xa0,0x3c,
      0x06,0x4b,0x5a,0x7e,0x3d,0xb1,0x81,0xf8
  };

  const byte key[] =
  {
      0x60,0x3d,0xeb,0x10,0x15,0xca,0x71,0xbe,
      0x2b,0x73,0xae,0xf0,0x85,0x7d,0x77,0x81,
      0x1f,0x35,0x2c,0x07,0x3b,0x61,0x08,0xd7,
      0x2d,0x98,0x10,0xa3,0x09,0x14,0xdf,0xf4
  };

  byte plain[sizeof(msg)];
  byte cipher[sizeof(msg)];

  printf("openSSL extra test\n") ;


  AES_set_encrypt_key(key, sizeof(key)*8, &enc);
  AES_set_decrypt_key(key,  sizeof(key)*8, &dec);

  AES_encrypt(msg, cipher, &enc);

#ifdef HAVE_AES_DECRYPT
  AES_decrypt(cipher, plain, &dec);
  if (XMEMCMP(plain, msg, AES_BLOCK_SIZE))
      return OPENSSL_TEST_ERROR-60;
#endif /* HAVE_AES_DECRYPT */

  if (XMEMCMP(cipher, verify, AES_BLOCK_SIZE))
      return OPENSSL_TEST_ERROR-61;
}

#endif /* WOLFSSL_AES_DIRECT && WOLFSSL_AES_256 */

/* EVP_Cipher with EVP_aes_xxx_ctr() */
#ifdef WOLFSSL_AES_COUNTER
{
    byte plainBuff [64];
    byte cipherBuff[64];

#ifdef WOLFSSL_AES_128
    const byte ctrKey[] =
    {
        0x2b,0x7e,0x15,0x16,0x28,0xae,0xd2,0xa6,
        0xab,0xf7,0x15,0x88,0x09,0xcf,0x4f,0x3c
    };

    const byte ctrIv[] =
    {
        0xf0,0xf1,0xf2,0xf3,0xf4,0xf5,0xf6,0xf7,
        0xf8,0xf9,0xfa,0xfb,0xfc,0xfd,0xfe,0xff
    };

    const byte ctrPlain[] =
    {
        0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
        0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a,
        0xae,0x2d,0x8a,0x57,0x1e,0x03,0xac,0x9c,
        0x9e,0xb7,0x6f,0xac,0x45,0xaf,0x8e,0x51,
        0x30,0xc8,0x1c,0x46,0xa3,0x5c,0xe4,0x11,
        0xe5,0xfb,0xc1,0x19,0x1a,0x0a,0x52,0xef,
        0xf6,0x9f,0x24,0x45,0xdf,0x4f,0x9b,0x17,
        0xad,0x2b,0x41,0x7b,0xe6,0x6c,0x37,0x10
    };

    const byte ctrCipher[] =
    {
        0x87,0x4d,0x61,0x91,0xb6,0x20,0xe3,0x26,
        0x1b,0xef,0x68,0x64,0x99,0x0d,0xb6,0xce,
        0x98,0x06,0xf6,0x6b,0x79,0x70,0xfd,0xff,
        0x86,0x17,0x18,0x7b,0xb9,0xff,0xfd,0xff,
        0x5a,0xe4,0xdf,0x3e,0xdb,0xd5,0xd3,0x5e,
        0x5b,0x4f,0x09,0x02,0x0d,0xb0,0x3e,0xab,
        0x1e,0x03,0x1d,0xda,0x2f,0xbe,0x03,0xd1,
        0x79,0x21,0x70,0xa0,0xf3,0x00,0x9c,0xee
    };

    const byte oddCipher[] =
    {
        0xb9,0xd7,0xcb,0x08,0xb0,0xe1,0x7b,0xa0,
        0xc2
    };
#endif /* WOLFSSL_AES_128 */

#ifdef WOLFSSL_AES_192
    /* test vector from "Recommendation for Block Cipher Modes of Operation"
     * NIST Special Publication 800-38A */
    const byte ctr192Key[] =
    {
        0x8e,0x73,0xb0,0xf7,0xda,0x0e,0x64,0x52,
        0xc8,0x10,0xf3,0x2b,0x80,0x90,0x79,0xe5,
        0x62,0xf8,0xea,0xd2,0x52,0x2c,0x6b,0x7b
    };

    const byte ctr192Iv[] =
    {
        0xf0,0xf1,0xf2,0xf3,0xf4,0xf5,0xf6,0xf7,
        0xf8,0xf9,0xfa,0xfb,0xfc,0xfd,0xfe,0xff
    };


    const byte ctr192Plain[] =
    {
        0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
        0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a
    };

    const byte ctr192Cipher[] =
    {
        0x1a,0xbc,0x93,0x24,0x17,0x52,0x1c,0xa2,
        0x4f,0x2b,0x04,0x59,0xfe,0x7e,0x6e,0x0b
    };
#endif /* WOLFSSL_AES_192 */

#ifdef WOLFSSL_AES_256
    /* test vector from "Recommendation for Block Cipher Modes of Operation"
     * NIST Special Publication 800-38A */
    const byte ctr256Key[] =
    {
        0x60,0x3d,0xeb,0x10,0x15,0xca,0x71,0xbe,
        0x2b,0x73,0xae,0xf0,0x85,0x7d,0x77,0x81,
        0x1f,0x35,0x2c,0x07,0x3b,0x61,0x08,0xd7,
        0x2d,0x98,0x10,0xa3,0x09,0x14,0xdf,0xf4
    };

    const byte ctr256Iv[] =
    {
        0xf0,0xf1,0xf2,0xf3,0xf4,0xf5,0xf6,0xf7,
        0xf8,0xf9,0xfa,0xfb,0xfc,0xfd,0xfe,0xff
    };


    const byte ctr256Plain[] =
    {
        0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
        0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a
    };

    const byte ctr256Cipher[] =
    {
        0x60,0x1e,0xc3,0x13,0x77,0x57,0x89,0xa5,
        0xb7,0xa7,0xf5,0x04,0xbb,0xf3,0xd2,0x28
    };
#endif /* WOLFSSL_AES_256 */

    EVP_CIPHER_CTX en;
    EVP_CIPHER_CTX de;
#ifdef WOLFSSL_AES_128
    EVP_CIPHER_CTX *p_en;
    EVP_CIPHER_CTX *p_de;

    EVP_CIPHER_CTX_init(&en);
    if (EVP_CipherInit(&en, EVP_aes_128_ctr(),
            (unsigned char*)ctrKey, (unsigned char*)ctrIv, 0) == 0)
        return -8438;
    if (EVP_Cipher(&en, (byte*)cipherBuff, (byte*)ctrPlain,
                                                        AES_BLOCK_SIZE*4) == 0)
        return -8439;
    EVP_CIPHER_CTX_init(&de);
    if (EVP_CipherInit(&de, EVP_aes_128_ctr(),
            (unsigned char*)ctrKey, (unsigned char*)ctrIv, 0) == 0)
        return -8440;

    if (EVP_Cipher(&de, (byte*)plainBuff, (byte*)cipherBuff,
                                                        AES_BLOCK_SIZE*4) == 0)
        return -8441;

    if (XMEMCMP(cipherBuff, ctrCipher, AES_BLOCK_SIZE*4))
        return -8442;
    if (XMEMCMP(plainBuff, ctrPlain, AES_BLOCK_SIZE*4))
        return -8443;

    p_en = wolfSSL_EVP_CIPHER_CTX_new();
    if(p_en == NULL)return -8444;
    p_de = wolfSSL_EVP_CIPHER_CTX_new();
    if(p_de == NULL)return -8445;

    if (EVP_CipherInit(p_en, EVP_aes_128_ctr(),
            (unsigned char*)ctrKey, (unsigned char*)ctrIv, 0) == 0)
        return -8446;
    if (EVP_Cipher(p_en, (byte*)cipherBuff, (byte*)ctrPlain,
                                                        AES_BLOCK_SIZE*4) == 0)
        return -8447;
    if (EVP_CipherInit(p_de, EVP_aes_128_ctr(),
            (unsigned char*)ctrKey, (unsigned char*)ctrIv, 0) == 0)
        return -8448;

    if (EVP_Cipher(p_de, (byte*)plainBuff, (byte*)cipherBuff,
                                                        AES_BLOCK_SIZE*4) == 0)
        return -8449;

    wolfSSL_EVP_CIPHER_CTX_free(p_en);
    wolfSSL_EVP_CIPHER_CTX_free(p_de);

    if (XMEMCMP(cipherBuff, ctrCipher, AES_BLOCK_SIZE*4))
        return -8450;
    if (XMEMCMP(plainBuff, ctrPlain, AES_BLOCK_SIZE*4))
        return -8451;

    EVP_CIPHER_CTX_init(&en);
    if (EVP_CipherInit(&en, EVP_aes_128_ctr(),
        (unsigned char*)ctrKey, (unsigned char*)ctrIv, 0) == 0)
        return -8452;
    if (EVP_Cipher(&en, (byte*)cipherBuff, (byte*)ctrPlain, 9) == 0)
        return -8453;

    EVP_CIPHER_CTX_init(&de);
    if (EVP_CipherInit(&de, EVP_aes_128_ctr(),
        (unsigned char*)ctrKey, (unsigned char*)ctrIv, 0) == 0)
        return -8454;

    if (EVP_Cipher(&de, (byte*)plainBuff, (byte*)cipherBuff, 9) == 0)
        return -8455;

    if (XMEMCMP(plainBuff, ctrPlain, 9))
        return -8456;
    if (XMEMCMP(cipherBuff, ctrCipher, 9))
        return -8457;

    if (EVP_Cipher(&en, (byte*)cipherBuff, (byte*)ctrPlain, 9) == 0)
        return -8458;
    if (EVP_Cipher(&de, (byte*)plainBuff, (byte*)cipherBuff, 9) == 0)
        return -8459;

    if (XMEMCMP(plainBuff, ctrPlain, 9))
        return -8460;
    if (XMEMCMP(cipherBuff, oddCipher, 9))
        return -8461;
#endif /* WOLFSSL_AES_128 */

#ifdef WOLFSSL_AES_192
    EVP_CIPHER_CTX_init(&en);
    if (EVP_CipherInit(&en, EVP_aes_192_ctr(),
            (unsigned char*)ctr192Key, (unsigned char*)ctr192Iv, 0) == 0)
        return -8462;
    if (EVP_Cipher(&en, (byte*)cipherBuff, (byte*)ctr192Plain,
                                                        AES_BLOCK_SIZE) == 0)
        return -8463;
    EVP_CIPHER_CTX_init(&de);
    if (EVP_CipherInit(&de, EVP_aes_192_ctr(),
        (unsigned char*)ctr192Key, (unsigned char*)ctr192Iv, 0) == 0)
        return -8464;

    XMEMSET(plainBuff, 0, sizeof(plainBuff));
    if (EVP_Cipher(&de, (byte*)plainBuff, (byte*)cipherBuff,
                                                        AES_BLOCK_SIZE) == 0)
        return -8465;

    if (XMEMCMP(plainBuff, ctr192Plain, sizeof(ctr192Plain)))
        return -8466;
    if (XMEMCMP(ctr192Cipher, cipherBuff, sizeof(ctr192Cipher)))
        return -8467;
#endif /* WOLFSSL_AES_192 */

#ifdef WOLFSSL_AES_256
    EVP_CIPHER_CTX_init(&en);
    if (EVP_CipherInit(&en, EVP_aes_256_ctr(),
        (unsigned char*)ctr256Key, (unsigned char*)ctr256Iv, 0) == 0)
        return -8468;
    if (EVP_Cipher(&en, (byte*)cipherBuff, (byte*)ctr256Plain,
                                                        AES_BLOCK_SIZE) == 0)
        return -8469;
    EVP_CIPHER_CTX_init(&de);
    if (EVP_CipherInit(&de, EVP_aes_256_ctr(),
        (unsigned char*)ctr256Key, (unsigned char*)ctr256Iv, 0) == 0)
        return -8470;

    XMEMSET(plainBuff, 0, sizeof(plainBuff));
    if (EVP_Cipher(&de, (byte*)plainBuff, (byte*)cipherBuff,
                                                        AES_BLOCK_SIZE) == 0)
        return -8471;

    if (XMEMCMP(plainBuff, ctr256Plain, sizeof(ctr256Plain)))
        return -8472;
    if (XMEMCMP(ctr256Cipher, cipherBuff, sizeof(ctr256Cipher)))
        return -8473;
#endif /* WOLFSSL_AES_256 */
}
#endif /* HAVE_AES_COUNTER */

#if defined(HAVE_AES_CBC) && defined(WOLFSSL_AES_128)
{
      /* EVP_CipherUpdate test */


        const byte cbcPlain[] =
        {
            0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
            0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a,
            0xae,0x2d,0x8a,0x57,0x1e,0x03,0xac,0x9c,
            0x9e,0xb7,0x6f,0xac,0x45,0xaf,0x8e,0x51,
            0x30,0xc8,0x1c,0x46,0xa3,0x5c,0xe4,0x11,
            0xe5,0xfb,0xc1,0x19,0x1a,0x0a,0x52,0xef,
            0xf6,0x9f,0x24,0x45,0xdf,0x4f,0x9b,0x17,
            0xad,0x2b,0x41,0x7b,0xe6,0x6c,0x37,0x10
        };

        byte key[] = "0123456789abcdef   ";  /* align */
        byte iv[]  = "1234567890abcdef   ";  /* align */

        byte cipher[AES_BLOCK_SIZE * 4];
        byte plain [AES_BLOCK_SIZE * 4];
        EVP_CIPHER_CTX en;
        EVP_CIPHER_CTX de;
        int outlen ;
        int total = 0;

        EVP_CIPHER_CTX_init(&en);
        if (EVP_CipherInit(&en, EVP_aes_128_cbc(),
            (unsigned char*)key, (unsigned char*)iv, 1) == 0)
            return -8474;
        /* openSSL compatibility, if(inlen == 0)return 1; */
        if (EVP_CipherUpdate(&en, (byte*)cipher, &outlen,
                                                    (byte*)cbcPlain, 0) != 1)
            return -8475;

        EVP_CIPHER_CTX_init(&en);
        if (EVP_CipherInit(&en, EVP_aes_128_cbc(),
            (unsigned char*)key, (unsigned char*)iv, 1) == 0)
            return -8476;
        if (EVP_CipherUpdate(&en, (byte*)cipher, &outlen,
                                                    (byte*)cbcPlain, 9) == 0)
            return -8477;
        if(outlen != 0)
            return -8478;
        total += outlen;

        if (EVP_CipherUpdate(&en, (byte*)&cipher[total], &outlen,
                                                (byte*)&cbcPlain[9]  , 9) == 0)
            return -8479;
        if(outlen != 16)
            return -8480;
        total += outlen;

        if (EVP_CipherFinal(&en, (byte*)&cipher[total], &outlen) == 0)
            return -8481;
        if(outlen != 16)
            return -8482;
        total += outlen;
        if(total != 32)
            return -8483;

        total = 0;
        EVP_CIPHER_CTX_init(&de);
        if (EVP_CipherInit(&de, EVP_aes_128_cbc(),
            (unsigned char*)key, (unsigned char*)iv, 0) == 0)
            return -8484;

        if (EVP_CipherUpdate(&de, (byte*)plain, &outlen, (byte*)cipher, 6) == 0)
            return -8485;
        if(outlen != 0)
            return -8486;
        total += outlen;

        if (EVP_CipherUpdate(&de, (byte*)&plain[total], &outlen,
                                                    (byte*)&cipher[6], 12) == 0)
            return -8487;
        if(outlen != 0)
        total += outlen;

        if (EVP_CipherUpdate(&de, (byte*)&plain[total], &outlen,
                                                (byte*)&cipher[6+12], 14) == 0)
            return -8488;
        if(outlen != 16)
            return -8489;
        total += outlen;

        if (EVP_CipherFinal(&de, (byte*)&plain[total], &outlen) == 0)
            return -8490;
        if(outlen != 2)
            return -8491;
        total += outlen;

        if(total != 18)
            return -8492;

        if (XMEMCMP(plain, cbcPlain, 18))
            return -8493;

        total = 0;
        EVP_CIPHER_CTX_init(&en);
        if (EVP_EncryptInit(&en, EVP_aes_128_cbc(),
            (unsigned char*)key, (unsigned char*)iv) == 0)
            return -8494;
        if (EVP_CipherUpdate(&en, (byte*)cipher, &outlen, (byte*)cbcPlain, 9) == 0)
            return -8495;
        if(outlen != 0)
            return -8496;
        total += outlen;

        if (EVP_CipherUpdate(&en, (byte*)&cipher[total], &outlen, (byte*)&cbcPlain[9]  , 9) == 0)
            return -8497;
        if(outlen != 16)
            return -8498;
        total += outlen;

        if (EVP_EncryptFinal(&en, (byte*)&cipher[total], &outlen) == 0)
            return -8499;
        if(outlen != 16)
            return -8500;
        total += outlen;
        if(total != 32)
            return 3438;

        total = 0;
        EVP_CIPHER_CTX_init(&de);
        if (EVP_DecryptInit(&de, EVP_aes_128_cbc(),
            (unsigned char*)key, (unsigned char*)iv) == 0)
            return -8501;

        if (EVP_CipherUpdate(&de, (byte*)plain, &outlen, (byte*)cipher, 6) == 0)
            return -8502;
        if(outlen != 0)
            return -8503;
        total += outlen;

        if (EVP_CipherUpdate(&de, (byte*)&plain[total], &outlen, (byte*)&cipher[6], 12) == 0)
            return -8504;
        if(outlen != 0)
        total += outlen;

        if (EVP_CipherUpdate(&de, (byte*)&plain[total], &outlen, (byte*)&cipher[6+12], 14) == 0)
            return -8505;
        if(outlen != 16)
            return -8506;
        total += outlen;

        if (EVP_DecryptFinal(&de, (byte*)&plain[total], &outlen) == 0)
            return -8507;
        if(outlen != 2)
            return -8508;
        total += outlen;

        if(total != 18)
            return 3447;

        if (XMEMCMP(plain, cbcPlain, 18))
            return -8509;

        if (EVP_CIPHER_key_length(NULL) != 0)
            return -8510;

        if (EVP_CIPHER_key_length(EVP_aes_128_cbc()) != 16)
            return -8511;

        if (EVP_CIPHER_CTX_mode(NULL) != 0)
            return -8512;

        if (EVP_CIPHER_CTX_mode(&en) != (en.flags & WOLFSSL_EVP_CIPH_MODE))
            return -8513;

        EVP_CIPHER_CTX_init(&en);
        if (EVP_CipherInit_ex(&en, EVP_aes_128_cbc(), NULL,
            (unsigned char*)key, (unsigned char*)iv, 0) == 0)
            return -8514;

        EVP_CIPHER_CTX_init(&en);
        if (EVP_EncryptInit_ex(&en, EVP_aes_128_cbc(), NULL,
                (unsigned char*)key, (unsigned char*)iv) == 0)
            return -8515;

        if (wolfSSL_EVP_EncryptFinal_ex(NULL, NULL, NULL) != WOLFSSL_FAILURE)
            return -8516;

        if (wolfSSL_EVP_EncryptFinal(NULL, NULL, NULL) != WOLFSSL_FAILURE)
            return -8517;

        EVP_CIPHER_CTX_init(&de);
        if (EVP_DecryptInit_ex(&de, EVP_aes_128_cbc(), NULL,
                (unsigned char*)key, (unsigned char*)iv) == 0)
            return -8518;

        if (wolfSSL_EVP_DecryptFinal(NULL, NULL, NULL) != WOLFSSL_FAILURE)
            return -8519;

        if (wolfSSL_EVP_DecryptFinal_ex(NULL, NULL, NULL) != WOLFSSL_FAILURE)
            return -8520;

        if (EVP_CIPHER_CTX_block_size(NULL) != BAD_FUNC_ARG)
            return -8521;

        EVP_CIPHER_CTX_init(&en);
        EVP_EncryptInit_ex(&en, EVP_aes_128_cbc(), NULL,
                (unsigned char*)key, (unsigned char*)iv);
        if (EVP_CIPHER_CTX_block_size(&en) != en.block_size)
            return -8522;

        if (EVP_CIPHER_block_size(NULL) != BAD_FUNC_ARG)
            return -8523;

        if (EVP_CIPHER_block_size(EVP_aes_128_cbc()) != AES_BLOCK_SIZE)
            return -8524;

        if (WOLFSSL_EVP_CIPHER_mode(NULL) != 0)
            return -8525;

        if (EVP_CIPHER_flags(EVP_aes_128_cbc()) != WOLFSSL_EVP_CIPH_CBC_MODE)
            return -8526;

        EVP_CIPHER_CTX_clear_flags(&en, 0xFFFFFFFF);
        EVP_CIPHER_CTX_set_flags(&en, 42);
        if (en.flags != 42)
            return -8527;

        if (EVP_CIPHER_CTX_set_padding(NULL, 0) != BAD_FUNC_ARG)
            return -8528;
        if (EVP_CIPHER_CTX_set_padding(&en, 0) != WOLFSSL_SUCCESS)
            return -8529;
        if (EVP_CIPHER_CTX_set_padding(&en, 1) != WOLFSSL_SUCCESS)
            return -8530;

    }
#endif /* WOLFSSL_AES_128 && HAVE_AES_CBC */
#endif /* ifndef NO_AES */
    return 0;
}

int openSSL_evpMD_test(void)
{
    int ret = 0;
#if !defined(NO_SHA256) && !defined(NO_SHA)
    WOLFSSL_EVP_MD_CTX* ctx;
    WOLFSSL_EVP_MD_CTX* ctx2;

    ctx = EVP_MD_CTX_create();
    ctx2 = EVP_MD_CTX_create();

    ret = EVP_DigestInit(ctx, EVP_sha256());
    if (ret != SSL_SUCCESS) {
        ret = -8600;
        goto openSSL_evpMD_test_done;
    }

    ret = EVP_MD_CTX_copy(ctx2, ctx);
    if (ret != SSL_SUCCESS) {
        ret = -8601;
        goto openSSL_evpMD_test_done;
    }

    if (EVP_MD_type(EVP_sha256()) != EVP_MD_CTX_type(ctx2)) {
        ret = -8602;
        goto openSSL_evpMD_test_done;
    }

    ret = EVP_DigestInit(ctx, EVP_sha1());
    if (ret != SSL_SUCCESS) {
        ret = -8603;
        goto openSSL_evpMD_test_done;
    }

    if (EVP_MD_type(EVP_sha256()) != EVP_MD_CTX_type(ctx2)) {
        ret = -8604;
        goto openSSL_evpMD_test_done;
    }

    ret = EVP_MD_CTX_copy_ex(ctx2, ctx);
    if (ret != SSL_SUCCESS) {
        ret = -8605;
        goto openSSL_evpMD_test_done;
    }

    if (EVP_MD_type(EVP_sha256()) == EVP_MD_CTX_type(ctx2)) {
        ret = -8606;
        goto openSSL_evpMD_test_done;
    }

    if (EVP_MD_type(EVP_sha1()) != EVP_MD_CTX_type(ctx2)) {
        ret = -8607;
        goto openSSL_evpMD_test_done;
    }

    if (EVP_DigestInit_ex(ctx, EVP_sha1(), NULL) != SSL_SUCCESS) {
        ret = -8608;
        goto openSSL_evpMD_test_done;
    }

    if (EVP_add_digest(NULL) != 0) {
        ret = -8609;
        goto openSSL_evpMD_test_done;
    }

    if (wolfSSL_EVP_add_cipher(NULL) != 0) {
        ret = -8610;
        goto openSSL_evpMD_test_done;
    }

    ret = 0; /* got to success state without jumping to end with a fail */

openSSL_evpMD_test_done:
    EVP_MD_CTX_destroy(ctx);
    EVP_MD_CTX_destroy(ctx2);
#endif /* NO_SHA256 */

    return ret;
}

#ifdef DEBUG_SIGN
static void show(const char *title, const char *p, unsigned int s) {
    char* i;
    printf("%s: ", title);
    for (i = p;
            i < p + s;
            printf("%c", *i), i++);
    printf("\n");
}
#else
#define show(a,b,c)
#endif

#define FOURK_BUFF 4096

#define ERR_BASE_PKEY -5000
int openssl_pkey0_test(void)
{
    int ret = 0;
#if !defined(NO_RSA) && !defined(HAVE_USER_RSA) && !defined(NO_SHA)
    byte*   prvTmp;
    byte*   pubTmp;
    int prvBytes;
    int pubBytes;
    RSA *prvRsa = NULL;
    RSA *pubRsa = NULL;
    EVP_PKEY *prvPkey = NULL;
    EVP_PKEY *pubPkey = NULL;
    EVP_PKEY_CTX *enc = NULL;
    EVP_PKEY_CTX *dec = NULL;

    byte   in[] = "Everyone gets Friday off.";
    byte   out[256];
    size_t outlen;
    size_t keySz;
    byte   plain[256];
#if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048)
    XFILE  keyFile;
    XFILE  keypubFile;
    char cliKey[]    = "./certs/client-key.der";
    char cliKeypub[] = "./certs/client-keyPub.der";

#endif

    prvTmp = (byte*)XMALLOC(FOURK_BUFF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (prvTmp == NULL)
        return ERR_BASE_PKEY-1;
    pubTmp = (byte*)XMALLOC(FOURK_BUFF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (pubTmp == NULL) {
        XFREE(prvTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        return ERR_BASE_PKEY-2;
    }

#ifdef USE_CERT_BUFFERS_1024
    XMEMCPY(prvTmp, client_key_der_1024, sizeof_client_key_der_1024);
    prvBytes = sizeof_client_key_der_1024;
    XMEMCPY(pubTmp, client_keypub_der_1024, sizeof_client_keypub_der_1024);
    pubBytes = sizeof_client_keypub_der_1024;
#elif defined(USE_CERT_BUFFERS_2048)
    XMEMCPY(prvTmp, client_key_der_2048, sizeof_client_key_der_2048);
    prvBytes = sizeof_client_key_der_2048;
    XMEMCPY(pubTmp, client_keypub_der_2048, sizeof_client_keypub_der_2048);
    pubBytes = sizeof_client_keypub_der_2048;
#else
    keyFile = XFOPEN(cliKey, "rb");
    if (!keyFile) {
        XFREE(prvTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(pubTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        err_sys("can't open ./certs/client-key.der, "
                "Please run from wolfSSL home dir", ERR_BASE_PKEY-3);
        return ERR_BASE_PKEY-3;
    }
    prvBytes = (int)XFREAD(prvTmp, 1, (int)FOURK_BUFF, keyFile);
    XFCLOSE(keyFile);
    keypubFile = XFOPEN(cliKeypub, "rb");
    if (!keypubFile) {
        XFREE(prvTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(pubTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        err_sys("can't open ./certs/client-cert.der, "
                "Please run from wolfSSL home dir", -4);
        return ERR_BASE_PKEY-4;
    }
    pubBytes = (int)XFREAD(pubTmp, 1, (int)FOURK_BUFF, keypubFile);
    XFCLOSE(keypubFile);
#endif /* USE_CERT_BUFFERS */

        prvRsa = wolfSSL_RSA_new();
        pubRsa = wolfSSL_RSA_new();
        if((prvRsa == NULL) || (pubRsa == NULL)){
            printf("error with RSA_new\n");
            ret = ERR_BASE_PKEY-10;
            goto openssl_pkey0_test_done;
        }

        ret = wolfSSL_RSA_LoadDer_ex(prvRsa, prvTmp, prvBytes, WOLFSSL_RSA_LOAD_PRIVATE);
        if(ret != SSL_SUCCESS){
            printf("error with RSA_LoadDer_ex\n");
            ret = ERR_BASE_PKEY-11;
            goto openssl_pkey0_test_done;
        }

        ret = wolfSSL_RSA_LoadDer_ex(pubRsa, pubTmp, pubBytes, WOLFSSL_RSA_LOAD_PUBLIC);
        if(ret != SSL_SUCCESS){
            printf("error with RSA_LoadDer_ex\n");
            ret = ERR_BASE_PKEY-12;
            goto openssl_pkey0_test_done;
        }
        keySz = (size_t)RSA_size(pubRsa);

        prvPkey = wolfSSL_EVP_PKEY_new();
        pubPkey = wolfSSL_EVP_PKEY_new();
        if((prvPkey == NULL) || (pubPkey == NULL)){
            printf("error with PKEY_new\n");
            ret = ERR_BASE_PKEY-13;
            goto openssl_pkey0_test_done;
        }
        ret  = wolfSSL_EVP_PKEY_set1_RSA(prvPkey, prvRsa);
        ret += wolfSSL_EVP_PKEY_set1_RSA(pubPkey, pubRsa);
        if(ret != 2){
            printf("error with PKEY_set1_RSA\n");
            ret = ERR_BASE_PKEY-14;
            goto openssl_pkey0_test_done;
        }

        dec = EVP_PKEY_CTX_new(prvPkey, NULL);
        enc = EVP_PKEY_CTX_new(pubPkey, NULL);
        if((dec == NULL)||(enc==NULL)){
            printf("error with EVP_PKEY_CTX_new\n");
            ret = ERR_BASE_PKEY-15;
            goto openssl_pkey0_test_done;
        }

        ret = EVP_PKEY_decrypt_init(dec);
        if (ret != 1) {
            printf("error with decrypt init\n");
            ret = ERR_BASE_PKEY-16;
            goto openssl_pkey0_test_done;
        }
        ret = EVP_PKEY_encrypt_init(enc);
        if (ret != 1) {
            printf("error with encrypt init\n");
            ret = ERR_BASE_PKEY-17;
            goto openssl_pkey0_test_done;
        }
        XMEMSET(out, 0, sizeof(out));
        ret = EVP_PKEY_encrypt(enc, out, &outlen, in, sizeof(in));
        if (ret != 1) {
            printf("error encrypting msg\n");
            ret = ERR_BASE_PKEY-18;
            goto openssl_pkey0_test_done;
        }

        show("encrypted msg", out, outlen);

        XMEMSET(plain, 0, sizeof(plain));
        ret = EVP_PKEY_decrypt(dec, plain, &outlen, out, keySz);
        if (ret != 1) {
            printf("error decrypting msg\n");
            ret = ERR_BASE_PKEY-19;
            goto openssl_pkey0_test_done;
        }
        show("decrypted msg", plain, outlen);

        /* RSA_PKCS1_OAEP_PADDING test */
        ret = EVP_PKEY_decrypt_init(dec);
        if (ret != 1) {
            printf("error with decrypt init\n");
            ret = ERR_BASE_PKEY-30;
            goto openssl_pkey0_test_done;
        }
        ret = EVP_PKEY_encrypt_init(enc);
        if (ret != 1) {
            printf("error with encrypt init\n");
            ret = ERR_BASE_PKEY-31;
            goto openssl_pkey0_test_done;
        }

        if (EVP_PKEY_CTX_set_rsa_padding(dec, RSA_PKCS1_PADDING) <= 0) {
            printf("first set rsa padding error\n");
            ret = ERR_BASE_PKEY-32;
            goto openssl_pkey0_test_done;
        }

#ifndef HAVE_FIPS
        if (EVP_PKEY_CTX_set_rsa_padding(dec, RSA_PKCS1_OAEP_PADDING) <= 0){
            printf("second set rsa padding error\n");
            ret = ERR_BASE_PKEY-33;
            goto openssl_pkey0_test_done;
        }

        if (EVP_PKEY_CTX_set_rsa_padding(enc, RSA_PKCS1_OAEP_PADDING) <= 0) {
            printf("third set rsa padding error\n");
            ret = ERR_BASE_PKEY-34;
            goto openssl_pkey0_test_done;
        }
#endif

        XMEMSET(out, 0, sizeof(out));
        ret = EVP_PKEY_encrypt(enc, out, &outlen, in, sizeof(in));
        if (ret != 1) {
            printf("error encrypting msg\n");
            ret = ERR_BASE_PKEY-35;
            goto openssl_pkey0_test_done;
        }

        show("encrypted msg", out, outlen);

        XMEMSET(plain, 0, sizeof(plain));
        ret = EVP_PKEY_decrypt(dec, plain, &outlen, out, keySz);
        if (ret != 1) {
            printf("error decrypting msg\n");
            ret = ERR_BASE_PKEY-36;
            goto openssl_pkey0_test_done;
        }

        show("decrypted msg", plain, outlen);

        ret = 0; /* made it to this point without error then set success */
openssl_pkey0_test_done:

        wolfSSL_RSA_free(prvRsa);
        wolfSSL_RSA_free(pubRsa);
        EVP_PKEY_free(pubPkey);
        EVP_PKEY_free(prvPkey);
        EVP_PKEY_CTX_free(dec);
        EVP_PKEY_CTX_free(enc);
        XFREE(prvTmp, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(pubTmp, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
#endif /* NO_RSA */

        return ret;
}


int openssl_pkey1_test(void)
{
    int ret = 0;
#if !defined(NO_FILESYSTEM) && !defined(NO_RSA) && !defined(HAVE_USER_RSA) && \
    !defined(NO_SHA)
    EVP_PKEY_CTX* dec = NULL;
    EVP_PKEY_CTX* enc = NULL;
    EVP_PKEY* pubKey  = NULL;
    EVP_PKEY* prvKey  = NULL;
    X509* x509;

    const unsigned char msg[] = "sugar slapped";
    const unsigned char* clikey;
    unsigned char tmp[FOURK_BUF];
    long cliKeySz;
    unsigned char cipher[RSA_TEST_BYTES];
    unsigned char plain[RSA_TEST_BYTES];
    size_t outlen;
    int keyLenBits = 2048;

#if defined(USE_CERT_BUFFERS_1024)
    XMEMCPY(tmp, client_key_der_1024, sizeof_client_key_der_1024);
    cliKeySz = (long)sizeof_client_key_der_1024;

    x509 = wolfSSL_X509_load_certificate_buffer(client_cert_der_1024,
            sizeof_client_cert_der_1024, SSL_FILETYPE_ASN1);
    keyLenBits = 1024;
#elif defined(USE_CERT_BUFFERS_2048)
    XMEMCPY(tmp, client_key_der_2048, sizeof_client_key_der_2048);
    cliKeySz = (long)sizeof_client_key_der_2048;

    x509 = wolfSSL_X509_load_certificate_buffer(client_cert_der_2048,
            sizeof_client_cert_der_2048, SSL_FILETYPE_ASN1);
#elif defined(USE_CERT_BUFFERS_3072)
    XMEMCPY(tmp, client_key_der_3072, sizeof_client_key_der_3072);
    cliKeySz = (long)sizeof_client_key_der_3072;

    x509 = wolfSSL_X509_load_certificate_buffer(client_cert_der_3072,
            sizeof_client_cert_der_3072, SSL_FILETYPE_ASN1);
    keyLenBits = 3072;
#elif defined(USE_CERT_BUFFERS_4096)
    XMEMCPY(tmp, client_key_der_4096, sizeof_client_key_der_4096);
    cliKeySz = (long)sizeof_client_key_der_4096;

    x509 = wolfSSL_X509_load_certificate_buffer(client_cert_der_4096,
            sizeof_client_cert_der_4096, SSL_FILETYPE_ASN1);
    keyLenBits = 4096;
#else
    XFILE f;

    f = XFOPEN(clientKey, "rb");

    if (!f) {
        err_sys("can't open ./certs/client-key.der, "
                "Please run from wolfSSL home dir", -41);
        return -8800;
    }

    cliKeySz = (long)XFREAD(tmp, 1, FOURK_BUF, f);
    XFCLOSE(f);

    /* using existing wolfSSL api to get public and private key */
    x509 = wolfSSL_X509_load_certificate_file(clientCert, SSL_FILETYPE_ASN1);
#endif /* USE_CERT_BUFFERS */
    clikey = tmp;

    if ((prvKey = EVP_PKEY_new()) == NULL) {
        return -8801;
    }
    EVP_PKEY_free(prvKey);
    prvKey = NULL;

    if (x509 == NULL) {
        ret = -8802;
        goto openssl_pkey1_test_done;
    }

    pubKey = X509_get_pubkey(x509);
    if (pubKey == NULL) {
        ret = -8803;
        goto openssl_pkey1_test_done;
    }

    prvKey = d2i_PrivateKey(EVP_PKEY_RSA, NULL, &clikey, cliKeySz);
    if (prvKey == NULL) {
        ret = -8804;
        goto openssl_pkey1_test_done;
    }

    /* phase 2 API to create EVP_PKEY_CTX and encrypt/decrypt */
    if (EVP_PKEY_bits(prvKey) != keyLenBits) {
        ret = -8805;
        goto openssl_pkey1_test_done;
    }

    if (EVP_PKEY_size(prvKey) != keyLenBits/8) {
        ret = -8806;
        goto openssl_pkey1_test_done;
    }

    dec = EVP_PKEY_CTX_new(prvKey, NULL);
    enc = EVP_PKEY_CTX_new(pubKey, NULL);
    if (dec == NULL || enc == NULL) {
        ret = -8807;
        goto openssl_pkey1_test_done;
    }

    if (EVP_PKEY_decrypt_init(dec) != 1) {
        ret = -8808;
        goto openssl_pkey1_test_done;
    }

    if (EVP_PKEY_encrypt_init(enc) != 1) {
        ret = -8809;
        goto openssl_pkey1_test_done;
    }

    if (EVP_PKEY_CTX_set_rsa_padding(dec, RSA_PKCS1_PADDING) <= 0) {
        ret = -8810;
        goto openssl_pkey1_test_done;
    }

#ifndef HAVE_FIPS
    if (EVP_PKEY_CTX_set_rsa_padding(dec, RSA_PKCS1_OAEP_PADDING) <= 0){
        ret = -8811;
        goto openssl_pkey1_test_done;
    }

    if (EVP_PKEY_CTX_set_rsa_padding(enc, RSA_PKCS1_OAEP_PADDING) <= 0) {
        ret = -8812;
        goto openssl_pkey1_test_done;
    }
#endif

    XMEMSET(cipher, 0, sizeof(cipher));
    outlen = keyLenBits/8;
    if (EVP_PKEY_encrypt(enc, cipher, &outlen, msg, sizeof(msg)) < 0) {
        ret = -8813;
        goto openssl_pkey1_test_done;
    }

    XMEMSET(plain, 0, sizeof(plain));
    if (EVP_PKEY_decrypt(dec, plain, &outlen, cipher, outlen) != 1) {
        ret = -8814;
        goto openssl_pkey1_test_done;
    }

openssl_pkey1_test_done:
    if (pubKey != NULL) {
        EVP_PKEY_free(pubKey);
    }
    if (prvKey != NULL) {
        EVP_PKEY_free(prvKey);
    }
    if (dec != NULL) {
        EVP_PKEY_CTX_free(dec);
    }
    if (enc != NULL) {
        EVP_PKEY_CTX_free(enc);
    }
    if (x509 != NULL) {
        X509_free(x509);
    }

#endif
    return ret;
}


#define ERR_BASE_EVPSIG -5100

int openssl_evpSig_test(void)
{
#if !defined(NO_RSA) && !defined(NO_SHA) && !defined(HAVE_USER_RSA)
  	byte*   prvTmp;
	byte*   pubTmp;
	int prvBytes;
	int pubBytes;
    RSA *prvRsa;
	RSA *pubRsa;
	EVP_PKEY *prvPkey;
	EVP_PKEY *pubPkey;

    EVP_MD_CTX* sign;
    EVP_MD_CTX* verf;
    char msg[] = "see spot run";
    unsigned char sig[256];
    unsigned int sigSz;
    const void* pt;
    unsigned int count;
    int ret, ret1, ret2;

    #if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048)
    XFILE   keyFile;
    XFILE   keypubFile;
    char cliKey[]    = "./certs/client-key.der";
    char cliKeypub[] = "./certs/client-keyPub.der";
    #endif

    prvTmp = (byte*)XMALLOC(FOURK_BUFF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (prvTmp == NULL)
        return ERR_BASE_EVPSIG-1;
    pubTmp = (byte*)XMALLOC(FOURK_BUFF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (pubTmp == NULL) {
        XFREE(prvTmp, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        return ERR_BASE_EVPSIG-2;
    }

#ifdef USE_CERT_BUFFERS_1024
    XMEMCPY(prvTmp, client_key_der_1024, sizeof_client_key_der_1024);
    prvBytes = sizeof_client_key_der_1024;
    XMEMCPY(pubTmp, client_keypub_der_1024, sizeof_client_keypub_der_1024);
    pubBytes = sizeof_client_keypub_der_1024;
#elif defined(USE_CERT_BUFFERS_2048)
    XMEMCPY(prvTmp, client_key_der_2048, sizeof_client_key_der_2048);
    prvBytes = sizeof_client_key_der_2048;
    XMEMCPY(pubTmp, client_keypub_der_2048, sizeof_client_keypub_der_2048);
    pubBytes = sizeof_client_keypub_der_2048;
#else
    keyFile = XFOPEN(cliKey, "rb");
    if (!keyFile) {
        XFREE(pubTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(prvTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        err_sys("can't open ./certs/client-key.der, "
                "Please run from wolfSSL home dir", -40);
        return ERR_BASE_EVPSIG-3;
    }
    prvBytes = (int)XFREAD(prvTmp, 1, (int)FOURK_BUFF, keyFile);
    XFCLOSE(keyFile);
    keypubFile = XFOPEN(cliKeypub, "rb");
    if (!keypubFile) {
        XFREE(pubTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(prvTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        err_sys("can't open ./certs/client-cert.der, "
                "Please run from wolfSSL home dir", -41);
        return ERR_BASE_EVPSIG-4;
    }
    pubBytes = (int)XFREAD(pubTmp, 1, (int)FOURK_BUFF, keypubFile);
    XFCLOSE(keypubFile);
    #endif /* USE_CERT_BUFFERS */

    prvRsa = wolfSSL_RSA_new();
    pubRsa = wolfSSL_RSA_new();
    if((prvRsa == NULL) || (pubRsa == NULL)){
        XFREE(pubTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(prvTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        err_sys("ERROR with RSA_new", -8900);
        return ERR_BASE_EVPSIG-5;
    }

    ret1 = wolfSSL_RSA_LoadDer_ex(prvRsa, prvTmp, prvBytes, WOLFSSL_RSA_LOAD_PRIVATE);
    ret2 = wolfSSL_RSA_LoadDer_ex(pubRsa, pubTmp, pubBytes, WOLFSSL_RSA_LOAD_PUBLIC);
    if((ret1 != SSL_SUCCESS) || (ret2 != SSL_SUCCESS)){
      printf("error with RSA_LoadDer_ex\n");
      return ERR_BASE_EVPSIG-6;
    }

    prvPkey = wolfSSL_EVP_PKEY_new();
    pubPkey = wolfSSL_EVP_PKEY_new();
    if((prvPkey == NULL) || (pubPkey == NULL)){
        XFREE(pubTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(prvTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        printf("error with KEY_new\n");
        return ERR_BASE_EVPSIG-7;
    }
    ret1  = wolfSSL_EVP_PKEY_set1_RSA(prvPkey, prvRsa);
    ret2  = wolfSSL_EVP_PKEY_set1_RSA(pubPkey, pubRsa);
    if((ret1 != 1) || (ret2 != 1)){
        XFREE(pubTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(prvTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        printf("error with EVP_PKEY_set1_RSA\n");
        return ERR_BASE_EVPSIG-8;
    }

    /****************** sign and verify *******************/
    sign = EVP_MD_CTX_create();
    verf = EVP_MD_CTX_create();
    if((sign == NULL)||(verf == NULL)){
        printf("error with EVP_MD_CTX_create\n");
        EVP_MD_CTX_destroy(sign);
        EVP_MD_CTX_destroy(verf);
        return ERR_BASE_EVPSIG-10;
    }

    ret = EVP_SignInit(sign, EVP_sha1());
    if (ret != SSL_SUCCESS){
        printf("error with EVP_SignInit\n");
        EVP_MD_CTX_destroy(sign);
        EVP_MD_CTX_destroy(verf);
        return ERR_BASE_EVPSIG-11;
    }

    count = sizeof(msg);
    show("message = ", (char *)msg, count);

    /* sign */
    XMEMSET(sig, 0, sizeof(sig));
    pt = (const void*)msg;
    ret1 = EVP_SignUpdate(sign, pt, count);
    ret2 = EVP_SignFinal(sign, sig, &sigSz, prvPkey);
    if((ret1 != SSL_SUCCESS) || (ret2 != SSL_SUCCESS)){
        XFREE(pubTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(prvTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        EVP_MD_CTX_destroy(sign);
        EVP_MD_CTX_destroy(verf);
        printf("error with EVP_MD_CTX_create\n");
        return ERR_BASE_EVPSIG-12;
    }
    show("signature = ", (char *)sig, sigSz);

    /* verify */
    pt = (const void*)msg;
    ret1 = EVP_VerifyInit(verf, EVP_sha1());
    ret2 = EVP_VerifyUpdate(verf, pt, count);
    if((ret1 != SSL_SUCCESS) || (ret2 != SSL_SUCCESS)){
        XFREE(pubTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(prvTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        EVP_MD_CTX_destroy(sign);
        EVP_MD_CTX_destroy(verf);
        printf("error with EVP_Verify\n");
        return ERR_BASE_EVPSIG-13;
    }
    if (EVP_VerifyFinal(verf, sig, sigSz, pubPkey) != 1) {
        XFREE(pubTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(prvTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        EVP_MD_CTX_destroy(sign);
        EVP_MD_CTX_destroy(verf);
        printf("error with EVP_VerifyFinal\n");
        return ERR_BASE_EVPSIG-14;
    }

    /* expect fail without update */
    EVP_VerifyInit(verf, EVP_sha1());
    if (EVP_VerifyFinal(verf, sig, sigSz, pubPkey) == 1) {
        XFREE(pubTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(prvTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
        EVP_MD_CTX_destroy(sign);
        EVP_MD_CTX_destroy(verf);
        printf("EVP_VerifyInit without update not detected\n");
        return ERR_BASE_EVPSIG-15;
    }

    XFREE(pubTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(prvTmp, HEAP_HINT ,DYNAMIC_TYPE_TMP_BUFFER);
    EVP_MD_CTX_destroy(sign);
    EVP_MD_CTX_destroy(verf);

    wolfSSL_RSA_free(prvRsa);
    wolfSSL_RSA_free(pubRsa);
    EVP_PKEY_free(pubPkey);
    EVP_PKEY_free(prvPkey);

#endif /* NO_RSA */
    return 0;
}
#endif /* OPENSSL_EXTRA */


#ifndef NO_PWDBASED
#ifdef HAVE_SCRYPT
/* Test vectors taken from RFC 7914: scrypt PBKDF - Section 12. */
int scrypt_test(void)
{
    int   ret;
    byte  derived[64];

    const byte verify1[] = {
        0x77, 0xd6, 0x57, 0x62, 0x38, 0x65, 0x7b, 0x20,
        0x3b, 0x19, 0xca, 0x42, 0xc1, 0x8a, 0x04, 0x97,
        0xf1, 0x6b, 0x48, 0x44, 0xe3, 0x07, 0x4a, 0xe8,
        0xdf, 0xdf, 0xfa, 0x3f, 0xed, 0xe2, 0x14, 0x42,
        0xfc, 0xd0, 0x06, 0x9d, 0xed, 0x09, 0x48, 0xf8,
        0x32, 0x6a, 0x75, 0x3a, 0x0f, 0xc8, 0x1f, 0x17,
        0xe8, 0xd3, 0xe0, 0xfb, 0x2e, 0x0d, 0x36, 0x28,
        0xcf, 0x35, 0xe2, 0x0c, 0x38, 0xd1, 0x89, 0x06
    };
    const byte verify2[] = {
        0xfd, 0xba, 0xbe, 0x1c, 0x9d, 0x34, 0x72, 0x00,
        0x78, 0x56, 0xe7, 0x19, 0x0d, 0x01, 0xe9, 0xfe,
        0x7c, 0x6a, 0xd7, 0xcb, 0xc8, 0x23, 0x78, 0x30,
        0xe7, 0x73, 0x76, 0x63, 0x4b, 0x37, 0x31, 0x62,
        0x2e, 0xaf, 0x30, 0xd9, 0x2e, 0x22, 0xa3, 0x88,
        0x6f, 0xf1, 0x09, 0x27, 0x9d, 0x98, 0x30, 0xda,
        0xc7, 0x27, 0xaf, 0xb9, 0x4a, 0x83, 0xee, 0x6d,
        0x83, 0x60, 0xcb, 0xdf, 0xa2, 0xcc, 0x06, 0x40
    };
#if !defined(BENCH_EMBEDDED) && !defined(HAVE_INTEL_QA)
    const byte verify3[] = {
        0x70, 0x23, 0xbd, 0xcb, 0x3a, 0xfd, 0x73, 0x48,
        0x46, 0x1c, 0x06, 0xcd, 0x81, 0xfd, 0x38, 0xeb,
        0xfd, 0xa8, 0xfb, 0xba, 0x90, 0x4f, 0x8e, 0x3e,
        0xa9, 0xb5, 0x43, 0xf6, 0x54, 0x5d, 0xa1, 0xf2,
        0xd5, 0x43, 0x29, 0x55, 0x61, 0x3f, 0x0f, 0xcf,
        0x62, 0xd4, 0x97, 0x05, 0x24, 0x2a, 0x9a, 0xf9,
        0xe6, 0x1e, 0x85, 0xdc, 0x0d, 0x65, 0x1e, 0x40,
        0xdf, 0xcf, 0x01, 0x7b, 0x45, 0x57, 0x58, 0x87
    };
#endif
#ifdef SCRYPT_TEST_ALL
    /* Test case is very slow.
     * Use for confirmation after code change or new platform.
     */
    const byte verify4[] = {
        0x21, 0x01, 0xcb, 0x9b, 0x6a, 0x51, 0x1a, 0xae,
        0xad, 0xdb, 0xbe, 0x09, 0xcf, 0x70, 0xf8, 0x81,
        0xec, 0x56, 0x8d, 0x57, 0x4a, 0x2f, 0xfd, 0x4d,
        0xab, 0xe5, 0xee, 0x98, 0x20, 0xad, 0xaa, 0x47,
        0x8e, 0x56, 0xfd, 0x8f, 0x4b, 0xa5, 0xd0, 0x9f,
        0xfa, 0x1c, 0x6d, 0x92, 0x7c, 0x40, 0xf4, 0xc3,
        0x37, 0x30, 0x40, 0x49, 0xe8, 0xa9, 0x52, 0xfb,
        0xcb, 0xf4, 0x5c, 0x6f, 0xa7, 0x7a, 0x41, 0xa4
    };
#endif

    ret = wc_scrypt(derived, NULL, 0, NULL, 0, 4, 1, 1, sizeof(verify1));
    if (ret != 0)
        return -9000;
    if (XMEMCMP(derived, verify1, sizeof(verify1)) != 0)
        return -9001;

    ret = wc_scrypt(derived, (byte*)"password", 8, (byte*)"NaCl", 4, 10, 8, 16,
                    sizeof(verify2));
    if (ret != 0)
        return -9002;
    if (XMEMCMP(derived, verify2, sizeof(verify2)) != 0)
        return -9003;

    /* Don't run these test on embedded, since they use large mallocs */
#if !defined(BENCH_EMBEDDED) && !defined(HAVE_INTEL_QA)
    ret = wc_scrypt(derived, (byte*)"pleaseletmein", 13,
                    (byte*)"SodiumChloride", 14, 14, 8, 1, sizeof(verify3));
    if (ret != 0)
        return -9004;
    if (XMEMCMP(derived, verify3, sizeof(verify3)) != 0)
        return -9005;

#ifdef SCRYPT_TEST_ALL
    ret = wc_scrypt(derived, (byte*)"pleaseletmein", 13,
                    (byte*)"SodiumChloride", 14, 20, 8, 1, sizeof(verify4));
    if (ret != 0)
        return -9006;
    if (XMEMCMP(derived, verify4, sizeof(verify4)) != 0)
        return -9007;
#endif
#endif /* !BENCH_EMBEDDED && !HAVE_INTEL_QA */

    ret = wc_scrypt_ex(derived, (byte*)"password", 8, (byte*)"NaCl", 4, 1<<10,
                       8, 16, sizeof(verify2));
    if (ret != 0)
        return -9008;
    if (XMEMCMP(derived, verify2, sizeof(verify2)) != 0)
        return -9009;

    return 0;
}
#endif

#ifdef HAVE_PKCS12
int pkcs12_test(void)
{
    const byte passwd[] = { 0x00, 0x73, 0x00, 0x6d, 0x00, 0x65, 0x00, 0x67,
                            0x00, 0x00 };
    const byte salt[] =   { 0x0a, 0x58, 0xCF, 0x64, 0x53, 0x0d, 0x82, 0x3f };

    const byte passwd2[] = { 0x00, 0x71, 0x00, 0x75, 0x00, 0x65, 0x00, 0x65,
                             0x00, 0x67, 0x00, 0x00 };
    const byte salt2[] =   { 0x16, 0x82, 0xC0, 0xfC, 0x5b, 0x3f, 0x7e, 0xc5 };
    byte  derived[64];

    const byte verify[] = {
        0x27, 0xE9, 0x0D, 0x7E, 0xD5, 0xA1, 0xC4, 0x11,
        0xBA, 0x87, 0x8B, 0xC0, 0x90, 0xF5, 0xCE, 0xBE,
        0x5E, 0x9D, 0x5F, 0xE3, 0xD6, 0x2B, 0x73, 0xAA
    };

    const byte verify2[] = {
        0x90, 0x1B, 0x49, 0x70, 0xF0, 0x94, 0xF0, 0xF8,
        0x45, 0xC0, 0xF3, 0xF3, 0x13, 0x59, 0x18, 0x6A,
        0x35, 0xE3, 0x67, 0xFE, 0xD3, 0x21, 0xFD, 0x7C
    };

    int id         =  1;
    int kLen       = 24;
    int iterations =  1;
    int ret = wc_PKCS12_PBKDF(derived, passwd, sizeof(passwd), salt, 8,
                                                  iterations, kLen, WC_SHA256, id);

    if (ret < 0)
        return -9100;

    if ( (ret = XMEMCMP(derived, verify, kLen)) != 0)
        return -9101;

    iterations = 1000;
    ret = wc_PKCS12_PBKDF(derived, passwd2, sizeof(passwd2), salt2, 8,
                                                  iterations, kLen, WC_SHA256, id);
    if (ret < 0)
        return -9102;

    ret = wc_PKCS12_PBKDF_ex(derived, passwd2, sizeof(passwd2), salt2, 8,
                                       iterations, kLen, WC_SHA256, id, HEAP_HINT);
    if (ret < 0)
        return -9103;

    if ( (ret = XMEMCMP(derived, verify2, 24)) != 0)
        return -9104;

    return 0;
}
#endif /* HAVE_PKCS12 */

#if defined(HAVE_PBKDF2) && !defined(NO_SHA256)
int pbkdf2_test(void)
{
    char passwd[] = "passwordpassword";
    const byte salt[] = { 0x78, 0x57, 0x8E, 0x5a, 0x5d, 0x63, 0xcb, 0x06 };
    int   iterations = 2048;
    int   kLen = 24;
    byte  derived[64];

    const byte verify[] = {
        0x43, 0x6d, 0xb5, 0xe8, 0xd0, 0xfb, 0x3f, 0x35, 0x42, 0x48, 0x39, 0xbc,
        0x2d, 0xd4, 0xf9, 0x37, 0xd4, 0x95, 0x16, 0xa7, 0x2a, 0x9a, 0x21, 0xd1
    };

    int ret = wc_PBKDF2_ex(derived, (byte*)passwd, (int)XSTRLEN(passwd), salt,
              (int)sizeof(salt), iterations, kLen, WC_SHA256, HEAP_HINT, devId);
    if (ret != 0)
        return ret;

    if (XMEMCMP(derived, verify, sizeof(verify)) != 0)
        return -9200;

    return 0;

}
#endif /* HAVE_PBKDF2 && !NO_SHA256 */

#if defined(HAVE_PBKDF1) && !defined(NO_SHA)
int pbkdf1_test(void)
{
    char passwd[] = "password";
    const byte salt[] = { 0x78, 0x57, 0x8E, 0x5a, 0x5d, 0x63, 0xcb, 0x06 };
    int   iterations = 1000;
    int   kLen = 16;
    byte  derived[16];

    const byte verify[] = {
        0xDC, 0x19, 0x84, 0x7E, 0x05, 0xC6, 0x4D, 0x2F,
        0xAF, 0x10, 0xEB, 0xFB, 0x4A, 0x3D, 0x2A, 0x20
    };

    int ret = wc_PBKDF1_ex(derived, kLen, NULL, 0, (byte*)passwd,
        (int)XSTRLEN(passwd), salt, (int)sizeof(salt), iterations, WC_SHA,
        HEAP_HINT);
    if (ret != 0)
        return ret;

    if (XMEMCMP(derived, verify, sizeof(verify)) != 0)
        return -9300;

    return 0;
}
#endif /* HAVE_PBKDF2 && !NO_SHA */

int pwdbased_test(void)
{
   int ret = 0;

#if defined(HAVE_PBKDF1) && !defined(NO_SHA)
   ret = pbkdf1_test();
   if (ret != 0)
      return ret;
#endif
#if defined(HAVE_PBKDF2) && !defined(NO_SHA256)
   ret = pbkdf2_test();
   if (ret != 0)
      return ret;
#endif
#ifdef HAVE_PKCS12
   ret = pkcs12_test();
   if (ret != 0)
      return ret;
#endif
#ifdef HAVE_SCRYPT
   ret = scrypt_test();
   if (ret != 0)
      return ret;
#endif
   return ret;
}

#endif /* NO_PWDBASED */

#if defined(HAVE_HKDF) && (!defined(NO_SHA) || !defined(NO_SHA256))

int hkdf_test(void)
{
    int ret;
    int L = 42;
    byte okm1[42];
    byte ikm1[22] = { 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
                      0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
                      0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b };
    byte salt1[13] ={ 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
                      0x08, 0x09, 0x0a, 0x0b, 0x0c };
    byte info1[10] ={ 0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7,
                      0xf8, 0xf9 };
    byte res1[42] = { 0x0a, 0xc1, 0xaf, 0x70, 0x02, 0xb3, 0xd7, 0x61,
                      0xd1, 0xe5, 0x52, 0x98, 0xda, 0x9d, 0x05, 0x06,
                      0xb9, 0xae, 0x52, 0x05, 0x72, 0x20, 0xa3, 0x06,
                      0xe0, 0x7b, 0x6b, 0x87, 0xe8, 0xdf, 0x21, 0xd0,
                      0xea, 0x00, 0x03, 0x3d, 0xe0, 0x39, 0x84, 0xd3,
                      0x49, 0x18 };
    byte res2[42] = { 0x08, 0x5a, 0x01, 0xea, 0x1b, 0x10, 0xf3, 0x69,
                      0x33, 0x06, 0x8b, 0x56, 0xef, 0xa5, 0xad, 0x81,
                      0xa4, 0xf1, 0x4b, 0x82, 0x2f, 0x5b, 0x09, 0x15,
                      0x68, 0xa9, 0xcd, 0xd4, 0xf1, 0x55, 0xfd, 0xa2,
                      0xc2, 0x2e, 0x42, 0x24, 0x78, 0xd3, 0x05, 0xf3,
                      0xf8, 0x96 };
    byte res3[42] = { 0x8d, 0xa4, 0xe7, 0x75, 0xa5, 0x63, 0xc1, 0x8f,
                      0x71, 0x5f, 0x80, 0x2a, 0x06, 0x3c, 0x5a, 0x31,
                      0xb8, 0xa1, 0x1f, 0x5c, 0x5e, 0xe1, 0x87, 0x9e,
                      0xc3, 0x45, 0x4e, 0x5f, 0x3c, 0x73, 0x8d, 0x2d,
                      0x9d, 0x20, 0x13, 0x95, 0xfa, 0xa4, 0xb6, 0x1a,
                      0x96, 0xc8 };
    byte res4[42] = { 0x3c, 0xb2, 0x5f, 0x25, 0xfa, 0xac, 0xd5, 0x7a,
                      0x90, 0x43, 0x4f, 0x64, 0xd0, 0x36, 0x2f, 0x2a,
                      0x2d, 0x2d, 0x0a, 0x90, 0xcf, 0x1a, 0x5a, 0x4c,
                      0x5d, 0xb0, 0x2d, 0x56, 0xec, 0xc4, 0xc5, 0xbf,
                      0x34, 0x00, 0x72, 0x08, 0xd5, 0xb8, 0x87, 0x18,
                      0x58, 0x65 };

    (void)res1;
    (void)res2;
    (void)res3;
    (void)res4;
    (void)salt1;
    (void)info1;

#ifndef NO_SHA
    ret = wc_HKDF(WC_SHA, ikm1, 22, NULL, 0, NULL, 0, okm1, L);
    if (ret != 0)
        return -9500;

    if (XMEMCMP(okm1, res1, L) != 0)
        return -9501;

#ifndef HAVE_FIPS
    /* fips can't have key size under 14 bytes, salt is key too */
    ret = wc_HKDF(WC_SHA, ikm1, 11, salt1, 13, info1, 10, okm1, L);
    if (ret != 0)
        return -9502;

    if (XMEMCMP(okm1, res2, L) != 0)
        return -9503;
#endif /* HAVE_FIPS */
#endif /* NO_SHA */

#ifndef NO_SHA256
    ret = wc_HKDF(WC_SHA256, ikm1, 22, NULL, 0, NULL, 0, okm1, L);
    if (ret != 0)
        return -9504;

    if (XMEMCMP(okm1, res3, L) != 0)
        return -9505;

#ifndef HAVE_FIPS
    /* fips can't have key size under 14 bytes, salt is key too */
    ret = wc_HKDF(WC_SHA256, ikm1, 22, salt1, 13, info1, 10, okm1, L);
    if (ret != 0)
        return -9506;

    if (XMEMCMP(okm1, res4, L) != 0)
        return -9507;
#endif /* HAVE_FIPS */
#endif /* NO_SHA256 */

    return 0;
}

#endif /* HAVE_HKDF */


#if defined(HAVE_ECC) && defined(HAVE_X963_KDF)

int x963kdf_test(void)
{
    int ret;
    byte kek[128];

#ifndef NO_SHA
    /* SHA-1, COUNT = 0
     * shared secret length: 192
     * SharedInfo length: 0
     * key data length: 128
     */
    const byte Z[] = {
        0x1c, 0x7d, 0x7b, 0x5f, 0x05, 0x97, 0xb0, 0x3d,
        0x06, 0xa0, 0x18, 0x46, 0x6e, 0xd1, 0xa9, 0x3e,
        0x30, 0xed, 0x4b, 0x04, 0xdc, 0x64, 0xcc, 0xdd
    };

    const byte verify[] = {
        0xbf, 0x71, 0xdf, 0xfd, 0x8f, 0x4d, 0x99, 0x22,
        0x39, 0x36, 0xbe, 0xb4, 0x6f, 0xee, 0x8c, 0xcc
    };
#endif

#ifndef NO_SHA256
    /* SHA-256, COUNT = 3
     * shared secret length: 192
     * SharedInfo length: 0
     * key data length: 128
     */
    const byte Z2[] = {
        0xd3, 0x8b, 0xdb, 0xe5, 0xc4, 0xfc, 0x16, 0x4c,
        0xdd, 0x96, 0x7f, 0x63, 0xc0, 0x4f, 0xe0, 0x7b,
        0x60, 0xcd, 0xe8, 0x81, 0xc2, 0x46, 0x43, 0x8c
    };

    const byte verify2[] = {
        0x5e, 0x67, 0x4d, 0xb9, 0x71, 0xba, 0xc2, 0x0a,
        0x80, 0xba, 0xd0, 0xd4, 0x51, 0x4d, 0xc4, 0x84
    };
#endif

#ifdef WOLFSSL_SHA512
    /* SHA-512, COUNT = 0
     * shared secret length: 192
     * SharedInfo length: 0
     * key data length: 128
     */
    const byte Z3[] = {
        0x87, 0xfc, 0x0d, 0x8c, 0x44, 0x77, 0x48, 0x5b,
        0xb5, 0x74, 0xf5, 0xfc, 0xea, 0x26, 0x4b, 0x30,
        0x88, 0x5d, 0xc8, 0xd9, 0x0a, 0xd8, 0x27, 0x82
    };

    const byte verify3[] = {
        0x94, 0x76, 0x65, 0xfb, 0xb9, 0x15, 0x21, 0x53,
        0xef, 0x46, 0x02, 0x38, 0x50, 0x6a, 0x02, 0x45
    };

    /* SHA-512, COUNT = 0
     * shared secret length: 521
     * SharedInfo length: 128
     * key data length: 1024
     */
    const byte Z4[] = {
        0x00, 0xaa, 0x5b, 0xb7, 0x9b, 0x33, 0xe3, 0x89,
        0xfa, 0x58, 0xce, 0xad, 0xc0, 0x47, 0x19, 0x7f,
        0x14, 0xe7, 0x37, 0x12, 0xf4, 0x52, 0xca, 0xa9,
        0xfc, 0x4c, 0x9a, 0xdb, 0x36, 0x93, 0x48, 0xb8,
        0x15, 0x07, 0x39, 0x2f, 0x1a, 0x86, 0xdd, 0xfd,
        0xb7, 0xc4, 0xff, 0x82, 0x31, 0xc4, 0xbd, 0x0f,
        0x44, 0xe4, 0x4a, 0x1b, 0x55, 0xb1, 0x40, 0x47,
        0x47, 0xa9, 0xe2, 0xe7, 0x53, 0xf5, 0x5e, 0xf0,
        0x5a, 0x2d
    };

    const byte info4[] = {
        0xe3, 0xb5, 0xb4, 0xc1, 0xb0, 0xd5, 0xcf, 0x1d,
        0x2b, 0x3a, 0x2f, 0x99, 0x37, 0x89, 0x5d, 0x31
    };

    const byte verify4[] = {
        0x44, 0x63, 0xf8, 0x69, 0xf3, 0xcc, 0x18, 0x76,
        0x9b, 0x52, 0x26, 0x4b, 0x01, 0x12, 0xb5, 0x85,
        0x8f, 0x7a, 0xd3, 0x2a, 0x5a, 0x2d, 0x96, 0xd8,
        0xcf, 0xfa, 0xbf, 0x7f, 0xa7, 0x33, 0x63, 0x3d,
        0x6e, 0x4d, 0xd2, 0xa5, 0x99, 0xac, 0xce, 0xb3,
        0xea, 0x54, 0xa6, 0x21, 0x7c, 0xe0, 0xb5, 0x0e,
        0xef, 0x4f, 0x6b, 0x40, 0xa5, 0xc3, 0x02, 0x50,
        0xa5, 0xa8, 0xee, 0xee, 0x20, 0x80, 0x02, 0x26,
        0x70, 0x89, 0xdb, 0xf3, 0x51, 0xf3, 0xf5, 0x02,
        0x2a, 0xa9, 0x63, 0x8b, 0xf1, 0xee, 0x41, 0x9d,
        0xea, 0x9c, 0x4f, 0xf7, 0x45, 0xa2, 0x5a, 0xc2,
        0x7b, 0xda, 0x33, 0xca, 0x08, 0xbd, 0x56, 0xdd,
        0x1a, 0x59, 0xb4, 0x10, 0x6c, 0xf2, 0xdb, 0xbc,
        0x0a, 0xb2, 0xaa, 0x8e, 0x2e, 0xfa, 0x7b, 0x17,
        0x90, 0x2d, 0x34, 0x27, 0x69, 0x51, 0xce, 0xcc,
        0xab, 0x87, 0xf9, 0x66, 0x1c, 0x3e, 0x88, 0x16
    };
#endif

#ifndef NO_SHA
    ret = wc_X963_KDF(WC_HASH_TYPE_SHA, Z, sizeof(Z), NULL, 0,
                      kek, sizeof(verify));
    if (ret != 0)
        return -9600;

    if (XMEMCMP(verify, kek, sizeof(verify)) != 0)
        return -9601;
#endif

#ifndef NO_SHA256
    ret = wc_X963_KDF(WC_HASH_TYPE_SHA256, Z2, sizeof(Z2), NULL, 0,
                      kek, sizeof(verify2));
    if (ret != 0)
        return -9602;

    if (XMEMCMP(verify2, kek, sizeof(verify2)) != 0)
        return -9603;
#endif

#ifdef WOLFSSL_SHA512
    ret = wc_X963_KDF(WC_HASH_TYPE_SHA512, Z3, sizeof(Z3), NULL, 0,
                      kek, sizeof(verify3));
    if (ret != 0)
        return -9604;

    if (XMEMCMP(verify3, kek, sizeof(verify3)) != 0)
        return -9605;

    ret = wc_X963_KDF(WC_HASH_TYPE_SHA512, Z4, sizeof(Z4), info4,
                      sizeof(info4), kek, sizeof(verify4));
    if (ret != 0)
        return -9606;

    if (XMEMCMP(verify4, kek, sizeof(verify4)) != 0)
        return -9607;
#endif

    return 0;
}

#endif /* HAVE_X963_KDF */


#ifdef HAVE_ECC

/* size to use for ECC key gen tests */
#ifndef ECC_KEYGEN_SIZE
    #ifndef NO_ECC256
        #define ECC_KEYGEN_SIZE 32
    #elif defined(HAVE_ECC384)
        #define ECC_KEYGEN_SIZE 48
    #elif defined(HAVE_ECC224)
        #define ECC_KEYGEN_SIZE 28
    #else
        #error No ECC keygen size defined for test
    #endif
#endif
#ifdef BENCH_EMBEDDED
    #define ECC_SHARED_SIZE 128
#else
    #define ECC_SHARED_SIZE MAX_ECC_BYTES
#endif
#define ECC_DIGEST_SIZE     MAX_ECC_BYTES
#define ECC_SIG_SIZE        ECC_MAX_SIG_SIZE

#ifndef NO_ECC_VECTOR_TEST
    #if (defined(HAVE_ECC192) || defined(HAVE_ECC224) ||\
         !defined(NO_ECC256) || defined(HAVE_ECC384) ||\
         defined(HAVE_ECC521) || defined(HAVE_ALL_CURVES))
        #define HAVE_ECC_VECTOR_TEST
    #endif
#endif

#ifdef HAVE_ECC_VECTOR_TEST
typedef struct eccVector {
    const char* msg; /* SHA-1 Encoded Message */
    const char* Qx;
    const char* Qy;
    const char* d; /* Private Key */
    const char* R;
    const char* S;
    const char* curveName;
    word32 msgLen;
    word32 keySize;
#ifndef NO_ASN
    const byte* r;
    word32      rSz;
    const byte* s;
    word32      sSz;
#endif
} eccVector;

static int ecc_test_vector_item(const eccVector* vector)
{
    int ret = 0, verify = 0;
    word32  sigSz;
    ecc_key userA;
    DECLARE_VAR(sig, byte, ECC_SIG_SIZE, HEAP_HINT);
#if !defined(NO_ASN) && !defined(HAVE_SELFTEST)
    word32  sigRawSz;
    DECLARE_VAR(sigRaw, byte, ECC_SIG_SIZE, HEAP_HINT);
#endif

    ret = wc_ecc_init_ex(&userA, HEAP_HINT, devId);
    if (ret != 0) {
        FREE_VAR(sig, HEAP_HINT);
        return ret;
    }

    ret = wc_ecc_import_raw(&userA, vector->Qx, vector->Qy,
                                                  vector->d, vector->curveName);
    if (ret != 0)
        goto done;

    XMEMSET(sig, 0, ECC_SIG_SIZE);
    sigSz = ECC_SIG_SIZE;
    ret = wc_ecc_rs_to_sig(vector->R, vector->S, sig, &sigSz);
    if (ret != 0)
        goto done;

#if !defined(NO_ASN) && !defined(HAVE_SELFTEST)
    XMEMSET(sigRaw, 0, ECC_SIG_SIZE);
    sigRawSz = ECC_SIG_SIZE;
    ret = wc_ecc_rs_raw_to_sig(vector->r, vector->rSz, vector->s, vector->sSz,
                                                             sigRaw, &sigRawSz);
    if (ret != 0)
        goto done;

    if (sigSz != sigRawSz || XMEMCMP(sig, sigRaw, sigSz) != 0) {
        ret = -9608;
        goto done;
    }
#endif

    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &userA.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret == 0)
            ret = wc_ecc_verify_hash(sig, sigSz, (byte*)vector->msg,
                                               vector->msgLen, &verify, &userA);
    } while (ret == WC_PENDING_E);
    if (ret != 0)
        goto done;
    TEST_SLEEP();

    if (verify != 1)
        ret = -9609;

done:
    wc_ecc_free(&userA);

#if !defined(NO_ASN) && !defined(HAVE_SELFTEST)
    FREE_VAR(sigRaw, HEAP_HINT);
#endif
    FREE_VAR(sig, HEAP_HINT);

    return ret;
}

static int ecc_test_vector(int keySize)
{
    int     ret;
    eccVector vec;

    XMEMSET(&vec, 0, sizeof(vec));
    vec.keySize = (word32)keySize;

    switch(keySize) {

#if defined(HAVE_ECC112) || defined(HAVE_ALL_CURVES)
    case 14:
        return 0;
#endif /* HAVE_ECC112 */
#if defined(HAVE_ECC128) || defined(HAVE_ALL_CURVES)
    case 16:
        return 0;
#endif /* HAVE_ECC128 */
#if defined(HAVE_ECC160) || defined(HAVE_ALL_CURVES)
    case 20:
        return 0;
#endif /* HAVE_ECC160 */

#if defined(HAVE_ECC192) || defined(HAVE_ALL_CURVES)
    case 24:
        /* first [P-192,SHA-1] vector from FIPS 186-3 NIST vectors */
        #if 1
            vec.msg = "\x60\x80\x79\x42\x3f\x12\x42\x1d\xe6\x16\xb7\x49\x3e\xbe\x55\x1c\xf4\xd6\x5b\x92";
            vec.msgLen = 20;
        #else
            /* This is the raw message prior to SHA-1 */
            vec.msg =
                "\xeb\xf7\x48\xd7\x48\xeb\xbc\xa7\xd2\x9f\xb4\x73\x69\x8a\x6e\x6b"
                "\x4f\xb1\x0c\x86\x5d\x4a\xf0\x24\xcc\x39\xae\x3d\xf3\x46\x4b\xa4"
                "\xf1\xd6\xd4\x0f\x32\xbf\x96\x18\xa9\x1b\xb5\x98\x6f\xa1\xa2\xaf"
                "\x04\x8a\x0e\x14\xdc\x51\xe5\x26\x7e\xb0\x5e\x12\x7d\x68\x9d\x0a"
                "\xc6\xf1\xa7\xf1\x56\xce\x06\x63\x16\xb9\x71\xcc\x7a\x11\xd0\xfd"
                "\x7a\x20\x93\xe2\x7c\xf2\xd0\x87\x27\xa4\xe6\x74\x8c\xc3\x2f\xd5"
                "\x9c\x78\x10\xc5\xb9\x01\x9d\xf2\x1c\xdc\xc0\xbc\xa4\x32\xc0\xa3"
                "\xee\xd0\x78\x53\x87\x50\x88\x77\x11\x43\x59\xce\xe4\xa0\x71\xcf";
            vec.msgLen = 128;
        #endif
        vec.Qx  = "07008ea40b08dbe76432096e80a2494c94982d2d5bcf98e6";
        vec.Qy  = "76fab681d00b414ea636ba215de26d98c41bd7f2e4d65477";
        vec.d   = "e14f37b3d1374ff8b03f41b9b3fdd2f0ebccf275d660d7f3";
        vec.R   = "6994d962bdd0d793ffddf855ec5bf2f91a9698b46258a63e";
        vec.S   = "02ba6465a234903744ab02bc8521405b73cf5fc00e1a9f41";
        vec.curveName = "SECP192R1";
    #ifndef NO_ASN
        vec.r   = (byte*)"\x69\x94\xd9\x62\xbd\xd0\xd7\x93\xff\xdd\xf8\x55"
                         "\xec\x5b\xf2\xf9\x1a\x96\x98\xb4\x62\x58\xa6\x3e";
        vec.rSz = 24;
        vec.s   = (byte*)"\x02\xba\x64\x65\xa2\x34\x90\x37\x44\xab\x02\xbc"
                         "\x85\x21\x40\x5b\x73\xcf\x5f\xc0\x0e\x1a\x9f\x41";
        vec.sSz = 24;
    #endif
        break;
#endif /* HAVE_ECC192 */

#if defined(HAVE_ECC224) || defined(HAVE_ALL_CURVES)
    case 28:
        /* first [P-224,SHA-1] vector from FIPS 186-3 NIST vectors */
        #if 1
            vec.msg = "\xb9\xa3\xb8\x6d\xb0\xba\x99\xfd\xc6\xd2\x94\x6b\xfe\xbe\x9c\xe8\x3f\x10\x74\xfc";
            vec.msgLen = 20;
        #else
            /* This is the raw message prior to SHA-1 */
            vec.msg =
                "\x36\xc8\xb2\x29\x86\x48\x7f\x67\x7c\x18\xd0\x97\x2a\x9e\x20\x47"
                "\xb3\xaf\xa5\x9e\xc1\x62\x76\x4e\xc3\x0b\x5b\x69\xe0\x63\x0f\x99"
                "\x0d\x4e\x05\xc2\x73\xb0\xe5\xa9\xd4\x28\x27\xb6\x95\xfc\x2d\x64"
                "\xd9\x13\x8b\x1c\xf4\xc1\x21\x55\x89\x4c\x42\x13\x21\xa7\xbb\x97"
                "\x0b\xdc\xe0\xfb\xf0\xd2\xae\x85\x61\xaa\xd8\x71\x7f\x2e\x46\xdf"
                "\xe3\xff\x8d\xea\xb4\xd7\x93\x23\x56\x03\x2c\x15\x13\x0d\x59\x9e"
                "\x26\xc1\x0f\x2f\xec\x96\x30\x31\xac\x69\x38\xa1\x8d\x66\x45\x38"
                "\xb9\x4d\xac\x55\x34\xef\x7b\x59\x94\x24\xd6\x9b\xe1\xf7\x1c\x20";
            vec.msgLen = 128;
        #endif
        vec.Qx  = "8a4dca35136c4b70e588e23554637ae251077d1365a6ba5db9585de7";
        vec.Qy  = "ad3dee06de0be8279d4af435d7245f14f3b4f82eb578e519ee0057b1";
        vec.d   = "97c4b796e1639dd1035b708fc00dc7ba1682cec44a1002a1a820619f";
        vec.R   = "147b33758321e722a0360a4719738af848449e2c1d08defebc1671a7";
        vec.S   = "24fc7ed7f1352ca3872aa0916191289e2e04d454935d50fe6af3ad5b";
        vec.curveName = "SECP224R1";
    #ifndef NO_ASN
        vec.r   = (byte*)"\x14\x7b\x33\x75\x83\x21\xe7\x22\xa0\x36\x0a\x47"
                         "\x19\x73\x8a\xf8\x48\x44\x9e\x2c\x1d\x08\xde\xfe"
                         "\xbc\x16\x71\xa7";
        vec.rSz = 28;
        vec.s   = (byte*)"\x24\xfc\x7e\xd7\xf1\x35\x2c\xa3\x87\x2a\xa0\x91"
                         "\x61\x91\x28\x9e\x2e\x04\xd4\x54\x93\x5d\x50\xfe"
                         "\x6a\xf3\xad\x5b";
        vec.sSz = 28;
    #endif
        break;
#endif /* HAVE_ECC224 */

#if defined(HAVE_ECC239) || defined(HAVE_ALL_CURVES)
    case 30:
        return 0;
#endif /* HAVE_ECC239 */

#if !defined(NO_ECC256) || defined(HAVE_ALL_CURVES)
    case 32:
        /* first [P-256,SHA-1] vector from FIPS 186-3 NIST vectors */
        #if 1
            vec.msg = "\xa3\xf9\x1a\xe2\x1b\xa6\xb3\x03\x98\x64\x47\x2f\x18\x41\x44\xc6\xaf\x62\xcd\x0e";
            vec.msgLen = 20;
        #else
            /* This is the raw message prior to SHA-1 */
            vec.msg =
                "\xa2\x4b\x21\x76\x2e\x6e\xdb\x15\x3c\xc1\x14\x38\xdb\x0e\x92\xcd"
                "\xf5\x2b\x86\xb0\x6c\xa9\x70\x16\x06\x27\x59\xc7\x0d\x36\xd1\x56"
                "\x2c\xc9\x63\x0d\x7f\xc7\xc7\x74\xb2\x8b\x54\xe3\x1e\xf5\x58\x72"
                "\xb2\xa6\x5d\xf1\xd7\xec\x26\xde\xbb\x33\xe7\xd9\x27\xef\xcc\xf4"
                "\x6b\x63\xde\x52\xa4\xf4\x31\xea\xca\x59\xb0\x5d\x2e\xde\xc4\x84"
                "\x5f\xff\xc0\xee\x15\x03\x94\xd6\x1f\x3d\xfe\xcb\xcd\xbf\x6f\x5a"
                "\x73\x38\xd0\xbe\x3f\x2a\x77\x34\x51\x98\x3e\xba\xeb\x48\xf6\x73"
                "\x8f\xc8\x95\xdf\x35\x7e\x1a\x48\xa6\x53\xbb\x35\x5a\x31\xa1\xb4"
            vec.msgLen = 128;
        #endif
        vec.Qx  = "fa2737fb93488d19caef11ae7faf6b7f4bcd67b286e3fc54e8a65c2b74aeccb0";
        vec.Qy  = "d4ccd6dae698208aa8c3a6f39e45510d03be09b2f124bfc067856c324f9b4d09";
        vec.d   = "be34baa8d040a3b991f9075b56ba292f755b90e4b6dc10dad36715c33cfdac25";
        vec.R   = "2b826f5d44e2d0b6de531ad96b51e8f0c56fdfead3c236892e4d84eacfc3b75c";
        vec.S   = "a2248b62c03db35a7cd63e8a120a3521a89d3d2f61ff99035a2148ae32e3a248";
    #ifndef NO_ASN
        vec.r   = (byte*)"\x2b\x82\x6f\x5d\x44\xe2\xd0\xb6\xde\x53\x1a\xd9"
                         "\x6b\x51\xe8\xf0\xc5\x6f\xdf\xea\xd3\xc2\x36\x89"
                         "\x2e\x4d\x84\xea\xcf\xc3\xb7\x5c";
        vec.rSz = 32;
        vec.s   = (byte*)"\xa2\x24\x8b\x62\xc0\x3d\xb3\x5a\x7c\xd6\x3e\x8a"
                         "\x12\x0a\x35\x21\xa8\x9d\x3d\x2f\x61\xff\x99\x03"
                         "\x5a\x21\x48\xae\x32\xe3\xa2\x48";
        vec.sSz = 32;
    #endif
        vec.curveName = "SECP256R1";
        break;
#endif /* !NO_ECC256 */

#if defined(HAVE_ECC320) || defined(HAVE_ALL_CURVES)
    case 40:
        return 0;
#endif /* HAVE_ECC320 */

#if defined(HAVE_ECC384) || defined(HAVE_ALL_CURVES)
    case 48:
        /* first [P-384,SHA-1] vector from FIPS 186-3 NIST vectors */
        #if 1
            vec.msg = "\x9b\x9f\x8c\x95\x35\xa5\xca\x26\x60\x5d\xb7\xf2\xfa\x57\x3b\xdf\xc3\x2e\xab\x8b";
            vec.msgLen = 20;
        #else
            /* This is the raw message prior to SHA-1 */
            vec.msg =
                "\xab\xe1\x0a\xce\x13\xe7\xe1\xd9\x18\x6c\x48\xf7\x88\x9d\x51\x47"
                "\x3d\x3a\x09\x61\x98\x4b\xc8\x72\xdf\x70\x8e\xcc\x3e\xd3\xb8\x16"
                "\x9d\x01\xe3\xd9\x6f\xc4\xf1\xd5\xea\x00\xa0\x36\x92\xbc\xc5\xcf"
                "\xfd\x53\x78\x7c\x88\xb9\x34\xaf\x40\x4c\x03\x9d\x32\x89\xb5\xba"
                "\xc5\xae\x7d\xb1\x49\x68\x75\xb5\xdc\x73\xc3\x09\xf9\x25\xc1\x3d"
                "\x1c\x01\xab\xda\xaf\xeb\xcd\xac\x2c\xee\x43\x39\x39\xce\x8d\x4a"
                "\x0a\x5d\x57\xbb\x70\x5f\x3b\xf6\xec\x08\x47\x95\x11\xd4\xb4\xa3"
                "\x21\x1f\x61\x64\x9a\xd6\x27\x43\x14\xbf\x0d\x43\x8a\x81\xe0\x60"
            vec.msgLen = 128;
        #endif
        vec.Qx  = "e55fee6c49d8d523f5ce7bf9c0425ce4ff650708b7de5cfb095901523979a7f042602db30854735369813b5c3f5ef868";
        vec.Qy  = "28f59cc5dc509892a988d38a8e2519de3d0c4fd0fbdb0993e38f18506c17606c5e24249246f1ce94983a5361c5be983e";
        vec.d   = "a492ce8fa90084c227e1a32f7974d39e9ff67a7e8705ec3419b35fb607582bebd461e0b1520ac76ec2dd4e9b63ebae71";
        vec.R   = "6820b8585204648aed63bdff47f6d9acebdea62944774a7d14f0e14aa0b9a5b99545b2daee6b3c74ebf606667a3f39b7";
        vec.S   = "491af1d0cccd56ddd520b233775d0bc6b40a6255cc55207d8e9356741f23c96c14714221078dbd5c17f4fdd89b32a907";
        vec.curveName = "SECP384R1";
    #ifndef NO_ASN
        vec.r   = (byte*)"\x68\x20\xb8\x58\x52\x04\x64\x8a\xed\x63\xbd\xff"
                         "\x47\xf6\xd9\xac\xeb\xde\xa6\x29\x44\x77\x4a\x7d"
                         "\x14\xf0\xe1\x4a\xa0\xb9\xa5\xb9\x95\x45\xb2\xda"
                         "\xee\x6b\x3c\x74\xeb\xf6\x06\x66\x7a\x3f\x39\xb7";
        vec.rSz = 48;
        vec.s   = (byte*)"\x49\x1a\xf1\xd0\xcc\xcd\x56\xdd\xd5\x20\xb2\x33"
                         "\x77\x5d\x0b\xc6\xb4\x0a\x62\x55\xcc\x55\x20\x7d"
                         "\x8e\x93\x56\x74\x1f\x23\xc9\x6c\x14\x71\x42\x21"
                         "\x07\x8d\xbd\x5c\x17\xf4\xfd\xd8\x9b\x32\xa9\x07";
        vec.sSz = 48;
    #endif
        break;
#endif /* HAVE_ECC384 */

#if defined(HAVE_ECC512) || defined(HAVE_ALL_CURVES)
    case 64:
        return 0;
#endif /* HAVE_ECC512 */

#if defined(HAVE_ECC521) || defined(HAVE_ALL_CURVES)
    case 66:
        /* first [P-521,SHA-1] vector from FIPS 186-3 NIST vectors */
        #if 1
            vec.msg = "\x1b\xf7\x03\x9c\xca\x23\x94\x27\x3f\x11\xa1\xd4\x8d\xcc\xb4\x46\x6f\x31\x61\xdf";
            vec.msgLen = 20;
        #else
            /* This is the raw message prior to SHA-1 */
            vec.msg =
                "\x50\x3f\x79\x39\x34\x0a\xc7\x23\xcd\x4a\x2f\x4e\x6c\xcc\x27\x33"
                "\x38\x3a\xca\x2f\xba\x90\x02\x19\x9d\x9e\x1f\x94\x8b\xe0\x41\x21"
                "\x07\xa3\xfd\xd5\x14\xd9\x0c\xd4\xf3\x7c\xc3\xac\x62\xef\x00\x3a"
                "\x2d\xb1\xd9\x65\x7a\xb7\x7f\xe7\x55\xbf\x71\xfa\x59\xe4\xd9\x6e"
                "\xa7\x2a\xe7\xbf\x9d\xe8\x7d\x79\x34\x3b\xc1\xa4\xbb\x14\x4d\x16"
                "\x28\xd1\xe9\xe9\xc8\xed\x80\x8b\x96\x2c\x54\xe5\xf9\x6d\x53\xda"
                "\x14\x7a\x96\x38\xf9\x4a\x91\x75\xd8\xed\x61\x05\x5f\x0b\xa5\x73"
                "\xa8\x2b\xb7\xe0\x18\xee\xda\xc4\xea\x7b\x36\x2e\xc8\x9c\x38\x2b"
            vec.msgLen = 128;
        #endif
        vec.Qx  = "12fbcaeffa6a51f3ee4d3d2b51c5dec6d7c726ca353fc014ea2bf7cfbb9b910d32cbfa6a00fe39b6cdb8946f22775398b2e233c0cf144d78c8a7742b5c7a3bb5d23";
        vec.Qy  = "09cdef823dd7bf9a79e8cceacd2e4527c231d0ae5967af0958e931d7ddccf2805a3e618dc3039fec9febbd33052fe4c0fee98f033106064982d88f4e03549d4a64d";
        vec.d   = "1bd56bd106118eda246155bd43b42b8e13f0a6e25dd3bb376026fab4dc92b6157bc6dfec2d15dd3d0cf2a39aa68494042af48ba9601118da82c6f2108a3a203ad74";
        vec.R   = "0bd117b4807710898f9dd7778056485777668f0e78e6ddf5b000356121eb7a220e9493c7f9a57c077947f89ac45d5acb6661bbcd17abb3faea149ba0aa3bb1521be";
        vec.S   = "019cd2c5c3f9870ecdeb9b323abdf3a98cd5e231d85c6ddc5b71ab190739f7f226e6b134ba1d5889ddeb2751dabd97911dff90c34684cdbe7bb669b6c3d22f2480c";
        vec.curveName = "SECP521R1";
    #ifndef NO_ASN
        vec.r   = (byte*)"\x00\xbd\x11\x7b\x48\x07\x71\x08\x98\xf9\xdd\x77"
                         "\x78\x05\x64\x85\x77\x76\x68\xf0\xe7\x8e\x6d\xdf"
                         "\x5b\x00\x03\x56\x12\x1e\xb7\xa2\x20\xe9\x49\x3c"
                         "\x7f\x9a\x57\xc0\x77\x94\x7f\x89\xac\x45\xd5\xac"
                         "\xb6\x66\x1b\xbc\xd1\x7a\xbb\x3f\xae\xa1\x49\xba"
                         "\x0a\xa3\xbb\x15\x21\xbe";
        vec.rSz = 66;
        vec.s   = (byte*)"\x00\x19\xcd\x2c\x5c\x3f\x98\x70\xec\xde\xb9\xb3"
                         "\x23\xab\xdf\x3a\x98\xcd\x5e\x23\x1d\x85\xc6\xdd"
                         "\xc5\xb7\x1a\xb1\x90\x73\x9f\x7f\x22\x6e\x6b\x13"
                         "\x4b\xa1\xd5\x88\x9d\xde\xb2\x75\x1d\xab\xd9\x79"
                         "\x11\xdf\xf9\x0c\x34\x68\x4c\xdb\xe7\xbb\x66\x9b"
                         "\x6c\x3d\x22\xf2\x48\x0c";
        vec.sSz = 66;
    #endif
        break;
#endif /* HAVE_ECC521 */
    default:
        return NOT_COMPILED_IN; /* Invalid key size / Not supported */
    }; /* Switch */

    ret = ecc_test_vector_item(&vec);
    if (ret < 0) {
        return ret;
    }

    return 0;
}

#if defined(HAVE_ECC_SIGN) && defined(WOLFSSL_ECDSA_SET_K)
static int ecc_test_sign_vectors(WC_RNG* rng)
{
    int ret;
    ecc_key key;
    byte sig[72];
    word32 sigSz;
    unsigned char hash[32] = "test wolfSSL deterministic sign";
    const char* dIUT =   "7d7dc5f71eb29ddaf80d6214632eeae03d9058af1fb6d22ed80badb62bc1a534";
    const char* QIUTx =  "ead218590119e8876b29146ff89ca61770c4edbbf97d38ce385ed281d8a6b230";
    const char* QIUTy =  "28af61281fd35e2fa7002523acc85a429cb06ee6648325389f59edfce1405141";
    const byte k[1] = { 0x02 };
    const byte expSig[71] = {
        0x30, 0x45, 0x02, 0x20, 0x7c, 0xf2, 0x7b, 0x18,
        0x8d, 0x03, 0x4f, 0x7e, 0x8a, 0x52, 0x38, 0x03,
        0x04, 0xb5, 0x1a, 0xc3, 0xc0, 0x89, 0x69, 0xe2,
        0x77, 0xf2, 0x1b, 0x35, 0xa6, 0x0b, 0x48, 0xfc,
        0x47, 0x66, 0x99, 0x78, 0x02, 0x21, 0x00, 0xa8,
        0x43, 0xa0, 0xce, 0x6c, 0x5e, 0x17, 0x8a, 0x53,
        0x4d, 0xaf, 0xd2, 0x95, 0x78, 0x9f, 0x84, 0x4f,
        0x94, 0xb8, 0x75, 0xa3, 0x19, 0xa5, 0xd4, 0xdf,
        0xe1, 0xd4, 0x5e, 0x9d, 0x97, 0xfe, 0x81
    };

    ret = wc_ecc_init_ex(&key, HEAP_HINT, devId);
    if (ret != 0) {
        return ret;
    }
    ret = wc_ecc_import_raw(&key, QIUTx, QIUTy, dIUT, "SECP256R1");
    if (ret != 0) {
        goto done;
    }

    ret = wc_ecc_sign_set_k(k, sizeof(k), &key);
    if (ret != 0) {
        goto done;
    }

    sigSz = sizeof(sig);
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret == 0)
            ret = wc_ecc_sign_hash(hash, sizeof(hash), sig, &sigSz, rng, &key);
    } while (ret == WC_PENDING_E);
    if (ret != 0) {
        goto done;
    }
    TEST_SLEEP();

    if (sigSz != sizeof(expSig)) {
        ret = -9610;
        goto done;
    }
    if (XMEMCMP(sig, expSig, sigSz) != 0) {
        ret = -9611;
        goto done;
    }

    sigSz = sizeof(sig);
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret == 0)
            ret = wc_ecc_sign_hash(hash, sizeof(hash), sig, &sigSz, rng, &key);
    } while (ret == WC_PENDING_E);
    if (ret != 0) {
        goto done;
    }
    TEST_SLEEP();

done:
    wc_ecc_free(&key);
    return ret;
}
#endif

#ifdef HAVE_ECC_CDH
static int ecc_test_cdh_vectors(WC_RNG* rng)
{
    int ret;
    ecc_key pub_key, priv_key;
    byte    sharedA[32] = {0}, sharedB[32] = {0};
    word32  x, z;

    const char* QCAVSx = "700c48f77f56584c5cc632ca65640db91b6bacce3a4df6b42ce7cc838833d287";
    const char* QCAVSy = "db71e509e3fd9b060ddb20ba5c51dcc5948d46fbf640dfe0441782cab85fa4ac";
    const char* dIUT =   "7d7dc5f71eb29ddaf80d6214632eeae03d9058af1fb6d22ed80badb62bc1a534";
    const char* QIUTx =  "ead218590119e8876b29146ff89ca61770c4edbbf97d38ce385ed281d8a6b230";
    const char* QIUTy =  "28af61281fd35e2fa7002523acc85a429cb06ee6648325389f59edfce1405141";
    const char* ZIUT =   "46fc62106420ff012e54a434fbdd2d25ccc5852060561e68040dd7778997bd7b";

    /* setup private and public keys */
    ret = wc_ecc_init_ex(&pub_key, HEAP_HINT, devId);
    if (ret != 0)
        return ret;
    ret = wc_ecc_init_ex(&priv_key, HEAP_HINT, devId);
    if (ret != 0) {
        wc_ecc_free(&pub_key);
        return ret;
    }
    wc_ecc_set_flags(&pub_key, WC_ECC_FLAG_COFACTOR);
    wc_ecc_set_flags(&priv_key, WC_ECC_FLAG_COFACTOR);
    ret = wc_ecc_import_raw(&pub_key, QCAVSx, QCAVSy, NULL, "SECP256R1");
    if (ret != 0)
        goto done;
    ret = wc_ecc_import_raw(&priv_key, QIUTx, QIUTy, dIUT, "SECP256R1");
    if (ret != 0)
        goto done;

#if defined(ECC_TIMING_RESISTANT) && (!defined(HAVE_FIPS) || \
    (!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION != 2))) && \
    !defined(HAVE_SELFTEST)
    ret = wc_ecc_set_rng(&priv_key, rng);
    if (ret != 0)
        goto done;
#else
    (void)rng;
#endif

    /* compute ECC Cofactor shared secret */
    x = sizeof(sharedA);
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &priv_key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret == 0)
            ret = wc_ecc_shared_secret(&priv_key, &pub_key, sharedA, &x);
    } while (ret == WC_PENDING_E);
    if (ret != 0) {
        goto done;
    }
    TEST_SLEEP();

    /* read in expected Z */
    z = sizeof(sharedB);
    ret = Base16_Decode((const byte*)ZIUT, (word32)XSTRLEN(ZIUT), sharedB, &z);
    if (ret != 0)
        goto done;

    /* compare results */
    if (x != z || XMEMCMP(sharedA, sharedB, x)) {
        ERROR_OUT(-9612, done);
    }

done:
    wc_ecc_free(&priv_key);
    wc_ecc_free(&pub_key);
    return ret;
}
#endif /* HAVE_ECC_CDH */
#endif /* HAVE_ECC_VECTOR_TEST */

#ifdef HAVE_ECC_KEY_IMPORT
/* returns 0 on success */
static int ecc_test_make_pub(WC_RNG* rng)
{
    ecc_key key;
    byte exportBuf[ECC_BUFSIZE];
    byte tmp[ECC_BUFSIZE];
    const byte* msg = (const byte*)"test wolfSSL ECC public gen";
    word32 x, tmpSz;
    int ret = 0;
    ecc_point* pubPoint = NULL;
#if defined(HAVE_ECC_DHE) && defined(HAVE_ECC_KEY_EXPORT)
    ecc_key pub;
#endif
#ifdef HAVE_ECC_VERIFY
    int verify = 0;
#endif
#ifndef USE_CERT_BUFFERS_256
    XFILE file;
#endif

    wc_ecc_init_ex(&key, HEAP_HINT, devId);

#ifndef NO_ECC256
#ifdef USE_CERT_BUFFERS_256
    XMEMCPY(tmp, ecc_key_der_256, (size_t)sizeof_ecc_key_der_256);
    tmpSz = (size_t)sizeof_ecc_key_der_256;
#else
    file = XFOPEN(eccKeyDerFile, "rb");
    if (!file) {
        ERROR_OUT(-9617, done);
    }

    tmpSz = (word32)XFREAD(tmp, 1, sizeof(tmp), file);
    XFCLOSE(file);
#endif /* USE_CERT_BUFFERS_256 */

    /* import private only then test with */
    ret = wc_ecc_import_private_key(tmp, tmpSz, NULL, 0, NULL);
    if (ret == 0) {
        ERROR_OUT(-9618, done);
    }

    ret = wc_ecc_import_private_key(NULL, tmpSz, NULL, 0, &key);
    if (ret == 0) {
        ERROR_OUT(-9619, done);
    }

    x = 0;
    ret = wc_EccPrivateKeyDecode(tmp, &x, &key, tmpSz);
    if (ret != 0) {
        ERROR_OUT(-9620, done);
    }

#ifdef HAVE_ECC_KEY_EXPORT
    x = sizeof(exportBuf);
    ret = wc_ecc_export_private_only(&key, exportBuf, &x);
    if (ret != 0) {
        ERROR_OUT(-9621, done);
    }

    /* make private only key */
    wc_ecc_free(&key);
    wc_ecc_init_ex(&key, HEAP_HINT, devId);
    ret = wc_ecc_import_private_key(exportBuf, x, NULL, 0, &key);
    if (ret != 0) {
        ERROR_OUT(-9622, done);
    }

    x = sizeof(exportBuf);
    ret = wc_ecc_export_x963_ex(&key, exportBuf, &x, 0);
    if (ret == 0) {
        ERROR_OUT(-9623, done);
    }

#endif /* HAVE_ECC_KEY_EXPORT */

    ret = wc_ecc_make_pub(NULL, NULL);
    if (ret == 0) {
        ERROR_OUT(-9624, done);
    }
    TEST_SLEEP();

    pubPoint = wc_ecc_new_point_h(HEAP_HINT);
    if (pubPoint == NULL) {
        ERROR_OUT(-9625, done);
    }

    ret = wc_ecc_make_pub(&key, pubPoint);
    if (ret != 0) {
        ERROR_OUT(-9626, done);
    }

    TEST_SLEEP();

#ifdef HAVE_ECC_KEY_EXPORT
    /* export should still fail, is private only key */
    x = sizeof(exportBuf);
    ret = wc_ecc_export_x963_ex(&key, exportBuf, &x, 0);
    if (ret == 0) {
        ERROR_OUT(-9627, done);
    }
#endif /* HAVE_ECC_KEY_EXPORT */
#endif /* !NO_ECC256 */

    /* create a new key since above test for loading key is not supported */
#if defined(WOLFSSL_CRYPTOCELL) || defined(NO_ECC256)
    ret  = wc_ecc_make_key(rng, ECC_KEYGEN_SIZE, &key);
    if (ret != 0) {
        ERROR_OUT(-9628, done);
    }
#endif

#ifdef HAVE_ECC_SIGN
    tmpSz = sizeof(tmp);
    ret = 0;
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret == 0)
            ret = wc_ecc_sign_hash(msg, (word32)XSTRLEN((const char* )msg), tmp, &tmpSz, rng, &key);
    } while (ret == WC_PENDING_E);
    if (ret != 0) {
        ERROR_OUT(-9629, done);
    }
    TEST_SLEEP();

#ifdef HAVE_ECC_VERIFY
    /* try verify with private only key */
    ret = 0;
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret == 0)
            ret = wc_ecc_verify_hash(tmp, tmpSz, msg, (word32)XSTRLEN((const char* )msg), &verify, &key);
    } while (ret == WC_PENDING_E);
    if (ret != 0) {
        ERROR_OUT(-9630, done);
    }

    if (verify != 1) {
        ERROR_OUT(-9631, done);
    }
    TEST_SLEEP();
#ifdef HAVE_ECC_KEY_EXPORT
    /* exporting the public part should now work */
    x = sizeof(exportBuf);
    ret = wc_ecc_export_x963_ex(&key, exportBuf, &x, 0);
    if (ret != 0) {
        ERROR_OUT(-9632, done);
    }
#endif /* HAVE_ECC_KEY_EXPORT */
#endif /* HAVE_ECC_VERIFY */

#endif /* HAVE_ECC_SIGN */

#if defined(HAVE_ECC_DHE) && defined(HAVE_ECC_KEY_EXPORT)
    /* now test private only key with creating a shared secret */
    x = sizeof(exportBuf);
    ret = wc_ecc_export_private_only(&key, exportBuf, &x);
    if (ret != 0) {
        ERROR_OUT(-9633, done);
    }

    /* make private only key */
    wc_ecc_free(&key);
    wc_ecc_init_ex(&key, HEAP_HINT, devId);
    ret = wc_ecc_import_private_key(exportBuf, x, NULL, 0, &key);
    if (ret != 0) {
        ERROR_OUT(-9634, done);
    }

    /* check that public export fails with private only key */
    x = sizeof(exportBuf);
    ret = wc_ecc_export_x963_ex(&key, exportBuf, &x, 0);
    if (ret == 0) {
        ERROR_OUT(-9635, done);
    }

    /* make public key for shared secret */
    wc_ecc_init_ex(&pub, HEAP_HINT, devId);
    ret = wc_ecc_make_key(rng, ECC_KEYGEN_SIZE, &pub);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &pub.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0) {
        ERROR_OUT(-9636, done);
    }
    TEST_SLEEP();

#if defined(ECC_TIMING_RESISTANT) && (!defined(HAVE_FIPS) || \
    (!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION != 2))) && \
    !defined(HAVE_SELFTEST)
    ret = wc_ecc_set_rng(&key, rng);
    if (ret != 0)
        goto done;
#endif

    x = sizeof(exportBuf);
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret == 0) {
            ret = wc_ecc_shared_secret(&key, &pub, exportBuf, &x);
        }
    } while (ret == WC_PENDING_E);
    wc_ecc_free(&pub);
    if (ret != 0) {
        ERROR_OUT(-9637, done);
    }
    TEST_SLEEP();
#endif /* HAVE_ECC_DHE && HAVE_ECC_KEY_EXPORT */

    ret = 0;

done:

    wc_ecc_del_point_h(pubPoint, HEAP_HINT);
    wc_ecc_free(&key);

    return ret;
}

static int ecc_test_key_decode(WC_RNG* rng, int keySize)
{
    int ret;
    ecc_key eccKey;
    byte tmpBuf[ECC_BUFSIZE];
    word32 tmpSz;
    word32 idx;

    ret = wc_ecc_init(&eccKey);
    if (ret != 0) {
        return ret;
    }
    ret = wc_ecc_make_key(rng, keySize, &eccKey);
    if (ret != 0) {
        wc_ecc_free(&eccKey);
        return ret;
    }

    tmpSz = sizeof(tmpBuf);
    ret = wc_EccKeyToDer(&eccKey, tmpBuf, tmpSz);
    wc_ecc_free(&eccKey);
    if (ret < 0) {
        return ret;
    }
    tmpSz = ret;

    ret = wc_ecc_init(&eccKey);
    if (ret != 0) {
        return ret;
    }
    idx = 0;
    ret = wc_EccPrivateKeyDecode(tmpBuf, &idx, &eccKey, tmpSz);
    wc_ecc_free(&eccKey);
    if (ret != 0) {
        return ret;
    }

    ret = wc_ecc_init(&eccKey);
    if (ret != 0) {
        return 0;
    }

    idx = 0;
    ret = wc_EccPublicKeyDecode(tmpBuf, &idx, &eccKey, tmpSz);
    wc_ecc_free(&eccKey);

    return ret;
}
#endif /* HAVE_ECC_KEY_IMPORT */

static int ecc_test_key_gen(WC_RNG* rng, int keySize)
{
    int    ret = 0;
    int    derSz;
#ifdef HAVE_PKCS8
    word32 pkcs8Sz;
#endif
    byte der[ECC_BUFSIZE];
    ecc_key userA;

    ret = wc_ecc_init_ex(&userA, HEAP_HINT, devId);
    if (ret != 0)
        goto done;

    ret = wc_ecc_make_key(rng, keySize, &userA);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &userA.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        goto done;
    TEST_SLEEP();

    ret = wc_ecc_check_key(&userA);
    if (ret != 0)
        goto done;
    TEST_SLEEP();

    derSz = wc_EccKeyToDer(&userA, der, sizeof(der));
    if (derSz < 0) {
        ERROR_OUT(derSz, done);
    }

    ret = SaveDerAndPem(der, derSz, eccCaKeyTempFile, eccCaKeyPemFile,
        ECC_PRIVATEKEY_TYPE, -8347);
    if (ret != 0) {
        goto done;
    }

    /* test export of public key */
    derSz = wc_EccPublicKeyToDer(&userA, der, sizeof(der), 1);
    if (derSz < 0) {
        ERROR_OUT(derSz, done);
    }
    if (derSz == 0) {
        ERROR_OUT(-9640, done);
    }

    ret = SaveDerAndPem(der, derSz, eccPubKeyDerFile, NULL, 0, -8348);
    if (ret != 0) {
        goto done;
    }

#ifdef HAVE_PKCS8
    /* test export of PKCS#8 unencrypted private key */
    pkcs8Sz = FOURK_BUF;
    derSz = wc_EccPrivateKeyToPKCS8(&userA, der, &pkcs8Sz);
    if (derSz < 0) {
        ERROR_OUT(derSz, done);
    }

    if (derSz == 0) {
        ERROR_OUT(-9641, done);
    }

    ret = SaveDerAndPem(der, derSz, eccPkcs8KeyDerFile, NULL, 0, -8349);
    if (ret != 0) {
        goto done;
    }
#endif /* HAVE_PKCS8 */

done:

    wc_ecc_free(&userA);

    return ret;
}

static int ecc_test_curve_size(WC_RNG* rng, int keySize, int testVerifyCount,
    int curve_id, const ecc_set_type* dp)
{
#if (defined(HAVE_ECC_DHE) || defined(HAVE_ECC_CDH)) && \
    !defined(WOLFSSL_ATECC508A) && !defined(WOLFSSL_ATECC608A)
    DECLARE_VAR(sharedA, byte, ECC_SHARED_SIZE, HEAP_HINT);
    DECLARE_VAR(sharedB, byte, ECC_SHARED_SIZE, HEAP_HINT);
#endif
#ifdef HAVE_ECC_KEY_EXPORT
    byte    exportBuf[MAX_ECC_BYTES * 2 + 32];
#endif
    word32  x = 0;
#if (defined(HAVE_ECC_DHE) || defined(HAVE_ECC_CDH)) && \
    !defined(WOLFSSL_ATECC508A) && !defined(WOLFSSL_ATECC608A)
    word32  y;
#endif
#ifdef HAVE_ECC_SIGN
    DECLARE_VAR(sig, byte, ECC_SIG_SIZE, HEAP_HINT);
    DECLARE_VAR(digest, byte, ECC_DIGEST_SIZE, HEAP_HINT);
    int     i;
#ifdef HAVE_ECC_VERIFY
    int     verify;
#endif /* HAVE_ECC_VERIFY */
#endif /* HAVE_ECC_SIGN */
    int     ret;
    ecc_key userA, userB, pubKey;
    int     curveSize;

    (void)testVerifyCount;
    (void)dp;
    (void)x;

    XMEMSET(&userA, 0, sizeof(ecc_key));
    XMEMSET(&userB, 0, sizeof(ecc_key));
    XMEMSET(&pubKey, 0, sizeof(ecc_key));

    ret = wc_ecc_init_ex(&userA, HEAP_HINT, devId);
    if (ret != 0)
        goto done;
    ret = wc_ecc_init_ex(&userB, HEAP_HINT, devId);
    if (ret != 0)
        goto done;
    ret = wc_ecc_init_ex(&pubKey, HEAP_HINT, devId);
    if (ret != 0)
        goto done;

#ifdef WOLFSSL_CUSTOM_CURVES
    if (dp != NULL) {
        ret = wc_ecc_set_custom_curve(&userA, dp);
        if (ret != 0)
            goto done;
        ret = wc_ecc_set_custom_curve(&userB, dp);
        if (ret != 0)
            goto done;
    }
#endif

    ret = wc_ecc_make_key_ex(rng, keySize, &userA, curve_id);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &userA.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        goto done;
    TEST_SLEEP();

    if (wc_ecc_get_curve_idx(curve_id) != -1) {
        curveSize = wc_ecc_get_curve_size_from_id(userA.dp->id);
        if (curveSize != userA.dp->size) {
            ret = -9642;
            goto done;
        }
    }

    ret = wc_ecc_check_key(&userA);
    if (ret != 0)
        goto done;
    TEST_SLEEP();

/* ATECC508/608 configuration may not support more than one ECDH key */
#if !defined(WOLFSSL_ATECC508A) && !defined(WOLFSSL_ATECC608A)

    ret = wc_ecc_make_key_ex(rng, keySize, &userB, curve_id);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &userB.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0)
        goto done;
    TEST_SLEEP();

    /* only perform the below tests if the key size matches */
    if (dp == NULL && keySize > 0 && wc_ecc_size(&userA) != keySize) {
        ret = ECC_CURVE_OID_E;
        goto done;
    }

#ifdef HAVE_ECC_DHE
#if defined(ECC_TIMING_RESISTANT) && (!defined(HAVE_FIPS) || \
    (!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION != 2))) && \
    !defined(HAVE_SELFTEST)
    ret = wc_ecc_set_rng(&userA, rng);
    if (ret != 0)
        goto done;
    ret = wc_ecc_set_rng(&userB, rng);
    if (ret != 0)
        goto done;
#endif

    x = ECC_SHARED_SIZE;
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &userA.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret == 0)
            ret = wc_ecc_shared_secret(&userA, &userB, sharedA, &x);
    } while (ret == WC_PENDING_E);
    if (ret != 0) {
        goto done;
    }
    TEST_SLEEP();

    y = ECC_SHARED_SIZE;
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &userB.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret == 0)
            ret = wc_ecc_shared_secret(&userB, &userA, sharedB, &y);
    } while (ret == WC_PENDING_E);
    if (ret != 0)
        goto done;

    if (y != x)
        ERROR_OUT(-9643, done);

    if (XMEMCMP(sharedA, sharedB, x))
        ERROR_OUT(-9644, done);
    TEST_SLEEP();
#endif /* HAVE_ECC_DHE */

#ifdef HAVE_ECC_CDH
    /* add cofactor flag */
    wc_ecc_set_flags(&userA, WC_ECC_FLAG_COFACTOR);
    wc_ecc_set_flags(&userB, WC_ECC_FLAG_COFACTOR);

    x = ECC_SHARED_SIZE;
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &userA.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret == 0)
            ret = wc_ecc_shared_secret(&userA, &userB, sharedA, &x);
    } while (ret == WC_PENDING_E);
    if (ret != 0) {
        goto done;
    }
    TEST_SLEEP();

    y = ECC_SHARED_SIZE;
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &userB.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret == 0)
            ret = wc_ecc_shared_secret(&userB, &userA, sharedB, &y);
    } while (ret == WC_PENDING_E);
    if (ret != 0)
        goto done;

    if (y != x)
        ERROR_OUT(-9645, done);

    if (XMEMCMP(sharedA, sharedB, x))
        ERROR_OUT(-9646, done);
    TEST_SLEEP();

    /* remove cofactor flag */
    wc_ecc_set_flags(&userA, 0);
    wc_ecc_set_flags(&userB, 0);
#endif /* HAVE_ECC_CDH */
#endif /* WOLFSSL_ATECC508A */

#ifdef HAVE_ECC_KEY_EXPORT
    x = sizeof(exportBuf);
    ret = wc_ecc_export_x963_ex(&userA, exportBuf, &x, 0);
    if (ret != 0)
        goto done;

#ifdef HAVE_ECC_KEY_IMPORT
    #ifdef WOLFSSL_CUSTOM_CURVES
        if (dp != NULL) {
            ret = wc_ecc_set_custom_curve(&pubKey, dp);
            if (ret != 0) goto done;
        }
    #endif
    ret = wc_ecc_import_x963_ex(exportBuf, x, &pubKey, curve_id);
    if (ret != 0)
        goto done;

#if !defined(WOLFSSL_ATECC508A) && !defined(WOLFSSL_ATECC608A)
#ifdef HAVE_ECC_DHE
    y = ECC_SHARED_SIZE;
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &userB.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret == 0)
            ret = wc_ecc_shared_secret(&userB, &pubKey, sharedB, &y);
    } while (ret == WC_PENDING_E);
    if (ret != 0)
        goto done;

    if (XMEMCMP(sharedA, sharedB, y))
        ERROR_OUT(-9647, done);
    TEST_SLEEP();
#endif /* HAVE_ECC_DHE */

    #ifdef HAVE_COMP_KEY
        /* try compressed export / import too */
        x = sizeof(exportBuf);
        ret = wc_ecc_export_x963_ex(&userA, exportBuf, &x, 1);
        if (ret != 0)
            goto done;
        wc_ecc_free(&pubKey);

        ret = wc_ecc_init_ex(&pubKey, HEAP_HINT, devId);
        if (ret != 0)
            goto done;
    #ifdef WOLFSSL_CUSTOM_CURVES
        if (dp != NULL) {
            ret = wc_ecc_set_custom_curve(&pubKey, dp);
            if (ret != 0) goto done;
        }
    #endif
        ret = wc_ecc_import_x963_ex(exportBuf, x, &pubKey, curve_id);
        if (ret != 0)
            goto done;

    #ifdef HAVE_ECC_DHE
        y = ECC_SHARED_SIZE;
        do {
        #if defined(WOLFSSL_ASYNC_CRYPT)
            ret = wc_AsyncWait(ret, &userB.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
        #endif
            if (ret == 0)
                ret = wc_ecc_shared_secret(&userB, &pubKey, sharedB, &y);
        } while (ret == WC_PENDING_E);
        if (ret != 0)
            goto done;

        if (XMEMCMP(sharedA, sharedB, y))
            ERROR_OUT(-9648, done);
        TEST_SLEEP();
    #endif /* HAVE_ECC_DHE */
    #endif /* HAVE_COMP_KEY */
#endif /* WOLFSSL_ATECC508A */

#endif /* HAVE_ECC_KEY_IMPORT */
#endif /* HAVE_ECC_KEY_EXPORT */

#ifdef HAVE_ECC_SIGN
    /* ECC w/out Shamir has issue with all 0 digest */
    /* WC_BIGINT doesn't have 0 len well on hardware */
#if defined(ECC_SHAMIR) && !defined(WOLFSSL_ASYNC_CRYPT)
    /* test DSA sign hash with zeros */
    for (i = 0; i < (int)ECC_DIGEST_SIZE; i++) {
        digest[i] = 0;
    }

    x = ECC_SIG_SIZE;
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &userA.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret == 0)
            ret = wc_ecc_sign_hash(digest, ECC_DIGEST_SIZE, sig, &x, rng,
                                                                        &userA);
    } while (ret == WC_PENDING_E);
    if (ret != 0)
        goto done;
    TEST_SLEEP();

#ifdef HAVE_ECC_VERIFY
    for (i=0; i<testVerifyCount; i++) {
        verify = 0;
        do {
        #if defined(WOLFSSL_ASYNC_CRYPT)
            ret = wc_AsyncWait(ret, &userA.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
        #endif
            if (ret == 0)
                ret = wc_ecc_verify_hash(sig, x, digest, ECC_DIGEST_SIZE,
                                                               &verify, &userA);
        } while (ret == WC_PENDING_E);
        if (ret != 0)
            goto done;
        if (verify != 1)
            ERROR_OUT(-9649, done);
        TEST_SLEEP();
    }
#endif /* HAVE_ECC_VERIFY */
#endif /* ECC_SHAMIR && !WOLFSSL_ASYNC_CRYPT */

    /* test DSA sign hash with sequence (0,1,2,3,4,...) */
    for (i = 0; i < (int)ECC_DIGEST_SIZE; i++) {
        digest[i] = (byte)i;
    }

    x = ECC_SIG_SIZE;
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &userA.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret == 0)
            ret = wc_ecc_sign_hash(digest, ECC_DIGEST_SIZE, sig, &x, rng,
                                                                        &userA);
    } while (ret == WC_PENDING_E);
    if (ret != 0)
        ERROR_OUT(-9650, done);
    TEST_SLEEP();

#ifdef HAVE_ECC_VERIFY
    for (i=0; i<testVerifyCount; i++) {
        verify = 0;
        do {
        #if defined(WOLFSSL_ASYNC_CRYPT)
            ret = wc_AsyncWait(ret, &userA.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
        #endif
            if (ret == 0)
                ret = wc_ecc_verify_hash(sig, x, digest, ECC_DIGEST_SIZE,
                                                               &verify, &userA);
        } while (ret == WC_PENDING_E);
        if (ret != 0)
            goto done;
        if (verify != 1)
            ERROR_OUT(-9651, done);
        TEST_SLEEP();
    }
#endif /* HAVE_ECC_VERIFY */
#endif /* HAVE_ECC_SIGN */

#if defined(HAVE_ECC_KEY_EXPORT) && !defined(WOLFSSL_ATECC508) && \
    !defined(WOLFSSL_ATECC608A)
    x = sizeof(exportBuf);
    ret = wc_ecc_export_private_only(&userA, exportBuf, &x);
    if (ret != 0)
        goto done;
#endif /* HAVE_ECC_KEY_EXPORT */

done:
    wc_ecc_free(&pubKey);
    wc_ecc_free(&userB);
    wc_ecc_free(&userA);

#if defined(HAVE_ECC_DHE) || defined(HAVE_ECC_CDH)
    FREE_VAR(sharedA, HEAP_HINT);
    FREE_VAR(sharedB, HEAP_HINT);
#endif
#ifdef HAVE_ECC_SIGN
    FREE_VAR(sig, HEAP_HINT);
    FREE_VAR(digest, HEAP_HINT);
#endif

    return ret;
}

#undef  ECC_TEST_VERIFY_COUNT
#define ECC_TEST_VERIFY_COUNT 2
static int ecc_test_curve(WC_RNG* rng, int keySize)
{
    int ret;

    ret = ecc_test_curve_size(rng, keySize, ECC_TEST_VERIFY_COUNT,
        ECC_CURVE_DEF, NULL);
    if (ret < 0) {
        if (ret == ECC_CURVE_OID_E) {
            /* ignore error for curves not found */
            /* some curve sizes are only available with:
                HAVE_ECC_SECPR2, HAVE_ECC_SECPR3, HAVE_ECC_BRAINPOOL
                and HAVE_ECC_KOBLITZ */
        }
        else {
            printf("ecc_test_curve_size %d failed!: %d\n", keySize, ret);
            return ret;
        }
    }

#ifdef HAVE_ECC_VECTOR_TEST
    ret = ecc_test_vector(keySize);
    if (ret < 0) {
        printf("ecc_test_vector %d failed!: %d\n", keySize, ret);
        return ret;
    }
#endif

    ret = ecc_test_key_decode(rng, keySize);
    if (ret < 0) {
        if (ret == ECC_CURVE_OID_E) {
            /* ignore error for curves not found */
        }
        else {
            printf("ecc_test_key_decode %d failed!: %d\n", keySize, ret);
            return ret;
        }
    }

    ret = ecc_test_key_gen(rng, keySize);
    if (ret < 0) {
        if (ret == ECC_CURVE_OID_E) {
            /* ignore error for curves not found */
        }
        else {
            printf("ecc_test_key_gen %d failed!: %d\n", keySize, ret);
            return ret;
        }
    }

    return 0;
}

#if !defined(NO_ECC256) || defined(HAVE_ALL_CURVES)
#if !defined(WOLFSSL_ATECC508A) && !defined(WOLFSSL_ATECC608A) && \
    defined(HAVE_ECC_KEY_IMPORT) && defined(HAVE_ECC_KEY_EXPORT)
static int ecc_point_test(void)
{
    int        ret;
    ecc_point* point;
    ecc_point* point2;
#ifdef HAVE_COMP_KEY
    ecc_point* point3;
    ecc_point* point4;
#endif
    word32     outLen;
    byte       out[65];
    byte       der[] = { 0x04, /* = Uncompressed */
                         0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                         0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                         0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                         0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                         0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                         0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                         0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                         0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08 };
#ifdef HAVE_COMP_KEY
    byte       derComp0[] = { 0x02, /* = Compressed, y even */
                              0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                              0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                              0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                              0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08 };
    byte       derComp1[] = { 0x03, /* = Compressed, y odd */
                              0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                              0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                              0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                              0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08 };
#endif
    byte       altDer[] = { 0x04, /* = Uncompressed */
                            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
                            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
                            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
                            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
                            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
                            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
                            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
                            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07 };
    int curve_idx = wc_ecc_get_curve_idx(ECC_SECP256R1);

    /* if curve P256 is not enabled then test should not fail */
    if (curve_idx == ECC_CURVE_INVALID)
        return 0;

    outLen = sizeof(out);
    point = wc_ecc_new_point();
    if (point == NULL)
        return -9700;
    point2 = wc_ecc_new_point();
    if (point2 == NULL) {
        wc_ecc_del_point(point);
        return -9701;
    }
#ifdef HAVE_COMP_KEY
    point3 = wc_ecc_new_point();
    if (point3 == NULL) {
        wc_ecc_del_point(point2);
        wc_ecc_del_point(point);
        return -9702;
    }
    point4 = wc_ecc_new_point();
    if (point4 == NULL) {
        wc_ecc_del_point(point3);
        wc_ecc_del_point(point2);
        wc_ecc_del_point(point);
        return -9703;
    }
#endif

    /* Parameter Validation testing. */
    wc_ecc_del_point(NULL);
    ret = wc_ecc_import_point_der(NULL, sizeof(der), curve_idx, point);
    if (ret != ECC_BAD_ARG_E) {
        ret = -9704;
        goto done;
    }
    ret = wc_ecc_import_point_der(der, sizeof(der), ECC_CURVE_INVALID, point);
    if (ret != ECC_BAD_ARG_E) {
        ret = -9705;
        goto done;
    }
    ret = wc_ecc_import_point_der(der, sizeof(der), curve_idx, NULL);
    if (ret != ECC_BAD_ARG_E) {
        ret = -9706;
        goto done;
    }
    ret = wc_ecc_export_point_der(-1, point, out, &outLen);
    if (ret != ECC_BAD_ARG_E) {
        ret = -9707;
        goto done;
    }
    ret = wc_ecc_export_point_der(curve_idx, NULL, out, &outLen);
    if (ret != ECC_BAD_ARG_E) {
        ret = -9708;
        goto done;
    }
    ret = wc_ecc_export_point_der(curve_idx, point, NULL, &outLen);
    if (ret != LENGTH_ONLY_E || outLen != sizeof(out)) {
        ret = -9709;
        goto done;
    }
    ret = wc_ecc_export_point_der(curve_idx, point, out, NULL);
    if (ret != ECC_BAD_ARG_E) {
        ret = -9710;
        goto done;
    }
    outLen = 0;
    ret = wc_ecc_export_point_der(curve_idx, point, out, &outLen);
    if (ret != BUFFER_E) {
        ret = -9711;
        goto done;
    }
    ret = wc_ecc_copy_point(NULL, NULL);
    if (ret != ECC_BAD_ARG_E) {
        ret = -9712;
        goto done;
    }
    ret = wc_ecc_copy_point(NULL, point2);
    if (ret != ECC_BAD_ARG_E) {
        ret = -9713;
        goto done;
    }
    ret = wc_ecc_copy_point(point, NULL);
    if (ret != ECC_BAD_ARG_E) {
        ret = -9714;
        goto done;
    }
    ret = wc_ecc_cmp_point(NULL, NULL);
    if (ret != BAD_FUNC_ARG) {
        ret = -9715;
        goto done;
    }
    ret = wc_ecc_cmp_point(NULL, point2);
    if (ret != BAD_FUNC_ARG) {
        ret = -9716;
        goto done;
    }
    ret = wc_ecc_cmp_point(point, NULL);
    if (ret != BAD_FUNC_ARG) {
        ret = -9717;
        goto done;
    }

    /* Use API. */
    ret = wc_ecc_import_point_der(der, sizeof(der), curve_idx, point);
    if (ret != 0) {
        ret = -9718;
        goto done;
    }

    outLen = sizeof(out);
    ret = wc_ecc_export_point_der(curve_idx, point, out, &outLen);
    if (ret != 0) {
        ret = -9719;
        goto done;
    }
    if (outLen != sizeof(der)) {
        ret = -9720;
        goto done;
    }
    if (XMEMCMP(out, der, outLen) != 0) {
        ret = -9721;
        goto done;
    }

    ret = wc_ecc_copy_point(point2, point);
    if (ret != MP_OKAY) {
        ret = -9722;
        goto done;
    }
    ret = wc_ecc_cmp_point(point2, point);
    if (ret != MP_EQ) {
        ret = -9723;
        goto done;
    }

    ret = wc_ecc_import_point_der(altDer, sizeof(altDer), curve_idx, point2);
    if (ret != 0) {
        ret = -9724;
        goto done;
    }
    ret = wc_ecc_cmp_point(point2, point);
    if (ret != MP_GT) {
        ret = -9725;
        goto done;
    }

#ifdef HAVE_COMP_KEY
    ret = wc_ecc_import_point_der(derComp0, sizeof(derComp0)*2-1, curve_idx, point3);
    if (ret != 0) {
        ret = -9726;
        goto done;
    }

    ret = wc_ecc_import_point_der_ex(derComp0, sizeof(derComp0), curve_idx, point4, 0);
    if (ret != 0) {
        ret = -9727;
        goto done;
    }

    ret = wc_ecc_cmp_point(point3, point4);
    if (ret != MP_EQ) {
        ret = -9728;
        goto done;
    }

    ret = wc_ecc_import_point_der(derComp1, sizeof(derComp1)*2-1, curve_idx, point3);
    if (ret != 0) {
        ret = -9729;
        goto done;
    }

    ret = wc_ecc_import_point_der_ex(derComp1, sizeof(derComp1), curve_idx, point4, 0);
    if (ret != 0) {
        ret = -9730;
        goto done;
    }

    ret = wc_ecc_cmp_point(point3, point4);
    if (ret != MP_EQ) {
        ret = -9731;
        goto done;
    }
#endif

done:
#ifdef HAVE_COMP_KEY
    wc_ecc_del_point(point4);
    wc_ecc_del_point(point3);
#endif
    wc_ecc_del_point(point2);
    wc_ecc_del_point(point);

    return ret;
}
#endif /* !WOLFSSL_ATECC508A && HAVE_ECC_KEY_IMPORT && HAVE_ECC_KEY_EXPORT */

#ifndef NO_SIG_WRAPPER
static int ecc_sig_test(WC_RNG* rng, ecc_key* key)
{
    int     ret;
    word32  sigSz;
    int     size;
    byte    out[ECC_MAX_SIG_SIZE];
    byte    in[] = "Everyone gets Friday off.";
    const byte hash[] = {
        0xf2, 0x02, 0x95, 0x65, 0xcb, 0xf6, 0x2a, 0x59,
        0x39, 0x2c, 0x05, 0xff, 0x0e, 0x29, 0xaf, 0xfe,
        0x47, 0x33, 0x8c, 0x99, 0x8d, 0x58, 0x64, 0x83,
        0xa6, 0x58, 0x0a, 0x33, 0x0b, 0x84, 0x5f, 0x5f
    };
    word32 inLen = (word32)XSTRLEN((char*)in);

    size = wc_ecc_sig_size(key);

    ret = wc_SignatureGetSize(WC_SIGNATURE_TYPE_ECC, key, sizeof(*key));
    if (ret != size)
        return -9728;

    sigSz = (word32)ret;
    ret = wc_SignatureGenerate(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_ECC, in,
                               inLen, out, &sigSz, key, sizeof(*key), rng);
    if (ret != 0)
        return -9729;
    TEST_SLEEP();

    ret = wc_SignatureVerify(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_ECC, in,
                             inLen, out, sigSz, key, sizeof(*key));
    if (ret != 0)
        return -9730;
    TEST_SLEEP();

    sigSz = (word32)sizeof(out);
    ret = wc_SignatureGenerateHash(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_ECC,
        hash, (int)sizeof(hash), out, &sigSz, key, sizeof(*key), rng);
    if (ret != 0)
        return -9731;
    TEST_SLEEP();

    ret = wc_SignatureVerifyHash(WC_HASH_TYPE_SHA256, WC_SIGNATURE_TYPE_ECC,
        hash, (int)sizeof(hash), out, sigSz, key, sizeof(*key));
    if (ret != 0)
        return -9732;
    TEST_SLEEP();

    return 0;
}
#endif

#if defined(HAVE_ECC_KEY_IMPORT) && defined(HAVE_ECC_KEY_EXPORT) && \
    !defined(WOLFSSL_ATECC508A) && !defined(WOLFSSL_ATECC608A)
static int ecc_exp_imp_test(ecc_key* key)
{
    int        ret;
    int        curve_id;
    ecc_key    keyImp;
    byte       priv[32];
    word32     privLen;
    byte       pub[65];
    word32     pubLen, pubLenX, pubLenY;
    const char qx[] = "7a4e287890a1a47ad3457e52f2f76a83"
                      "ce46cbc947616d0cbaa82323818a793d";
    const char qy[] = "eec4084f5b29ebf29c44cce3b3059610"
                      "922f8b30ea6e8811742ac7238fe87308";
    const char d[]  = "8c14b793cb19137e323a6d2e2a870bca"
                      "2e7a493ec1153b3a95feb8a4873f8d08";

    wc_ecc_init_ex(&keyImp, HEAP_HINT, devId);

    privLen = sizeof(priv);
    ret = wc_ecc_export_private_only(key, priv, &privLen);
    if (ret != 0) {
        ret = -9733;
        goto done;
    }
    pubLen = sizeof(pub);
    ret = wc_ecc_export_point_der(key->idx, &key->pubkey, pub, &pubLen);
    if (ret != 0) {
        ret = -9734;
        goto done;
    }

    ret = wc_ecc_import_private_key(priv, privLen, pub, pubLen, &keyImp);
    if (ret != 0) {
        ret = -9735;
        goto done;
    }

    wc_ecc_free(&keyImp);
    wc_ecc_init_ex(&keyImp, HEAP_HINT, devId);

    ret = wc_ecc_import_raw_ex(&keyImp, qx, qy, d, ECC_SECP256R1);
    if (ret != 0) {
        ret = -9736;
        goto done;
    }

    wc_ecc_free(&keyImp);
    wc_ecc_init_ex(&keyImp, HEAP_HINT, devId);

    curve_id = wc_ecc_get_curve_id(key->idx);
    if (curve_id < 0) {
        ret = -9737;
        goto done;
    }

    /* test import private only */
    ret = wc_ecc_import_private_key_ex(priv, privLen, NULL, 0, &keyImp,
                                       curve_id);
    if (ret != 0) {
        ret = -9738;
        goto done;
    }

    wc_ecc_free(&keyImp);
    wc_ecc_init_ex(&keyImp, HEAP_HINT, devId);

    /* test export public raw */
    pubLenX = pubLenY = 32;
    ret = wc_ecc_export_public_raw(key, pub, &pubLenX, &pub[32], &pubLenY);
    if (ret != 0) {
        ret = -9739;
        goto done;
    }

#ifndef HAVE_SELFTEST
    /* test import of public */
    ret = wc_ecc_import_unsigned(&keyImp, pub, &pub[32], NULL, ECC_SECP256R1);
    if (ret != 0) {
        ret = -9740;
        goto done;
    }
#endif

    wc_ecc_free(&keyImp);
    wc_ecc_init_ex(&keyImp, HEAP_HINT, devId);

    /* test export private and public raw */
    pubLenX = pubLenY = privLen = 32;
    ret = wc_ecc_export_private_raw(key, pub, &pubLenX, &pub[32], &pubLenY,
        priv, &privLen);
    if (ret != 0) {
        ret = -9741;
        goto done;
    }

#ifndef HAVE_SELFTEST
    /* test import of private and public */
    ret = wc_ecc_import_unsigned(&keyImp, pub, &pub[32], priv, ECC_SECP256R1);
    if (ret != 0) {
        ret = -9742;
        goto done;
    }
#endif

done:
    wc_ecc_free(&keyImp);
    return ret;
}
#endif /* HAVE_ECC_KEY_IMPORT && HAVE_ECC_KEY_EXPORT */

#if !defined(WOLFSSL_ATECC508A) && !defined(WOLFSSL_ATECC608A) && \
    !defined(WOLFSSL_CRYPTOCELL)
#if defined(HAVE_ECC_KEY_IMPORT) && !defined(WOLFSSL_VALIDATE_ECC_IMPORT)
static int ecc_mulmod_test(ecc_key* key1)
{
    int ret;
    ecc_key    key2;
    ecc_key    key3;

    wc_ecc_init_ex(&key2, HEAP_HINT, devId);
    wc_ecc_init_ex(&key3, HEAP_HINT, devId);

    /* TODO: Use test data, test with WOLFSSL_VALIDATE_ECC_IMPORT. */
    /* Need base point (Gx,Gy) and parameter A - load them as the public and
     * private key in key2.
     */
    ret = wc_ecc_import_raw_ex(&key2, key1->dp->Gx, key1->dp->Gy, key1->dp->Af,
                               ECC_SECP256R1);
    if (ret != 0)
        goto done;

    /* Need a point (Gx,Gy) and prime - load them as the public and private key
     * in key3.
     */
    ret = wc_ecc_import_raw_ex(&key3, key1->dp->Gx, key1->dp->Gy,
                               key1->dp->prime, ECC_SECP256R1);
    if (ret != 0)
        goto done;

    ret = wc_ecc_mulmod(&key1->k, &key2.pubkey, &key3.pubkey, &key2.k, &key3.k,
                        1);
    if (ret != 0) {
        ret = -9743;
        goto done;
    }

done:
    wc_ecc_free(&key3);
    wc_ecc_free(&key2);
    return ret;
}
#endif

#ifdef HAVE_ECC_DHE
static int ecc_ssh_test(ecc_key* key, WC_RNG* rng)
{
    int    ret;
    byte   out[128];
    word32 outLen = sizeof(out);

    /* Parameter Validation testing. */
    ret = wc_ecc_shared_secret_ssh(NULL, &key->pubkey, out, &outLen);
    if (ret != BAD_FUNC_ARG)
        return -9744;
    ret = wc_ecc_shared_secret_ssh(key, NULL, out, &outLen);
    if (ret != BAD_FUNC_ARG)
        return -9745;
    ret = wc_ecc_shared_secret_ssh(key, &key->pubkey, NULL, &outLen);
    if (ret != BAD_FUNC_ARG)
        return -9746;
    ret = wc_ecc_shared_secret_ssh(key, &key->pubkey, out, NULL);
    if (ret != BAD_FUNC_ARG)
        return -9747;

#if defined(ECC_TIMING_RESISTANT) && (!defined(HAVE_FIPS) || \
    (!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION != 2))) && \
    !defined(HAVE_SELFTEST)
    ret = wc_ecc_set_rng(key, rng);
    if (ret != 0)
        return -9748;
#else
    (void)rng;
#endif

    /* Use API. */
    ret = 0;
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &key->asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret == 0)
            ret = wc_ecc_shared_secret_ssh(key, &key->pubkey, out, &outLen);
    } while (ret == WC_PENDING_E);
    if (ret != 0)
        return -9749;
    TEST_SLEEP();
    return 0;
}
#endif /* HAVE_ECC_DHE */
#endif

static int ecc_def_curve_test(WC_RNG *rng)
{
    int     ret;
    ecc_key key;

    wc_ecc_init_ex(&key, HEAP_HINT, devId);

    /* Use API */
    ret = wc_ecc_set_flags(NULL, 0);
    if (ret != BAD_FUNC_ARG) {
        ret = -9749;
        goto done;
    }
    ret = wc_ecc_set_flags(&key, 0);
    if (ret != 0) {
        ret = -9750;
        goto done;
    }

    ret = wc_ecc_make_key(rng, ECC_KEYGEN_SIZE, &key);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &key.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0) {
        ret = -9751;
        goto done;
    }
    TEST_SLEEP();

#ifndef NO_SIG_WRAPPER
    ret = ecc_sig_test(rng, &key);
    if (ret < 0)
        goto done;
#endif
#if defined(HAVE_ECC_KEY_IMPORT) && defined(HAVE_ECC_KEY_EXPORT) && \
    !defined(WOLFSSL_ATECC508A) && !defined(WOLFSSL_ATECC608A)
    ret = ecc_exp_imp_test(&key);
    if (ret < 0)
        goto done;
#endif
#if !defined(WOLFSSL_ATECC508A) && !defined(WOLFSSL_ATECC608A) && \
    !defined(WOLFSSL_CRYPTOCELL)
#if defined(HAVE_ECC_KEY_IMPORT) && !defined(WOLFSSL_VALIDATE_ECC_IMPORT)
    ret = ecc_mulmod_test(&key);
    if (ret < 0)
        goto done;
#endif
#ifdef HAVE_ECC_DHE
    ret = ecc_ssh_test(&key, rng);
    if (ret < 0)
        goto done;
#endif
#endif /* WOLFSSL_ATECC508A */
done:
    wc_ecc_free(&key);
    return ret;
}
#endif /* !NO_ECC256 || HAVE_ALL_CURVES */

#ifdef WOLFSSL_CERT_EXT
static int ecc_decode_test(void)
{
    int        ret;
    word32     inSz;
    word32     inOutIdx;
    ecc_key    key;

    /* SECP256R1 OID: 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07 */

    /* This is ecc_clikeypub_der_256. */
    static const byte good[] = {
            0x30, 0x59, 0x30, 0x13, 0x06, 0x07, 0x2a, 0x86, 0x48, 0xce,
            0x3d, 0x02, 0x01, 0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d,
            0x03, 0x01, 0x07, 0x03, 0x42, 0x00, 0x04, 0x55, 0xbf, 0xf4,
            0x0f, 0x44, 0x50, 0x9a, 0x3d, 0xce, 0x9b, 0xb7, 0xf0, 0xc5,
            0x4d, 0xf5, 0x70, 0x7b, 0xd4, 0xec, 0x24, 0x8e, 0x19, 0x80,
            0xec, 0x5a, 0x4c, 0xa2, 0x24, 0x03, 0x62, 0x2c, 0x9b, 0xda,
            0xef, 0xa2, 0x35, 0x12, 0x43, 0x84, 0x76, 0x16, 0xc6, 0x56,
            0x95, 0x06, 0xcc, 0x01, 0xa9, 0xbd, 0xf6, 0x75, 0x1a, 0x42,
            0xf7, 0xbd, 0xa9, 0xb2, 0x36, 0x22, 0x5f, 0xc7, 0x5d, 0x7f,
            0xb4 };
    static const byte badNoObjId[] = { 0x30, 0x08, 0x30, 0x06, 0x03, 0x04,
            0x00, 0x04, 0x01, 0x01 };
    static const byte badOneObjId[] = { 0x30, 0x0a, 0x30, 0x08, 0x06, 0x00,
            0x03, 0x04, 0x00, 0x04, 0x01, 0x01 };
    static const byte badObjId1Len[] = { 0x30, 0x0c, 0x30, 0x0a, 0x06, 0x09,
            0x06, 0x00, 0x03, 0x04, 0x00, 0x04, 0x01, 0x01 };
    static const byte badObj2d1Len[] = { 0x30, 0x0c, 0x30, 0x0a, 0x06, 0x00,
            0x06, 0x07, 0x03, 0x04, 0x00, 0x04, 0x01, 0x01 };
    static const byte badNotBitStr[] = { 0x30, 0x14, 0x30, 0x0b, 0x06, 0x00,
            0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07,
            0x04, 0x04, 0x00, 0x04, 0x01, 0x01 };
    static const byte badBitStrLen[] = { 0x30, 0x14, 0x30, 0x0b, 0x06, 0x00,
            0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07,
            0x03, 0x05, 0x00, 0x04, 0x01, 0x01 };
    static const byte badNoBitStrZero[] = { 0x30, 0x13, 0x30, 0x0a, 0x06, 0x00,
            0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07,
            0x03, 0x03, 0x04, 0x01, 0x01 };
    static const byte badPoint[] = { 0x30, 0x12, 0x30, 0x09, 0x06, 0x00,
            0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07,
            0x03, 0x03, 0x00, 0x04, 0x01 };

    XMEMSET(&key, 0, sizeof(key));
    wc_ecc_init_ex(&key, HEAP_HINT, devId);

    inSz = sizeof(good);
    ret = wc_EccPublicKeyDecode(NULL, &inOutIdx, &key, inSz);
    if (ret != BAD_FUNC_ARG) {
        ret = -9800;
        goto done;
    }
    ret = wc_EccPublicKeyDecode(good, NULL, &key, inSz);
    if (ret != BAD_FUNC_ARG) {
        ret = -9801;
        goto done;
    }
    ret = wc_EccPublicKeyDecode(good, &inOutIdx, NULL, inSz);
    if (ret != BAD_FUNC_ARG) {
        ret = -9802;
        goto done;
    }
    ret = wc_EccPublicKeyDecode(good, &inOutIdx, &key, 0);
    if (ret != BAD_FUNC_ARG) {
        ret = -9803;
        goto done;
    }

    /* Change offset to produce bad input data. */
    inOutIdx = 2;
    inSz = sizeof(good) - inOutIdx;
    ret = wc_EccPublicKeyDecode(good, &inOutIdx, &key, inSz);
    if (ret != ASN_PARSE_E) {
        ret = -9804;
        goto done;
    }
    inOutIdx = 4;
    inSz = sizeof(good) - inOutIdx;
    ret = wc_EccPublicKeyDecode(good, &inOutIdx, &key, inSz);
    if (ret != ASN_PARSE_E) {
        ret = -9805;
        goto done;
    }
    /* Bad data. */
    inSz = sizeof(badNoObjId);
    inOutIdx = 0;
    ret = wc_EccPublicKeyDecode(badNoObjId, &inOutIdx, &key, inSz);
    if (ret != ASN_OBJECT_ID_E) {
        ret = -9806;
        goto done;
    }
    inSz = sizeof(badOneObjId);
    inOutIdx = 0;
    ret = wc_EccPublicKeyDecode(badOneObjId, &inOutIdx, &key, inSz);
    if (ret != ASN_OBJECT_ID_E) {
        ret = -9807;
        goto done;
    }
    inSz = sizeof(badObjId1Len);
    inOutIdx = 0;
    ret = wc_EccPublicKeyDecode(badObjId1Len, &inOutIdx, &key, inSz);
    if (ret != ASN_PARSE_E) {
        ret = -9808;
        goto done;
    }
    inSz = sizeof(badObj2d1Len);
    inOutIdx = 0;
    ret = wc_EccPublicKeyDecode(badObj2d1Len, &inOutIdx, &key, inSz);
    if (ret != ASN_PARSE_E) {
        ret = -9809;
        goto done;
    }
    inSz = sizeof(badNotBitStr);
    inOutIdx = 0;
    ret = wc_EccPublicKeyDecode(badNotBitStr, &inOutIdx, &key, inSz);
    if (ret != ASN_BITSTR_E) {
        ret = -9810;
        goto done;
    }
    inSz = sizeof(badBitStrLen);
    inOutIdx = 0;
    ret = wc_EccPublicKeyDecode(badBitStrLen, &inOutIdx, &key, inSz);
    if (ret != ASN_PARSE_E) {
        ret = -9811;
        goto done;
    }
    inSz = sizeof(badNoBitStrZero);
    inOutIdx = 0;
    ret = wc_EccPublicKeyDecode(badNoBitStrZero, &inOutIdx, &key, inSz);
    if (ret != ASN_EXPECT_0_E) {
        ret = -9812;
        goto done;
    }
    inSz = sizeof(badPoint);
    inOutIdx = 0;
    ret = wc_EccPublicKeyDecode(badPoint, &inOutIdx, &key, inSz);
    if (ret != ASN_ECC_KEY_E) {
        ret = -9813;
        goto done;
    }

    inSz = sizeof(good);
    inOutIdx = 0;
    ret = wc_EccPublicKeyDecode(good, &inOutIdx, &key, inSz);
    if (ret != 0) {
        ret = -9814;
        goto done;
    }

done:
    wc_ecc_free(&key);
    return ret;
}
#endif /* WOLFSSL_CERT_EXT */

#ifdef WOLFSSL_CUSTOM_CURVES
static const byte eccKeyExplicitCurve[] = {
    0x30, 0x81, 0xf5, 0x30, 0x81, 0xae, 0x06, 0x07,
    0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01, 0x30,
    0x81, 0xa2, 0x02, 0x01, 0x01, 0x30, 0x2c, 0x06,
    0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x01, 0x01,
    0x02, 0x21, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xff,
    0xff, 0xfc, 0x2f, 0x30, 0x06, 0x04, 0x01, 0x00,
    0x04, 0x01, 0x07, 0x04, 0x41, 0x04, 0x79, 0xbe,
    0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac, 0x55, 0xa0,
    0x62, 0x95, 0xce, 0x87, 0x0b, 0x07, 0x02, 0x9b,
    0xfc, 0xdb, 0x2d, 0xce, 0x28, 0xd9, 0x59, 0xf2,
    0x81, 0x5b, 0x16, 0xf8, 0x17, 0x98, 0x48, 0x3a,
    0xda, 0x77, 0x26, 0xa3, 0xc4, 0x65, 0x5d, 0xa4,
    0xfb, 0xfc, 0x0e, 0x11, 0x08, 0xa8, 0xfd, 0x17,
    0xb4, 0x48, 0xa6, 0x85, 0x54, 0x19, 0x9c, 0x47,
    0xd0, 0x8f, 0xfb, 0x10, 0xd4, 0xb8, 0x02, 0x21,
    0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xfe, 0xba, 0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0,
    0x3b, 0xbf, 0xd2, 0x5e, 0x8c, 0xd0, 0x36, 0x41,
    0x41, 0x02, 0x01, 0x01, 0x03, 0x42, 0x00, 0x04,
    0x3c, 0x4c, 0xc9, 0x5e, 0x2e, 0xa2, 0x3d, 0x49,
    0xcc, 0x5b, 0xff, 0x4f, 0xc9, 0x2e, 0x1d, 0x4a,
    0xc6, 0x21, 0xf6, 0xf3, 0xe6, 0x0b, 0x4f, 0xa9,
    0x9d, 0x74, 0x99, 0xdd, 0x97, 0xc7, 0x6e, 0xbe,
    0x14, 0x2b, 0x39, 0x9d, 0x63, 0xc7, 0x97, 0x0d,
    0x45, 0x25, 0x40, 0x30, 0x77, 0x05, 0x76, 0x88,
    0x38, 0x96, 0x29, 0x7d, 0x9c, 0xe1, 0x50, 0xbe,
    0xac, 0xf0, 0x1d, 0x86, 0xf4, 0x2f, 0x65, 0x0b
};

static int ecc_test_custom_curves(WC_RNG* rng)
{
    int     ret;
    word32  inOutIdx;
    ecc_key key;

    /* test use of custom curve - using BRAINPOOLP256R1 for test */
    #ifndef WOLFSSL_ECC_CURVE_STATIC
        const ecc_oid_t ecc_oid_brainpoolp256r1[] = {
            0x2B,0x24,0x03,0x03,0x02,0x08,0x01,0x01,0x07
        };
        const word32 ecc_oid_brainpoolp256r1_sz =
            sizeof(ecc_oid_brainpoolp256r1) / sizeof(ecc_oid_t);
    #else
        #define ecc_oid_brainpoolp256r1 { \
            0x2B,0x24,0x03,0x03,0x02,0x08,0x01,0x01,0x07 \
        }
        #define ecc_oid_brainpoolp256r1_sz 9
    #endif
    const word32 ecc_oid_brainpoolp256r1_sum = 104;

    const ecc_set_type ecc_dp_brainpool256r1 = {
        32,                                                                 /* size/bytes */
        ECC_CURVE_CUSTOM,                                                   /* ID         */
        "BRAINPOOLP256R1",                                                  /* curve name */
        "A9FB57DBA1EEA9BC3E660A909D838D726E3BF623D52620282013481D1F6E5377", /* prime      */
        "7D5A0975FC2C3057EEF67530417AFFE7FB8055C126DC5C6CE94A4B44F330B5D9", /* A          */
        "26DC5C6CE94A4B44F330B5D9BBD77CBF958416295CF7E1CE6BCCDC18FF8C07B6", /* B          */
        "A9FB57DBA1EEA9BC3E660A909D838D718C397AA3B561A6F7901E0E82974856A7", /* order      */
        "8BD2AEB9CB7E57CB2C4B482FFC81B7AFB9DE27E1E3BD23C23A4453BD9ACE3262", /* Gx         */
        "547EF835C3DAC4FD97F8461A14611DC9C27745132DED8E545C1D54C72F046997", /* Gy         */
        ecc_oid_brainpoolp256r1,                                            /* oid/oidSz  */
        ecc_oid_brainpoolp256r1_sz,
        ecc_oid_brainpoolp256r1_sum,                                        /* oid sum    */
        1,                                                                  /* cofactor   */
    };

    ret = ecc_test_curve_size(rng, 0, ECC_TEST_VERIFY_COUNT, ECC_CURVE_DEF,
        &ecc_dp_brainpool256r1);
    if (ret != 0) {
        printf("ECC test for custom curve failed! %d\n", ret);
        return ret;
    }

    #if defined(HAVE_ECC_BRAINPOOL) || defined(HAVE_ECC_KOBLITZ)
    {
        int curve_id;
        #ifdef HAVE_ECC_BRAINPOOL
            curve_id = ECC_BRAINPOOLP256R1;
        #else
            curve_id = ECC_SECP256K1;
        #endif
        /* Test and demonstrate use of non-SECP curve */
        ret = ecc_test_curve_size(rng, 0, ECC_TEST_VERIFY_COUNT, curve_id, NULL);
        if (ret < 0) {
            printf("ECC test for curve_id %d failed! %d\n", curve_id, ret);
            return ret;
        }
    }
    #endif

    ret = wc_ecc_init_ex(&key, HEAP_HINT, devId);
    if (ret != 0) {
        return -9815;
    }

    inOutIdx = 0;
    ret = wc_EccPublicKeyDecode(eccKeyExplicitCurve, &inOutIdx, &key,
                                                   sizeof(eccKeyExplicitCurve));
    if (ret != 0)
        return -9816;

    wc_ecc_free(&key);

    return ret;
}
#endif /* WOLFSSL_CUSTOM_CURVES */

#ifdef WOLFSSL_CERT_GEN

/* Make Cert / Sign example for ECC cert and ECC CA */
static int ecc_test_cert_gen(WC_RNG* rng)
{
    int ret;
    Cert        myCert;
    int         certSz;
    size_t      bytes;
    word32      idx = 0;
#ifndef USE_CERT_BUFFERS_256
    XFILE       file;
#endif
#ifdef WOLFSSL_TEST_CERT
    DecodedCert decode;
#endif
#ifdef WOLFSSL_SMALL_STACK
    byte* der = NULL;
#else
    byte der[FOURK_BUF];
#endif
    ecc_key caEccKey;
    ecc_key certPubKey;

    XMEMSET(&caEccKey, 0, sizeof(caEccKey));
    XMEMSET(&certPubKey, 0, sizeof(certPubKey));

#ifdef WOLFSSL_SMALL_STACK
    der = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (der == NULL) {
        ERROR_OUT(-9818, exit);
    }
#endif

    /* Get cert private key */
#ifdef ENABLE_ECC384_CERT_GEN_TEST
    /* Get Cert Key 384 */
#ifdef USE_CERT_BUFFERS_256
    XMEMCPY(der, ca_ecc_key_der_384, sizeof_ca_ecc_key_der_384);
    bytes = sizeof_ca_ecc_key_der_384;
#else
    file = XFOPEN(eccCaKey384File, "rb");
    if (!file) {
        ERROR_OUT(-9819, exit);
    }

    bytes = XFREAD(der, 1, FOURK_BUF, file);
    XFCLOSE(file);
    (void)eccCaKeyFile;
#endif /* USE_CERT_BUFFERS_256 */
#else
#ifdef USE_CERT_BUFFERS_256
    XMEMCPY(der, ca_ecc_key_der_256, sizeof_ca_ecc_key_der_256);
    bytes = sizeof_ca_ecc_key_der_256;
#else
    file = XFOPEN(eccCaKeyFile, "rb");
    if (!file) {
        ERROR_OUT(-9820, exit);
    }
    bytes = XFREAD(der, 1, FOURK_BUF, file);
    XFCLOSE(file);
#ifdef ENABLE_ECC384_CERT_GEN_TEST
    (void)eccCaKey384File;
#endif
#endif /* USE_CERT_BUFFERS_256 */
#endif /* ENABLE_ECC384_CERT_GEN_TEST */

    /* Get CA Key */
    ret = wc_ecc_init_ex(&caEccKey, HEAP_HINT, devId);
    if (ret != 0) {
        ERROR_OUT(-9821, exit);
    }
    ret = wc_EccPrivateKeyDecode(der, &idx, &caEccKey, (word32)bytes);
    if (ret != 0) {
        ERROR_OUT(-9822, exit);
    }

    /* Make a public key */
    ret = wc_ecc_init_ex(&certPubKey, HEAP_HINT, devId);
    if (ret != 0) {
        ERROR_OUT(-9823, exit);
    }

    ret = wc_ecc_make_key(rng, ECC_KEYGEN_SIZE, &certPubKey);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &certPubKey.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0) {
        ERROR_OUT(-9824, exit);
    }
    TEST_SLEEP();

    /* Setup Certificate */
    if (wc_InitCert(&myCert)) {
        ERROR_OUT(-9825, exit);
    }

#ifndef NO_SHA256
    myCert.sigType = CTC_SHA256wECDSA;
#else
    myCert.sigType = CTC_SHAwECDSA;
#endif
    XMEMCPY(&myCert.subject, &certDefaultName, sizeof(CertName));

#ifdef WOLFSSL_CERT_EXT
    /* add Policies */
    XSTRNCPY(myCert.certPolicies[0], "2.4.589440.587.101.2.1.9632587.1",
            CTC_MAX_CERTPOL_SZ);
    XSTRNCPY(myCert.certPolicies[1], "1.2.13025.489.1.113549",
            CTC_MAX_CERTPOL_SZ);
    myCert.certPoliciesNb = 2;

    /* add SKID from the Public Key */
    if (wc_SetSubjectKeyIdFromPublicKey(&myCert, NULL, &certPubKey) != 0) {
        ERROR_OUT(-9826, exit);
    }

    /* add AKID from the Public Key */
    if (wc_SetAuthKeyIdFromPublicKey(&myCert, NULL, &caEccKey) != 0) {
        ERROR_OUT(-9827, exit);
    }

    /* add Key Usage */
    if (wc_SetKeyUsage(&myCert, certKeyUsage) != 0) {
        ERROR_OUT(-9828, exit);
    }
#endif /* WOLFSSL_CERT_EXT */

#ifdef ENABLE_ECC384_CERT_GEN_TEST
    #if defined(USE_CERT_BUFFERS_256)
    ret = wc_SetIssuerBuffer(&myCert, ca_ecc_cert_der_384,
                                      sizeof_ca_ecc_cert_der_384);
#else
    ret = wc_SetIssuer(&myCert, eccCaCert384File);
    (void)eccCaCertFile;
#endif
#else
#if defined(USE_CERT_BUFFERS_256)
    ret = wc_SetIssuerBuffer(&myCert, ca_ecc_cert_der_256,
                                      sizeof_ca_ecc_cert_der_256);
#else
    ret = wc_SetIssuer(&myCert, eccCaCertFile);
#ifdef ENABLE_ECC384_CERT_GEN_TEST
    (void)eccCaCert384File;
#endif
#endif
#endif /* ENABLE_ECC384_CERT_GEN_TEST */
    if (ret < 0) {
        ERROR_OUT(-9829, exit);
    }

    certSz = wc_MakeCert(&myCert, der, FOURK_BUF, NULL, &certPubKey, rng);
    if (certSz < 0) {
        ERROR_OUT(-9830, exit);
    }

    ret = 0;
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &caEccKey.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret >= 0) {
            ret = wc_SignCert(myCert.bodySz, myCert.sigType, der,
                              FOURK_BUF, NULL, &caEccKey, rng);
        }
    } while (ret == WC_PENDING_E);
    if (ret < 0) {
        ERROR_OUT(-9831, exit);
    }
    certSz = ret;
    TEST_SLEEP();

#ifdef WOLFSSL_TEST_CERT
    InitDecodedCert(&decode, der, certSz, 0);
    ret = ParseCert(&decode, CERT_TYPE, NO_VERIFY, 0);
    if (ret != 0) {
        FreeDecodedCert(&decode);
        ERROR_OUT(-9832, exit);

    }
    FreeDecodedCert(&decode);
#endif

    ret = SaveDerAndPem(der, certSz, certEccDerFile, certEccPemFile,
        CERT_TYPE, -6735);
    if (ret != 0) {
        goto exit;
    }

exit:
#ifdef WOLFSSL_SMALL_STACK
    XFREE(der, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
#endif
    wc_ecc_free(&certPubKey);
    wc_ecc_free(&caEccKey);

    return ret;
}
#endif /* WOLFSSL_CERT_GEN */

#if !defined(HAVE_FIPS) && !defined(HAVE_SELFTEST)
/* Test for the wc_ecc_key_new() and wc_ecc_key_free() functions. */
static int ecc_test_allocator(WC_RNG* rng)
{
    int ret = 0;
    ecc_key* key;

    key = wc_ecc_key_new(HEAP_HINT);
    if (key == NULL) {
        ERROR_OUT(-9833, exit);
    }

    ret = wc_ecc_make_key(rng, ECC_KEYGEN_SIZE, key);
    if (ret != 0) {
        ERROR_OUT(-9834, exit);
    }

exit:
    wc_ecc_key_free(key);
    return ret;
}
#endif

/* ECC Non-blocking tests for Sign and Verify */
/* Requires SP math and supports P384 or P256 */
/* ./configure --enable-ecc=nonblock --enable-sp=yes,nonblock CFLAGS="-DWOLFSSL_PUBLIC_MP" */
#if defined(WC_ECC_NONBLOCK) && defined(WOLFSSL_PUBLIC_MP) && \
    defined(HAVE_ECC_SIGN) && defined(HAVE_ECC_VERIFY)
/* Test Data - Random */
static const uint8_t kMsg[] = {
    0x69, 0xbc, 0x9f, 0xce, 0x68, 0x17, 0xc2, 0x10, 0xea, 0xfc, 0x10, 0x65, 0x67, 0x52, 0xed, 0x78, 
    0x6e, 0xb8, 0x83, 0x9c, 0x9a, 0xb4, 0x56, 0x0d, 0xc1, 0x0d, 0x1f, 0x78, 0x6e, 0x75, 0xd7, 0xbe, 
    0x92, 0x6b, 0x12, 0xf6, 0x76, 0x60, 0x8e, 0xb1, 0xf4, 0x19, 0x0c, 0x81, 0xe7, 0x54, 0x5e, 0xbc, 
    0xe0, 0xae, 0xc2, 0x7d, 0x1b, 0xc4, 0x6e, 0xec, 0xb1, 0x99, 0x6c, 0xbf, 0x0e, 0x38, 0xa8, 0x01, 
    0xa6, 0x9a, 0x48, 0x12, 0xe4, 0xc9, 0x3b, 0xf0, 0x63, 0x46, 0x15, 0xb4, 0x61, 0xa8, 0x1a, 0x60, 
    0x71, 0x87, 0x98, 0xd7, 0x6f, 0x98, 0x7b, 0x2d, 0xb9, 0x19, 0x1b, 0x21, 0x9c, 0x70, 0x58, 0xe8, 
    0x0d, 0x0f, 0xe9, 0x2d, 0x9a, 0x9a, 0xf1, 0x55, 0xa0, 0x4c, 0xd3, 0x07, 0xbd, 0x97, 0x48, 0xec, 
    0x88, 0x0a, 0xaf, 0xb3, 0x80, 0x78, 0xa4, 0x59, 0x43, 0x57, 0xd3, 0xa7, 0x01, 0x66, 0x0e, 0xfc
};

/* ECC Private Key "d" */
static const uint8_t kPrivKey[] = {
#ifdef HAVE_ECC384
    /* SECP384R1 */
    /* d */
    0xa4, 0xe5, 0x06, 0xe8, 0x06, 0x16, 0x3e, 0xab, 
    0x89, 0xf8, 0x60, 0x43, 0xc0, 0x60, 0x25, 0xdb,
    0xba, 0x7b, 0xfe, 0x19, 0x35, 0x08, 0x55, 0x65, 
    0x76, 0xe2, 0xdc, 0xe0, 0x01, 0x8b, 0x6b, 0x68, 
    0xdf, 0xcf, 0x6f, 0x80, 0x12, 0xce, 0x79, 0x37, 
    0xeb, 0x2b, 0x9c, 0x7b, 0xc4, 0x68, 0x1c, 0x74
#else
    /* SECP256R1 */
    /* d */
    0x1e, 0xe7, 0x70, 0x07, 0xd3, 0x30, 0x94, 0x39, 
    0x28, 0x90, 0xdf, 0x23, 0x88, 0x2c, 0x4a, 0x34, 
    0x15, 0xdb, 0x4c, 0x43, 0xcd, 0xfa, 0xe5, 0x1f, 
    0x3d, 0x4c, 0x37, 0xfe, 0x59, 0x3b, 0x96, 0xd8
#endif
};

/* ECC public key Qx/Qy */
static const uint8_t kPubKey[] = {
#ifdef HAVE_ECC384
    /* SECP384R1 */
    /* Qx */
    0xea, 0xcf, 0x93, 0x4f, 0x2c, 0x09, 0xbb, 0x39, 
    0x14, 0x0f, 0x56, 0x64, 0xc3, 0x40, 0xb4, 0xdf, 
    0x0e, 0x63, 0xae, 0xe5, 0x71, 0x4b, 0x00, 0xcc, 
    0x04, 0x97, 0xff, 0xe1, 0xe9, 0x38, 0x96, 0xbb, 
    0x5f, 0x91, 0xb2, 0x6a, 0xcc, 0xb5, 0x39, 0x5f, 
    0x8f, 0x70, 0x59, 0xf1, 0x01, 0xf6, 0x5a, 0x2b,
    /* Qy */
    0x01, 0x6c, 0x68, 0x0b, 0xcf, 0x55, 0x25, 0xaf, 
    0x6d, 0x98, 0x48, 0x0a, 0xa8, 0x74, 0xc9, 0xa9, 
    0x17, 0xa0, 0x0c, 0xc3, 0xfb, 0xd3, 0x23, 0x68, 
    0xfe, 0x04, 0x3c, 0x63, 0x50, 0x88, 0x3b, 0xb9, 
    0x4f, 0x7c, 0x67, 0x34, 0xf7, 0x3b, 0xa9, 0x73, 
    0xe7, 0x1b, 0xc3, 0x51, 0x5e, 0x22, 0x18, 0xec
#else
    /* SECP256R1 */
    /* Qx */
    0x96, 0x93, 0x1c, 0x53, 0x0b, 0x43, 0x6c, 0x42, 
    0x0c, 0x52, 0x90, 0xe4, 0xa7, 0xec, 0x98, 0xb1, 
    0xaf, 0xd4, 0x14, 0x49, 0xd8, 0xc1, 0x42, 0x82, 
    0x04, 0x78, 0xd1, 0x90, 0xae, 0xa0, 0x6c, 0x07, 
    /* Qy */
    0xf2, 0x3a, 0xb5, 0x10, 0x32, 0x8d, 0xce, 0x9e, 
    0x76, 0xa0, 0xd2, 0x8c, 0xf3, 0xfc, 0xa9, 0x94, 
    0x43, 0x24, 0xe6, 0x82, 0x00, 0x40, 0xc6, 0xdb, 
    0x1c, 0x2f, 0xcd, 0x38, 0x4b, 0x60, 0xdd, 0x61
#endif
};

/* ECC Curve */
#ifdef HAVE_ECC384
    /* SECP384R1 */
    #define ECC_CURVE_SZ 48
    #define ECC_CURVE_ID ECC_SECP384R1
#else
    /* SECP256R1 */
    #define ECC_CURVE_SZ 32
    #define ECC_CURVE_ID ECC_SECP256R1
#endif

/* Hash Algorithm */
#if defined(HAVE_ECC384) && defined(WOLFSSL_SHA3)
    #define HASH_DIGEST_SZ  WC_SHA3_384_DIGEST_SIZE
    #define HASH_SHA_VER    3
    #define CRYPTO_HASH_FN  crypto_sha3_384
#elif defined(HAVE_ECC384) && defined(WOLFSSL_SHA384)
    #define HASH_DIGEST_SZ  WC_SHA384_DIGEST_SIZE
    #define HASH_SHA_VER    2
    #define CRYPTO_HASH_FN  crypto_sha2_384
#elif !defined(NO_SHA256)
    #define HASH_DIGEST_SZ  WC_SHA256_DIGEST_SIZE
    #define HASH_SHA_VER    2
    #define CRYPTO_HASH_FN  crypto_sha2_256
#else
    #error test configuration not supported
#endif

#if defined(HAVE_ECC384) && defined(WOLFSSL_SHA3)
/* helper to perform hashing block by block */
static int crypto_sha3_384(const uint8_t *buf, uint32_t len, uint8_t *hash, 
    uint32_t hashSz, uint32_t blkSz)
{
    int ret;
    uint32_t i = 0, chunk;
    wc_Sha3 sha3;
    
    /* validate arguments */
    if ((buf == NULL && len > 0) || hash == NULL || 
        hashSz < WC_SHA3_384_DIGEST_SIZE || blkSz == 0)
    {
        return BAD_FUNC_ARG;
    }

    /* Init Sha3_384 structure */
    ret = wc_InitSha3_384(&sha3, NULL, INVALID_DEVID);
    if (ret != 0) {
        return ret;
    }
    while (i < len) {
        chunk = blkSz;
        if ((chunk + i) > len)
            chunk = len - i;
        /* Perform chunked update */
        ret = wc_Sha3_384_Update(&sha3, (buf + i), chunk);
        if (ret != 0) {
            break;
        }
        i += chunk;
    }
    if (ret == 0) {
        /* Get final digest result */
        ret = wc_Sha3_384_Final(&sha3, hash);
    }
    return ret;
}
#elif defined(HAVE_ECC384) && defined(WOLFSSL_SHA384)
/* helper to perform hashing block by block */
static int crypto_sha2_384(const uint8_t *buf, uint32_t len, uint8_t *hash, 
    uint32_t hashSz, uint32_t blkSz)
{
    int ret;
    uint32_t i = 0, chunk;
    wc_Sha384 sha384;
    
    /* validate arguments */
    if ((buf == NULL && len > 0) || hash == NULL || 
        hashSz < WC_SHA384_DIGEST_SIZE || blkSz == 0)
    {
        return BAD_FUNC_ARG;
    }

    /* Init Sha384 structure */
    ret = wc_InitSha384(&sha384);
    if (ret != 0) {
        return ret;
    }
    while (i < len) {
        chunk = blkSz;
        if ((chunk + i) > len)
            chunk = len - i;
        /* Perform chunked update */
        ret = wc_Sha384Update(&sha384, (buf + i), chunk);
        if (ret != 0) {
            break;
        }
        i += chunk;
    }
    if (ret == 0) {
        /* Get final digest result */
        ret = wc_Sha384Final(&sha384, hash);
    }
    return ret;
}
#elif !defined(NO_SHA256)
/* helper to perform hashing block by block */
static int crypto_sha2_256(const uint8_t *buf, uint32_t len, uint8_t *hash, 
    uint32_t hashSz, uint32_t blkSz)
{
    int ret;
    uint32_t i = 0, chunk;
    wc_Sha256 sha256;
    
    /* validate arguments */
    if ((buf == NULL && len > 0) || hash == NULL || 
        hashSz < WC_SHA256_DIGEST_SIZE || blkSz == 0)
    {
        return BAD_FUNC_ARG;
    }

    /* Init Sha256 structure */
    ret = wc_InitSha256(&sha256);
    if (ret != 0) {
        return ret;
    }
    while (i < len) {
        chunk = blkSz;
        if ((chunk + i) > len)
            chunk = len - i;
        /* Perform chunked update */
        ret = wc_Sha256Update(&sha256, (buf + i), chunk);
        if (ret != 0) {
            break;
        }
        i += chunk;
    }
    if (ret == 0) {
        /* Get final digest result */
        ret = wc_Sha256Final(&sha256, hash);
    }
    return ret;
}
#endif

/* perform verify of signature and hash using public key */
/* key is public Qx + public Qy */
/* sig is r + s */
static int crypto_ecc_verify(const uint8_t *key, uint32_t keySz,
    const uint8_t *hash, uint32_t hashSz, const uint8_t *sig, uint32_t sigSz,
    uint32_t curveSz, int curveId)
{
    int ret, verify_res = 0, count = 0;
    mp_int r, s;
    ecc_key ecc;
    ecc_nb_ctx_t nb_ctx;

    /* validate arguments */
    if (key == NULL || hash == NULL || sig == NULL || curveSz == 0 || 
        hashSz == 0 || keySz < (curveSz*2) || sigSz < (curveSz*2))
    {
        return BAD_FUNC_ARG;
    }

    /* Setup the ECC key */
    ret = wc_ecc_init(&ecc);
    if (ret < 0) {
        return ret;
    }

    ret = wc_ecc_set_nonblock(&ecc, &nb_ctx);
    if (ret != MP_OKAY) {
        wc_ecc_free(&ecc);
        return ret;
    }

    /* Setup the signature r/s variables */
    ret = mp_init(&r);
    if (ret != MP_OKAY) {
        wc_ecc_free(&ecc);
        return ret;
    }
    ret = mp_init(&s);
    if (ret != MP_OKAY) {
        mp_clear(&r);
        wc_ecc_free(&ecc);
        return ret;
    }

    /* Import public key x/y */
    ret = wc_ecc_import_unsigned(
        &ecc, 
        (byte*)key,             /* Public "x" Coordinate */
        (byte*)(key + curveSz), /* Public "y" Coordinate */
        NULL,                   /* Private "d" (optional) */
        curveId                 /* ECC Curve Id */
    );
    /* Make sure it was a public key imported */
    if (ret == 0 && ecc.type != ECC_PUBLICKEY) {
        ret = ECC_BAD_ARG_E;
    }

    /* Import signature r/s */
    if (ret == 0) {
        ret = mp_read_unsigned_bin(&r, sig,  curveSz);
    }
    if (ret == 0) {
        ret = mp_read_unsigned_bin(&s, sig + curveSz, curveSz);
    }

    /* Verify ECC Signature */
    if (ret == 0) {
        do {
            ret = wc_ecc_verify_hash_ex(
                &r, &s,       /* r/s as mp_int */
                hash, hashSz, /* computed hash digest */
                &verify_res,  /* verification result 1=success */
                &ecc
            );
            count++;

            /* TODO: Real-time work can be called here */
        } while (ret == FP_WOULDBLOCK);
    #ifdef DEBUG_WOLFSSL
        printf("ECC non-block verify: %d times\n", count);
    #endif
    }
    
    /* check verify result */
    if (ret == 0 && verify_res == 0) {
        ret = SIG_VERIFY_E;
    }

    mp_clear(&r);
    mp_clear(&s);
    wc_ecc_free(&ecc);

    (void)count;

    return ret;
}

/* perform signature operation against hash using private key */
static int crypto_ecc_sign(const uint8_t *key, uint32_t keySz,
    const uint8_t *hash, uint32_t hashSz, uint8_t *sig, uint32_t* sigSz,
    uint32_t curveSz, int curveId, WC_RNG* rng)
{
    int ret, count = 0;
    mp_int r, s;
    ecc_key ecc;
    ecc_nb_ctx_t nb_ctx;

    /* validate arguments */
    if (key == NULL || hash == NULL || sig == NULL || sigSz == NULL ||
        curveSz == 0 || hashSz == 0 || keySz < curveSz || *sigSz < (curveSz*2))
    {
        return BAD_FUNC_ARG;
    }

    /* Initialize signature result */
    memset(sig, 0, curveSz*2);

    /* Setup the ECC key */
    ret = wc_ecc_init(&ecc);
    if (ret < 0) {
        return ret;
    }

    ret = wc_ecc_set_nonblock(&ecc, &nb_ctx);
    if (ret != MP_OKAY) {
        wc_ecc_free(&ecc);
        return ret;
    }

    /* Setup the signature r/s variables */
    ret = mp_init(&r);
    if (ret != MP_OKAY) {
        wc_ecc_free(&ecc);
        return ret;
    }
    ret = mp_init(&s);
    if (ret != MP_OKAY) {
        mp_clear(&r);
        wc_ecc_free(&ecc);
        return ret;
    }

    /* Import private key "k" */
    ret = wc_ecc_import_private_key_ex(
        key, keySz, /* private key "d" */
        NULL, 0,    /* public (optional) */
        &ecc,
        curveId     /* ECC Curve Id */
    );

    if (ret == 0) {
        do {
            /* Verify ECC Signature */
            ret = wc_ecc_sign_hash_ex(
                hash, hashSz, /* computed hash digest */
                rng, &ecc,    /* random and key context */
                &r, &s        /* r/s as mp_int */
            );
            count++;

            /* TODO: Real-time work can be called here */
        } while (ret == FP_WOULDBLOCK);

    #ifdef DEBUG_WOLFSSL
        printf("ECC non-block sign: %d times\n", count);
    #endif
    }

    if (ret == 0) {
        /* export r/s */
        mp_to_unsigned_bin(&r, sig);
        mp_to_unsigned_bin(&s, sig + curveSz);
    }

    mp_clear(&r);
    mp_clear(&s);
    wc_ecc_free(&ecc);

    (void)count;

    return ret;
}

static int ecc_test_nonblock(WC_RNG* rng)
{
    int ret;
    uint8_t hash[HASH_DIGEST_SZ];
    uint8_t sig[ECC_CURVE_SZ*2];
    uint32_t sigSz = sizeof(sig);

    ret = CRYPTO_HASH_FN(
        kMsg, sizeof(kMsg), /* input message */
        hash, sizeof(hash), /* hash digest result */
        32                  /* configurable block / chunk size */
    );
    if (ret == 0) {
        /* Sign hash using private key */
        /* Note: result of an ECC sign varies for each call even with same 
            private key and hash. This is because a new random public key is 
            used for each operation. */ 
        ret = crypto_ecc_sign(
            kPrivKey, sizeof(kPrivKey), /* private key */
            hash, sizeof(hash),         /* computed hash digest */
            sig, &sigSz,                /* signature r/s */
            ECC_CURVE_SZ,               /* curve size in bytes */
            ECC_CURVE_ID,               /* curve id */
            rng
        );
    }

    if (ret == 0) {
        /* Verify generated signature is valid */
        ret = crypto_ecc_verify(
            kPubKey, sizeof(kPubKey),   /* public key point x/y */
            hash, sizeof(hash),         /* computed hash digest */
            sig, sigSz,                 /* signature r/s */
            ECC_CURVE_SZ,               /* curve size in bytes */
            ECC_CURVE_ID                /* curve id */
        );
    }

    return ret;
}
#endif /* WC_ECC_NONBLOCK && WOLFSSL_PUBLIC_MP && HAVE_ECC_SIGN && HAVE_ECC_VERIFY */

int ecc_test(void)
{
    int ret;
    WC_RNG  rng;

#ifdef WOLFSSL_CERT_EXT
    ret = ecc_decode_test();
    if (ret < 0)
        return ret;
#endif

#ifndef HAVE_FIPS
    ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
    ret = wc_InitRng(&rng);
#endif
    if (ret != 0)
        return -9900;

#if defined(HAVE_ECC112) || defined(HAVE_ALL_CURVES)
    ret = ecc_test_curve(&rng, 14);
    if (ret < 0) {
        goto done;
    }
#endif /* HAVE_ECC112 */
#if defined(HAVE_ECC128) || defined(HAVE_ALL_CURVES)
    ret = ecc_test_curve(&rng, 16);
    if (ret < 0) {
        goto done;
    }
#endif /* HAVE_ECC128 */
#if defined(HAVE_ECC160) || defined(HAVE_ALL_CURVES)
    ret = ecc_test_curve(&rng, 20);
    if (ret < 0) {
        goto done;
    }
#endif /* HAVE_ECC160 */
#if defined(HAVE_ECC192) || defined(HAVE_ALL_CURVES)
    ret = ecc_test_curve(&rng, 24);
    if (ret < 0) {
        goto done;
    }
#endif /* HAVE_ECC192 */
#if defined(HAVE_ECC224) || defined(HAVE_ALL_CURVES)
    ret = ecc_test_curve(&rng, 28);
    if (ret < 0) {
        goto done;
    }
#endif /* HAVE_ECC224 */
#if defined(HAVE_ECC239) || defined(HAVE_ALL_CURVES)
    ret = ecc_test_curve(&rng, 30);
    if (ret < 0) {
        goto done;
    }
#endif /* HAVE_ECC239 */
#if !defined(NO_ECC256) || defined(HAVE_ALL_CURVES)
    ret = ecc_test_curve(&rng, 32);
    if (ret < 0) {
        goto done;
    }
#if !defined(WOLFSSL_ATECC508A) && !defined(WOLFSSL_ATECC608A) && \
    defined(HAVE_ECC_KEY_IMPORT) && defined(HAVE_ECC_KEY_EXPORT)
    ret = ecc_point_test();
    if (ret < 0) {
        goto done;
    }
#endif
    ret = ecc_def_curve_test(&rng);
    if (ret < 0) {
        goto done;
    }
#endif /* !NO_ECC256 */
#if defined(HAVE_ECC320) || defined(HAVE_ALL_CURVES)
    ret = ecc_test_curve(&rng, 40);
    if (ret < 0) {
        goto done;
    }
#endif /* HAVE_ECC320 */
#if defined(HAVE_ECC384) || defined(HAVE_ALL_CURVES)
    ret = ecc_test_curve(&rng, 48);
    if (ret < 0) {
        goto done;
    }
#endif /* HAVE_ECC384 */
#if defined(HAVE_ECC512) || defined(HAVE_ALL_CURVES)
    ret = ecc_test_curve(&rng, 64);
    if (ret < 0) {
        goto done;
    }
#endif /* HAVE_ECC512 */
#if defined(HAVE_ECC521) || defined(HAVE_ALL_CURVES)
    ret = ecc_test_curve(&rng, 66);
    if (ret < 0) {
        goto done;
    }
#endif /* HAVE_ECC521 */

#if defined(WOLFSSL_CUSTOM_CURVES)
    ret = ecc_test_custom_curves(&rng);
    if (ret != 0) {
        goto done;
    }
#endif

#if defined(HAVE_ECC_SIGN) && defined(WOLFSSL_ECDSA_SET_K)
    ret = ecc_test_sign_vectors(&rng);
    if (ret != 0) {
        printf("ecc_test_sign_vectors failed! %d\n", ret);
        goto done;
    }
#endif
#ifdef HAVE_ECC_CDH
    ret = ecc_test_cdh_vectors(&rng);
    if (ret != 0) {
        printf("ecc_test_cdh_vectors failed! %d\n", ret);
        goto done;
    }
#endif
#if !defined(WOLFSSL_ATECC508A) && !defined(WOLFSSL_ATECC608A) && \
    !defined(WOLFSSL_STM32_PKA)
    ret = ecc_test_make_pub(&rng);
    if (ret != 0) {
        printf("ecc_test_make_pub failed!: %d\n", ret);
        goto done;
    }
#elif defined(HAVE_ECC_KEY_IMPORT)
    (void) ecc_test_make_pub;/* for compiler warning */
#endif
#ifdef WOLFSSL_CERT_GEN
    ret = ecc_test_cert_gen(&rng);
    if (ret != 0) {
        printf("ecc_test_cert_gen failed!: %d\n", ret);
        goto done;
    }
#endif
#if !defined(HAVE_FIPS) && !defined(HAVE_SELFTEST)
    ret = ecc_test_allocator(&rng);
    if (ret != 0) {
        printf("ecc_test_allocator failed!: %d\n", ret);
    }
#endif

#if defined(WC_ECC_NONBLOCK) && defined(WOLFSSL_PUBLIC_MP) && \
    defined(HAVE_ECC_SIGN) && defined(HAVE_ECC_VERIFY)
    ret = ecc_test_nonblock(&rng);
    if (ret != 0) {
        printf("ecc_test_nonblock failed!: %d\n", ret);
    }
#endif

done:
    wc_FreeRng(&rng);

    return ret;
}

#if defined(HAVE_ECC_ENCRYPT) && defined(WOLFSSL_AES_128)

int ecc_encrypt_test(void)
{
    WC_RNG  rng;
    int     ret = 0;
    ecc_key userA, userB;
    byte    msg[48];
    byte    plain[48];
    byte    out[80];
    word32  outSz   = sizeof(out);
    word32  plainSz = sizeof(plain);
    int     i;
    ecEncCtx* cliCtx = NULL;
    ecEncCtx* srvCtx = NULL;
    byte cliSalt[EXCHANGE_SALT_SZ];
    byte srvSalt[EXCHANGE_SALT_SZ];
    const byte* tmpSalt;
    byte    msg2[48];
    byte    plain2[48];
    byte    out2[80];
    word32  outSz2   = sizeof(out2);
    word32  plainSz2 = sizeof(plain2);

#ifndef HAVE_FIPS
    ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
    ret = wc_InitRng(&rng);
#endif
    if (ret != 0)
        return -10000;

    XMEMSET(&userA, 0, sizeof(userA));
    XMEMSET(&userB, 0, sizeof(userB));

    ret = wc_ecc_init_ex(&userA, HEAP_HINT, devId);
    if (ret != 0)
        goto done;
    ret = wc_ecc_init_ex(&userB, HEAP_HINT, devId);
    if (ret != 0)
        goto done;

    ret  = wc_ecc_make_key(&rng, ECC_KEYGEN_SIZE, &userA);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &userA.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0){
        ret = -10001; goto done;
    }

    ret = wc_ecc_make_key(&rng, ECC_KEYGEN_SIZE, &userB);
#if defined(WOLFSSL_ASYNC_CRYPT)
    ret = wc_AsyncWait(ret, &userB.asyncDev, WC_ASYNC_FLAG_NONE);
#endif
    if (ret != 0){
        ret = -10002; goto done;
    }

    /* set message to incrementing 0,1,2,etc... */
    for (i = 0; i < (int)sizeof(msg); i++)
        msg[i] = i;

#if defined(ECC_TIMING_RESISTANT) && (!defined(HAVE_FIPS) || \
    (!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION != 2))) && \
    !defined(HAVE_SELFTEST)
    ret = wc_ecc_set_rng(&userA, &rng);
    if (ret != 0) {
        ret = -10011; goto done;
    }
    ret = wc_ecc_set_rng(&userB, &rng);
    if (ret != 0) {
        ret = -10012; goto done;
    }
#endif

    /* encrypt msg to B */
    ret = wc_ecc_encrypt(&userA, &userB, msg, sizeof(msg), out, &outSz, NULL);
    if (ret != 0) {
        ret = -10003; goto done;
    }

    /* decrypt msg from A */
    ret = wc_ecc_decrypt(&userB, &userA, out, outSz, plain, &plainSz, NULL);
    if (ret != 0) {
        ret = -10004; goto done;
    }

    if (XMEMCMP(plain, msg, sizeof(msg)) != 0) {
        ret = -10005; goto done;
    }

    /* let's verify message exchange works, A is client, B is server */
    cliCtx = wc_ecc_ctx_new(REQ_RESP_CLIENT, &rng);
    srvCtx = wc_ecc_ctx_new(REQ_RESP_SERVER, &rng);
    if (cliCtx == NULL || srvCtx == NULL) {
        ret = -10006; goto done;
    }

    /* get salt to send to peer */
    tmpSalt = wc_ecc_ctx_get_own_salt(cliCtx);
    if (tmpSalt == NULL) {
        ret = -10007; goto done;
    }
    XMEMCPY(cliSalt, tmpSalt, EXCHANGE_SALT_SZ);

    tmpSalt = wc_ecc_ctx_get_own_salt(srvCtx);
    if (tmpSalt == NULL) {
        ret = -10008; goto done;
    }
    XMEMCPY(srvSalt, tmpSalt, EXCHANGE_SALT_SZ);

    /* in actual use, we'd get the peer's salt over the transport */
    ret = wc_ecc_ctx_set_peer_salt(cliCtx, srvSalt);
    if (ret != 0)
        goto done;
    ret = wc_ecc_ctx_set_peer_salt(srvCtx, cliSalt);
    if (ret != 0)
        goto done;

    ret = wc_ecc_ctx_set_info(cliCtx, (byte*)"wolfSSL MSGE", 11);
    if (ret != 0)
        goto done;
    ret = wc_ecc_ctx_set_info(srvCtx, (byte*)"wolfSSL MSGE", 11);
    if (ret != 0)
        goto done;

    /* get encrypted msg (request) to send to B */
    outSz = sizeof(out);
    ret = wc_ecc_encrypt(&userA, &userB, msg, sizeof(msg), out, &outSz,cliCtx);
    if (ret != 0)
        goto done;

    /* B decrypts msg (request) from A */
    plainSz = sizeof(plain);
    ret = wc_ecc_decrypt(&userB, &userA, out, outSz, plain, &plainSz, srvCtx);
    if (ret != 0)
        goto done;

    if (XMEMCMP(plain, msg, sizeof(msg)) != 0) {
        ret = -10009; goto done;
    }

    /* msg2 (response) from B to A */
    for (i = 0; i < (int)sizeof(msg2); i++)
        msg2[i] = i + sizeof(msg2);

    /* get encrypted msg (response) to send to B */
    ret = wc_ecc_encrypt(&userB, &userA, msg2, sizeof(msg2), out2,
                      &outSz2, srvCtx);
    if (ret != 0)
        goto done;

    /* A decrypts msg (response) from B */
    ret = wc_ecc_decrypt(&userA, &userB, out2, outSz2, plain2, &plainSz2,
                     cliCtx);
    if (ret != 0)
        goto done;

    if (XMEMCMP(plain2, msg2, sizeof(msg2)) != 0) {
        ret = -10010; goto done;
    }

done:

    /* cleanup */
    wc_ecc_ctx_free(srvCtx);
    wc_ecc_ctx_free(cliCtx);

    wc_ecc_free(&userB);
    wc_ecc_free(&userA);
    wc_FreeRng(&rng);

    return ret;
}

#endif /* HAVE_ECC_ENCRYPT */

#if defined(USE_CERT_BUFFERS_256) && !defined(WOLFSSL_ATECC508A) && \
    !defined(WOLFSSL_ATECC608A) && !defined(NO_ECC256)
int ecc_test_buffers(void) {
    size_t bytes;
    ecc_key cliKey;
    ecc_key servKey;
    WC_RNG rng;
    word32 idx = 0;
    int    ret;
    /* pad our test message to 32 bytes so evenly divisible by AES_BLOCK_SZ */
    byte   in[] = "Everyone gets Friday off. ecc p";
    word32 inLen = (word32)XSTRLEN((char*)in);
    byte   out[256];
    byte   plain[256];
    int verify = 0;
    word32 x;

    ret = wc_ecc_init_ex(&cliKey, HEAP_HINT, devId);
    if (ret != 0)
        return -10011;
    ret = wc_ecc_init_ex(&servKey, HEAP_HINT, devId);
    if (ret != 0)
        return -10012;

    bytes = (size_t)sizeof_ecc_clikey_der_256;
    /* place client key into ecc_key struct cliKey */
    ret = wc_EccPrivateKeyDecode(ecc_clikey_der_256, &idx, &cliKey,
                                                                (word32)bytes);
    if (ret != 0)
        return -10013;

    idx = 0;
    bytes = (size_t)sizeof_ecc_key_der_256;

    /* place server key into ecc_key struct servKey */
    ret = wc_EccPrivateKeyDecode(ecc_key_der_256, &idx, &servKey,
                                                                (word32)bytes);
    if (ret != 0)
        return -10014;

#ifndef HAVE_FIPS
    ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
    ret = wc_InitRng(&rng);
#endif
    if (ret != 0)
        return -10015;

#if defined(ECC_TIMING_RESISTANT) && (!defined(HAVE_FIPS) || \
    (!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION != 2))) && \
    !defined(HAVE_SELFTEST)
    ret = wc_ecc_set_rng(&cliKey, &rng);
    if (ret != 0) {
        return -10023;
    }
#endif

#if defined(HAVE_ECC_ENCRYPT) && defined(HAVE_HKDF)
    {
        word32 y;
        /* test encrypt and decrypt if they're available */
        x = sizeof(out);
        ret = wc_ecc_encrypt(&cliKey, &servKey, in, sizeof(in), out, &x, NULL);
        if (ret < 0)
            return -10016;

        y = sizeof(plain);
        ret = wc_ecc_decrypt(&cliKey, &servKey, out, x, plain, &y, NULL);
        if (ret < 0)
            return -10017;

        if (XMEMCMP(plain, in, inLen))
            return -10018;
    }
#endif

    x = sizeof(out);
    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &cliKey.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret == 0)
            ret = wc_ecc_sign_hash(in, inLen, out, &x, &rng, &cliKey);
    } while (ret == WC_PENDING_E);
    if (ret < 0)
        return -10019;
    TEST_SLEEP();

    XMEMSET(plain, 0, sizeof(plain));

    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &cliKey.asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret == 0)
            ret = wc_ecc_verify_hash(out, x, plain, sizeof(plain), &verify,
                &cliKey);
    } while (ret == WC_PENDING_E);
    if (ret < 0)
        return -10020;

    if (XMEMCMP(plain, in, (word32)ret))
        return -10021;
    TEST_SLEEP();

#ifdef WOLFSSL_CERT_EXT
    idx = 0;

    bytes = sizeof_ecc_clikeypub_der_256;

    ret = wc_EccPublicKeyDecode(ecc_clikeypub_der_256, &idx, &cliKey,
                                                               (word32) bytes);
    if (ret != 0)
        return -10022;
#endif

    wc_ecc_free(&cliKey);
    wc_ecc_free(&servKey);
    wc_FreeRng(&rng);

    return 0;
}
#endif /* USE_CERT_BUFFERS_256 && !WOLFSSL_ATECCX08A && !NO_ECC256 */
#endif /* HAVE_ECC */


#ifdef HAVE_CURVE25519
#if defined(HAVE_CURVE25519_SHARED_SECRET) && \
                                             defined(HAVE_CURVE25519_KEY_IMPORT)
#ifdef CURVE25519_OVERFLOW_ALL_TESTS
#define X25519_TEST_CNT    5
#else
#define X25519_TEST_CNT    1
#endif
static int curve25519_overflow_test(void)
{
    /* secret key for party a */
    byte sa[X25519_TEST_CNT][32] = {
        {
            0x8d,0xaf,0x6e,0x7a,0xc1,0xeb,0x8d,0x30,
            0x99,0x86,0xd3,0x90,0x47,0x96,0x21,0x3c,
            0x3a,0x75,0xc0,0x7b,0x75,0x01,0x75,0xa3,
            0x81,0x4b,0xff,0x5a,0xbc,0x96,0x87,0x28
        },
#ifdef CURVE25519_OVERFLOW_ALL_TESTS
        {
            0x9d,0x63,0x5f,0xce,0xe2,0xe8,0xd7,0xfb,
            0x68,0x77,0x0e,0x44,0xd1,0xad,0x87,0x2b,
            0xf4,0x65,0x06,0xb7,0xbb,0xdb,0xbe,0x6e,
            0x02,0x43,0x24,0xc7,0x3d,0x7b,0x88,0x60
        },
        {
            0x63,0xbf,0x76,0xa9,0x73,0xa0,0x09,0xb9,
            0xcc,0xc9,0x4d,0x47,0x2d,0x14,0x0e,0x52,
            0xa3,0x84,0x55,0xb8,0x7c,0xdb,0xce,0xb1,
            0xe4,0x5b,0x8a,0xb9,0x30,0xf1,0xa4,0xa0
        },
        {
            0x63,0xbf,0x76,0xa9,0x73,0xa0,0x09,0xb9,
            0xcc,0xc9,0x4d,0x47,0x2d,0x14,0x0e,0x52,
            0xa3,0x84,0x55,0xb8,0x7c,0xdb,0xce,0xb1,
            0xe4,0x5b,0x8a,0xb9,0x30,0xf1,0xa4,0xa0
        },
        {
            0x63,0xbf,0x76,0xa9,0x73,0xa0,0x09,0xb9,
            0xcc,0xc9,0x4d,0x47,0x2d,0x14,0x0e,0x52,
            0xa3,0x84,0x55,0xb8,0x7c,0xdb,0xce,0xb1,
            0xe4,0x5b,0x8a,0xb9,0x30,0xf1,0xa4,0xa0
        }
#endif
    };

    /* public key for party b */
    byte pb[X25519_TEST_CNT][32] = {
        {
            0x7f,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xf0
        },
#ifdef CURVE25519_OVERFLOW_ALL_TESTS
        {
            /* 0xff first byte in original - invalid! */
            0x7f,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xf0
        },
        {
            0x36,0x1a,0x74,0x87,0x28,0x59,0xe0,0xb6,
            0xe4,0x2b,0x17,0x9b,0x16,0xb0,0x3b,0xf8,
            0xb8,0x9f,0x2a,0x8f,0xc5,0x33,0x68,0x4f,
            0xde,0x4d,0xd8,0x80,0x63,0xe7,0xb4,0x0a
        },
        {
            0x00,0x80,0x38,0x59,0x19,0x3a,0x66,0x12,
            0xfd,0xa1,0xec,0x1c,0x40,0x84,0x40,0xbd,
            0x64,0x10,0x8b,0x53,0x81,0x21,0x03,0x2d,
            0x7d,0x33,0xb4,0x01,0x57,0x0d,0xe1,0x89
        },
        {
            0x1d,0xf8,0xf8,0x33,0x89,0x6c,0xb7,0xba,
            0x94,0x73,0xfa,0xc2,0x36,0xac,0xbe,0x49,
            0xaf,0x85,0x3e,0x93,0x5f,0xae,0xb2,0xc0,
            0xc8,0x80,0x8f,0x4a,0xaa,0xd3,0x55,0x2b
        }
#endif
    };

    /* expected shared key */
    byte ss[X25519_TEST_CNT][32] = {
        {
            0x5c,0x4c,0x85,0x5f,0xfb,0x20,0x38,0xcc,
            0x55,0x16,0x5b,0x8a,0xa7,0xed,0x57,0x6e,
            0x35,0xaa,0x71,0x67,0x85,0x1f,0xb6,0x28,
            0x17,0x07,0x7b,0xda,0x76,0xdd,0xe0,0xb4
        },
#ifdef CURVE25519_OVERFLOW_ALL_TESTS
        {
            0x33,0xf6,0xc1,0x34,0x62,0x92,0x06,0x02,
            0x95,0xdb,0x91,0x4c,0x5d,0x52,0x54,0xc7,
            0xd2,0x5b,0x24,0xb5,0x4f,0x33,0x59,0x79,
            0x9f,0x6d,0x7e,0x4a,0x4c,0x30,0xd6,0x38
        },
        {
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x02
        },
        {
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x09
        },
        {
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x10
        }
#endif
    };

    int            i;
    word32         y;
    byte           shared[32];
    curve25519_key userA;

    wc_curve25519_init(&userA);

    for (i = 0; i < X25519_TEST_CNT; i++) {
        if (wc_curve25519_import_private_raw(sa[i], sizeof(sa[i]), pb[i],
                                                    sizeof(pb[i]), &userA) != 0)
            return -10100 - i;

        /* test against known test vector */
        XMEMSET(shared, 0, sizeof(shared));
        y = sizeof(shared);
        if (wc_curve25519_shared_secret(&userA, &userA, shared, &y) != 0)
            return -10110 - i;

        if (XMEMCMP(ss[i], shared, y))
            return -10120 - i;
    }

    return 0;
}

/* Test the wc_curve25519_check_public API.
 *
 * returns 0 on success and -ve on failure.
 */
static int curve25519_check_public_test(void)
{
    /* Little-endian values that will fail */
    byte fail_le[][CURVE25519_KEYSIZE] = {
        {
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
        },
        {
            0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
        },
        {
            0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x81
        },
    };
    /* Big-endian values that will fail */
    byte fail_be[][CURVE25519_KEYSIZE] = {
        {
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
        },
        {
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x01
        },
        {
            0x81,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x01
        },
    };
    /* Good or valid public value */
    byte good[CURVE25519_KEYSIZE] = {
        0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x01
    };
    int i;

    /* Parameter checks */
    /* NULL pointer */
    if (wc_curve25519_check_public(NULL, 0, EC25519_LITTLE_ENDIAN) !=
                                                                 BAD_FUNC_ARG) {
        return -10200;
    }
    if (wc_curve25519_check_public(NULL, 0, EC25519_BIG_ENDIAN) !=
                                                                 BAD_FUNC_ARG) {
        return -10201;
    }
    /* Length of 0 treated differently to other invalid lengths for TLS */
    if (wc_curve25519_check_public(good, 0, EC25519_LITTLE_ENDIAN) != BUFFER_E)
        return -10202;
    if (wc_curve25519_check_public(good, 0, EC25519_BIG_ENDIAN) != BUFFER_E)
        return -10203;

    /* Length not CURVE25519_KEYSIZE */
    for (i = 1; i < CURVE25519_KEYSIZE + 2; i++) {
        if (i == CURVE25519_KEYSIZE)
            continue;
        if (wc_curve25519_check_public(good, i, EC25519_LITTLE_ENDIAN) !=
                                                                ECC_BAD_ARG_E) {
            return -10204 - i;
        }
        if (wc_curve25519_check_public(good, i, EC25519_BIG_ENDIAN) !=
                                                                ECC_BAD_ARG_E) {
            return -10214 - i;
        }
    }

    /* Little-endian fail cases */
    for (i = 0; i < (int)(sizeof(fail_le) / sizeof(*fail_le)); i++) {
        if (wc_curve25519_check_public(fail_le[i], CURVE25519_KEYSIZE,
                                                  EC25519_LITTLE_ENDIAN) == 0) {
            return -10224 - i;
        }
    }
    /* Big-endian fail cases */
    for (i = 0; i < (int)(sizeof(fail_be) / sizeof(*fail_be)); i++) {
        if (wc_curve25519_check_public(fail_be[i], CURVE25519_KEYSIZE,
                                                     EC25519_BIG_ENDIAN) == 0) {
            return -10234 - i;
        }
    }

    /* Check a valid public value works! */
    if (wc_curve25519_check_public(good, CURVE25519_KEYSIZE,
                                                  EC25519_LITTLE_ENDIAN) != 0) {
        return -10244;
    }
    if (wc_curve25519_check_public(good, CURVE25519_KEYSIZE,
                                                     EC25519_BIG_ENDIAN) != 0) {
        return -10245;
    }

    return 0;
}

#endif /* HAVE_CURVE25519_SHARED_SECRET && HAVE_CURVE25519_KEY_IMPORT */

int curve25519_test(void)
{
    WC_RNG  rng;
    int ret;
#ifdef HAVE_CURVE25519_SHARED_SECRET
    byte    sharedA[32];
    byte    sharedB[32];
    word32  y;
#endif
#ifdef HAVE_CURVE25519_KEY_EXPORT
    byte    exportBuf[32];
#endif
    word32  x = 0;
    curve25519_key userA, userB, pubKey;

#if defined(HAVE_CURVE25519_SHARED_SECRET) && \
                                             defined(HAVE_CURVE25519_KEY_IMPORT)
    /* test vectors from
       https://tools.ietf.org/html/draft-josefsson-tls-curve25519-03
     */

    /* secret key for party a */
    byte sa[] = {
        0x5A,0xC9,0x9F,0x33,0x63,0x2E,0x5A,0x76,
        0x8D,0xE7,0xE8,0x1B,0xF8,0x54,0xC2,0x7C,
        0x46,0xE3,0xFB,0xF2,0xAB,0xBA,0xCD,0x29,
        0xEC,0x4A,0xFF,0x51,0x73,0x69,0xC6,0x60
    };

    /* public key for party a */
    byte pa[] = {
        0x05,0x7E,0x23,0xEA,0x9F,0x1C,0xBE,0x8A,
        0x27,0x16,0x8F,0x6E,0x69,0x6A,0x79,0x1D,
        0xE6,0x1D,0xD3,0xAF,0x7A,0xCD,0x4E,0xEA,
        0xCC,0x6E,0x7B,0xA5,0x14,0xFD,0xA8,0x63
    };

    /* secret key for party b */
    byte sb[] = {
        0x47,0xDC,0x3D,0x21,0x41,0x74,0x82,0x0E,
        0x11,0x54,0xB4,0x9B,0xC6,0xCD,0xB2,0xAB,
        0xD4,0x5E,0xE9,0x58,0x17,0x05,0x5D,0x25,
        0x5A,0xA3,0x58,0x31,0xB7,0x0D,0x32,0x60
    };

    /* public key for party b */
    byte pb[] = {
        0x6E,0xB8,0x9D,0xA9,0x19,0x89,0xAE,0x37,
        0xC7,0xEA,0xC7,0x61,0x8D,0x9E,0x5C,0x49,
        0x51,0xDB,0xA1,0xD7,0x3C,0x28,0x5A,0xE1,
        0xCD,0x26,0xA8,0x55,0x02,0x0E,0xEF,0x04
    };

    /* expected shared key */
    byte ss[] = {
        0x61,0x45,0x0C,0xD9,0x8E,0x36,0x01,0x6B,
        0x58,0x77,0x6A,0x89,0x7A,0x9F,0x0A,0xEF,
        0x73,0x8B,0x99,0xF0,0x94,0x68,0xB8,0xD6,
        0xB8,0x51,0x11,0x84,0xD5,0x34,0x94,0xAB
    };
#endif /* HAVE_CURVE25519_SHARED_SECRET */

    (void)x;

#ifndef HAVE_FIPS
    ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
    ret = wc_InitRng(&rng);
#endif
    if (ret != 0)
        return -10300;

    wc_curve25519_init(&userA);
    wc_curve25519_init(&userB);
    wc_curve25519_init(&pubKey);

    /* make curve25519 keys */
    if (wc_curve25519_make_key(&rng, 32, &userA) != 0)
        return -10301;

    if (wc_curve25519_make_key(&rng, 32, &userB) != 0)
        return -10302;

#ifdef HAVE_CURVE25519_SHARED_SECRET
    /* find shared secret key */
    x = sizeof(sharedA);
    if (wc_curve25519_shared_secret(&userA, &userB, sharedA, &x) != 0)
        return -10303;

    y = sizeof(sharedB);
    if (wc_curve25519_shared_secret(&userB, &userA, sharedB, &y) != 0)
        return -10304;

    /* compare shared secret keys to test they are the same */
    if (y != x)
        return -10305;

    if (XMEMCMP(sharedA, sharedB, x))
        return -10306;
#endif

#ifdef HAVE_CURVE25519_KEY_EXPORT
    /* export a public key and import it for another user */
    x = sizeof(exportBuf);
    if (wc_curve25519_export_public(&userA, exportBuf, &x) != 0)
        return -10307;

#ifdef HAVE_CURVE25519_KEY_IMPORT
    if (wc_curve25519_import_public(exportBuf, x, &pubKey) != 0)
        return -10308;
#endif
#endif

#if defined(HAVE_CURVE25519_SHARED_SECRET) && \
                                             defined(HAVE_CURVE25519_KEY_IMPORT)
    /* test shared key after importing a public key */
    XMEMSET(sharedB, 0, sizeof(sharedB));
    y = sizeof(sharedB);
    if (wc_curve25519_shared_secret(&userB, &pubKey, sharedB, &y) != 0)
        return -10309;

    if (XMEMCMP(sharedA, sharedB, y))
        return -10310;

    /* import RFC test vectors and compare shared key */
    if (wc_curve25519_import_private_raw(sa, sizeof(sa), pa, sizeof(pa), &userA)
            != 0)
        return -10311;

    if (wc_curve25519_import_private_raw(sb, sizeof(sb), pb, sizeof(pb), &userB)
            != 0)
        return -10312;

    /* test against known test vector */
    XMEMSET(sharedB, 0, sizeof(sharedB));
    y = sizeof(sharedB);
    if (wc_curve25519_shared_secret(&userA, &userB, sharedB, &y) != 0)
        return -10313;

    if (XMEMCMP(ss, sharedB, y))
        return -10314;

    /* test swapping roles of keys and generating same shared key */
    XMEMSET(sharedB, 0, sizeof(sharedB));
    y = sizeof(sharedB);
    if (wc_curve25519_shared_secret(&userB, &userA, sharedB, &y) != 0)
        return -10315;

    if (XMEMCMP(ss, sharedB, y))
        return -10316;

    /* test with 1 generated key and 1 from known test vector */
    if (wc_curve25519_import_private_raw(sa, sizeof(sa), pa, sizeof(pa), &userA)
        != 0)
        return -10317;

    if (wc_curve25519_make_key(&rng, 32, &userB) != 0)
        return -10318;

    x = sizeof(sharedA);
    if (wc_curve25519_shared_secret(&userA, &userB, sharedA, &x) != 0)
        return -10319;

    y = sizeof(sharedB);
    if (wc_curve25519_shared_secret(&userB, &userA, sharedB, &y) != 0)
        return -10320;

    /* compare shared secret keys to test they are the same */
    if (y != x)
        return -10321;

    if (XMEMCMP(sharedA, sharedB, x))
        return -10322;

    ret = curve25519_overflow_test();
    if (ret != 0)
        return ret;
    ret = curve25519_check_public_test();
    if (ret != 0)
        return ret;
#endif /* HAVE_CURVE25519_SHARED_SECRET && HAVE_CURVE25519_KEY_IMPORT */

    /* clean up keys when done */
    wc_curve25519_free(&pubKey);
    wc_curve25519_free(&userB);
    wc_curve25519_free(&userA);

    wc_FreeRng(&rng);

    return 0;
}
#endif /* HAVE_CURVE25519 */


#ifdef HAVE_ED25519
#ifdef WOLFSSL_TEST_CERT
static int ed25519_test_cert(void)
{
    DecodedCert  cert[2];
    DecodedCert* serverCert = NULL;
    DecodedCert* caCert = NULL;
#ifdef HAVE_ED25519_VERIFY
    ed25519_key  key;
    ed25519_key* pubKey = NULL;
    int          verify;
#endif /* HAVE_ED25519_VERIFY */
    int          ret;
    byte*        tmp;
    size_t       bytes;
    XFILE        file;

    tmp = XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (tmp == NULL) {
        ERROR_OUT(-10323, done);
    }

#ifdef USE_CERT_BUFFERS_256
    XMEMCPY(tmp, ca_ed25519_cert, sizeof_ca_ed25519_cert);
    bytes = sizeof_ca_ed25519_cert;
#elif !defined(NO_FILESYSTEM)
    file = XFOPEN(caEd25519Cert, "rb");
    if (file == NULL) {
        ERROR_OUT(-10324, done);
    }
    bytes = XFREAD(tmp, 1, FOURK_BUF, file);
    XFCLOSE(file);
#else
    /* No certificate to use. */
    ERROR_OUT(-10325, done);
#endif

    InitDecodedCert(&cert[0], tmp, (word32)bytes, 0);
    caCert = &cert[0];
    ret = ParseCert(caCert, CERT_TYPE, NO_VERIFY, NULL);
    if (ret != 0) {
        ERROR_OUT(-10326, done);
    }

#ifdef USE_CERT_BUFFERS_256
    XMEMCPY(tmp, server_ed25519_cert, sizeof_server_ed25519_cert);
    bytes = sizeof_server_ed25519_cert;
#elif !defined(NO_FILESYSTEM)
    file = XFOPEN(serverEd25519Cert, "rb");
    if (file == NULL) {
        ERROR_OUT(-10327, done);
    }
    bytes = XFREAD(tmp, 1, FOURK_BUF, file);
    XFCLOSE(file);
#else
    /* No certificate to use. */
    ERROR_OUT(-10328, done);
#endif

    InitDecodedCert(&cert[1], tmp, (word32)bytes, 0);
    serverCert = &cert[1];
    ret = ParseCert(serverCert, CERT_TYPE, NO_VERIFY, NULL);
    if (ret != 0) {
        ERROR_OUT(-10329, done);
    }

#ifdef HAVE_ED25519_VERIFY
    ret = wc_ed25519_init(&key);
    if (ret < 0) {
        ERROR_OUT(-10330, done);
    }
    pubKey = &key;
    ret = wc_ed25519_import_public(caCert->publicKey, caCert->pubKeySize,
                                                                        pubKey);
    if (ret < 0) {
        ERROR_OUT(-10331, done);
    }

    if (wc_ed25519_verify_msg(serverCert->signature, serverCert->sigLength,
                              serverCert->source + serverCert->certBegin,
                              serverCert->sigIndex - serverCert->certBegin,
                              &verify, pubKey) < 0 || verify != 1) {
        ERROR_OUT(-10332, done);
    }
#endif /* HAVE_ED25519_VERIFY */

done:
    if (tmp != NULL)
        XFREE(tmp, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
#ifdef HAVE_ED25519_VERIFY
    wc_ed25519_free(pubKey);
#endif /* HAVE_ED25519_VERIFY */
    if (caCert != NULL)
        FreeDecodedCert(caCert);
    if (serverCert != NULL)
        FreeDecodedCert(serverCert);

    return ret;
}

static int ed25519_test_make_cert(void)
{
    WC_RNG       rng;
    Cert         cert;
    DecodedCert  decode;
    ed25519_key  key;
    ed25519_key* privKey = NULL;
    int          ret = 0;
    byte*        tmp = NULL;

    wc_InitCert(&cert);

#ifndef HAVE_FIPS
    ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
    ret = wc_InitRng(&rng);
#endif
    if (ret != 0)
        return -10333;

    wc_ed25519_init(&key);
    privKey = &key;
    wc_ed25519_make_key(&rng, ED25519_KEY_SIZE, privKey);

    cert.daysValid = 365 * 2;
    cert.selfSigned = 1;
    XMEMCPY(&cert.issuer, &certDefaultName, sizeof(CertName));
    XMEMCPY(&cert.subject, &certDefaultName, sizeof(CertName));
    cert.isCA = 0;
#ifdef WOLFSSL_CERT_EXT
    ret = wc_SetKeyUsage(&cert, certKeyUsage);
    if (ret < 0) {
        ERROR_OUT(-10334, done);
    }
    ret = wc_SetSubjectKeyIdFromPublicKey_ex(&cert, ED25519_TYPE, privKey);
    if (ret < 0) {
        ERROR_OUT(-10335, done);
    }
    ret = wc_SetAuthKeyIdFromPublicKey_ex(&cert, ED25519_TYPE, privKey);
    if (ret < 0) {
        ERROR_OUT(-10336, done);
    }
#endif
    tmp = XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (tmp == NULL) {
        ERROR_OUT(-10337, done);
    }

    cert.sigType = CTC_ED25519;
    ret = wc_MakeCert_ex(&cert, tmp, FOURK_BUF, ED25519_TYPE, privKey, &rng);
    if (ret < 0) {
        ERROR_OUT(-10338, done);
    }
    ret = wc_SignCert_ex(cert.bodySz, cert.sigType, tmp, FOURK_BUF,
                                                   ED25519_TYPE, privKey, &rng);
    if (ret < 0) {
        ERROR_OUT(-10339, done);
    }

    InitDecodedCert(&decode, tmp, ret, HEAP_HINT);
    ret = ParseCert(&decode, CERT_TYPE, NO_VERIFY, 0);
    FreeDecodedCert(&decode);
    if (ret != 0) {
        ERROR_OUT(-10340, done);
    }

done:
    if (tmp != NULL)
        XFREE(tmp, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    wc_ed25519_free(privKey);
    wc_FreeRng(&rng);
    return ret;
}
#endif /* WOLFSSL_TEST_CERT */

#if defined(HAVE_ED25519_SIGN) && defined(HAVE_ED25519_KEY_EXPORT) && \
    defined(HAVE_ED25519_KEY_IMPORT)
static int ed25519ctx_test(void)
{
    byte   out[ED25519_SIG_SIZE];
    word32 outlen;
#ifdef HAVE_ED25519_VERIFY
    int    verify;
#endif /* HAVE_ED25519_VERIFY */
    ed25519_key key;

    static const byte sKeyCtx[] = {
        0x03,0x05,0x33,0x4e,0x38,0x1a,0xf7,0x8f,
        0x14,0x1c,0xb6,0x66,0xf6,0x19,0x9f,0x57,
        0xbc,0x34,0x95,0x33,0x5a,0x25,0x6a,0x95,
        0xbd,0x2a,0x55,0xbf,0x54,0x66,0x63,0xf6
    };

    static const byte pKeyCtx[] = {
        0xdf,0xc9,0x42,0x5e,0x4f,0x96,0x8f,0x7f,
        0x0c,0x29,0xf0,0x25,0x9c,0xf5,0xf9,0xae,
        0xd6,0x85,0x1c,0x2b,0xb4,0xad,0x8b,0xfb,
        0x86,0x0c,0xfe,0xe0,0xab,0x24,0x82,0x92
    };

    static const byte sigCtx1[] = {
        0x55,0xa4,0xcc,0x2f,0x70,0xa5,0x4e,0x04,
        0x28,0x8c,0x5f,0x4c,0xd1,0xe4,0x5a,0x7b,
        0xb5,0x20,0xb3,0x62,0x92,0x91,0x18,0x76,
        0xca,0xda,0x73,0x23,0x19,0x8d,0xd8,0x7a,
        0x8b,0x36,0x95,0x0b,0x95,0x13,0x00,0x22,
        0x90,0x7a,0x7f,0xb7,0xc4,0xe9,0xb2,0xd5,
        0xf6,0xcc,0xa6,0x85,0xa5,0x87,0xb4,0xb2,
        0x1f,0x4b,0x88,0x8e,0x4e,0x7e,0xdb,0x0d
    };

    static const byte sigCtx2[] = {
        0xcc,0x5e,0x63,0xa2,0x7e,0x94,0xaf,0xd3,
        0x41,0x83,0x38,0xd2,0x48,0x6f,0xa9,0x2a,
        0xf9,0x91,0x7c,0x2d,0x98,0x9e,0x06,0xe5,
        0x02,0x77,0x72,0x1c,0x34,0x38,0x18,0xb4,
        0x21,0x96,0xbc,0x29,0x2e,0x68,0xf3,0x4d,
        0x85,0x9b,0xbe,0xad,0x17,0x9f,0x54,0x54,
        0x2d,0x4b,0x04,0xdc,0xfb,0xfa,0x4a,0x68,
        0x4e,0x39,0x50,0xfb,0x1c,0xcd,0x8d,0x0d
    };

    static const byte msgCtx[] = {
        0xf7,0x26,0x93,0x6d,0x19,0xc8,0x00,0x49,
        0x4e,0x3f,0xda,0xff,0x20,0xb2,0x76,0xa8
    };

    static const byte contextCtx[] = {
        0x66,0x6f,0x6f
    };

    outlen = sizeof(out);
    XMEMSET(out, 0, sizeof(out));

    if (wc_ed25519_import_private_key(sKeyCtx, ED25519_KEY_SIZE, pKeyCtx,
                                      sizeof(pKeyCtx), &key) != 0)
        return -10400;

    if (wc_ed25519ctx_sign_msg(msgCtx, sizeof(msgCtx), out, &outlen, &key,
                               contextCtx, sizeof(contextCtx)) != 0)
        return -10401;

    if (XMEMCMP(out, sigCtx1, 64))
        return -10402;

#if defined(HAVE_ED25519_VERIFY)
    /* test verify on good msg */
    if (wc_ed25519ctx_verify_msg(out, outlen, msgCtx, sizeof(msgCtx), &verify,
                                 &key, contextCtx, sizeof(contextCtx)) != 0 ||
            verify != 1)
        return -10403;
#endif

    if (wc_ed25519ctx_sign_msg(msgCtx, sizeof(msgCtx), out, &outlen, &key, NULL,
                               0) != 0)
        return -10404;

    if (XMEMCMP(out, sigCtx2, 64))
        return -10405;

#if defined(HAVE_ED25519_VERIFY)
    /* test verify on good msg */
    if (wc_ed25519ctx_verify_msg(out, outlen, msgCtx, sizeof(msgCtx), &verify,
                                 &key, NULL, 0) != 0 || verify != 1)
        return -10406;
#endif

    wc_ed25519_free(&key);

    return 0;
}

static int ed25519ph_test(void)
{
    byte   out[ED25519_SIG_SIZE];
    word32 outlen;
#ifdef HAVE_ED25519_VERIFY
    int    verify;
#endif /* HAVE_ED25519_VERIFY */
    ed25519_key key;

    static const byte sKeyPh[] = {
        0x83,0x3f,0xe6,0x24,0x09,0x23,0x7b,0x9d,
        0x62,0xec,0x77,0x58,0x75,0x20,0x91,0x1e,
        0x9a,0x75,0x9c,0xec,0x1d,0x19,0x75,0x5b,
        0x7d,0xa9,0x01,0xb9,0x6d,0xca,0x3d,0x42
    };

    static const byte pKeyPh[] = {
        0xec,0x17,0x2b,0x93,0xad,0x5e,0x56,0x3b,
        0xf4,0x93,0x2c,0x70,0xe1,0x24,0x50,0x34,
        0xc3,0x54,0x67,0xef,0x2e,0xfd,0x4d,0x64,
        0xeb,0xf8,0x19,0x68,0x34,0x67,0xe2,0xbf
    };

    static const byte sigPh1[] = {
        0x98,0xa7,0x02,0x22,0xf0,0xb8,0x12,0x1a,
        0xa9,0xd3,0x0f,0x81,0x3d,0x68,0x3f,0x80,
        0x9e,0x46,0x2b,0x46,0x9c,0x7f,0xf8,0x76,
        0x39,0x49,0x9b,0xb9,0x4e,0x6d,0xae,0x41,
        0x31,0xf8,0x50,0x42,0x46,0x3c,0x2a,0x35,
        0x5a,0x20,0x03,0xd0,0x62,0xad,0xf5,0xaa,
        0xa1,0x0b,0x8c,0x61,0xe6,0x36,0x06,0x2a,
        0xaa,0xd1,0x1c,0x2a,0x26,0x08,0x34,0x06
    };

    static const byte sigPh2[] = {
        0xe0,0x39,0x70,0x2b,0x4c,0x25,0x95,0xa6,
        0xa5,0x41,0xac,0x85,0x09,0x23,0x6e,0x29,
        0x90,0x47,0x47,0x95,0x33,0x0c,0x9b,0x34,
        0xa7,0x5f,0x58,0xa6,0x60,0x12,0x9e,0x08,
        0xfd,0x73,0x69,0x43,0xfb,0x19,0x43,0xa5,
        0x57,0x20,0xb9,0xe0,0x95,0x7b,0x1e,0xd6,
        0x73,0x48,0x16,0x61,0x9f,0x13,0x88,0xf4,
        0x3f,0x73,0xe6,0xe3,0xba,0xa8,0x1c,0x0e
    };

    static const byte msgPh[] = {
        0x61,0x62,0x63
    };

    /* SHA-512 hash of msgPh */
    static const byte hashPh[] = {
        0xdd,0xaf,0x35,0xa1,0x93,0x61,0x7a,0xba,
        0xcc,0x41,0x73,0x49,0xae,0x20,0x41,0x31,
        0x12,0xe6,0xfa,0x4e,0x89,0xa9,0x7e,0xa2,
        0x0a,0x9e,0xee,0xe6,0x4b,0x55,0xd3,0x9a,
        0x21,0x92,0x99,0x2a,0x27,0x4f,0xc1,0xa8,
        0x36,0xba,0x3c,0x23,0xa3,0xfe,0xeb,0xbd,
        0x45,0x4d,0x44,0x23,0x64,0x3c,0xe8,0x0e,
        0x2a,0x9a,0xc9,0x4f,0xa5,0x4c,0xa4,0x9f
    };

    static const byte contextPh2[] = {
        0x66,0x6f,0x6f
    };

    outlen = sizeof(out);
    XMEMSET(out, 0, sizeof(out));

    if (wc_ed25519_import_private_key(sKeyPh, ED25519_KEY_SIZE, pKeyPh,
                                      sizeof(pKeyPh), &key) != 0) {
        return -10500;
    }

    if (wc_ed25519ph_sign_msg(msgPh, sizeof(msgPh), out, &outlen, &key, NULL,
                              0) != 0) {
        return -10501;
    }

    if (XMEMCMP(out, sigPh1, 64))
        return -10502;

#if defined(HAVE_ED25519_VERIFY)
    /* test verify on good msg */
    if (wc_ed25519ph_verify_msg(out, outlen, msgPh, sizeof(msgPh), &verify,
                                &key, NULL, 0) != 0 ||
            verify != 1) {
        return -10503;
    }
#endif

    if (wc_ed25519ph_sign_msg(msgPh, sizeof(msgPh), out, &outlen, &key,
                              contextPh2, sizeof(contextPh2)) != 0) {
        return -10504;
    }

    if (XMEMCMP(out, sigPh2, 64))
        return -10505;

#if defined(HAVE_ED25519_VERIFY)
    /* test verify on good msg */
    if (wc_ed25519ph_verify_msg(out, outlen, msgPh, sizeof(msgPh), &verify,
                                &key, contextPh2, sizeof(contextPh2)) != 0 ||
            verify != 1) {
        return -10506;
    }
#endif

    if (wc_ed25519ph_sign_hash(hashPh, sizeof(hashPh), out, &outlen, &key, NULL,
                              0) != 0) {
        return -10507;
    }

    if (XMEMCMP(out, sigPh1, 64))
        return -10508;

#if defined(HAVE_ED25519_VERIFY)
    if (wc_ed25519ph_verify_hash(out, outlen, hashPh, sizeof(hashPh), &verify,
                                &key, NULL, 0) != 0 ||
            verify != 1) {
        return -10509;
    }
#endif

    if (wc_ed25519ph_sign_hash(hashPh, sizeof(hashPh), out, &outlen, &key,
                              contextPh2, sizeof(contextPh2)) != 0) {
        return -10510;
    }

    if (XMEMCMP(out, sigPh2, 64))
        return -10511;

#if defined(HAVE_ED25519_VERIFY)
    if (wc_ed25519ph_verify_hash(out, outlen, hashPh, sizeof(hashPh), &verify,
                                &key, contextPh2, sizeof(contextPh2)) != 0 ||
            verify != 1) {
        return -10512;
    }
#endif

    wc_ed25519_free(&key);

    return 0;
}
#endif /* HAVE_ED25519_SIGN && HAVE_ED25519_KEY_EXPORT && HAVE_ED25519_KEY_IMPORT */

int ed25519_test(void)
{
    int ret;
    WC_RNG rng;
#if defined(HAVE_ED25519_SIGN) && defined(HAVE_ED25519_KEY_EXPORT) &&\
    defined(HAVE_ED25519_KEY_IMPORT)
    byte   out[ED25519_SIG_SIZE];
    byte   exportPKey[ED25519_KEY_SIZE];
    byte   exportSKey[ED25519_KEY_SIZE];
    word32 exportPSz;
    word32 exportSSz;
    int    i;
    word32 outlen;
#ifdef HAVE_ED25519_VERIFY
    int    verify;
#endif /* HAVE_ED25519_VERIFY */
#endif /* HAVE_ED25519_SIGN && HAVE_ED25519_KEY_EXPORT && HAVE_ED25519_KEY_IMPORT */
    word32 keySz, sigSz;
    ed25519_key key;
    ed25519_key key2;

#if defined(HAVE_ED25519_SIGN) && defined(HAVE_ED25519_KEY_EXPORT) && \
    defined(HAVE_ED25519_KEY_IMPORT)
    /* test vectors from
       https://tools.ietf.org/html/draft-josefsson-eddsa-ed25519-02
     */

    static const byte sKey1[] = {
        0x9d,0x61,0xb1,0x9d,0xef,0xfd,0x5a,0x60,
        0xba,0x84,0x4a,0xf4,0x92,0xec,0x2c,0xc4,
        0x44,0x49,0xc5,0x69,0x7b,0x32,0x69,0x19,
        0x70,0x3b,0xac,0x03,0x1c,0xae,0x7f,0x60
    };

    static const byte sKey2[] = {
        0x4c,0xcd,0x08,0x9b,0x28,0xff,0x96,0xda,
        0x9d,0xb6,0xc3,0x46,0xec,0x11,0x4e,0x0f,
        0x5b,0x8a,0x31,0x9f,0x35,0xab,0xa6,0x24,
        0xda,0x8c,0xf6,0xed,0x4f,0xb8,0xa6,0xfb
    };

    static const byte sKey3[] = {
        0xc5,0xaa,0x8d,0xf4,0x3f,0x9f,0x83,0x7b,
        0xed,0xb7,0x44,0x2f,0x31,0xdc,0xb7,0xb1,
        0x66,0xd3,0x85,0x35,0x07,0x6f,0x09,0x4b,
        0x85,0xce,0x3a,0x2e,0x0b,0x44,0x58,0xf7
    };

    /* uncompressed test */
    static const byte sKey4[] = {
        0x9d,0x61,0xb1,0x9d,0xef,0xfd,0x5a,0x60,
        0xba,0x84,0x4a,0xf4,0x92,0xec,0x2c,0xc4,
        0x44,0x49,0xc5,0x69,0x7b,0x32,0x69,0x19,
        0x70,0x3b,0xac,0x03,0x1c,0xae,0x7f,0x60
    };

    /* compressed prefix test */
    static const byte sKey5[] = {
        0x9d,0x61,0xb1,0x9d,0xef,0xfd,0x5a,0x60,
        0xba,0x84,0x4a,0xf4,0x92,0xec,0x2c,0xc4,
        0x44,0x49,0xc5,0x69,0x7b,0x32,0x69,0x19,
        0x70,0x3b,0xac,0x03,0x1c,0xae,0x7f,0x60
    };

    static const byte sKey6[] = {
        0xf5,0xe5,0x76,0x7c,0xf1,0x53,0x31,0x95,
        0x17,0x63,0x0f,0x22,0x68,0x76,0xb8,0x6c,
        0x81,0x60,0xcc,0x58,0x3b,0xc0,0x13,0x74,
        0x4c,0x6b,0xf2,0x55,0xf5,0xcc,0x0e,0xe5
    };

    static const byte* sKeys[] = {sKey1, sKey2, sKey3, sKey4, sKey5, sKey6};

    static const byte pKey1[] = {
        0xd7,0x5a,0x98,0x01,0x82,0xb1,0x0a,0xb7,
        0xd5,0x4b,0xfe,0xd3,0xc9,0x64,0x07,0x3a,
        0x0e,0xe1,0x72,0xf3,0xda,0xa6,0x23,0x25,
        0xaf,0x02,0x1a,0x68,0xf7,0x07,0x51,0x1a
    };

    static const byte pKey2[] = {
        0x3d,0x40,0x17,0xc3,0xe8,0x43,0x89,0x5a,
        0x92,0xb7,0x0a,0xa7,0x4d,0x1b,0x7e,0xbc,
        0x9c,0x98,0x2c,0xcf,0x2e,0xc4,0x96,0x8c,
        0xc0,0xcd,0x55,0xf1,0x2a,0xf4,0x66,0x0c
    };

    static const byte pKey3[] = {
        0xfc,0x51,0xcd,0x8e,0x62,0x18,0xa1,0xa3,
        0x8d,0xa4,0x7e,0xd0,0x02,0x30,0xf0,0x58,
        0x08,0x16,0xed,0x13,0xba,0x33,0x03,0xac,
        0x5d,0xeb,0x91,0x15,0x48,0x90,0x80,0x25
    };

    /* uncompressed test */
    static const byte pKey4[] = {
        0x04,0x55,0xd0,0xe0,0x9a,0x2b,0x9d,0x34,
        0x29,0x22,0x97,0xe0,0x8d,0x60,0xd0,0xf6,
        0x20,0xc5,0x13,0xd4,0x72,0x53,0x18,0x7c,
        0x24,0xb1,0x27,0x86,0xbd,0x77,0x76,0x45,
        0xce,0x1a,0x51,0x07,0xf7,0x68,0x1a,0x02,
        0xaf,0x25,0x23,0xa6,0xda,0xf3,0x72,0xe1,
        0x0e,0x3a,0x07,0x64,0xc9,0xd3,0xfe,0x4b,
        0xd5,0xb7,0x0a,0xb1,0x82,0x01,0x98,0x5a,
        0xd7
    };

    /* compressed prefix */
    static const byte pKey5[] = {
        0x40,0xd7,0x5a,0x98,0x01,0x82,0xb1,0x0a,0xb7,
        0xd5,0x4b,0xfe,0xd3,0xc9,0x64,0x07,0x3a,
        0x0e,0xe1,0x72,0xf3,0xda,0xa6,0x23,0x25,
        0xaf,0x02,0x1a,0x68,0xf7,0x07,0x51,0x1a
    };

    static const byte pKey6[] = {
        0x27,0x81,0x17,0xfc,0x14,0x4c,0x72,0x34,
        0x0f,0x67,0xd0,0xf2,0x31,0x6e,0x83,0x86,
        0xce,0xff,0xbf,0x2b,0x24,0x28,0xc9,0xc5,
        0x1f,0xef,0x7c,0x59,0x7f,0x1d,0x42,0x6e
    };

    static const byte* pKeys[] = {pKey1, pKey2, pKey3, pKey4, pKey5, pKey6};
    static const byte  pKeySz[] = {sizeof(pKey1), sizeof(pKey2), sizeof(pKey3),
                            sizeof(pKey4), sizeof(pKey5), sizeof(pKey6)};

    static const byte sig1[] = {
        0xe5,0x56,0x43,0x00,0xc3,0x60,0xac,0x72,
        0x90,0x86,0xe2,0xcc,0x80,0x6e,0x82,0x8a,
        0x84,0x87,0x7f,0x1e,0xb8,0xe5,0xd9,0x74,
        0xd8,0x73,0xe0,0x65,0x22,0x49,0x01,0x55,
        0x5f,0xb8,0x82,0x15,0x90,0xa3,0x3b,0xac,
        0xc6,0x1e,0x39,0x70,0x1c,0xf9,0xb4,0x6b,
        0xd2,0x5b,0xf5,0xf0,0x59,0x5b,0xbe,0x24,
        0x65,0x51,0x41,0x43,0x8e,0x7a,0x10,0x0b
    };

    static const byte sig2[] = {
        0x92,0xa0,0x09,0xa9,0xf0,0xd4,0xca,0xb8,
        0x72,0x0e,0x82,0x0b,0x5f,0x64,0x25,0x40,
        0xa2,0xb2,0x7b,0x54,0x16,0x50,0x3f,0x8f,
        0xb3,0x76,0x22,0x23,0xeb,0xdb,0x69,0xda,
        0x08,0x5a,0xc1,0xe4,0x3e,0x15,0x99,0x6e,
        0x45,0x8f,0x36,0x13,0xd0,0xf1,0x1d,0x8c,
        0x38,0x7b,0x2e,0xae,0xb4,0x30,0x2a,0xee,
        0xb0,0x0d,0x29,0x16,0x12,0xbb,0x0c,0x00
    };

    static const byte sig3[] = {
        0x62,0x91,0xd6,0x57,0xde,0xec,0x24,0x02,
        0x48,0x27,0xe6,0x9c,0x3a,0xbe,0x01,0xa3,
        0x0c,0xe5,0x48,0xa2,0x84,0x74,0x3a,0x44,
        0x5e,0x36,0x80,0xd7,0xdb,0x5a,0xc3,0xac,
        0x18,0xff,0x9b,0x53,0x8d,0x16,0xf2,0x90,
        0xae,0x67,0xf7,0x60,0x98,0x4d,0xc6,0x59,
        0x4a,0x7c,0x15,0xe9,0x71,0x6e,0xd2,0x8d,
        0xc0,0x27,0xbe,0xce,0xea,0x1e,0xc4,0x0a
    };

    /* uncompressed test */
    static const byte sig4[] = {
        0xe5,0x56,0x43,0x00,0xc3,0x60,0xac,0x72,
        0x90,0x86,0xe2,0xcc,0x80,0x6e,0x82,0x8a,
        0x84,0x87,0x7f,0x1e,0xb8,0xe5,0xd9,0x74,
        0xd8,0x73,0xe0,0x65,0x22,0x49,0x01,0x55,
        0x5f,0xb8,0x82,0x15,0x90,0xa3,0x3b,0xac,
        0xc6,0x1e,0x39,0x70,0x1c,0xf9,0xb4,0x6b,
        0xd2,0x5b,0xf5,0xf0,0x59,0x5b,0xbe,0x24,
        0x65,0x51,0x41,0x43,0x8e,0x7a,0x10,0x0b
    };

    /* compressed prefix */
    static const byte sig5[] = {
        0xe5,0x56,0x43,0x00,0xc3,0x60,0xac,0x72,
        0x90,0x86,0xe2,0xcc,0x80,0x6e,0x82,0x8a,
        0x84,0x87,0x7f,0x1e,0xb8,0xe5,0xd9,0x74,
        0xd8,0x73,0xe0,0x65,0x22,0x49,0x01,0x55,
        0x5f,0xb8,0x82,0x15,0x90,0xa3,0x3b,0xac,
        0xc6,0x1e,0x39,0x70,0x1c,0xf9,0xb4,0x6b,
        0xd2,0x5b,0xf5,0xf0,0x59,0x5b,0xbe,0x24,
        0x65,0x51,0x41,0x43,0x8e,0x7a,0x10,0x0b
    };

    static const byte sig6[] = {
        0x0a,0xab,0x4c,0x90,0x05,0x01,0xb3,0xe2,
        0x4d,0x7c,0xdf,0x46,0x63,0x32,0x6a,0x3a,
        0x87,0xdf,0x5e,0x48,0x43,0xb2,0xcb,0xdb,
        0x67,0xcb,0xf6,0xe4,0x60,0xfe,0xc3,0x50,
        0xaa,0x53,0x71,0xb1,0x50,0x8f,0x9f,0x45,
        0x28,0xec,0xea,0x23,0xc4,0x36,0xd9,0x4b,
        0x5e,0x8f,0xcd,0x4f,0x68,0x1e,0x30,0xa6,
        0xac,0x00,0xa9,0x70,0x4a,0x18,0x8a,0x03
    };

    static const byte* sigs[] = {sig1, sig2, sig3, sig4, sig5, sig6};

    static const byte msg1[]  = {0x0 };
    static const byte msg2[]  = {0x72};
    static const byte msg3[]  = {0xAF,0x82};

    /* test of a 1024 byte long message */
    static const byte msg4[]  = {
        0x08,0xb8,0xb2,0xb7,0x33,0x42,0x42,0x43,
        0x76,0x0f,0xe4,0x26,0xa4,0xb5,0x49,0x08,
        0x63,0x21,0x10,0xa6,0x6c,0x2f,0x65,0x91,
        0xea,0xbd,0x33,0x45,0xe3,0xe4,0xeb,0x98,
        0xfa,0x6e,0x26,0x4b,0xf0,0x9e,0xfe,0x12,
        0xee,0x50,0xf8,0xf5,0x4e,0x9f,0x77,0xb1,
        0xe3,0x55,0xf6,0xc5,0x05,0x44,0xe2,0x3f,
        0xb1,0x43,0x3d,0xdf,0x73,0xbe,0x84,0xd8,
        0x79,0xde,0x7c,0x00,0x46,0xdc,0x49,0x96,
        0xd9,0xe7,0x73,0xf4,0xbc,0x9e,0xfe,0x57,
        0x38,0x82,0x9a,0xdb,0x26,0xc8,0x1b,0x37,
        0xc9,0x3a,0x1b,0x27,0x0b,0x20,0x32,0x9d,
        0x65,0x86,0x75,0xfc,0x6e,0xa5,0x34,0xe0,
        0x81,0x0a,0x44,0x32,0x82,0x6b,0xf5,0x8c,
        0x94,0x1e,0xfb,0x65,0xd5,0x7a,0x33,0x8b,
        0xbd,0x2e,0x26,0x64,0x0f,0x89,0xff,0xbc,
        0x1a,0x85,0x8e,0xfc,0xb8,0x55,0x0e,0xe3,
        0xa5,0xe1,0x99,0x8b,0xd1,0x77,0xe9,0x3a,
        0x73,0x63,0xc3,0x44,0xfe,0x6b,0x19,0x9e,
        0xe5,0xd0,0x2e,0x82,0xd5,0x22,0xc4,0xfe,
        0xba,0x15,0x45,0x2f,0x80,0x28,0x8a,0x82,
        0x1a,0x57,0x91,0x16,0xec,0x6d,0xad,0x2b,
        0x3b,0x31,0x0d,0xa9,0x03,0x40,0x1a,0xa6,
        0x21,0x00,0xab,0x5d,0x1a,0x36,0x55,0x3e,
        0x06,0x20,0x3b,0x33,0x89,0x0c,0xc9,0xb8,
        0x32,0xf7,0x9e,0xf8,0x05,0x60,0xcc,0xb9,
        0xa3,0x9c,0xe7,0x67,0x96,0x7e,0xd6,0x28,
        0xc6,0xad,0x57,0x3c,0xb1,0x16,0xdb,0xef,
        0xef,0xd7,0x54,0x99,0xda,0x96,0xbd,0x68,
        0xa8,0xa9,0x7b,0x92,0x8a,0x8b,0xbc,0x10,
        0x3b,0x66,0x21,0xfc,0xde,0x2b,0xec,0xa1,
        0x23,0x1d,0x20,0x6b,0xe6,0xcd,0x9e,0xc7,
        0xaf,0xf6,0xf6,0xc9,0x4f,0xcd,0x72,0x04,
        0xed,0x34,0x55,0xc6,0x8c,0x83,0xf4,0xa4,
        0x1d,0xa4,0xaf,0x2b,0x74,0xef,0x5c,0x53,
        0xf1,0xd8,0xac,0x70,0xbd,0xcb,0x7e,0xd1,
        0x85,0xce,0x81,0xbd,0x84,0x35,0x9d,0x44,
        0x25,0x4d,0x95,0x62,0x9e,0x98,0x55,0xa9,
        0x4a,0x7c,0x19,0x58,0xd1,0xf8,0xad,0xa5,
        0xd0,0x53,0x2e,0xd8,0xa5,0xaa,0x3f,0xb2,
        0xd1,0x7b,0xa7,0x0e,0xb6,0x24,0x8e,0x59,
        0x4e,0x1a,0x22,0x97,0xac,0xbb,0xb3,0x9d,
        0x50,0x2f,0x1a,0x8c,0x6e,0xb6,0xf1,0xce,
        0x22,0xb3,0xde,0x1a,0x1f,0x40,0xcc,0x24,
        0x55,0x41,0x19,0xa8,0x31,0xa9,0xaa,0xd6,
        0x07,0x9c,0xad,0x88,0x42,0x5d,0xe6,0xbd,
        0xe1,0xa9,0x18,0x7e,0xbb,0x60,0x92,0xcf,
        0x67,0xbf,0x2b,0x13,0xfd,0x65,0xf2,0x70,
        0x88,0xd7,0x8b,0x7e,0x88,0x3c,0x87,0x59,
        0xd2,0xc4,0xf5,0xc6,0x5a,0xdb,0x75,0x53,
        0x87,0x8a,0xd5,0x75,0xf9,0xfa,0xd8,0x78,
        0xe8,0x0a,0x0c,0x9b,0xa6,0x3b,0xcb,0xcc,
        0x27,0x32,0xe6,0x94,0x85,0xbb,0xc9,0xc9,
        0x0b,0xfb,0xd6,0x24,0x81,0xd9,0x08,0x9b,
        0xec,0xcf,0x80,0xcf,0xe2,0xdf,0x16,0xa2,
        0xcf,0x65,0xbd,0x92,0xdd,0x59,0x7b,0x07,
        0x07,0xe0,0x91,0x7a,0xf4,0x8b,0xbb,0x75,
        0xfe,0xd4,0x13,0xd2,0x38,0xf5,0x55,0x5a,
        0x7a,0x56,0x9d,0x80,0xc3,0x41,0x4a,0x8d,
        0x08,0x59,0xdc,0x65,0xa4,0x61,0x28,0xba,
        0xb2,0x7a,0xf8,0x7a,0x71,0x31,0x4f,0x31,
        0x8c,0x78,0x2b,0x23,0xeb,0xfe,0x80,0x8b,
        0x82,0xb0,0xce,0x26,0x40,0x1d,0x2e,0x22,
        0xf0,0x4d,0x83,0xd1,0x25,0x5d,0xc5,0x1a,
        0xdd,0xd3,0xb7,0x5a,0x2b,0x1a,0xe0,0x78,
        0x45,0x04,0xdf,0x54,0x3a,0xf8,0x96,0x9b,
        0xe3,0xea,0x70,0x82,0xff,0x7f,0xc9,0x88,
        0x8c,0x14,0x4d,0xa2,0xaf,0x58,0x42,0x9e,
        0xc9,0x60,0x31,0xdb,0xca,0xd3,0xda,0xd9,
        0xaf,0x0d,0xcb,0xaa,0xaf,0x26,0x8c,0xb8,
        0xfc,0xff,0xea,0xd9,0x4f,0x3c,0x7c,0xa4,
        0x95,0xe0,0x56,0xa9,0xb4,0x7a,0xcd,0xb7,
        0x51,0xfb,0x73,0xe6,0x66,0xc6,0xc6,0x55,
        0xad,0xe8,0x29,0x72,0x97,0xd0,0x7a,0xd1,
        0xba,0x5e,0x43,0xf1,0xbc,0xa3,0x23,0x01,
        0x65,0x13,0x39,0xe2,0x29,0x04,0xcc,0x8c,
        0x42,0xf5,0x8c,0x30,0xc0,0x4a,0xaf,0xdb,
        0x03,0x8d,0xda,0x08,0x47,0xdd,0x98,0x8d,
        0xcd,0xa6,0xf3,0xbf,0xd1,0x5c,0x4b,0x4c,
        0x45,0x25,0x00,0x4a,0xa0,0x6e,0xef,0xf8,
        0xca,0x61,0x78,0x3a,0xac,0xec,0x57,0xfb,
        0x3d,0x1f,0x92,0xb0,0xfe,0x2f,0xd1,0xa8,
        0x5f,0x67,0x24,0x51,0x7b,0x65,0xe6,0x14,
        0xad,0x68,0x08,0xd6,0xf6,0xee,0x34,0xdf,
        0xf7,0x31,0x0f,0xdc,0x82,0xae,0xbf,0xd9,
        0x04,0xb0,0x1e,0x1d,0xc5,0x4b,0x29,0x27,
        0x09,0x4b,0x2d,0xb6,0x8d,0x6f,0x90,0x3b,
        0x68,0x40,0x1a,0xde,0xbf,0x5a,0x7e,0x08,
        0xd7,0x8f,0xf4,0xef,0x5d,0x63,0x65,0x3a,
        0x65,0x04,0x0c,0xf9,0xbf,0xd4,0xac,0xa7,
        0x98,0x4a,0x74,0xd3,0x71,0x45,0x98,0x67,
        0x80,0xfc,0x0b,0x16,0xac,0x45,0x16,0x49,
        0xde,0x61,0x88,0xa7,0xdb,0xdf,0x19,0x1f,
        0x64,0xb5,0xfc,0x5e,0x2a,0xb4,0x7b,0x57,
        0xf7,0xf7,0x27,0x6c,0xd4,0x19,0xc1,0x7a,
        0x3c,0xa8,0xe1,0xb9,0x39,0xae,0x49,0xe4,
        0x88,0xac,0xba,0x6b,0x96,0x56,0x10,0xb5,
        0x48,0x01,0x09,0xc8,0xb1,0x7b,0x80,0xe1,
        0xb7,0xb7,0x50,0xdf,0xc7,0x59,0x8d,0x5d,
        0x50,0x11,0xfd,0x2d,0xcc,0x56,0x00,0xa3,
        0x2e,0xf5,0xb5,0x2a,0x1e,0xcc,0x82,0x0e,
        0x30,0x8a,0xa3,0x42,0x72,0x1a,0xac,0x09,
        0x43,0xbf,0x66,0x86,0xb6,0x4b,0x25,0x79,
        0x37,0x65,0x04,0xcc,0xc4,0x93,0xd9,0x7e,
        0x6a,0xed,0x3f,0xb0,0xf9,0xcd,0x71,0xa4,
        0x3d,0xd4,0x97,0xf0,0x1f,0x17,0xc0,0xe2,
        0xcb,0x37,0x97,0xaa,0x2a,0x2f,0x25,0x66,
        0x56,0x16,0x8e,0x6c,0x49,0x6a,0xfc,0x5f,
        0xb9,0x32,0x46,0xf6,0xb1,0x11,0x63,0x98,
        0xa3,0x46,0xf1,0xa6,0x41,0xf3,0xb0,0x41,
        0xe9,0x89,0xf7,0x91,0x4f,0x90,0xcc,0x2c,
        0x7f,0xff,0x35,0x78,0x76,0xe5,0x06,0xb5,
        0x0d,0x33,0x4b,0xa7,0x7c,0x22,0x5b,0xc3,
        0x07,0xba,0x53,0x71,0x52,0xf3,0xf1,0x61,
        0x0e,0x4e,0xaf,0xe5,0x95,0xf6,0xd9,0xd9,
        0x0d,0x11,0xfa,0xa9,0x33,0xa1,0x5e,0xf1,
        0x36,0x95,0x46,0x86,0x8a,0x7f,0x3a,0x45,
        0xa9,0x67,0x68,0xd4,0x0f,0xd9,0xd0,0x34,
        0x12,0xc0,0x91,0xc6,0x31,0x5c,0xf4,0xfd,
        0xe7,0xcb,0x68,0x60,0x69,0x37,0x38,0x0d,
        0xb2,0xea,0xaa,0x70,0x7b,0x4c,0x41,0x85,
        0xc3,0x2e,0xdd,0xcd,0xd3,0x06,0x70,0x5e,
        0x4d,0xc1,0xff,0xc8,0x72,0xee,0xee,0x47,
        0x5a,0x64,0xdf,0xac,0x86,0xab,0xa4,0x1c,
        0x06,0x18,0x98,0x3f,0x87,0x41,0xc5,0xef,
        0x68,0xd3,0xa1,0x01,0xe8,0xa3,0xb8,0xca,
        0xc6,0x0c,0x90,0x5c,0x15,0xfc,0x91,0x08,
        0x40,0xb9,0x4c,0x00,0xa0,0xb9,0xd0
    };

    static const byte* msgs[] =   {msg1, msg2, msg3, msg1, msg1, msg4};
    static const word16 msgSz[] = {0 /*sizeof(msg1)*/,
                                   sizeof(msg2),
                                   sizeof(msg3),
                                   0 /*sizeof(msg1)*/,
                                   0 /*sizeof(msg1)*/,
                                   sizeof(msg4)
    };
#ifndef NO_ASN
    static byte privateEd25519[] = {
        0x30,0x2e,0x02,0x01,0x00,0x30,0x05,0x06,
        0x03,0x2b,0x65,0x70,0x04,0x22,0x04,0x20,
        0x9d,0x61,0xb1,0x9d,0xef,0xfd,0x5a,0x60,
        0xba,0x84,0x4a,0xf4,0x92,0xec,0x2c,0xc4,
        0x44,0x49,0xc5,0x69,0x7b,0x32,0x69,0x19,
        0x70,0x3b,0xac,0x03,0x1c,0xae,0x7f,0x60
    };
    static byte publicEd25519[] = {
        0x30,0x2a,0x30,0x05,0x06,0x03,0x2b,0x65,
        0x70,0x03,0x21,0x00,0xd7,0x5a,0x98,0x01,
        0x82,0xb1,0x0a,0xb7,0xd5,0x4b,0xfe,0xd3,
        0xc9,0x64,0x07,0x3a,0x0e,0xe1,0x72,0xf3,
        0xda,0xa6,0x23,0x25,0xaf,0x02,0x1a,0x68,
        0xf7,0x07,0x51,0x1a
    };
    static byte privPubEd25519[] = {
        0x30,0x52,0x02,0x01,0x00,0x30,0x05,0x06,
        0x03,0x2b,0x65,0x70,0x04,0x22,0x04,0x20,
        0x9d,0x61,0xb1,0x9d,0xef,0xfd,0x5a,0x60,
        0xba,0x84,0x4a,0xf4,0x92,0xec,0x2c,0xc4,
        0x44,0x49,0xc5,0x69,0x7b,0x32,0x69,0x19,
        0x70,0x3b,0xac,0x03,0x1c,0xae,0x7f,0x60,
        0xa1,0x22,0x04,0x20,0xd7,0x5a,0x98,0x01,
        0x82,0xb1,0x0a,0xb7,0xd5,0x4b,0xfe,0xd3,
        0xc9,0x64,0x07,0x3a,0x0e,0xe1,0x72,0xf3,
        0xda,0xa6,0x23,0x25,0xaf,0x02,0x1a,0x68,
        0xf7,0x07,0x51,0x1a
    };

    word32 idx;
    ed25519_key key3;
#endif /* NO_ASN */
#endif /* HAVE_ED25519_SIGN && HAVE_ED25519_KEY_EXPORT && HAVE_ED25519_KEY_IMPORT */

    /* create ed25519 keys */
#ifndef HAVE_FIPS
    ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
    ret = wc_InitRng(&rng);
#endif
    if (ret != 0)
        return -10600;

    wc_ed25519_init(&key);
    wc_ed25519_init(&key2);
#ifndef NO_ASN
    wc_ed25519_init(&key3);
#endif
    wc_ed25519_make_key(&rng, ED25519_KEY_SIZE, &key);
    wc_ed25519_make_key(&rng, ED25519_KEY_SIZE, &key2);

    /* helper functions for signature and key size */
    keySz = wc_ed25519_size(&key);
    sigSz = wc_ed25519_sig_size(&key);

#if defined(HAVE_ED25519_SIGN) && defined(HAVE_ED25519_KEY_EXPORT) &&\
        defined(HAVE_ED25519_KEY_IMPORT)
    for (i = 0; i < 6; i++) {
        outlen = sizeof(out);
        XMEMSET(out, 0, sizeof(out));

        if (wc_ed25519_import_private_key(sKeys[i], ED25519_KEY_SIZE, pKeys[i],
                pKeySz[i], &key) != 0)
            return -10601 - i;

        if (wc_ed25519_sign_msg(msgs[i], msgSz[i], out, &outlen, &key) != 0)
            return -10611 - i;

        if (XMEMCMP(out, sigs[i], 64))
            return -10621 - i;

#if defined(HAVE_ED25519_VERIFY)
        /* test verify on good msg */
        if (wc_ed25519_verify_msg(out, outlen, msgs[i], msgSz[i], &verify,
                    &key) != 0 || verify != 1)
            return -10631 - i;

        /* test verify on bad msg */
        out[outlen-1] = out[outlen-1] + 1;
        if (wc_ed25519_verify_msg(out, outlen, msgs[i], msgSz[i], &verify,
                    &key) == 0 || verify == 1)
            return -10641 - i;
#endif /* HAVE_ED25519_VERIFY */

        /* test api for import/exporting keys */
        exportPSz = sizeof(exportPKey);
        exportSSz = sizeof(exportSKey);
        if (wc_ed25519_export_public(&key, exportPKey, &exportPSz) != 0)
            return -10651 - i;

        if (wc_ed25519_import_public(exportPKey, exportPSz, &key2) != 0)
            return -10661 - i;

        if (wc_ed25519_export_private_only(&key, exportSKey, &exportSSz) != 0)
            return -10671 - i;

        if (wc_ed25519_import_private_key(exportSKey, exportSSz,
                                          exportPKey, exportPSz, &key2) != 0)
            return -10681 - i;

        /* clear "out" buffer and test sign with imported keys */
        outlen = sizeof(out);
        XMEMSET(out, 0, sizeof(out));
        if (wc_ed25519_sign_msg(msgs[i], msgSz[i], out, &outlen, &key2) != 0)
            return -10691 - i;

#if defined(HAVE_ED25519_VERIFY)
        if (wc_ed25519_verify_msg(out, outlen, msgs[i], msgSz[i], &verify,
                                  &key2) != 0 || verify != 1)
            return -10701 - i;

        if (XMEMCMP(out, sigs[i], 64))
            return -10711 - i;
#endif /* HAVE_ED25519_VERIFY */
    }

    ret = ed25519ctx_test();
    if (ret != 0)
        return ret;

    ret = ed25519ph_test();
    if (ret != 0)
        return ret;

#ifndef NO_ASN
    /* Try ASN.1 encoded private-only key and public key. */
    idx = 0;
    if (wc_Ed25519PrivateKeyDecode(privateEd25519, &idx, &key3,
                                   sizeof(privateEd25519)) != 0)
        return -10721 - i;

    if (wc_ed25519_sign_msg(msgs[0], msgSz[0], out, &outlen, &key3)
                != BAD_FUNC_ARG)
        return -10731 - i;

    idx = 0;
    if (wc_Ed25519PublicKeyDecode(publicEd25519, &idx, &key3,
                                  sizeof(publicEd25519)) != 0)
        return -10741 - i;

    if (wc_ed25519_sign_msg(msgs[0], msgSz[0], out, &outlen, &key3) != 0)
        return -10751 - i;

    if (XMEMCMP(out, sigs[0], 64))
        return -10761 - i;

#if defined(HAVE_ED25519_VERIFY)
    /* test verify on good msg */
    if (wc_ed25519_verify_msg(out, outlen, msgs[0], msgSz[0], &verify, &key3)
                != 0 || verify != 1)
        return -10771 - i;
#endif /* HAVE_ED25519_VERIFY */

    wc_ed25519_free(&key3);
    wc_ed25519_init(&key3);

    idx = 0;
    if (wc_Ed25519PrivateKeyDecode(privPubEd25519, &idx, &key3,
                                   sizeof(privPubEd25519)) != 0)
        return -10781 - i;

    if (wc_ed25519_sign_msg(msgs[0], msgSz[0], out, &outlen, &key3) != 0)
        return -10791 - i;

    if (XMEMCMP(out, sigs[0], 64))
        return -10801 - i;

    wc_ed25519_free(&key3);
#endif /* NO_ASN */
#endif /* HAVE_ED25519_SIGN && HAVE_ED25519_KEY_EXPORT && HAVE_ED25519_KEY_IMPORT */

    /* clean up keys when done */
    wc_ed25519_free(&key);
    wc_ed25519_free(&key2);

#if defined(HAVE_HASHDRBG) || defined(NO_RC4)
    wc_FreeRng(&rng);
#endif

    /* hush warnings of unused keySz and sigSz */
    (void)keySz;
    (void)sigSz;

#ifdef WOLFSSL_TEST_CERT
    ret = ed25519_test_cert();
    if (ret < 0)
        return ret;
#ifdef WOLFSSL_CERT_GEN
    ret = ed25519_test_make_cert();
    if (ret < 0)
        return ret;
#endif /* WOLFSSL_CERT_GEN */
#endif /* WOLFSSL_TEST_CERT */

    return 0;
}
#endif /* HAVE_ED25519 */

#ifdef HAVE_CURVE448
#if defined(HAVE_CURVE448_SHARED_SECRET) && \
                                             defined(HAVE_CURVE448_KEY_IMPORT)
/* Test the wc_curve448_check_public API.
 *
 * returns 0 on success and -ve on failure.
 */
static int curve448_check_public_test(void)
{
    /* Little-endian values that will fail */
    byte fail_le[][CURVE448_KEY_SIZE] = {
        {
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
        },
        {
            0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
        },
    };
    /* Big-endian values that will fail */
    byte fail_be[][CURVE448_KEY_SIZE] = {
        {
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
        },
        {
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x01
        },
    };
    /* Good or valid public value */
    byte good[CURVE448_KEY_SIZE] = {
        0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x01
    };
    int i;

    /* Parameter checks */
    /* NULL pointer */
    if (wc_curve448_check_public(NULL, 0, EC448_LITTLE_ENDIAN) !=
                                                                 BAD_FUNC_ARG) {
        return -10900;
    }
    if (wc_curve448_check_public(NULL, 0, EC448_BIG_ENDIAN) != BAD_FUNC_ARG) {
        return -10901;
    }
    /* Length of 0 treated differently to other invalid lengths for TLS */
    if (wc_curve448_check_public(good, 0, EC448_LITTLE_ENDIAN) != BUFFER_E)
        return -10902;
    if (wc_curve448_check_public(good, 0, EC448_BIG_ENDIAN) != BUFFER_E)
        return -10903;

    /* Length not CURVE448_KEY_SIZE */
    for (i = 1; i < CURVE448_KEY_SIZE + 2; i++) {
        if (i == CURVE448_KEY_SIZE)
            continue;
        if (wc_curve448_check_public(good, i, EC448_LITTLE_ENDIAN) !=
                                                                ECC_BAD_ARG_E) {
            return -10904 - i;
        }
        if (wc_curve448_check_public(good, i, EC448_BIG_ENDIAN) !=
                                                                ECC_BAD_ARG_E) {
            return -10914 - i;
        }
    }

    /* Little-endian fail cases */
    for (i = 0; i < (int)(sizeof(fail_le) / sizeof(*fail_le)); i++) {
        if (wc_curve448_check_public(fail_le[i], CURVE448_KEY_SIZE,
                                                    EC448_LITTLE_ENDIAN) == 0) {
            return -10924 - i;
        }
    }
    /* Big-endian fail cases */
    for (i = 0; i < (int)(sizeof(fail_be) / sizeof(*fail_be)); i++) {
        if (wc_curve448_check_public(fail_be[i], CURVE448_KEY_SIZE,
                                                       EC448_BIG_ENDIAN) == 0) {
            return -10934 - i;
        }
    }

    /* Check a valid public value works! */
    if (wc_curve448_check_public(good, CURVE448_KEY_SIZE,
                                                    EC448_LITTLE_ENDIAN) != 0) {
        return -10944;
    }
    if (wc_curve448_check_public(good, CURVE448_KEY_SIZE,
                                                       EC448_BIG_ENDIAN) != 0) {
        return -10945;
    }

    return 0;
}

#endif /* HAVE_CURVE448_SHARED_SECRET && HAVE_CURVE448_KEY_IMPORT */

int curve448_test(void)
{
    WC_RNG  rng;
    int ret;
#ifdef HAVE_CURVE448_SHARED_SECRET
    byte    sharedA[CURVE448_KEY_SIZE];
    byte    sharedB[CURVE448_KEY_SIZE];
    word32  y;
#endif
#ifdef HAVE_CURVE448_KEY_EXPORT
    byte    exportBuf[CURVE448_KEY_SIZE];
#endif
    word32  x;
    curve448_key userA, userB, pubKey;

    (void)x;

#if defined(HAVE_CURVE448_SHARED_SECRET) && \
                                             defined(HAVE_CURVE448_KEY_IMPORT)
    /* test vectors from
       https://www.rfc-editor.org/rfc/rfc7748.html
     */

    /* secret key for party a */
    byte sa[] = {
        0x6b, 0x72, 0x98, 0xa5, 0xc0, 0xd8, 0xc2, 0x9a,
        0x1d, 0xab, 0x27, 0xf1, 0xa6, 0x82, 0x63, 0x00,
        0x91, 0x73, 0x89, 0x44, 0x97, 0x41, 0xa9, 0x74,
        0xf5, 0xba, 0xc9, 0xd9, 0x8d, 0xc2, 0x98, 0xd4,
        0x65, 0x55, 0xbc, 0xe8, 0xba, 0xe8, 0x9e, 0xee,
        0xd4, 0x00, 0x58, 0x4b, 0xb0, 0x46, 0xcf, 0x75,
        0x57, 0x9f, 0x51, 0xd1, 0x25, 0x49, 0x8f, 0x9a,
    };

    /* public key for party a */
    byte pa[] = {
        0xa0, 0x1f, 0xc4, 0x32, 0xe5, 0x80, 0x7f, 0x17,
        0x53, 0x0d, 0x12, 0x88, 0xda, 0x12, 0x5b, 0x0c,
        0xd4, 0x53, 0xd9, 0x41, 0x72, 0x64, 0x36, 0xc8,
        0xbb, 0xd9, 0xc5, 0x22, 0x2c, 0x3d, 0xa7, 0xfa,
        0x63, 0x9c, 0xe0, 0x3d, 0xb8, 0xd2, 0x3b, 0x27,
        0x4a, 0x07, 0x21, 0xa1, 0xae, 0xd5, 0x22, 0x7d,
        0xe6, 0xe3, 0xb7, 0x31, 0xcc, 0xf7, 0x08, 0x9b,
    };

    /* secret key for party b */
    byte sb[] = {
        0x2d, 0x99, 0x73, 0x51, 0xb6, 0x10, 0x6f, 0x36,
        0xb0, 0xd1, 0x09, 0x1b, 0x92, 0x9c, 0x4c, 0x37,
        0x21, 0x3e, 0x0d, 0x2b, 0x97, 0xe8, 0x5e, 0xbb,
        0x20, 0xc1, 0x27, 0x69, 0x1d, 0x0d, 0xad, 0x8f,
        0x1d, 0x81, 0x75, 0xb0, 0x72, 0x37, 0x45, 0xe6,
        0x39, 0xa3, 0xcb, 0x70, 0x44, 0x29, 0x0b, 0x99,
        0xe0, 0xe2, 0xa0, 0xc2, 0x7a, 0x6a, 0x30, 0x1c,
    };

    /* public key for party b */
    byte pb[] = {
        0x09, 0x36, 0xf3, 0x7b, 0xc6, 0xc1, 0xbd, 0x07,
        0xae, 0x3d, 0xec, 0x7a, 0xb5, 0xdc, 0x06, 0xa7,
        0x3c, 0xa1, 0x32, 0x42, 0xfb, 0x34, 0x3e, 0xfc,
        0x72, 0xb9, 0xd8, 0x27, 0x30, 0xb4, 0x45, 0xf3,
        0xd4, 0xb0, 0xbd, 0x07, 0x71, 0x62, 0xa4, 0x6d,
        0xcf, 0xec, 0x6f, 0x9b, 0x59, 0x0b, 0xfc, 0xbc,
        0xf5, 0x20, 0xcd, 0xb0, 0x29, 0xa8, 0xb7, 0x3e,
    };

    /* expected shared key */
    byte ss[] = {
        0x9d, 0x87, 0x4a, 0x51, 0x37, 0x50, 0x9a, 0x44,
        0x9a, 0xd5, 0x85, 0x30, 0x40, 0x24, 0x1c, 0x52,
        0x36, 0x39, 0x54, 0x35, 0xc3, 0x64, 0x24, 0xfd,
        0x56, 0x0b, 0x0c, 0xb6, 0x2b, 0x28, 0x1d, 0x28,
        0x52, 0x75, 0xa7, 0x40, 0xce, 0x32, 0xa2, 0x2d,
        0xd1, 0x74, 0x0f, 0x4a, 0xa9, 0x16, 0x1c, 0xec,
        0x95, 0xcc, 0xc6, 0x1a, 0x18, 0xf4, 0xff, 0x07,
    };
#endif /* HAVE_CURVE448_SHARED_SECRET */

#ifndef HAVE_FIPS
    ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
    ret = wc_InitRng(&rng);
#endif
    if (ret != 0)
        return -11000;

    wc_curve448_init(&userA);
    wc_curve448_init(&userB);
    wc_curve448_init(&pubKey);

    /* make curve448 keys */
    if (wc_curve448_make_key(&rng, CURVE448_KEY_SIZE, &userA) != 0)
        return -11001;

    if (wc_curve448_make_key(&rng, CURVE448_KEY_SIZE, &userB) != 0)
        return -11002;

#ifdef HAVE_CURVE448_SHARED_SECRET
    /* find shared secret key */
    x = sizeof(sharedA);
    if (wc_curve448_shared_secret(&userA, &userB, sharedA, &x) != 0)
        return -11003;

    y = sizeof(sharedB);
    if (wc_curve448_shared_secret(&userB, &userA, sharedB, &y) != 0)
        return -11004;

    /* compare shared secret keys to test they are the same */
    if (y != x)
        return -11005;

    if (XMEMCMP(sharedA, sharedB, x))
        return -11006;
#endif

#ifdef HAVE_CURVE448_KEY_EXPORT
    /* export a public key and import it for another user */
    x = sizeof(exportBuf);
    if (wc_curve448_export_public(&userA, exportBuf, &x) != 0)
        return -11007;

#ifdef HAVE_CURVE448_KEY_IMPORT
    if (wc_curve448_import_public(exportBuf, x, &pubKey) != 0)
        return -11008;
#endif
#endif

#if defined(HAVE_CURVE448_SHARED_SECRET) && \
                                             defined(HAVE_CURVE448_KEY_IMPORT)
    /* test shared key after importing a public key */
    XMEMSET(sharedB, 0, sizeof(sharedB));
    y = sizeof(sharedB);
    if (wc_curve448_shared_secret(&userB, &pubKey, sharedB, &y) != 0)
        return -11009;

    if (XMEMCMP(sharedA, sharedB, y))
        return -11010;

    /* import RFC test vectors and compare shared key */
    if (wc_curve448_import_private_raw(sa, sizeof(sa), pa, sizeof(pa), &userA)
            != 0)
        return -11011;

    if (wc_curve448_import_private_raw(sb, sizeof(sb), pb, sizeof(pb), &userB)
            != 0)
        return -11012;

    /* test against known test vector */
    XMEMSET(sharedB, 0, sizeof(sharedB));
    y = sizeof(sharedB);
    if (wc_curve448_shared_secret(&userA, &userB, sharedB, &y) != 0)
        return -11013;

    if (XMEMCMP(ss, sharedB, y))
        return -11014;

    /* test swapping roles of keys and generating same shared key */
    XMEMSET(sharedB, 0, sizeof(sharedB));
    y = sizeof(sharedB);
    if (wc_curve448_shared_secret(&userB, &userA, sharedB, &y) != 0)
        return -11015;

    if (XMEMCMP(ss, sharedB, y))
        return -11016;

    /* test with 1 generated key and 1 from known test vector */
    if (wc_curve448_import_private_raw(sa, sizeof(sa), pa, sizeof(pa), &userA)
        != 0)
        return -11017;

    if (wc_curve448_make_key(&rng, 56, &userB) != 0)
        return -11018;

    x = sizeof(sharedA);
    if (wc_curve448_shared_secret(&userA, &userB, sharedA, &x) != 0)
        return -11019;

    y = sizeof(sharedB);
    if (wc_curve448_shared_secret(&userB, &userA, sharedB, &y) != 0)
        return -11020;

    /* compare shared secret keys to test they are the same */
    if (y != x)
        return -11021;

    if (XMEMCMP(sharedA, sharedB, x))
        return -11022;

    ret = curve448_check_public_test();
    if (ret != 0)
        return ret;
#endif /* HAVE_CURVE448_SHARED_SECRET && HAVE_CURVE448_KEY_IMPORT */

    /* clean up keys when done */
    wc_curve448_free(&pubKey);
    wc_curve448_free(&userB);
    wc_curve448_free(&userA);

    wc_FreeRng(&rng);

    return 0;
}
#endif /* HAVE_CURVE448 */

#ifdef HAVE_ED448
#ifdef WOLFSSL_TEST_CERT
static int ed448_test_cert(void)
{
    DecodedCert  cert[2];
    DecodedCert* serverCert = NULL;
    DecodedCert* caCert = NULL;
#ifdef HAVE_ED448_VERIFY
    ed448_key  key;
    ed448_key* pubKey = NULL;
    int          verify;
#endif /* HAVE_ED448_VERIFY */
    int          ret;
    byte*        tmp;
    size_t       bytes;
    XFILE        file;

    tmp = XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (tmp == NULL) {
        ERROR_OUT(-11023, done);
    }

#ifdef USE_CERT_BUFFERS_256
    XMEMCPY(tmp, ca_ed448_cert, sizeof_ca_ed448_cert);
    bytes = sizeof_ca_ed448_cert;
#elif !defined(NO_FILESYSTEM)
    file = XFOPEN(caEd448Cert, "rb");
    if (file == NULL) {
        ERROR_OUT(-11024, done);
    }
    bytes = XFREAD(tmp, 1, FOURK_BUF, file);
    XFCLOSE(file);
#else
    /* No certificate to use. */
    ERROR_OUT(-11025, done);
#endif

    InitDecodedCert(&cert[0], tmp, (word32)bytes, 0);
    caCert = &cert[0];
    ret = ParseCert(caCert, CERT_TYPE, NO_VERIFY, NULL);
    if (ret != 0) {
        ERROR_OUT(-11026, done);
    }

#ifdef USE_CERT_BUFFERS_256
    XMEMCPY(tmp, server_ed448_cert, sizeof_server_ed448_cert);
    bytes = sizeof_server_ed448_cert;
#elif !defined(NO_FILESYSTEM)
    file = XFOPEN(serverEd448Cert, "rb");
    if (file == NULL) {
        ERROR_OUT(-11027, done);
    }
    bytes = XFREAD(tmp, 1, FOURK_BUF, file);
    XFCLOSE(file);
#else
    /* No certificate to use. */
    ERROR_OUT(-11028, done);
#endif

    InitDecodedCert(&cert[1], tmp, (word32)bytes, 0);
    serverCert = &cert[1];
    ret = ParseCert(serverCert, CERT_TYPE, NO_VERIFY, NULL);
    if (ret != 0) {
        ERROR_OUT(-11029, done);
    }

#ifdef HAVE_ED448_VERIFY
    ret = wc_ed448_init(&key);
    if (ret < 0) {
        ERROR_OUT(-11030, done);
    }
    pubKey = &key;
    ret = wc_ed448_import_public(caCert->publicKey, caCert->pubKeySize, pubKey);
    if (ret < 0) {
        ERROR_OUT(-11031, done);
    }

    if (wc_ed448_verify_msg(serverCert->signature, serverCert->sigLength,
                            serverCert->source + serverCert->certBegin,
                            serverCert->sigIndex - serverCert->certBegin,
                            &verify, pubKey, NULL, 0) < 0 || verify != 1) {
        ERROR_OUT(-11032, done);
    }
#endif /* HAVE_ED448_VERIFY */

done:
    if (tmp != NULL)
        XFREE(tmp, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
#ifdef HAVE_ED448_VERIFY
    wc_ed448_free(pubKey);
#endif /* HAVE_ED448_VERIFY */
    if (caCert != NULL)
        FreeDecodedCert(caCert);
    if (serverCert != NULL)
        FreeDecodedCert(serverCert);

    return ret;
}

static int ed448_test_make_cert(void)
{
    WC_RNG       rng;
    Cert         cert;
    DecodedCert  decode;
    ed448_key  key;
    ed448_key* privKey = NULL;
    int          ret = 0;
    byte*        tmp = NULL;

    wc_InitCert(&cert);

#ifndef HAVE_FIPS
    ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
    ret = wc_InitRng(&rng);
#endif
    if (ret != 0)
        return -11033;

    wc_ed448_init(&key);
    privKey = &key;
    wc_ed448_make_key(&rng, ED448_KEY_SIZE, privKey);

    cert.daysValid = 365 * 2;
    cert.selfSigned = 1;
    XMEMCPY(&cert.issuer, &certDefaultName, sizeof(CertName));
    XMEMCPY(&cert.subject, &certDefaultName, sizeof(CertName));
    cert.isCA = 0;
#ifdef WOLFSSL_CERT_EXT
    ret = wc_SetKeyUsage(&cert, certKeyUsage);
    if (ret < 0) {
        ERROR_OUT(-11034, done);
    }
    ret = wc_SetSubjectKeyIdFromPublicKey_ex(&cert, ED448_TYPE, privKey);
    if (ret < 0) {
        ERROR_OUT(-11035, done);
    }
    ret = wc_SetAuthKeyIdFromPublicKey_ex(&cert, ED448_TYPE, privKey);
    if (ret < 0) {
        ERROR_OUT(-11036, done);
    }
#endif
    tmp = XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (tmp == NULL) {
        ERROR_OUT(-11037, done);
    }

    cert.sigType = CTC_ED448;
    ret = wc_MakeCert_ex(&cert, tmp, FOURK_BUF, ED448_TYPE, privKey, &rng);
    if (ret < 0) {
        ERROR_OUT(-11038, done);
    }
    ret = wc_SignCert_ex(cert.bodySz, cert.sigType, tmp, FOURK_BUF, ED448_TYPE,
                                                                 privKey, &rng);
    if (ret < 0) {
        ERROR_OUT(-11039, done);
    }

    InitDecodedCert(&decode, tmp, ret, HEAP_HINT);
    ret = ParseCert(&decode, CERT_TYPE, NO_VERIFY, 0);
    FreeDecodedCert(&decode);
    if (ret != 0) {
        ERROR_OUT(-11040, done);
    }

done:
    if (tmp != NULL)
        XFREE(tmp, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    wc_ed448_free(privKey);
    wc_FreeRng(&rng);
    return ret;
}
#endif /* WOLFSSL_TEST_CERT */

#if defined(HAVE_ED448_SIGN) && defined(HAVE_ED448_KEY_EXPORT) && \
    defined(HAVE_ED448_KEY_IMPORT)
static int ed448_ctx_test(void)
{
    byte   out[ED448_SIG_SIZE];
    word32 outlen;
#ifdef HAVE_ED448_VERIFY
    int    verify;
#endif /* HAVE_ED448_VERIFY */
    ed448_key key;

    static const byte sKeyCtx[] = {
        0xc4, 0xea, 0xb0, 0x5d, 0x35, 0x70, 0x07, 0xc6,
        0x32, 0xf3, 0xdb, 0xb4, 0x84, 0x89, 0x92, 0x4d,
        0x55, 0x2b, 0x08, 0xfe, 0x0c, 0x35, 0x3a, 0x0d,
        0x4a, 0x1f, 0x00, 0xac, 0xda, 0x2c, 0x46, 0x3a,
        0xfb, 0xea, 0x67, 0xc5, 0xe8, 0xd2, 0x87, 0x7c,
        0x5e, 0x3b, 0xc3, 0x97, 0xa6, 0x59, 0x94, 0x9e,
        0xf8, 0x02, 0x1e, 0x95, 0x4e, 0x0a, 0x12, 0x27,
        0x4e
    };

    static const byte pKeyCtx[] = {
        0x43, 0xba, 0x28, 0xf4, 0x30, 0xcd, 0xff, 0x45,
        0x6a, 0xe5, 0x31, 0x54, 0x5f, 0x7e, 0xcd, 0x0a,
        0xc8, 0x34, 0xa5, 0x5d, 0x93, 0x58, 0xc0, 0x37,
        0x2b, 0xfa, 0x0c, 0x6c, 0x67, 0x98, 0xc0, 0x86,
        0x6a, 0xea, 0x01, 0xeb, 0x00, 0x74, 0x28, 0x02,
        0xb8, 0x43, 0x8e, 0xa4, 0xcb, 0x82, 0x16, 0x9c,
        0x23, 0x51, 0x60, 0x62, 0x7b, 0x4c, 0x3a, 0x94,
        0x80
    };

    static const byte sigCtx[] = {
        0xd4, 0xf8, 0xf6, 0x13, 0x17, 0x70, 0xdd, 0x46,
        0xf4, 0x08, 0x67, 0xd6, 0xfd, 0x5d, 0x50, 0x55,
        0xde, 0x43, 0x54, 0x1f, 0x8c, 0x5e, 0x35, 0xab,
        0xbc, 0xd0, 0x01, 0xb3, 0x2a, 0x89, 0xf7, 0xd2,
        0x15, 0x1f, 0x76, 0x47, 0xf1, 0x1d, 0x8c, 0xa2,
        0xae, 0x27, 0x9f, 0xb8, 0x42, 0xd6, 0x07, 0x21,
        0x7f, 0xce, 0x6e, 0x04, 0x2f, 0x68, 0x15, 0xea,
        0x00, 0x0c, 0x85, 0x74, 0x1d, 0xe5, 0xc8, 0xda,
        0x11, 0x44, 0xa6, 0xa1, 0xab, 0xa7, 0xf9, 0x6d,
        0xe4, 0x25, 0x05, 0xd7, 0xa7, 0x29, 0x85, 0x24,
        0xfd, 0xa5, 0x38, 0xfc, 0xcb, 0xbb, 0x75, 0x4f,
        0x57, 0x8c, 0x1c, 0xad, 0x10, 0xd5, 0x4d, 0x0d,
        0x54, 0x28, 0x40, 0x7e, 0x85, 0xdc, 0xbc, 0x98,
        0xa4, 0x91, 0x55, 0xc1, 0x37, 0x64, 0xe6, 0x6c,
        0x3c, 0x00
    };

    static const byte msgCtx[] = {
        0x03
    };

    static const byte contextCtx[] = {
        0x66,0x6f,0x6f
    };

    outlen = sizeof(out);
    XMEMSET(out, 0, sizeof(out));

    if (wc_ed448_import_private_key(sKeyCtx, ED448_KEY_SIZE, pKeyCtx,
                                    sizeof(pKeyCtx), &key) != 0)
        return -11100;

    if (wc_ed448_sign_msg(msgCtx, sizeof(msgCtx), out, &outlen, &key,
                          contextCtx, sizeof(contextCtx)) != 0)
        return -11101;

    if (XMEMCMP(out, sigCtx, sizeof(sigCtx)))
        return -11102;

#if defined(HAVE_ED448_VERIFY)
    /* test verify on good msg */
    if (wc_ed448_verify_msg(out, outlen, msgCtx, sizeof(msgCtx), &verify, &key,
                            contextCtx, sizeof(contextCtx)) != 0 || verify != 1)
        return -11103;
#endif

    wc_ed448_free(&key);

    return 0;
}

static int ed448ph_test(void)
{
    byte   out[ED448_SIG_SIZE];
    word32 outlen;
#ifdef HAVE_ED448_VERIFY
    int    verify;
#endif /* HAVE_ED448_VERIFY */
    ed448_key key;

    static const byte sKeyPh[] = {
        0x83, 0x3f, 0xe6, 0x24, 0x09, 0x23, 0x7b, 0x9d,
        0x62, 0xec, 0x77, 0x58, 0x75, 0x20, 0x91, 0x1e,
        0x9a, 0x75, 0x9c, 0xec, 0x1d, 0x19, 0x75, 0x5b,
        0x7d, 0xa9, 0x01, 0xb9, 0x6d, 0xca, 0x3d, 0x42,
        0xef, 0x78, 0x22, 0xe0, 0xd5, 0x10, 0x41, 0x27,
        0xdc, 0x05, 0xd6, 0xdb, 0xef, 0xde, 0x69, 0xe3,
        0xab, 0x2c, 0xec, 0x7c, 0x86, 0x7c, 0x6e, 0x2c,
        0x49
    };

    static const byte pKeyPh[] = {
        0x25, 0x9b, 0x71, 0xc1, 0x9f, 0x83, 0xef, 0x77,
        0xa7, 0xab, 0xd2, 0x65, 0x24, 0xcb, 0xdb, 0x31,
        0x61, 0xb5, 0x90, 0xa4, 0x8f, 0x7d, 0x17, 0xde,
        0x3e, 0xe0, 0xba, 0x9c, 0x52, 0xbe, 0xb7, 0x43,
        0xc0, 0x94, 0x28, 0xa1, 0x31, 0xd6, 0xb1, 0xb5,
        0x73, 0x03, 0xd9, 0x0d, 0x81, 0x32, 0xc2, 0x76,
        0xd5, 0xed, 0x3d, 0x5d, 0x01, 0xc0, 0xf5, 0x38,
        0x80
    };

    static const byte sigPh1[] = {
        0x82, 0x2f, 0x69, 0x01, 0xf7, 0x48, 0x0f, 0x3d,
        0x5f, 0x56, 0x2c, 0x59, 0x29, 0x94, 0xd9, 0x69,
        0x36, 0x02, 0x87, 0x56, 0x14, 0x48, 0x32, 0x56,
        0x50, 0x56, 0x00, 0xbb, 0xc2, 0x81, 0xae, 0x38,
        0x1f, 0x54, 0xd6, 0xbc, 0xe2, 0xea, 0x91, 0x15,
        0x74, 0x93, 0x2f, 0x52, 0xa4, 0xe6, 0xca, 0xdd,
        0x78, 0x76, 0x93, 0x75, 0xec, 0x3f, 0xfd, 0x1b,
        0x80, 0x1a, 0x0d, 0x9b, 0x3f, 0x40, 0x30, 0xcd,
        0x43, 0x39, 0x64, 0xb6, 0x45, 0x7e, 0xa3, 0x94,
        0x76, 0x51, 0x12, 0x14, 0xf9, 0x74, 0x69, 0xb5,
        0x7d, 0xd3, 0x2d, 0xbc, 0x56, 0x0a, 0x9a, 0x94,
        0xd0, 0x0b, 0xff, 0x07, 0x62, 0x04, 0x64, 0xa3,
        0xad, 0x20, 0x3d, 0xf7, 0xdc, 0x7c, 0xe3, 0x60,
        0xc3, 0xcd, 0x36, 0x96, 0xd9, 0xd9, 0xfa, 0xb9,
        0x0f, 0x00
    };

    static const byte sigPh2[] = {
        0xc3, 0x22, 0x99, 0xd4, 0x6e, 0xc8, 0xff, 0x02,
        0xb5, 0x45, 0x40, 0x98, 0x28, 0x14, 0xdc, 0xe9,
        0xa0, 0x58, 0x12, 0xf8, 0x19, 0x62, 0xb6, 0x49,
        0xd5, 0x28, 0x09, 0x59, 0x16, 0xa2, 0xaa, 0x48,
        0x10, 0x65, 0xb1, 0x58, 0x04, 0x23, 0xef, 0x92,
        0x7e, 0xcf, 0x0a, 0xf5, 0x88, 0x8f, 0x90, 0xda,
        0x0f, 0x6a, 0x9a, 0x85, 0xad, 0x5d, 0xc3, 0xf2,
        0x80, 0xd9, 0x12, 0x24, 0xba, 0x99, 0x11, 0xa3,
        0x65, 0x3d, 0x00, 0xe4, 0x84, 0xe2, 0xce, 0x23,
        0x25, 0x21, 0x48, 0x1c, 0x86, 0x58, 0xdf, 0x30,
        0x4b, 0xb7, 0x74, 0x5a, 0x73, 0x51, 0x4c, 0xdb,
        0x9b, 0xf3, 0xe1, 0x57, 0x84, 0xab, 0x71, 0x28,
        0x4f, 0x8d, 0x07, 0x04, 0xa6, 0x08, 0xc5, 0x4a,
        0x6b, 0x62, 0xd9, 0x7b, 0xeb, 0x51, 0x1d, 0x13,
        0x21, 0x00
    };

    static const byte msgPh[] = {
        0x61,0x62,0x63
    };

    /* SHA-512 hash of msgPh */
    static const byte hashPh[] = {
        0x48, 0x33, 0x66, 0x60, 0x13, 0x60, 0xa8, 0x77,
        0x1c, 0x68, 0x63, 0x08, 0x0c, 0xc4, 0x11, 0x4d,
        0x8d, 0xb4, 0x45, 0x30, 0xf8, 0xf1, 0xe1, 0xee,
        0x4f, 0x94, 0xea, 0x37, 0xe7, 0x8b, 0x57, 0x39,
        0xd5, 0xa1, 0x5b, 0xef, 0x18, 0x6a, 0x53, 0x86,
        0xc7, 0x57, 0x44, 0xc0, 0x52, 0x7e, 0x1f, 0xaa,
        0x9f, 0x87, 0x26, 0xe4, 0x62, 0xa1, 0x2a, 0x4f,
        0xeb, 0x06, 0xbd, 0x88, 0x01, 0xe7, 0x51, 0xe4
    };

    static const byte contextPh2[] = {
        0x66,0x6f,0x6f
    };

    outlen = sizeof(out);
    XMEMSET(out, 0, sizeof(out));

    if (wc_ed448_import_private_key(sKeyPh, ED448_KEY_SIZE, pKeyPh,
                                    sizeof(pKeyPh), &key) != 0) {
        return -11200;
    }

    if (wc_ed448ph_sign_msg(msgPh, sizeof(msgPh), out, &outlen, &key, NULL,
                            0) != 0) {
        return -11201;
    }

    if (XMEMCMP(out, sigPh1, sizeof(sigPh1)))
        return -11202;

#if defined(HAVE_ED448_VERIFY)
    /* test verify on good msg */
    if (wc_ed448ph_verify_msg(out, outlen, msgPh, sizeof(msgPh), &verify, &key,
                              NULL, 0) != 0 || verify != 1) {
        return -11203;
    }
#endif

    if (wc_ed448ph_sign_msg(msgPh, sizeof(msgPh), out, &outlen, &key,
                            contextPh2, sizeof(contextPh2)) != 0) {
        return -11204;
    }

    if (XMEMCMP(out, sigPh2, sizeof(sigPh2)))
        return -11205;

#if defined(HAVE_ED448_VERIFY)
    /* test verify on good msg */
    if (wc_ed448ph_verify_msg(out, outlen, msgPh, sizeof(msgPh), &verify, &key,
                              contextPh2, sizeof(contextPh2)) != 0 ||
            verify != 1) {
        return -11206;
    }
#endif

    if (wc_ed448ph_sign_hash(hashPh, sizeof(hashPh), out, &outlen, &key, NULL,
                             0) != 0) {
        return -11207;
    }

    if (XMEMCMP(out, sigPh1, sizeof(sigPh1)))
        return -11208;

#if defined(HAVE_ED448_VERIFY)
    if (wc_ed448ph_verify_hash(out, outlen, hashPh, sizeof(hashPh), &verify,
                               &key, NULL, 0) != 0 || verify != 1) {
        return -11209;
    }
#endif

    if (wc_ed448ph_sign_hash(hashPh, sizeof(hashPh), out, &outlen, &key,
                             contextPh2, sizeof(contextPh2)) != 0) {
        return -11210;
    }

    if (XMEMCMP(out, sigPh2, sizeof(sigPh2)))
        return -11211;

#if defined(HAVE_ED448_VERIFY)
    if (wc_ed448ph_verify_hash(out, outlen, hashPh, sizeof(hashPh), &verify,
                               &key, contextPh2, sizeof(contextPh2)) != 0 ||
            verify != 1) {
        return -11212;
    }
#endif

    wc_ed448_free(&key);

    return 0;
}
#endif /* HAVE_ED448_SIGN && HAVE_ED448_KEY_EXPORT && HAVE_ED448_KEY_IMPORT */

int ed448_test(void)
{
    int ret;
    WC_RNG rng;
#if defined(HAVE_ED448_SIGN) && defined(HAVE_ED448_KEY_EXPORT) &&\
    defined(HAVE_ED448_KEY_IMPORT)
    byte   out[ED448_SIG_SIZE];
    byte   exportPKey[ED448_KEY_SIZE];
    byte   exportSKey[ED448_KEY_SIZE];
    word32 exportPSz;
    word32 exportSSz;
    int    i;
    word32 outlen;
#ifdef HAVE_ED448_VERIFY
    int    verify;
#endif /* HAVE_ED448_VERIFY */
#endif /* HAVE_ED448_SIGN && HAVE_ED448_KEY_EXPORT && HAVE_ED448_KEY_IMPORT */
    word32 keySz, sigSz;
    ed448_key key;
    ed448_key key2;

#if defined(HAVE_ED448_SIGN) && defined(HAVE_ED448_KEY_EXPORT) && \
    defined(HAVE_ED448_KEY_IMPORT)
    /* test vectors from
       https://tools.ietf.org/html/rfc8032
     */

    static const byte sKey1[] = {
        0x6c, 0x82, 0xa5, 0x62, 0xcb, 0x80, 0x8d, 0x10,
        0xd6, 0x32, 0xbe, 0x89, 0xc8, 0x51, 0x3e, 0xbf,
        0x6c, 0x92, 0x9f, 0x34, 0xdd, 0xfa, 0x8c, 0x9f,
        0x63, 0xc9, 0x96, 0x0e, 0xf6, 0xe3, 0x48, 0xa3,
        0x52, 0x8c, 0x8a, 0x3f, 0xcc, 0x2f, 0x04, 0x4e,
        0x39, 0xa3, 0xfc, 0x5b, 0x94, 0x49, 0x2f, 0x8f,
        0x03, 0x2e, 0x75, 0x49, 0xa2, 0x00, 0x98, 0xf9,
        0x5b
    };

    static const byte sKey2[] = {
        0xc4, 0xea, 0xb0, 0x5d, 0x35, 0x70, 0x07, 0xc6,
        0x32, 0xf3, 0xdb, 0xb4, 0x84, 0x89, 0x92, 0x4d,
        0x55, 0x2b, 0x08, 0xfe, 0x0c, 0x35, 0x3a, 0x0d,
        0x4a, 0x1f, 0x00, 0xac, 0xda, 0x2c, 0x46, 0x3a,
        0xfb, 0xea, 0x67, 0xc5, 0xe8, 0xd2, 0x87, 0x7c,
        0x5e, 0x3b, 0xc3, 0x97, 0xa6, 0x59, 0x94, 0x9e,
        0xf8, 0x02, 0x1e, 0x95, 0x4e, 0x0a, 0x12, 0x27,
        0x4e
    };

    static const byte sKey3[] = {
        0x25, 0x8c, 0xdd, 0x4a, 0xda, 0x32, 0xed, 0x9c,
        0x9f, 0xf5, 0x4e, 0x63, 0x75, 0x6a, 0xe5, 0x82,
        0xfb, 0x8f, 0xab, 0x2a, 0xc7, 0x21, 0xf2, 0xc8,
        0xe6, 0x76, 0xa7, 0x27, 0x68, 0x51, 0x3d, 0x93,
        0x9f, 0x63, 0xdd, 0xdb, 0x55, 0x60, 0x91, 0x33,
        0xf2, 0x9a, 0xdf, 0x86, 0xec, 0x99, 0x29, 0xdc,
        0xcb, 0x52, 0xc1, 0xc5, 0xfd, 0x2f, 0xf7, 0xe2,
        0x1b
    };

    /* uncompressed test */
    static const byte sKey4[] = {
        0x6c, 0x82, 0xa5, 0x62, 0xcb, 0x80, 0x8d, 0x10,
        0xd6, 0x32, 0xbe, 0x89, 0xc8, 0x51, 0x3e, 0xbf,
        0x6c, 0x92, 0x9f, 0x34, 0xdd, 0xfa, 0x8c, 0x9f,
        0x63, 0xc9, 0x96, 0x0e, 0xf6, 0xe3, 0x48, 0xa3,
        0x52, 0x8c, 0x8a, 0x3f, 0xcc, 0x2f, 0x04, 0x4e,
        0x39, 0xa3, 0xfc, 0x5b, 0x94, 0x49, 0x2f, 0x8f,
        0x03, 0x2e, 0x75, 0x49, 0xa2, 0x00, 0x98, 0xf9,
        0x5b
    };

    /* compressed prefix test */
    static const byte sKey5[] = {
        0x6c, 0x82, 0xa5, 0x62, 0xcb, 0x80, 0x8d, 0x10,
        0xd6, 0x32, 0xbe, 0x89, 0xc8, 0x51, 0x3e, 0xbf,
        0x6c, 0x92, 0x9f, 0x34, 0xdd, 0xfa, 0x8c, 0x9f,
        0x63, 0xc9, 0x96, 0x0e, 0xf6, 0xe3, 0x48, 0xa3,
        0x52, 0x8c, 0x8a, 0x3f, 0xcc, 0x2f, 0x04, 0x4e,
        0x39, 0xa3, 0xfc, 0x5b, 0x94, 0x49, 0x2f, 0x8f,
        0x03, 0x2e, 0x75, 0x49, 0xa2, 0x00, 0x98, 0xf9,
        0x5b
    };

    static const byte sKey6[] = {
        0x87, 0x2d, 0x09, 0x37, 0x80, 0xf5, 0xd3, 0x73,
        0x0d, 0xf7, 0xc2, 0x12, 0x66, 0x4b, 0x37, 0xb8,
        0xa0, 0xf2, 0x4f, 0x56, 0x81, 0x0d, 0xaa, 0x83,
        0x82, 0xcd, 0x4f, 0xa3, 0xf7, 0x76, 0x34, 0xec,
        0x44, 0xdc, 0x54, 0xf1, 0xc2, 0xed, 0x9b, 0xea,
        0x86, 0xfa, 0xfb, 0x76, 0x32, 0xd8, 0xbe, 0x19,
        0x9e, 0xa1, 0x65, 0xf5, 0xad, 0x55, 0xdd, 0x9c,
        0xe8
    };

    static const byte* sKeys[] = {sKey1, sKey2, sKey3, sKey4, sKey5, sKey6};

    static const byte pKey1[] = {
        0x5f, 0xd7, 0x44, 0x9b, 0x59, 0xb4, 0x61, 0xfd,
        0x2c, 0xe7, 0x87, 0xec, 0x61, 0x6a, 0xd4, 0x6a,
        0x1d, 0xa1, 0x34, 0x24, 0x85, 0xa7, 0x0e, 0x1f,
        0x8a, 0x0e, 0xa7, 0x5d, 0x80, 0xe9, 0x67, 0x78,
        0xed, 0xf1, 0x24, 0x76, 0x9b, 0x46, 0xc7, 0x06,
        0x1b, 0xd6, 0x78, 0x3d, 0xf1, 0xe5, 0x0f, 0x6c,
        0xd1, 0xfa, 0x1a, 0xbe, 0xaf, 0xe8, 0x25, 0x61,
        0x80
    };

    static const byte pKey2[] = {
        0x43, 0xba, 0x28, 0xf4, 0x30, 0xcd, 0xff, 0x45,
        0x6a, 0xe5, 0x31, 0x54, 0x5f, 0x7e, 0xcd, 0x0a,
        0xc8, 0x34, 0xa5, 0x5d, 0x93, 0x58, 0xc0, 0x37,
        0x2b, 0xfa, 0x0c, 0x6c, 0x67, 0x98, 0xc0, 0x86,
        0x6a, 0xea, 0x01, 0xeb, 0x00, 0x74, 0x28, 0x02,
        0xb8, 0x43, 0x8e, 0xa4, 0xcb, 0x82, 0x16, 0x9c,
        0x23, 0x51, 0x60, 0x62, 0x7b, 0x4c, 0x3a, 0x94,
        0x80
    };

    static const byte pKey3[] = {
        0x3b, 0xa1, 0x6d, 0xa0, 0xc6, 0xf2, 0xcc, 0x1f,
        0x30, 0x18, 0x77, 0x40, 0x75, 0x6f, 0x5e, 0x79,
        0x8d, 0x6b, 0xc5, 0xfc, 0x01, 0x5d, 0x7c, 0x63,
        0xcc, 0x95, 0x10, 0xee, 0x3f, 0xd4, 0x4a, 0xdc,
        0x24, 0xd8, 0xe9, 0x68, 0xb6, 0xe4, 0x6e, 0x6f,
        0x94, 0xd1, 0x9b, 0x94, 0x53, 0x61, 0x72, 0x6b,
        0xd7, 0x5e, 0x14, 0x9e, 0xf0, 0x98, 0x17, 0xf5,
        0x80
    };

    /* uncompressed test */
    static const byte pKey4[] = {
        0x5f, 0xd7, 0x44, 0x9b, 0x59, 0xb4, 0x61, 0xfd,
        0x2c, 0xe7, 0x87, 0xec, 0x61, 0x6a, 0xd4, 0x6a,
        0x1d, 0xa1, 0x34, 0x24, 0x85, 0xa7, 0x0e, 0x1f,
        0x8a, 0x0e, 0xa7, 0x5d, 0x80, 0xe9, 0x67, 0x78,
        0xed, 0xf1, 0x24, 0x76, 0x9b, 0x46, 0xc7, 0x06,
        0x1b, 0xd6, 0x78, 0x3d, 0xf1, 0xe5, 0x0f, 0x6c,
        0xd1, 0xfa, 0x1a, 0xbe, 0xaf, 0xe8, 0x25, 0x61,
        0x80
    };

    /* compressed prefix */
    static const byte pKey5[] = {
        0x5f, 0xd7, 0x44, 0x9b, 0x59, 0xb4, 0x61, 0xfd,
        0x2c, 0xe7, 0x87, 0xec, 0x61, 0x6a, 0xd4, 0x6a,
        0x1d, 0xa1, 0x34, 0x24, 0x85, 0xa7, 0x0e, 0x1f,
        0x8a, 0x0e, 0xa7, 0x5d, 0x80, 0xe9, 0x67, 0x78,
        0xed, 0xf1, 0x24, 0x76, 0x9b, 0x46, 0xc7, 0x06,
        0x1b, 0xd6, 0x78, 0x3d, 0xf1, 0xe5, 0x0f, 0x6c,
        0xd1, 0xfa, 0x1a, 0xbe, 0xaf, 0xe8, 0x25, 0x61,
        0x80
    };

    static const byte pKey6[] = {
        0xa8, 0x1b, 0x2e, 0x8a, 0x70, 0xa5, 0xac, 0x94,
        0xff, 0xdb, 0xcc, 0x9b, 0xad, 0xfc, 0x3f, 0xeb,
        0x08, 0x01, 0xf2, 0x58, 0x57, 0x8b, 0xb1, 0x14,
        0xad, 0x44, 0xec, 0xe1, 0xec, 0x0e, 0x79, 0x9d,
        0xa0, 0x8e, 0xff, 0xb8, 0x1c, 0x5d, 0x68, 0x5c,
        0x0c, 0x56, 0xf6, 0x4e, 0xec, 0xae, 0xf8, 0xcd,
        0xf1, 0x1c, 0xc3, 0x87, 0x37, 0x83, 0x8c, 0xf4,
        0x00
    };

    static const byte* pKeys[] = {pKey1, pKey2, pKey3, pKey4, pKey5, pKey6};
    static const byte  pKeySz[] = {sizeof(pKey1), sizeof(pKey2), sizeof(pKey3),
                            sizeof(pKey4), sizeof(pKey5), sizeof(pKey6)};

    static const byte sig1[] = {
        0x53, 0x3a, 0x37, 0xf6, 0xbb, 0xe4, 0x57, 0x25,
        0x1f, 0x02, 0x3c, 0x0d, 0x88, 0xf9, 0x76, 0xae,
        0x2d, 0xfb, 0x50, 0x4a, 0x84, 0x3e, 0x34, 0xd2,
        0x07, 0x4f, 0xd8, 0x23, 0xd4, 0x1a, 0x59, 0x1f,
        0x2b, 0x23, 0x3f, 0x03, 0x4f, 0x62, 0x82, 0x81,
        0xf2, 0xfd, 0x7a, 0x22, 0xdd, 0xd4, 0x7d, 0x78,
        0x28, 0xc5, 0x9b, 0xd0, 0xa2, 0x1b, 0xfd, 0x39,
        0x80, 0xff, 0x0d, 0x20, 0x28, 0xd4, 0xb1, 0x8a,
        0x9d, 0xf6, 0x3e, 0x00, 0x6c, 0x5d, 0x1c, 0x2d,
        0x34, 0x5b, 0x92, 0x5d, 0x8d, 0xc0, 0x0b, 0x41,
        0x04, 0x85, 0x2d, 0xb9, 0x9a, 0xc5, 0xc7, 0xcd,
        0xda, 0x85, 0x30, 0xa1, 0x13, 0xa0, 0xf4, 0xdb,
        0xb6, 0x11, 0x49, 0xf0, 0x5a, 0x73, 0x63, 0x26,
        0x8c, 0x71, 0xd9, 0x58, 0x08, 0xff, 0x2e, 0x65,
        0x26, 0x00
    };

    static const byte sig2[] = {
        0x26, 0xb8, 0xf9, 0x17, 0x27, 0xbd, 0x62, 0x89,
        0x7a, 0xf1, 0x5e, 0x41, 0xeb, 0x43, 0xc3, 0x77,
        0xef, 0xb9, 0xc6, 0x10, 0xd4, 0x8f, 0x23, 0x35,
        0xcb, 0x0b, 0xd0, 0x08, 0x78, 0x10, 0xf4, 0x35,
        0x25, 0x41, 0xb1, 0x43, 0xc4, 0xb9, 0x81, 0xb7,
        0xe1, 0x8f, 0x62, 0xde, 0x8c, 0xcd, 0xf6, 0x33,
        0xfc, 0x1b, 0xf0, 0x37, 0xab, 0x7c, 0xd7, 0x79,
        0x80, 0x5e, 0x0d, 0xbc, 0xc0, 0xaa, 0xe1, 0xcb,
        0xce, 0xe1, 0xaf, 0xb2, 0xe0, 0x27, 0xdf, 0x36,
        0xbc, 0x04, 0xdc, 0xec, 0xbf, 0x15, 0x43, 0x36,
        0xc1, 0x9f, 0x0a, 0xf7, 0xe0, 0xa6, 0x47, 0x29,
        0x05, 0xe7, 0x99, 0xf1, 0x95, 0x3d, 0x2a, 0x0f,
        0xf3, 0x34, 0x8a, 0xb2, 0x1a, 0xa4, 0xad, 0xaf,
        0xd1, 0xd2, 0x34, 0x44, 0x1c, 0xf8, 0x07, 0xc0,
        0x3a, 0x00
    };

    static const byte sig3[] = {
        0x7e, 0xee, 0xab, 0x7c, 0x4e, 0x50, 0xfb, 0x79,
        0x9b, 0x41, 0x8e, 0xe5, 0xe3, 0x19, 0x7f, 0xf6,
        0xbf, 0x15, 0xd4, 0x3a, 0x14, 0xc3, 0x43, 0x89,
        0xb5, 0x9d, 0xd1, 0xa7, 0xb1, 0xb8, 0x5b, 0x4a,
        0xe9, 0x04, 0x38, 0xac, 0xa6, 0x34, 0xbe, 0xa4,
        0x5e, 0x3a, 0x26, 0x95, 0xf1, 0x27, 0x0f, 0x07,
        0xfd, 0xcd, 0xf7, 0xc6, 0x2b, 0x8e, 0xfe, 0xaf,
        0x00, 0xb4, 0x5c, 0x2c, 0x96, 0xba, 0x45, 0x7e,
        0xb1, 0xa8, 0xbf, 0x07, 0x5a, 0x3d, 0xb2, 0x8e,
        0x5c, 0x24, 0xf6, 0xb9, 0x23, 0xed, 0x4a, 0xd7,
        0x47, 0xc3, 0xc9, 0xe0, 0x3c, 0x70, 0x79, 0xef,
        0xb8, 0x7c, 0xb1, 0x10, 0xd3, 0xa9, 0x98, 0x61,
        0xe7, 0x20, 0x03, 0xcb, 0xae, 0x6d, 0x6b, 0x8b,
        0x82, 0x7e, 0x4e, 0x6c, 0x14, 0x30, 0x64, 0xff,
        0x3c, 0x00
    };

    /* uncompressed test */
    static const byte sig4[] = {
        0x53, 0x3a, 0x37, 0xf6, 0xbb, 0xe4, 0x57, 0x25,
        0x1f, 0x02, 0x3c, 0x0d, 0x88, 0xf9, 0x76, 0xae,
        0x2d, 0xfb, 0x50, 0x4a, 0x84, 0x3e, 0x34, 0xd2,
        0x07, 0x4f, 0xd8, 0x23, 0xd4, 0x1a, 0x59, 0x1f,
        0x2b, 0x23, 0x3f, 0x03, 0x4f, 0x62, 0x82, 0x81,
        0xf2, 0xfd, 0x7a, 0x22, 0xdd, 0xd4, 0x7d, 0x78,
        0x28, 0xc5, 0x9b, 0xd0, 0xa2, 0x1b, 0xfd, 0x39,
        0x80, 0xff, 0x0d, 0x20, 0x28, 0xd4, 0xb1, 0x8a,
        0x9d, 0xf6, 0x3e, 0x00, 0x6c, 0x5d, 0x1c, 0x2d,
        0x34, 0x5b, 0x92, 0x5d, 0x8d, 0xc0, 0x0b, 0x41,
        0x04, 0x85, 0x2d, 0xb9, 0x9a, 0xc5, 0xc7, 0xcd,
        0xda, 0x85, 0x30, 0xa1, 0x13, 0xa0, 0xf4, 0xdb,
        0xb6, 0x11, 0x49, 0xf0, 0x5a, 0x73, 0x63, 0x26,
        0x8c, 0x71, 0xd9, 0x58, 0x08, 0xff, 0x2e, 0x65,
        0x26, 0x00
    };

    /* compressed prefix */
    static const byte sig5[] = {
        0x53, 0x3a, 0x37, 0xf6, 0xbb, 0xe4, 0x57, 0x25,
        0x1f, 0x02, 0x3c, 0x0d, 0x88, 0xf9, 0x76, 0xae,
        0x2d, 0xfb, 0x50, 0x4a, 0x84, 0x3e, 0x34, 0xd2,
        0x07, 0x4f, 0xd8, 0x23, 0xd4, 0x1a, 0x59, 0x1f,
        0x2b, 0x23, 0x3f, 0x03, 0x4f, 0x62, 0x82, 0x81,
        0xf2, 0xfd, 0x7a, 0x22, 0xdd, 0xd4, 0x7d, 0x78,
        0x28, 0xc5, 0x9b, 0xd0, 0xa2, 0x1b, 0xfd, 0x39,
        0x80, 0xff, 0x0d, 0x20, 0x28, 0xd4, 0xb1, 0x8a,
        0x9d, 0xf6, 0x3e, 0x00, 0x6c, 0x5d, 0x1c, 0x2d,
        0x34, 0x5b, 0x92, 0x5d, 0x8d, 0xc0, 0x0b, 0x41,
        0x04, 0x85, 0x2d, 0xb9, 0x9a, 0xc5, 0xc7, 0xcd,
        0xda, 0x85, 0x30, 0xa1, 0x13, 0xa0, 0xf4, 0xdb,
        0xb6, 0x11, 0x49, 0xf0, 0x5a, 0x73, 0x63, 0x26,
        0x8c, 0x71, 0xd9, 0x58, 0x08, 0xff, 0x2e, 0x65,
        0x26, 0x00
    };

    static const byte sig6[] = {
        0xe3, 0x01, 0x34, 0x5a, 0x41, 0xa3, 0x9a, 0x4d,
        0x72, 0xff, 0xf8, 0xdf, 0x69, 0xc9, 0x80, 0x75,
        0xa0, 0xcc, 0x08, 0x2b, 0x80, 0x2f, 0xc9, 0xb2,
        0xb6, 0xbc, 0x50, 0x3f, 0x92, 0x6b, 0x65, 0xbd,
        0xdf, 0x7f, 0x4c, 0x8f, 0x1c, 0xb4, 0x9f, 0x63,
        0x96, 0xaf, 0xc8, 0xa7, 0x0a, 0xbe, 0x6d, 0x8a,
        0xef, 0x0d, 0xb4, 0x78, 0xd4, 0xc6, 0xb2, 0x97,
        0x00, 0x76, 0xc6, 0xa0, 0x48, 0x4f, 0xe7, 0x6d,
        0x76, 0xb3, 0xa9, 0x76, 0x25, 0xd7, 0x9f, 0x1c,
        0xe2, 0x40, 0xe7, 0xc5, 0x76, 0x75, 0x0d, 0x29,
        0x55, 0x28, 0x28, 0x6f, 0x71, 0x9b, 0x41, 0x3d,
        0xe9, 0xad, 0xa3, 0xe8, 0xeb, 0x78, 0xed, 0x57,
        0x36, 0x03, 0xce, 0x30, 0xd8, 0xbb, 0x76, 0x17,
        0x85, 0xdc, 0x30, 0xdb, 0xc3, 0x20, 0x86, 0x9e,
        0x1a, 0x00
    };

    static const byte* sigs[] = {sig1, sig2, sig3, sig4, sig5, sig6};
    #define SIGSZ sizeof(sig1)

    static const byte msg1[]  = { };
    static const byte msg2[]  = { 0x03 };
    static const byte msg3[]  = { 0x64, 0xa6, 0x5f, 0x3c, 0xde, 0xdc, 0xdd,
                                  0x66, 0x81, 0x1e, 0x29, 0x15 };

    /* test of a 1023 byte long message */
    static const byte msg4[]  = {
        0x6d, 0xdf, 0x80, 0x2e, 0x1a, 0xae, 0x49, 0x86,
        0x93, 0x5f, 0x7f, 0x98, 0x1b, 0xa3, 0xf0, 0x35,
        0x1d, 0x62, 0x73, 0xc0, 0xa0, 0xc2, 0x2c, 0x9c,
        0x0e, 0x83, 0x39, 0x16, 0x8e, 0x67, 0x54, 0x12,
        0xa3, 0xde, 0xbf, 0xaf, 0x43, 0x5e, 0xd6, 0x51,
        0x55, 0x80, 0x07, 0xdb, 0x43, 0x84, 0xb6, 0x50,
        0xfc, 0xc0, 0x7e, 0x3b, 0x58, 0x6a, 0x27, 0xa4,
        0xf7, 0xa0, 0x0a, 0xc8, 0xa6, 0xfe, 0xc2, 0xcd,
        0x86, 0xae, 0x4b, 0xf1, 0x57, 0x0c, 0x41, 0xe6,
        0xa4, 0x0c, 0x93, 0x1d, 0xb2, 0x7b, 0x2f, 0xaa,
        0x15, 0xa8, 0xce, 0xdd, 0x52, 0xcf, 0xf7, 0x36,
        0x2c, 0x4e, 0x6e, 0x23, 0xda, 0xec, 0x0f, 0xbc,
        0x3a, 0x79, 0xb6, 0x80, 0x6e, 0x31, 0x6e, 0xfc,
        0xc7, 0xb6, 0x81, 0x19, 0xbf, 0x46, 0xbc, 0x76,
        0xa2, 0x60, 0x67, 0xa5, 0x3f, 0x29, 0x6d, 0xaf,
        0xdb, 0xdc, 0x11, 0xc7, 0x7f, 0x77, 0x77, 0xe9,
        0x72, 0x66, 0x0c, 0xf4, 0xb6, 0xa9, 0xb3, 0x69,
        0xa6, 0x66, 0x5f, 0x02, 0xe0, 0xcc, 0x9b, 0x6e,
        0xdf, 0xad, 0x13, 0x6b, 0x4f, 0xab, 0xe7, 0x23,
        0xd2, 0x81, 0x3d, 0xb3, 0x13, 0x6c, 0xfd, 0xe9,
        0xb6, 0xd0, 0x44, 0x32, 0x2f, 0xee, 0x29, 0x47,
        0x95, 0x2e, 0x03, 0x1b, 0x73, 0xab, 0x5c, 0x60,
        0x33, 0x49, 0xb3, 0x07, 0xbd, 0xc2, 0x7b, 0xc6,
        0xcb, 0x8b, 0x8b, 0xbd, 0x7b, 0xd3, 0x23, 0x21,
        0x9b, 0x80, 0x33, 0xa5, 0x81, 0xb5, 0x9e, 0xad,
        0xeb, 0xb0, 0x9b, 0x3c, 0x4f, 0x3d, 0x22, 0x77,
        0xd4, 0xf0, 0x34, 0x36, 0x24, 0xac, 0xc8, 0x17,
        0x80, 0x47, 0x28, 0xb2, 0x5a, 0xb7, 0x97, 0x17,
        0x2b, 0x4c, 0x5c, 0x21, 0xa2, 0x2f, 0x9c, 0x78,
        0x39, 0xd6, 0x43, 0x00, 0x23, 0x2e, 0xb6, 0x6e,
        0x53, 0xf3, 0x1c, 0x72, 0x3f, 0xa3, 0x7f, 0xe3,
        0x87, 0xc7, 0xd3, 0xe5, 0x0b, 0xdf, 0x98, 0x13,
        0xa3, 0x0e, 0x5b, 0xb1, 0x2c, 0xf4, 0xcd, 0x93,
        0x0c, 0x40, 0xcf, 0xb4, 0xe1, 0xfc, 0x62, 0x25,
        0x92, 0xa4, 0x95, 0x88, 0x79, 0x44, 0x94, 0xd5,
        0x6d, 0x24, 0xea, 0x4b, 0x40, 0xc8, 0x9f, 0xc0,
        0x59, 0x6c, 0xc9, 0xeb, 0xb9, 0x61, 0xc8, 0xcb,
        0x10, 0xad, 0xde, 0x97, 0x6a, 0x5d, 0x60, 0x2b,
        0x1c, 0x3f, 0x85, 0xb9, 0xb9, 0xa0, 0x01, 0xed,
        0x3c, 0x6a, 0x4d, 0x3b, 0x14, 0x37, 0xf5, 0x20,
        0x96, 0xcd, 0x19, 0x56, 0xd0, 0x42, 0xa5, 0x97,
        0xd5, 0x61, 0xa5, 0x96, 0xec, 0xd3, 0xd1, 0x73,
        0x5a, 0x8d, 0x57, 0x0e, 0xa0, 0xec, 0x27, 0x22,
        0x5a, 0x2c, 0x4a, 0xaf, 0xf2, 0x63, 0x06, 0xd1,
        0x52, 0x6c, 0x1a, 0xf3, 0xca, 0x6d, 0x9c, 0xf5,
        0xa2, 0xc9, 0x8f, 0x47, 0xe1, 0xc4, 0x6d, 0xb9,
        0xa3, 0x32, 0x34, 0xcf, 0xd4, 0xd8, 0x1f, 0x2c,
        0x98, 0x53, 0x8a, 0x09, 0xeb, 0xe7, 0x69, 0x98,
        0xd0, 0xd8, 0xfd, 0x25, 0x99, 0x7c, 0x7d, 0x25,
        0x5c, 0x6d, 0x66, 0xec, 0xe6, 0xfa, 0x56, 0xf1,
        0x11, 0x44, 0x95, 0x0f, 0x02, 0x77, 0x95, 0xe6,
        0x53, 0x00, 0x8f, 0x4b, 0xd7, 0xca, 0x2d, 0xee,
        0x85, 0xd8, 0xe9, 0x0f, 0x3d, 0xc3, 0x15, 0x13,
        0x0c, 0xe2, 0xa0, 0x03, 0x75, 0xa3, 0x18, 0xc7,
        0xc3, 0xd9, 0x7b, 0xe2, 0xc8, 0xce, 0x5b, 0x6d,
        0xb4, 0x1a, 0x62, 0x54, 0xff, 0x26, 0x4f, 0xa6,
        0x15, 0x5b, 0xae, 0xe3, 0xb0, 0x77, 0x3c, 0x0f,
        0x49, 0x7c, 0x57, 0x3f, 0x19, 0xbb, 0x4f, 0x42,
        0x40, 0x28, 0x1f, 0x0b, 0x1f, 0x4f, 0x7b, 0xe8,
        0x57, 0xa4, 0xe5, 0x9d, 0x41, 0x6c, 0x06, 0xb4,
        0xc5, 0x0f, 0xa0, 0x9e, 0x18, 0x10, 0xdd, 0xc6,
        0xb1, 0x46, 0x7b, 0xae, 0xac, 0x5a, 0x36, 0x68,
        0xd1, 0x1b, 0x6e, 0xca, 0xa9, 0x01, 0x44, 0x00,
        0x16, 0xf3, 0x89, 0xf8, 0x0a, 0xcc, 0x4d, 0xb9,
        0x77, 0x02, 0x5e, 0x7f, 0x59, 0x24, 0x38, 0x8c,
        0x7e, 0x34, 0x0a, 0x73, 0x2e, 0x55, 0x44, 0x40,
        0xe7, 0x65, 0x70, 0xf8, 0xdd, 0x71, 0xb7, 0xd6,
        0x40, 0xb3, 0x45, 0x0d, 0x1f, 0xd5, 0xf0, 0x41,
        0x0a, 0x18, 0xf9, 0xa3, 0x49, 0x4f, 0x70, 0x7c,
        0x71, 0x7b, 0x79, 0xb4, 0xbf, 0x75, 0xc9, 0x84,
        0x00, 0xb0, 0x96, 0xb2, 0x16, 0x53, 0xb5, 0xd2,
        0x17, 0xcf, 0x35, 0x65, 0xc9, 0x59, 0x74, 0x56,
        0xf7, 0x07, 0x03, 0x49, 0x7a, 0x07, 0x87, 0x63,
        0x82, 0x9b, 0xc0, 0x1b, 0xb1, 0xcb, 0xc8, 0xfa,
        0x04, 0xea, 0xdc, 0x9a, 0x6e, 0x3f, 0x66, 0x99,
        0x58, 0x7a, 0x9e, 0x75, 0xc9, 0x4e, 0x5b, 0xab,
        0x00, 0x36, 0xe0, 0xb2, 0xe7, 0x11, 0x39, 0x2c,
        0xff, 0x00, 0x47, 0xd0, 0xd6, 0xb0, 0x5b, 0xd2,
        0xa5, 0x88, 0xbc, 0x10, 0x97, 0x18, 0x95, 0x42,
        0x59, 0xf1, 0xd8, 0x66, 0x78, 0xa5, 0x79, 0xa3,
        0x12, 0x0f, 0x19, 0xcf, 0xb2, 0x96, 0x3f, 0x17,
        0x7a, 0xeb, 0x70, 0xf2, 0xd4, 0x84, 0x48, 0x26,
        0x26, 0x2e, 0x51, 0xb8, 0x02, 0x71, 0x27, 0x20,
        0x68, 0xef, 0x5b, 0x38, 0x56, 0xfa, 0x85, 0x35,
        0xaa, 0x2a, 0x88, 0xb2, 0xd4, 0x1f, 0x2a, 0x0e,
        0x2f, 0xda, 0x76, 0x24, 0xc2, 0x85, 0x02, 0x72,
        0xac, 0x4a, 0x2f, 0x56, 0x1f, 0x8f, 0x2f, 0x7a,
        0x31, 0x8b, 0xfd, 0x5c, 0xaf, 0x96, 0x96, 0x14,
        0x9e, 0x4a, 0xc8, 0x24, 0xad, 0x34, 0x60, 0x53,
        0x8f, 0xdc, 0x25, 0x42, 0x1b, 0xee, 0xc2, 0xcc,
        0x68, 0x18, 0x16, 0x2d, 0x06, 0xbb, 0xed, 0x0c,
        0x40, 0xa3, 0x87, 0x19, 0x23, 0x49, 0xdb, 0x67,
        0xa1, 0x18, 0xba, 0xda, 0x6c, 0xd5, 0xab, 0x01,
        0x40, 0xee, 0x27, 0x32, 0x04, 0xf6, 0x28, 0xaa,
        0xd1, 0xc1, 0x35, 0xf7, 0x70, 0x27, 0x9a, 0x65,
        0x1e, 0x24, 0xd8, 0xc1, 0x4d, 0x75, 0xa6, 0x05,
        0x9d, 0x76, 0xb9, 0x6a, 0x6f, 0xd8, 0x57, 0xde,
        0xf5, 0xe0, 0xb3, 0x54, 0xb2, 0x7a, 0xb9, 0x37,
        0xa5, 0x81, 0x5d, 0x16, 0xb5, 0xfa, 0xe4, 0x07,
        0xff, 0x18, 0x22, 0x2c, 0x6d, 0x1e, 0xd2, 0x63,
        0xbe, 0x68, 0xc9, 0x5f, 0x32, 0xd9, 0x08, 0xbd,
        0x89, 0x5c, 0xd7, 0x62, 0x07, 0xae, 0x72, 0x64,
        0x87, 0x56, 0x7f, 0x9a, 0x67, 0xda, 0xd7, 0x9a,
        0xbe, 0xc3, 0x16, 0xf6, 0x83, 0xb1, 0x7f, 0x2d,
        0x02, 0xbf, 0x07, 0xe0, 0xac, 0x8b, 0x5b, 0xc6,
        0x16, 0x2c, 0xf9, 0x46, 0x97, 0xb3, 0xc2, 0x7c,
        0xd1, 0xfe, 0xa4, 0x9b, 0x27, 0xf2, 0x3b, 0xa2,
        0x90, 0x18, 0x71, 0x96, 0x25, 0x06, 0x52, 0x0c,
        0x39, 0x2d, 0xa8, 0xb6, 0xad, 0x0d, 0x99, 0xf7,
        0x01, 0x3f, 0xbc, 0x06, 0xc2, 0xc1, 0x7a, 0x56,
        0x95, 0x00, 0xc8, 0xa7, 0x69, 0x64, 0x81, 0xc1,
        0xcd, 0x33, 0xe9, 0xb1, 0x4e, 0x40, 0xb8, 0x2e,
        0x79, 0xa5, 0xf5, 0xdb, 0x82, 0x57, 0x1b, 0xa9,
        0x7b, 0xae, 0x3a, 0xd3, 0xe0, 0x47, 0x95, 0x15,
        0xbb, 0x0e, 0x2b, 0x0f, 0x3b, 0xfc, 0xd1, 0xfd,
        0x33, 0x03, 0x4e, 0xfc, 0x62, 0x45, 0xed, 0xdd,
        0x7e, 0xe2, 0x08, 0x6d, 0xda, 0xe2, 0x60, 0x0d,
        0x8c, 0xa7, 0x3e, 0x21, 0x4e, 0x8c, 0x2b, 0x0b,
        0xdb, 0x2b, 0x04, 0x7c, 0x6a, 0x46, 0x4a, 0x56,
        0x2e, 0xd7, 0x7b, 0x73, 0xd2, 0xd8, 0x41, 0xc4,
        0xb3, 0x49, 0x73, 0x55, 0x12, 0x57, 0x71, 0x3b,
        0x75, 0x36, 0x32, 0xef, 0xba, 0x34, 0x81, 0x69,
        0xab, 0xc9, 0x0a, 0x68, 0xf4, 0x26, 0x11, 0xa4,
        0x01, 0x26, 0xd7, 0xcb, 0x21, 0xb5, 0x86, 0x95,
        0x56, 0x81, 0x86, 0xf7, 0xe5, 0x69, 0xd2, 0xff,
        0x0f, 0x9e, 0x74, 0x5d, 0x04, 0x87, 0xdd, 0x2e,
        0xb9, 0x97, 0xca, 0xfc, 0x5a, 0xbf, 0x9d, 0xd1,
        0x02, 0xe6, 0x2f, 0xf6, 0x6c, 0xba, 0x87
    };

    static const byte* msgs[] =   {msg1, msg2, msg3, msg1, msg1, msg4};
    static const word16 msgSz[] = {0 /*sizeof(msg1)*/,
                                   sizeof(msg2),
                                   sizeof(msg3),
                                   0 /*sizeof(msg1)*/,
                                   0 /*sizeof(msg1)*/,
                                   sizeof(msg4)
    };
#ifndef NO_ASN
    static byte privateEd448[] = {
        0x30, 0x47, 0x02, 0x01, 0x00, 0x30, 0x05, 0x06,
        0x03, 0x2b, 0x65, 0x71, 0x04, 0x3b, 0x04, 0x39,
        0x6c, 0x82, 0xa5, 0x62, 0xcb, 0x80, 0x8d, 0x10,
        0xd6, 0x32, 0xbe, 0x89, 0xc8, 0x51, 0x3e, 0xbf,
        0x6c, 0x92, 0x9f, 0x34, 0xdd, 0xfa, 0x8c, 0x9f,
        0x63, 0xc9, 0x96, 0x0e, 0xf6, 0xe3, 0x48, 0xa3,
        0x52, 0x8c, 0x8a, 0x3f, 0xcc, 0x2f, 0x04, 0x4e,
        0x39, 0xa3, 0xfc, 0x5b, 0x94, 0x49, 0x2f, 0x8f,
        0x03, 0x2e, 0x75, 0x49, 0xa2, 0x00, 0x98, 0xf9,
        0x5b
    };
    static byte publicEd448[] = {
        0x30, 0x43, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65,
        0x71, 0x03, 0x3a, 0x00, 0x5f, 0xd7, 0x44, 0x9b,
        0x59, 0xb4, 0x61, 0xfd, 0x2c, 0xe7, 0x87, 0xec,
        0x61, 0x6a, 0xd4, 0x6a, 0x1d, 0xa1, 0x34, 0x24,
        0x85, 0xa7, 0x0e, 0x1f, 0x8a, 0x0e, 0xa7, 0x5d,
        0x80, 0xe9, 0x67, 0x78, 0xed, 0xf1, 0x24, 0x76,
        0x9b, 0x46, 0xc7, 0x06, 0x1b, 0xd6, 0x78, 0x3d,
        0xf1, 0xe5, 0x0f, 0x6c, 0xd1, 0xfa, 0x1a, 0xbe,
        0xaf, 0xe8, 0x25, 0x61, 0x80
    };
    static byte privPubEd448[] = {
        0x30, 0x81, 0x84, 0x02, 0x01, 0x00, 0x30, 0x05,
        0x06, 0x03, 0x2b, 0x65, 0x71, 0x04, 0x3b, 0x04,
        0x39, 0x6c, 0x82, 0xa5, 0x62, 0xcb, 0x80, 0x8d,
        0x10, 0xd6, 0x32, 0xbe, 0x89, 0xc8, 0x51, 0x3e,
        0xbf, 0x6c, 0x92, 0x9f, 0x34, 0xdd, 0xfa, 0x8c,
        0x9f, 0x63, 0xc9, 0x96, 0x0e, 0xf6, 0xe3, 0x48,
        0xa3, 0x52, 0x8c, 0x8a, 0x3f, 0xcc, 0x2f, 0x04,
        0x4e, 0x39, 0xa3, 0xfc, 0x5b, 0x94, 0x49, 0x2f,
        0x8f, 0x03, 0x2e, 0x75, 0x49, 0xa2, 0x00, 0x98,
        0xf9, 0x5b, 0xa1, 0x3b, 0x04, 0x39, 0x5f, 0xd7,
        0x44, 0x9b, 0x59, 0xb4, 0x61, 0xfd, 0x2c, 0xe7,
        0x87, 0xec, 0x61, 0x6a, 0xd4, 0x6a, 0x1d, 0xa1,
        0x34, 0x24, 0x85, 0xa7, 0x0e, 0x1f, 0x8a, 0x0e,
        0xa7, 0x5d, 0x80, 0xe9, 0x67, 0x78, 0xed, 0xf1,
        0x24, 0x76, 0x9b, 0x46, 0xc7, 0x06, 0x1b, 0xd6,
        0x78, 0x3d, 0xf1, 0xe5, 0x0f, 0x6c, 0xd1, 0xfa,
        0x1a, 0xbe, 0xaf, 0xe8, 0x25, 0x61, 0x80
    };

    word32 idx;
    ed448_key key3;
#endif /* NO_ASN */
#endif /* HAVE_ED448_SIGN && HAVE_ED448_KEY_EXPORT && HAVE_ED448_KEY_IMPORT */

    /* create ed448 keys */
#ifndef HAVE_FIPS
    ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
    ret = wc_InitRng(&rng);
#endif
    if (ret != 0)
        return -11300;

    wc_ed448_init(&key);
    wc_ed448_init(&key2);
#ifndef NO_ASN
    wc_ed448_init(&key3);
#endif
    wc_ed448_make_key(&rng, ED448_KEY_SIZE, &key);
    wc_ed448_make_key(&rng, ED448_KEY_SIZE, &key2);

    /* helper functions for signature and key size */
    keySz = wc_ed448_size(&key);
    sigSz = wc_ed448_sig_size(&key);

#if defined(HAVE_ED448_SIGN) && defined(HAVE_ED448_KEY_EXPORT) &&\
        defined(HAVE_ED448_KEY_IMPORT)
    for (i = 0; i < 6; i++) {
        outlen = sizeof(out);
        XMEMSET(out, 0, sizeof(out));

        if (wc_ed448_import_private_key(sKeys[i], ED448_KEY_SIZE, pKeys[i],
                pKeySz[i], &key) != 0)
            return -11301 - i;

        if (wc_ed448_sign_msg(msgs[i], msgSz[i], out, &outlen, &key, NULL,
                                                                      0) != 0) {
            return -11311 - i;
        }

        if (XMEMCMP(out, sigs[i], 114))
            return -11321 - i;

#if defined(HAVE_ED448_VERIFY)
        /* test verify on good msg */
        if (wc_ed448_verify_msg(out, outlen, msgs[i], msgSz[i], &verify, &key,
                                                 NULL, 0) != 0 || verify != 1) {
            return -11331 - i;
        }

        /* test verify on bad msg */
        out[outlen-2] = out[outlen-2] + 1;
        if (wc_ed448_verify_msg(out, outlen, msgs[i], msgSz[i], &verify, &key,
                                                 NULL, 0) == 0 || verify == 1) {
            return -11341 - i;
        }
#endif /* HAVE_ED448_VERIFY */

        /* test api for import/exporting keys */
        exportPSz = sizeof(exportPKey);
        exportSSz = sizeof(exportSKey);
        if (wc_ed448_export_public(&key, exportPKey, &exportPSz) != 0)
            return -11351 - i;

        if (wc_ed448_import_public(exportPKey, exportPSz, &key2) != 0)
            return -11361 - i;

        if (wc_ed448_export_private_only(&key, exportSKey, &exportSSz) != 0)
            return -11371 - i;

        if (wc_ed448_import_private_key(exportSKey, exportSSz,
                                        exportPKey, exportPSz, &key2) != 0)
            return -11381 - i;

        /* clear "out" buffer and test sign with imported keys */
        outlen = sizeof(out);
        XMEMSET(out, 0, sizeof(out));
        if (wc_ed448_sign_msg(msgs[i], msgSz[i], out, &outlen, &key2, NULL,
                                                                      0) != 0) {
            return -11391 - i;
        }

#if defined(HAVE_ED448_VERIFY)
        if (wc_ed448_verify_msg(out, outlen, msgs[i], msgSz[i], &verify, &key2,
                                NULL, 0) != 0 || verify != 1)
            return -11401 - i;

        if (XMEMCMP(out, sigs[i], SIGSZ))
            return -11411 - i;
#endif /* HAVE_ED448_VERIFY */
    }

    ret = ed448_ctx_test();
    if (ret != 0)
        return ret;

    ret = ed448ph_test();
    if (ret != 0)
        return ret;

#ifndef NO_ASN
    /* Try ASN.1 encoded private-only key and public key. */
    idx = 0;
    if (wc_Ed448PrivateKeyDecode(privateEd448, &idx, &key3,
                                 sizeof(privateEd448)) != 0)
        return -11421 - i;

    if (wc_ed448_sign_msg(msgs[0], msgSz[0], out, &outlen, &key3, NULL, 0)
                != BAD_FUNC_ARG)
        return -11431 - i;

    idx = 0;
    if (wc_Ed448PublicKeyDecode(publicEd448, &idx, &key3,
                                sizeof(publicEd448)) != 0)
        return -11441 - i;

    if (wc_ed448_sign_msg(msgs[0], msgSz[0], out, &outlen, &key3, NULL, 0) != 0)
        return -11451 - i;

    if (XMEMCMP(out, sigs[0], SIGSZ))
        return -11461 - i;

#if defined(HAVE_ED448_VERIFY)
    /* test verify on good msg */
    if (wc_ed448_verify_msg(out, outlen, msgs[0], msgSz[0], &verify, &key3,
                NULL, 0) != 0 || verify != 1)
        return -11471 - i;
#endif /* HAVE_ED448_VERIFY */

    wc_ed448_free(&key3);
    wc_ed448_init(&key3);

    idx = 0;
    if (wc_Ed448PrivateKeyDecode(privPubEd448, &idx, &key3,
                                 sizeof(privPubEd448)) != 0)
        return -11481 - i;

    if (wc_ed448_sign_msg(msgs[0], msgSz[0], out, &outlen, &key3, NULL, 0) != 0)
        return -11491 - i;

    if (XMEMCMP(out, sigs[0], SIGSZ))
        return -11501 - i;

    wc_ed448_free(&key3);
#endif /* NO_ASN */
#endif /* HAVE_ED448_SIGN && HAVE_ED448_KEY_EXPORT && HAVE_ED448_KEY_IMPORT */

    /* clean up keys when done */
    wc_ed448_free(&key);
    wc_ed448_free(&key2);

#if defined(HAVE_HASHDRBG) || defined(NO_RC4)
    wc_FreeRng(&rng);
#endif

    /* hush warnings of unused keySz and sigSz */
    (void)keySz;
    (void)sigSz;

#ifdef WOLFSSL_TEST_CERT
    ret = ed448_test_cert();
    if (ret < 0)
        return ret;
#ifdef WOLFSSL_CERT_GEN
    ret = ed448_test_make_cert();
    if (ret < 0)
        return ret;
#endif /* WOLFSSL_CERT_GEN */
#endif /* WOLFSSL_TEST_CERT */

    return 0;
}
#endif /* HAVE_ED448 */

#if defined(WOLFSSL_CMAC) && !defined(NO_AES)

typedef struct CMAC_Test_Case {
    int type;
    int partial;
    const byte* m;
    word32 mSz;
    const byte* k;
    word32 kSz;
    const byte* t;
    word32 tSz;
} CMAC_Test_Case;

int cmac_test(void)
{
#ifdef WOLFSSL_AES_128
    const byte k128[] =
    {
        0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
        0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c
    };
    #define KLEN_128 (sizeof(k128))
#endif
#ifdef WOLFSSL_AES_192
    const byte k192[] =
    {
        0x8e, 0x73, 0xb0, 0xf7, 0xda, 0x0e, 0x64, 0x52,
        0xc8, 0x10, 0xf3, 0x2b, 0x80, 0x90, 0x79, 0xe5,
        0x62, 0xf8, 0xea, 0xd2, 0x52, 0x2c, 0x6b, 0x7b
    };
    #define KLEN_192 (sizeof(k192))
#endif
#ifdef WOLFSSL_AES_256
    const byte k256[] =
    {
        0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe,
        0x2b, 0x73, 0xae, 0xf0, 0x85, 0x7d, 0x77, 0x81,
        0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61, 0x08, 0xd7,
        0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4
    };
    #define KLEN_256 (sizeof(k256))
#endif

    const byte m[] =
    {
        0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
        0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
        0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03, 0xac, 0x9c,
        0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51,
        0x30, 0xc8, 0x1c, 0x46, 0xa3, 0x5c, 0xe4, 0x11,
        0xe5, 0xfb, 0xc1, 0x19, 0x1a, 0x0a, 0x52, 0xef,
        0xf6, 0x9f, 0x24, 0x45, 0xdf, 0x4f, 0x9b, 0x17,
        0xad, 0x2b, 0x41, 0x7b, 0xe6, 0x6c, 0x37, 0x10
    };
    #define MLEN_0 (0)
    #define MLEN_128 (128/8)
    #define MLEN_320 (320/8)
    #define MLEN_319 (MLEN_320 - 1)
    #define MLEN_512 (512/8)

#ifdef WOLFSSL_AES_128
    const byte t128_0[] =
    {
        0xbb, 0x1d, 0x69, 0x29, 0xe9, 0x59, 0x37, 0x28,
        0x7f, 0xa3, 0x7d, 0x12, 0x9b, 0x75, 0x67, 0x46
    };
    const byte t128_128[] =
    {
        0x07, 0x0a, 0x16, 0xb4, 0x6b, 0x4d, 0x41, 0x44,
        0xf7, 0x9b, 0xdd, 0x9d, 0xd0, 0x4a, 0x28, 0x7c
    };
    const byte t128_319[] =
    {
        0x2c, 0x17, 0x84, 0x4c, 0x93, 0x1c, 0x07, 0x95,
        0x15, 0x92, 0x73, 0x0a, 0x34, 0xd0, 0xd9, 0xd2
    };
    const byte t128_320[] =
    {
        0xdf, 0xa6, 0x67, 0x47, 0xde, 0x9a, 0xe6, 0x30,
        0x30, 0xca, 0x32, 0x61, 0x14, 0x97, 0xc8, 0x27
    };
    const byte t128_512[] =
    {
        0x51, 0xf0, 0xbe, 0xbf, 0x7e, 0x3b, 0x9d, 0x92,
        0xfc, 0x49, 0x74, 0x17, 0x79, 0x36, 0x3c, 0xfe
    };
#endif
#ifdef WOLFSSL_AES_192
    const byte t192_0[] =
    {
        0xd1, 0x7d, 0xdf, 0x46, 0xad, 0xaa, 0xcd, 0xe5,
        0x31, 0xca, 0xc4, 0x83, 0xde, 0x7a, 0x93, 0x67
    };
    const byte t192_128[] =
    {
        0x9e, 0x99, 0xa7, 0xbf, 0x31, 0xe7, 0x10, 0x90,
        0x06, 0x62, 0xf6, 0x5e, 0x61, 0x7c, 0x51, 0x84
    };
    const byte t192_320[] =
    {
        0x8a, 0x1d, 0xe5, 0xbe, 0x2e, 0xb3, 0x1a, 0xad,
        0x08, 0x9a, 0x82, 0xe6, 0xee, 0x90, 0x8b, 0x0e
    };
    const byte t192_512[] =
    {
        0xa1, 0xd5, 0xdf, 0x0e, 0xed, 0x79, 0x0f, 0x79,
        0x4d, 0x77, 0x58, 0x96, 0x59, 0xf3, 0x9a, 0x11
    };
#endif
#ifdef WOLFSSL_AES_256
    const byte t256_0[] =
    {
        0x02, 0x89, 0x62, 0xf6, 0x1b, 0x7b, 0xf8, 0x9e,
        0xfc, 0x6b, 0x55, 0x1f, 0x46, 0x67, 0xd9, 0x83
    };
    const byte t256_128[] =
    {
        0x28, 0xa7, 0x02, 0x3f, 0x45, 0x2e, 0x8f, 0x82,
        0xbd, 0x4b, 0xf2, 0x8d, 0x8c, 0x37, 0xc3, 0x5c
    };
    const byte t256_320[] =
    {
        0xaa, 0xf3, 0xd8, 0xf1, 0xde, 0x56, 0x40, 0xc2,
        0x32, 0xf5, 0xb1, 0x69, 0xb9, 0xc9, 0x11, 0xe6
    };
    const byte t256_512[] =
    {
        0xe1, 0x99, 0x21, 0x90, 0x54, 0x9f, 0x6e, 0xd5,
        0x69, 0x6a, 0x2c, 0x05, 0x6c, 0x31, 0x54, 0x10
    };
#endif
    const CMAC_Test_Case testCases[] =
    {
#ifdef WOLFSSL_AES_128
        {WC_CMAC_AES, 0, m, MLEN_0, k128, KLEN_128, t128_0, AES_BLOCK_SIZE},
        {WC_CMAC_AES, 0, m, MLEN_128, k128, KLEN_128, t128_128, AES_BLOCK_SIZE},
        {WC_CMAC_AES, 0, m, MLEN_320, k128, KLEN_128, t128_320, AES_BLOCK_SIZE},
        {WC_CMAC_AES, 0, m, MLEN_512, k128, KLEN_128, t128_512, AES_BLOCK_SIZE},
        {WC_CMAC_AES, 5, m, MLEN_512, k128, KLEN_128, t128_512, AES_BLOCK_SIZE},
#endif
#ifdef WOLFSSL_AES_192
        {WC_CMAC_AES, 0, m, MLEN_0, k192, KLEN_192, t192_0, AES_BLOCK_SIZE},
        {WC_CMAC_AES, 0, m, MLEN_128, k192, KLEN_192, t192_128, AES_BLOCK_SIZE},
        {WC_CMAC_AES, 0, m, MLEN_320, k192, KLEN_192, t192_320, AES_BLOCK_SIZE},
        {WC_CMAC_AES, 0, m, MLEN_512, k192, KLEN_192, t192_512, AES_BLOCK_SIZE},
#endif
#ifdef WOLFSSL_AES_256
        {WC_CMAC_AES, 0, m, MLEN_0, k256, KLEN_256, t256_0, AES_BLOCK_SIZE},
        {WC_CMAC_AES, 0, m, MLEN_128, k256, KLEN_256, t256_128, AES_BLOCK_SIZE},
        {WC_CMAC_AES, 0, m, MLEN_320, k256, KLEN_256, t256_320, AES_BLOCK_SIZE},
        {WC_CMAC_AES, 0, m, MLEN_512, k256, KLEN_256, t256_512, AES_BLOCK_SIZE},
#endif
#ifdef WOLFSSL_AES_128
        {WC_CMAC_AES, 0, m, MLEN_319, k128, KLEN_128, t128_319, AES_BLOCK_SIZE}
#endif
    };

    Cmac cmac;
    byte tag[AES_BLOCK_SIZE];
    const CMAC_Test_Case* tc;
    word32 i, tagSz;

    for (i = 0, tc = testCases;
         i < sizeof(testCases)/sizeof(CMAC_Test_Case);
         i++, tc++) {

        XMEMSET(tag, 0, sizeof(tag));
        tagSz = AES_BLOCK_SIZE;
        if (wc_InitCmac(&cmac, tc->k, tc->kSz, tc->type, NULL) != 0)
            return -11600;
        if (tc->partial) {
            if (wc_CmacUpdate(&cmac, tc->m,
                                 tc->mSz/2 - tc->partial) != 0)
                return -11601;
            if (wc_CmacUpdate(&cmac, tc->m + tc->mSz/2 - tc->partial,
                                 tc->mSz/2 + tc->partial) != 0)
                return -11602;
        }
        else {
            if (wc_CmacUpdate(&cmac, tc->m, tc->mSz) != 0)
                return -11603;
        }
        if (wc_CmacFinal(&cmac, tag, &tagSz) != 0)
            return -11604;
        if (XMEMCMP(tag, tc->t, AES_BLOCK_SIZE) != 0)
            return -11605;

        XMEMSET(tag, 0, sizeof(tag));
        tagSz = sizeof(tag);
        if (wc_AesCmacGenerate(tag, &tagSz, tc->m, tc->mSz,
                               tc->k, tc->kSz) != 0)
            return -11606;
        if (XMEMCMP(tag, tc->t, AES_BLOCK_SIZE) != 0)
            return -11607;
        if (wc_AesCmacVerify(tc->t, tc->tSz, tc->m, tc->mSz,
                             tc->k, tc->kSz) != 0)
            return -11608;
    }

    return 0;
}

#endif /* NO_AES && WOLFSSL_CMAC */

#ifdef HAVE_LIBZ

const byte sample_text[] =
    "Biodiesel cupidatat marfa, cliche aute put a bird on it incididunt elit\n"
    "polaroid. Sunt tattooed bespoke reprehenderit. Sint twee organic id\n"
    "marfa. Commodo veniam ad esse gastropub. 3 wolf moon sartorial vero,\n"
    "plaid delectus biodiesel squid +1 vice. Post-ironic keffiyeh leggings\n"
    "selfies cray fap hoodie, forage anim. Carles cupidatat shoreditch, VHS\n"
    "small batch meggings kogi dolore food truck bespoke gastropub.\n"
    "\n"
    "Terry richardson adipisicing actually typewriter tumblr, twee whatever\n"
    "four loko you probably haven't heard of them high life. Messenger bag\n"
    "whatever tattooed deep v mlkshk. Brooklyn pinterest assumenda chillwave\n"
    "et, banksy ullamco messenger bag umami pariatur direct trade forage.\n"
    "Typewriter culpa try-hard, pariatur sint brooklyn meggings. Gentrify\n"
    "food truck next level, tousled irony non semiotics PBR ethical anim cred\n"
    "readymade. Mumblecore brunch lomo odd future, portland organic terry\n"
    "richardson elit leggings adipisicing ennui raw denim banjo hella. Godard\n"
    "mixtape polaroid, pork belly readymade organic cray typewriter helvetica\n"
    "four loko whatever street art yr farm-to-table.\n"
    "\n"
    "Vinyl keytar vice tofu. Locavore you probably haven't heard of them pug\n"
    "pickled, hella tonx labore truffaut DIY mlkshk elit cosby sweater sint\n"
    "et mumblecore. Elit swag semiotics, reprehenderit DIY sartorial nisi ugh\n"
    "nesciunt pug pork belly wayfarers selfies delectus. Ethical hoodie\n"
    "seitan fingerstache kale chips. Terry richardson artisan williamsburg,\n"
    "eiusmod fanny pack irony tonx ennui lo-fi incididunt tofu YOLO\n"
    "readymade. 8-bit sed ethnic beard officia. Pour-over iphone DIY butcher,\n"
    "ethnic art party qui letterpress nisi proident jean shorts mlkshk\n"
    "locavore.\n"
    "\n"
    "Narwhal flexitarian letterpress, do gluten-free voluptate next level\n"
    "banh mi tonx incididunt carles DIY. Odd future nulla 8-bit beard ut\n"
    "cillum pickled velit, YOLO officia you probably haven't heard of them\n"
    "trust fund gastropub. Nisi adipisicing tattooed, Austin mlkshk 90's\n"
    "small batch american apparel. Put a bird on it cosby sweater before they\n"
    "sold out pork belly kogi hella. Street art mollit sustainable polaroid,\n"
    "DIY ethnic ea pug beard dreamcatcher cosby sweater magna scenester nisi.\n"
    "Sed pork belly skateboard mollit, labore proident eiusmod. Sriracha\n"
    "excepteur cosby sweater, anim deserunt laborum eu aliquip ethical et\n"
    "neutra PBR selvage.\n"
    "\n"
    "Raw denim pork belly truffaut, irony plaid sustainable put a bird on it\n"
    "next level jean shorts exercitation. Hashtag keytar whatever, nihil\n"
    "authentic aliquip disrupt laborum. Tattooed selfies deserunt trust fund\n"
    "wayfarers. 3 wolf moon synth church-key sartorial, gastropub leggings\n"
    "tattooed. Labore high life commodo, meggings raw denim fingerstache pug\n"
    "trust fund leggings seitan forage. Nostrud ullamco duis, reprehenderit\n"
    "incididunt flannel sustainable helvetica pork belly pug banksy you\n"
    "probably haven't heard of them nesciunt farm-to-table. Disrupt nostrud\n"
    "mollit magna, sriracha sartorial helvetica.\n"
    "\n"
    "Nulla kogi reprehenderit, skateboard sustainable duis adipisicing viral\n"
    "ad fanny pack salvia. Fanny pack trust fund you probably haven't heard\n"
    "of them YOLO vice nihil. Keffiyeh cray lo-fi pinterest cardigan aliqua,\n"
    "reprehenderit aute. Culpa tousled williamsburg, marfa lomo actually anim\n"
    "skateboard. Iphone aliqua ugh, semiotics pariatur vero readymade\n"
    "organic. Marfa squid nulla, in laborum disrupt laboris irure gastropub.\n"
    "Veniam sunt food truck leggings, sint vinyl fap.\n"
    "\n"
    "Hella dolore pork belly, truffaut carles you probably haven't heard of\n"
    "them PBR helvetica in sapiente. Fashion axe ugh bushwick american\n"
    "apparel. Fingerstache sed iphone, jean shorts blue bottle nisi bushwick\n"
    "flexitarian officia veniam plaid bespoke fap YOLO lo-fi. Blog\n"
    "letterpress mumblecore, food truck id cray brooklyn cillum ad sed.\n"
    "Assumenda chambray wayfarers vinyl mixtape sustainable. VHS vinyl\n"
    "delectus, culpa williamsburg polaroid cliche swag church-key synth kogi\n"
    "magna pop-up literally. Swag thundercats ennui shoreditch vegan\n"
    "pitchfork neutra truffaut etsy, sed single-origin coffee craft beer.\n"
    "\n"
    "Odio letterpress brooklyn elit. Nulla single-origin coffee in occaecat\n"
    "meggings. Irony meggings 8-bit, chillwave lo-fi adipisicing cred\n"
    "dreamcatcher veniam. Put a bird on it irony umami, trust fund bushwick\n"
    "locavore kale chips. Sriracha swag thundercats, chillwave disrupt\n"
    "tousled beard mollit mustache leggings portland next level. Nihil esse\n"
    "est, skateboard art party etsy thundercats sed dreamcatcher ut iphone\n"
    "swag consectetur et. Irure skateboard banjo, nulla deserunt messenger\n"
    "bag dolor terry richardson sapiente.\n";

const byte sample_text_gz[] = {
    0x1F, 0x8B, 0x08, 0x08, 0xC5, 0x49, 0xB5, 0x5B, 0x00, 0x03, 0x63, 0x69, 0x70,
    0x68, 0x65, 0x72, 0x74, 0x65, 0x78, 0x74, 0x2E, 0x74, 0x78, 0x74, 0x00, 0x8D,
    0x58, 0xCB, 0x92, 0xE4, 0xB6, 0x11, 0xBC, 0xE3, 0x2B, 0xEA, 0xA6, 0x83, 0xD9,
    0x1D, 0x72, 0xF8, 0x22, 0x1F, 0xB5, 0x96, 0xA5, 0xDD, 0x90, 0xBC, 0xAB, 0xD0,
    0x28, 0x36, 0x42, 0x47, 0x90, 0x2C, 0x36, 0xA1, 0x06, 0x09, 0x0A, 0x8F, 0xEE,
    0xE1, 0xDF, 0x3B, 0x0B, 0xE0, 0x73, 0x2C, 0x4B, 0xBA, 0xCD, 0xCE, 0x80, 0x78,
    0x64, 0x65, 0x65, 0x66, 0xED, 0x3B, 0xE3, 0x5A, 0xC3, 0x81, 0x2D, 0x35, 0x69,
    0x32, 0xAD, 0x8E, 0x3A, 0xD2, 0xA0, 0x7D, 0xA7, 0x2B, 0x6A, 0xAC, 0x69, 0x7A,
    0x26, 0x9D, 0x22, 0xD3, 0x94, 0x22, 0x69, 0xAA, 0x8D, 0x6F, 0xC9, 0x8D, 0x64,
    0x22, 0x99, 0xB1, 0x31, 0xAD, 0x69, 0xD3, 0x18, 0x89, 0xAD, 0x89, 0x6A, 0x72,
    0x56, 0x7B, 0x67, 0xDA, 0x2B, 0xBD, 0xC8, 0xEF, 0xB0, 0x4D, 0x74, 0x8E, 0x5B,
    0xAA, 0x39, 0x4C, 0xEE, 0xCE, 0xE4, 0x79, 0xF2, 0xDC, 0xF3, 0xD8, 0xB2, 0x37,
    0x11, 0x8B, 0x8C, 0x2C, 0x7A, 0x32, 0x93, 0xF3, 0x37, 0x3D, 0x9A, 0x86, 0x4C,
    0xAB, 0xF2, 0xB9, 0x57, 0xFA, 0x97, 0x1B, 0x06, 0xD7, 0x3A, 0x7A, 0xF0, 0x68,
    0xF4, 0x40, 0xBA, 0x25, 0x0E, 0x81, 0xE9, 0xA6, 0x43, 0xF4, 0x6E, 0x4A, 0xF5,
    0x95, 0xFE, 0x41, 0x4F, 0x67, 0x3B, 0x1A, 0x1C, 0xEE, 0x12, 0xB4, 0x8F, 0xCE,
    0x1B, 0x6D, 0xB1, 0xDE, 0xBB, 0x4A, 0x4D, 0x56, 0x9B, 0x96, 0x5A, 0xB6, 0xDC,
    0xC4, 0x14, 0x70, 0xE5, 0xF5, 0x7D, 0xE1, 0xB7, 0x84, 0x3F, 0xFC, 0xED, 0xEF,
    0xF4, 0x30, 0x0D, 0x5F, 0xE9, 0x47, 0x17, 0xE2, 0xC5, 0x78, 0x27, 0x67, 0xDF,
    0xB9, 0xEB, 0xCC, 0xCC, 0x3D, 0x59, 0xBE, 0xDD, 0xCC, 0x78, 0x0B, 0x0A, 0x1F,
    0x74, 0xF8, 0x8C, 0x1A, 0xAF, 0x67, 0xEA, 0xF4, 0x44, 0xBD, 0x93, 0x7D, 0x2A,
    0xEA, 0x9C, 0xD7, 0x37, 0x80, 0x32, 0x9A, 0x01, 0x37, 0xD5, 0xDE, 0xCA, 0xA2,
    0x0D, 0xB9, 0xD0, 0x3B, 0xCF, 0xAD, 0x89, 0x4D, 0x5F, 0xD1, 0xE7, 0xF7, 0x2F,
    0x2A, 0x0C, 0xDA, 0x5A, 0xAA, 0x35, 0x7E, 0x41, 0xC3, 0xB2, 0x37, 0xDD, 0xDD,
    0xCD, 0x50, 0xEB, 0x2C, 0x96, 0x62, 0x3B, 0xD7, 0x52, 0xF4, 0xA9, 0xB9, 0x6F,
    0x48, 0xED, 0xEF, 0x54, 0xEA, 0x67, 0xF6, 0x7E, 0x26, 0x8F, 0x3A, 0x68, 0xDF,
    0x06, 0xBC, 0x56, 0xB7, 0x66, 0x32, 0xC1, 0x34, 0xD8, 0x88, 0x34, 0x1E, 0x88,
    0xED, 0x67, 0x8A, 0xF3, 0xC4, 0x4F, 0xC0, 0xCA, 0x9E, 0x62, 0x1A, 0x6A, 0xEB,
    0xAB, 0x02, 0xED, 0xB3, 0xD7, 0x91, 0x81, 0x8A, 0xEA, 0x5C, 0xF2, 0x64, 0xDD,
    0xDD, 0xD1, 0xEC, 0x12, 0x4D, 0xDE, 0xD5, 0xBA, 0xC6, 0x77, 0xBD, 0x06, 0xC4,
    0x5F, 0x44, 0xEA, 0x59, 0x4B, 0x5D, 0x3B, 0x8A, 0x3D, 0x0F, 0xD4, 0x9B, 0x1B,
    0x80, 0x30, 0x1D, 0x30, 0xFA, 0x8F, 0x00, 0x3F, 0xDE, 0xB0, 0x6F, 0xAD, 0x6F,
    0x6A, 0xDD, 0x6E, 0x2F, 0x6E, 0xCB, 0x3C, 0xD1, 0x83, 0x06, 0x7B, 0x0F, 0xFD,
    0xFD, 0x4A, 0xEF, 0xBC, 0x73, 0x77, 0x3B, 0x8F, 0x34, 0xA1, 0xBA, 0xEC, 0x39,
    0x80, 0x33, 0x21, 0xA4, 0x01, 0x55, 0xD7, 0xD4, 0xF4, 0xC6, 0xDA, 0x27, 0x4E,
    0x54, 0x1C, 0x2B, 0xEC, 0x37, 0xDE, 0xC3, 0x4C, 0xC9, 0x5A, 0x3D, 0x34, 0x0E,
    0xD8, 0x1C, 0x0E, 0xA2, 0x34, 0xE8, 0xC1, 0xD0, 0xA4, 0x51, 0xD5, 0x88, 0x8B,
    0xB7, 0xC6, 0xA3, 0x96, 0x40, 0x49, 0xB7, 0xBC, 0xE0, 0x7F, 0x55, 0x3F, 0xEF,
    0x6F, 0x6E, 0x92, 0x9D, 0x34, 0xFE, 0x3C, 0x5F, 0x04, 0xA5, 0x6A, 0xFF, 0x30,
    0x08, 0xC9, 0xEA, 0xF5, 0x52, 0x2B, 0xFE, 0x57, 0xFA, 0x8E, 0xC7, 0xE8, 0x4D,
    0x37, 0xAB, 0x03, 0xFA, 0x23, 0xBF, 0x46, 0x94, 0xFF, 0xC1, 0x16, 0xE0, 0xB9,
    0x14, 0x2C, 0x9E, 0x27, 0xEC, 0x98, 0x69, 0x14, 0x92, 0xF1, 0x60, 0x5C, 0x34,
    0x4D, 0xA0, 0x1F, 0xDF, 0xFD, 0x44, 0x1C, 0x7B, 0xD3, 0x80, 0x70, 0x42, 0x02,
    0x30, 0x84, 0x5B, 0xE5, 0x59, 0xB7, 0xF3, 0x80, 0xFB, 0x01, 0x33, 0xA9, 0x00,
    0x37, 0x52, 0xDC, 0xDA, 0xA7, 0x11, 0x85, 0xB7, 0x6E, 0x70, 0xE4, 0xDA, 0x96,
    0xBA, 0x84, 0x5B, 0x81, 0x43, 0x93, 0xF3, 0xD1, 0xEA, 0xB1, 0xDD, 0xB8, 0x1F,
    0xA5, 0xCC, 0xEA, 0x50, 0x66, 0x69, 0xA9, 0x8D, 0x8C, 0xA7, 0xA2, 0xF3, 0x38,
    0x26, 0x43, 0x5E, 0x3F, 0x01, 0xBE, 0x1C, 0x0F, 0x20, 0x7F, 0x75, 0xA8, 0x20,
    0x80, 0xC4, 0xC3, 0x5C, 0x8B, 0x0D, 0xD4, 0x60, 0x5E, 0xA3, 0x9E, 0xD0, 0xB4,
    0x4B, 0x4F, 0xE6, 0x13, 0x85, 0x60, 0x42, 0x96, 0xED, 0xAA, 0xDB, 0xE9, 0x99,
    0xE3, 0x07, 0x0E, 0x61, 0xB3, 0x07, 0xE3, 0xB1, 0xFA, 0xC0, 0x9B, 0xAD, 0xF6,
    0xE0, 0x26, 0x33, 0xEA, 0xEA, 0x23, 0xCD, 0x1E, 0x9D, 0xE1, 0x87, 0x4B, 0x74,
    0x97, 0x08, 0x3E, 0xA1, 0x28, 0xEA, 0xB3, 0x19, 0x67, 0x8B, 0x76, 0x9A, 0xA3,
    0xF6, 0xB9, 0xCF, 0x80, 0x65, 0x97, 0xAE, 0xF4, 0x83, 0x6B, 0xF4, 0x43, 0x20,
    0xF9, 0x0B, 0xFC, 0x9B, 0xD2, 0x4D, 0x4D, 0xA6, 0xB9, 0xA3, 0x02, 0x55, 0x79,
    0x18, 0x36, 0x19, 0x5F, 0xC9, 0xEA, 0x5A, 0x76, 0x40, 0xB9, 0xBA, 0x0E, 0x9A,
    0x44, 0xDF, 0x7C, 0xF8, 0x65, 0x61, 0x5E, 0x81, 0xAB, 0x71, 0xA1, 0x9E, 0x29,
    0x3C, 0x59, 0xCB, 0x23, 0xA4, 0xF6, 0x60, 0x1A, 0x0D, 0x5B, 0x39, 0xAE, 0xF4,
    0x6F, 0x59, 0x16, 0x9E, 0x60, 0xD8, 0x56, 0xCF, 0xEA, 0x2C, 0x4C, 0x79, 0xD3,
    0x5D, 0x51, 0x46, 0xA0, 0x4E, 0xE9, 0xD6, 0xAB, 0x91, 0x43, 0x63, 0x44, 0xD7,
    0x70, 0xB9, 0x23, 0x98, 0x4F, 0x3D, 0x03, 0x02, 0xF6, 0x81, 0x56, 0xC1, 0x58,
    0x85, 0x07, 0xA7, 0x2D, 0x2C, 0x29, 0xCA, 0x01, 0x45, 0x31, 0x51, 0x8F, 0xD4,
    0x19, 0xA1, 0x79, 0x88, 0x5A, 0xA4, 0xF5, 0xAE, 0x2D, 0x4B, 0x63, 0x4C, 0x58,
    0xFE, 0xBF, 0xAD, 0xEE, 0xA3, 0x09, 0xF8, 0xE2, 0x89, 0xBE, 0x81, 0x0E, 0x86,
    0x3A, 0xF9, 0x5B, 0xA5, 0xD8, 0xA4, 0x00, 0x75, 0x04, 0xF2, 0x23, 0xB8, 0x39,
    0x69, 0x50, 0xB7, 0xD0, 0x34, 0x63, 0x54, 0xD8, 0x61, 0xDD, 0xA5, 0x33, 0x47,
    0x85, 0x96, 0x22, 0xD0, 0x2F, 0x9F, 0x7E, 0xF8, 0x74, 0x24, 0xEA, 0x57, 0x97,
    0x5A, 0xE0, 0x00, 0xCF, 0xC1, 0x67, 0xE1, 0x41, 0xBD, 0x94, 0xA1, 0x03, 0xD3,
    0xB4, 0x08, 0x64, 0xF2, 0x17, 0x27, 0x35, 0x37, 0x53, 0xEF, 0x46, 0xCE, 0xD8,
    0xD4, 0x09, 0x52, 0xC6, 0x1E, 0xF7, 0x28, 0xDF, 0x08, 0x0F, 0xD0, 0x6F, 0x71,
    0xA6, 0xDF, 0xE4, 0x60, 0x8E, 0xC0, 0x1E, 0x78, 0x86, 0x50, 0xB0, 0x9B, 0x84,
    0x7E, 0xE8, 0x36, 0xFA, 0x95, 0xF1, 0x12, 0x51, 0xC7, 0x18, 0x96, 0xA2, 0x29,
    0xBB, 0x70, 0x02, 0xB4, 0xF9, 0xA8, 0x3D, 0x08, 0x66, 0xA9, 0xB3, 0xFC, 0x0A,
    0x94, 0x80, 0xFD, 0x78, 0xDC, 0xAB, 0x82, 0x5A, 0xD2, 0xCD, 0xC2, 0x87, 0xC6,
    0x4B, 0x07, 0xFA, 0xD1, 0xC3, 0xD9, 0x34, 0x41, 0x85, 0xF8, 0xD0, 0xB6, 0x0A,
    0x9D, 0x00, 0x91, 0x35, 0x05, 0x88, 0xC3, 0xE3, 0x9B, 0x22, 0xD2, 0xB8, 0xFD,
    0x95, 0x3E, 0x6D, 0x5D, 0x48, 0xA3, 0x68, 0xCF, 0x02, 0x42, 0x79, 0x79, 0x8A,
    0xAA, 0x01, 0xD6, 0x09, 0x14, 0x2C, 0xF4, 0x83, 0xA3, 0x80, 0x31, 0x55, 0x46,
    0x6E, 0xC5, 0xE5, 0x2F, 0x30, 0x58, 0x81, 0xA2, 0x90, 0xBE, 0x2E, 0xA1, 0xC3,
    0x0F, 0xA6, 0xF5, 0x51, 0x00, 0x39, 0xB6, 0xF2, 0x2A, 0xA3, 0x15, 0x7D, 0x8D,
    0xF5, 0x66, 0x5C, 0xD9, 0xFC, 0xCF, 0x2F, 0xBF, 0x08, 0x27, 0xE7, 0xD0, 0x03,
    0xB8, 0xD9, 0x00, 0x13, 0x3D, 0x01, 0x6B, 0xB6, 0xA8, 0xCD, 0x5B, 0x3B, 0x3E,
    0x93, 0xBF, 0xE6, 0x2E, 0xB7, 0x4A, 0xCF, 0xB3, 0x0A, 0xCE, 0x62, 0x11, 0xD6,
    0x1F, 0x68, 0x9B, 0x1D, 0x68, 0xD1, 0x8C, 0x97, 0xBD, 0xA1, 0x07, 0x67, 0x73,
    0x87, 0xE0, 0x36, 0xDA, 0x8C, 0xD2, 0xD2, 0xBB, 0x84, 0x28, 0xA9, 0xFE, 0x52,
    0x74, 0xD6, 0xB9, 0x0F, 0x0A, 0x6A, 0x2D, 0x28, 0x35, 0x34, 0x3A, 0xD3, 0xE2,
    0xCD, 0x35, 0x06, 0x7D, 0x1B, 0x35, 0x85, 0x86, 0xD1, 0x3E, 0xF2, 0x6F, 0xA1,
    0xC4, 0x55, 0xBD, 0x00, 0xD8, 0xC3, 0x5D, 0xC2, 0x1D, 0x6B, 0x6B, 0x27, 0x5B,
    0x95, 0xF3, 0xAB, 0xB5, 0xD3, 0x37, 0xF2, 0x2C, 0x9C, 0xC7, 0x5D, 0xBD, 0xF1,
    0x68, 0x1C, 0xAD, 0xF8, 0xB5, 0xE1, 0x29, 0x72, 0x7A, 0x73, 0x62, 0x55, 0x24,
    0xB9, 0x85, 0xDF, 0x7B, 0x29, 0x7D, 0xDE, 0x08, 0xF5, 0xE4, 0x44, 0xDA, 0x1A,
    0x30, 0x74, 0xDA, 0xB4, 0x9B, 0x23, 0x9A, 0x3A, 0xC1, 0x53, 0xB2, 0xA2, 0xA3,
    0x7B, 0x1F, 0xD9, 0x56, 0xD4, 0x4F, 0x9B, 0xB2, 0x1E, 0xEE, 0xB8, 0x6A, 0x4E,
    0xB5, 0xF4, 0x5A, 0xC9, 0x18, 0x27, 0x9C, 0xDE, 0x14, 0x44, 0xED, 0xC4, 0x3C,
    0x71, 0x9F, 0x5F, 0xD9, 0x37, 0xA0, 0x78, 0x34, 0x6E, 0xBC, 0xD2, 0x7B, 0x1D,
    0xFA, 0x08, 0x39, 0x5A, 0x04, 0x73, 0x15, 0xD9, 0x0A, 0x48, 0xC1, 0x2D, 0x15,
    0x4E, 0x84, 0x30, 0x45, 0x69, 0xB3, 0xE5, 0xF6, 0xAD, 0x09, 0x1E, 0xCC, 0x5F,
    0x1F, 0x06, 0xD5, 0x58, 0xAD, 0x78, 0xD7, 0x9F, 0xE5, 0xED, 0x3B, 0x09, 0xD5,
    0xA6, 0x52, 0x6F, 0x92, 0xD3, 0x3C, 0xC6, 0x1E, 0xF2, 0x93, 0x7C, 0xD3, 0x5F,
    0x70, 0x85, 0x5D, 0xF8, 0xAA, 0x9D, 0xB7, 0x7B, 0x24, 0x5A, 0xE9, 0x0A, 0x35,
    0x2F, 0xF5, 0xD9, 0x82, 0x02, 0x8A, 0x90, 0x13, 0x5B, 0xB5, 0x67, 0x9C, 0xDD,
    0xA0, 0x4E, 0x82, 0x27, 0xDA, 0x7E, 0xE8, 0x8E, 0xCD, 0xE1, 0x56, 0x71, 0x2C,
    0xE6, 0x4E, 0x1F, 0x91, 0xCD, 0x7C, 0x6A, 0xB7, 0x78, 0xD0, 0x26, 0xF3, 0x56,
    0xA9, 0xD5, 0xA1, 0xC3, 0x3B, 0x98, 0xE9, 0x28, 0x09, 0xEF, 0x50, 0x90, 0xCD,
    0xC4, 0x8E, 0x75, 0xCC, 0xAC, 0x2D, 0xC9, 0x03, 0x6D, 0xAC, 0xFE, 0xC4, 0x88,
    0x36, 0xD1, 0x3F, 0xBB, 0x1C, 0x7D, 0xB3, 0x14, 0x61, 0x2C, 0xB7, 0x54, 0x4B,
    0xDB, 0x64, 0xB6, 0x57, 0x14, 0x16, 0x8E, 0x1E, 0x6C, 0x64, 0xBB, 0x8B, 0x48,
    0x5D, 0x96, 0x9D, 0xDC, 0x80, 0xA7, 0xF7, 0x54, 0xC7, 0x46, 0x38, 0x3E, 0x44,
    0xDE, 0x7E, 0x92, 0x8D, 0x07, 0xF6, 0x07, 0x37, 0x4E, 0x16, 0x10, 0xB4, 0x7D,
    0x88, 0x66, 0x7F, 0xBB, 0xFF, 0xEA, 0x00, 0xF3, 0xFF, 0x97, 0x2C, 0xB5, 0xBE,
    0x35, 0x4B, 0x5C, 0x36, 0xEC, 0x4C, 0xBD, 0x2B, 0x7D, 0xBF, 0x46, 0xE2, 0x9C,
    0x0E, 0x8A, 0xA3, 0xEC, 0xB1, 0x0E, 0x9A, 0xDA, 0x9A, 0x9B, 0x28, 0x92, 0x10,
    0x53, 0x57, 0xEA, 0xEC, 0xA2, 0x32, 0x32, 0x20, 0x1D, 0x97, 0x5C, 0xB6, 0x84,
    0xA9, 0x93, 0x8D, 0x95, 0x11, 0xA3, 0x24, 0xA3, 0x2D, 0xC6, 0x4A, 0xEF, 0xAA,
    0x1D, 0x85, 0x2B, 0x7D, 0x28, 0xBE, 0x53, 0xCE, 0x10, 0x1F, 0xAE, 0x0E, 0x41,
    0x6C, 0x4B, 0x79, 0x12, 0xFB, 0xF7, 0x54, 0xA3, 0x96, 0x54, 0x83, 0x20, 0x96,
    0x8F, 0x28, 0xA9, 0x3F, 0x8B, 0x3D, 0xBA, 0x77, 0xDC, 0x24, 0xE1, 0xD4, 0x49,
    0x40, 0xD8, 0x78, 0x31, 0x85, 0x43, 0xF6, 0xFE, 0x5C, 0xA6, 0x8F, 0x90, 0x09,
    0xB0, 0xE7, 0xC4, 0x95, 0xB2, 0x55, 0x49, 0x97, 0x8F, 0x1C, 0x78, 0x30, 0x20,
    0xA0, 0xB4, 0xEF, 0x73, 0x56, 0x59, 0x82, 0xFD, 0xCE, 0xBA, 0x6A, 0x8F, 0x2C,
    0x8B, 0x15, 0xFD, 0xA1, 0x85, 0xA8, 0x5C, 0x0F, 0x11, 0xA5, 0x9D, 0xC2, 0x46,
    0xC6, 0x9C, 0xC9, 0x40, 0x0B, 0x58, 0x6A, 0x1C, 0x7A, 0x23, 0xF9, 0xE0, 0x95,
    0x05, 0x13, 0x58, 0x72, 0xE8, 0x9F, 0x30, 0xAC, 0xCD, 0x26, 0xD4, 0x66, 0x13,
    0xDF, 0x1E, 0x7B, 0x4F, 0x9C, 0xBE, 0x38, 0x79, 0x75, 0x92, 0xA4, 0xDA, 0x26,
    0x44, 0x55, 0x17, 0xA3, 0xE5, 0x62, 0xDA, 0xEB, 0x86, 0xEA, 0x68, 0xC7, 0xAB,
    0xFD, 0x2D, 0x43, 0x59, 0x51, 0xC0, 0x75, 0x64, 0x91, 0x01, 0x29, 0x33, 0x28,
    0xF3, 0x04, 0x83, 0x80, 0x75, 0x37, 0x75, 0x0C, 0x03, 0x7B, 0x0A, 0xAB, 0x8E,
    0x60, 0x62, 0x8B, 0x4C, 0xAF, 0x2D, 0xA3, 0x2F, 0xFE, 0xAB, 0x45, 0xCF, 0xDA,
    0xAB, 0xFA, 0xFA, 0x30, 0x3D, 0xE8, 0xA1, 0x96, 0xA5, 0x7B, 0xE2, 0x2A, 0xD0,
    0xAF, 0x59, 0xF7, 0xD0, 0x32, 0x57, 0x19, 0xBD, 0xCA, 0x9F, 0xD5, 0x1A, 0xC7,
    0xAA, 0x65, 0x4A, 0x38, 0xB2, 0x70, 0x33, 0xB7, 0x75, 0xD2, 0xCD, 0xD1, 0xF0,
    0xA8, 0x87, 0x59, 0x20, 0xA5, 0x57, 0x55, 0xB1, 0xB2, 0xC9, 0x4D, 0x97, 0x34,
    0x41, 0xF3, 0xF0, 0x30, 0xA1, 0x2C, 0x1C, 0x49, 0x3E, 0x89, 0x7D, 0x12, 0xE2,
    0xC3, 0x04, 0xC3, 0x92, 0xC0, 0xF6, 0x39, 0x10, 0x80, 0x81, 0x8F, 0x08, 0xB4,
    0xF8, 0xB9, 0x13, 0x4E, 0x2C, 0xAE, 0xB3, 0x71, 0x82, 0x63, 0x98, 0xAB, 0x5C,
    0x1C, 0x10, 0xEA, 0x66, 0xF9, 0x02, 0x3A, 0x82, 0x61, 0xD0, 0xD4, 0xAE, 0x43,
    0xD4, 0x01, 0x3E, 0x9D, 0x04, 0x14, 0xF6, 0x60, 0xD8, 0xA7, 0xD6, 0xB8, 0x53,
    0xC8, 0xDA, 0x80, 0x93, 0xA0, 0x02, 0xDD, 0xCC, 0xE2, 0xF2, 0xBB, 0xFB, 0xE0,
    0x27, 0xD7, 0x34, 0x9A, 0x71, 0x49, 0xB5, 0x4F, 0x42, 0x1F, 0xB2, 0x9D, 0x6D,
    0xAA, 0x9D, 0xD3, 0x50, 0xB5, 0x8F, 0x6A, 0x4B, 0xDF, 0x1F, 0xD5, 0x27, 0x8F,
    0x3B, 0x27, 0xCF, 0x2F, 0x8C, 0xF8, 0x9D, 0x4C, 0x52, 0xBC, 0x32, 0x0F, 0x73,
    0xD5, 0x51, 0x8E, 0x36, 0x7E, 0xAD, 0x09, 0xF0, 0x94, 0x83, 0x5F, 0x36, 0xFD,
    0x7C, 0x03, 0xED, 0xF1, 0x5E, 0x4B, 0xF7, 0xAA, 0x55, 0x5C, 0x4A, 0x14, 0x59,
    0x85, 0x38, 0x2D, 0x8C, 0xDF, 0xEC, 0x65, 0x1B, 0xB8, 0x76, 0x57, 0x96, 0x3C,
    0x86, 0xED, 0xF2, 0x7F, 0x2D, 0x28, 0x48, 0xDA, 0x49, 0x7F, 0xF7, 0x54, 0x2B,
    0xD5, 0x39, 0xD5, 0x57, 0x0A, 0x75, 0x7A, 0x3E, 0x5E, 0x5D, 0xBA, 0x4A, 0x15,
    0xFA, 0xB8, 0x31, 0x80, 0x71, 0x2C, 0xCA, 0xC4, 0x51, 0x10, 0x16, 0x5D, 0x39,
    0xEC, 0x9D, 0x07, 0xB6, 0x6A, 0x89, 0x9F, 0x9B, 0x5B, 0x6F, 0x03, 0xB0, 0x92,
    0x01, 0x38, 0x6B, 0x48, 0x99, 0x0A, 0x8F, 0x13, 0xC1, 0xA6, 0x01, 0xEA, 0xBF,
    0x6F, 0x86, 0x43, 0x51, 0xB6, 0x11, 0x00, 0x00
};

int compress_test(void)
{
    int ret = 0;
    word32 dSz = sizeof(sample_text);
    word32 cSz = (dSz + (word32)(dSz * 0.001) + 12);
    byte *c;
    byte *d;

    c = XMALLOC(cSz * sizeof(byte), HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    d = XMALLOC(dSz * sizeof(byte), HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (c == NULL || d == NULL) {
        ERROR_OUT(-11700, exit);
    }

    /* follow calloc and initialize to 0 */
    XMEMSET(c, 0, cSz);
    XMEMSET(d, 0, dSz);

    if ((ret = wc_Compress(c, cSz, sample_text, dSz, 0)) < 0) {
        ERROR_OUT(-11701, exit);
    }
    cSz = (word32)ret;

    if ((ret = wc_DeCompress(d, dSz, c, cSz)) != (int)dSz) {
        ERROR_OUT(-11702, exit);
    }

    if (XMEMCMP(d, sample_text, dSz) != 0) {
        ERROR_OUT(-11703, exit);
    }

    /* GZIP tests */
    cSz = (dSz + (word32)(dSz * 0.001) + 12); /* reset cSz */
    XMEMSET(c, 0, cSz);
    XMEMSET(d, 0, dSz);

    ret = wc_Compress_ex(c, cSz, sample_text, dSz, 0, LIBZ_WINBITS_GZIP);
    if (ret < 0) {
        ERROR_OUT(-11704, exit);
    }
    cSz = (word32)ret;

    ret = wc_DeCompress_ex(d, dSz, c, cSz, LIBZ_WINBITS_GZIP);
    if (ret < 0) {
        ERROR_OUT(-11705, exit);
    }

    if (XMEMCMP(d, sample_text, dSz) != 0) {
        ERROR_OUT(-11706, exit);
    }

    /* Try with gzip generated output */
    XMEMSET(d, 0, dSz);
    ret = wc_DeCompress_ex(d, dSz, sample_text_gz, sizeof(sample_text_gz),
        LIBZ_WINBITS_GZIP);
    if (ret < 0) {
        ERROR_OUT(-11707, exit);
    }
    dSz = (word32)ret;

    if (XMEMCMP(d, sample_text, dSz) != 0) {
        ERROR_OUT(-11708, exit);
    }

    ret = 0; /* success */

exit:
    if (c) XFREE(c, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (d) XFREE(d, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);

    return ret;
}

#endif /* HAVE_LIBZ */

#ifdef HAVE_PKCS7

/* External Debugging/Testing Note:
 *
 * PKCS#7 test functions can output generated PKCS#7/CMS bundles for
 * additional testing. To dump bundles to files DER encoded files, please
 * define:
 *
 * #define PKCS7_OUTPUT_TEST_BUNDLES
 */


/* Loads certs and keys for use with PKCS7 tests, from either files
 * or buffers.
 *
 * rsaClientCertBuf      - output buffer for RSA client cert
 * rsaClientCertBufSz    - IN/OUT size of output buffer, size of RSA client cert
 * rsaClientPrivKeyBuf   - output buffer for RSA client private key
 * rsaClientPrivKeyBufSz - IN/OUT size of output buffer, size of RSA client key
 *
 * rsaServerCertBuf      - output buffer for RSA server cert
 * rsaServerCertBufSz    - IN/OUT size of output buffer, size of RSA server cert
 * rsaServerPrivKeyBuf   - output buffer for RSA server private key
 * rsaServerPrivKeyBufSz - IN/OUT size of output buffer, size of RSA server key
 *
 * rsaCaCertBuf          - output buffer for RSA CA cert
 * rsaCaCertBufSz        - IN/OUT size of output buffer, size of RSA ca cert
 * rsaCaPrivKeyBuf       - output buffer for RSA CA private key
 * rsaCaPrivKeyBufSz     - IN/OUT size of output buffer, size of RSA CA key
 *
 * eccClientCertBuf      - output buffer for ECC cert
 * eccClientCertBufSz    - IN/OUT size of output buffer, size of ECC cert
 * eccClientPrivKeyBuf   - output buffer for ECC private key
 * eccClientPrivKeyBufSz - IN/OUT size of output buffer, size of ECC private key
 *
 * Returns 0 on success, negative on error
 */
static int pkcs7_load_certs_keys(
                       byte* rsaClientCertBuf,    word32* rsaClientCertBufSz,
                       byte* rsaClientPrivKeyBuf, word32* rsaClientPrivKeyBufSz,
                       byte* rsaServerCertBuf,    word32* rsaServerCertBufSz,
                       byte* rsaServerPrivKeyBuf, word32* rsaServerPrivKeyBufSz,
                       byte* rsaCaCertBuf,        word32* rsaCaCertBufSz,
                       byte* rsaCaPrivKeyBuf,     word32* rsaCaPrivKeyBufSz,
                       byte* eccClientCertBuf,    word32* eccClientCertBufSz,
                       byte* eccClientPrivKeyBuf, word32* eccClientPrivKeyBufSz)
{
#ifndef NO_FILESYSTEM
    XFILE  certFile;
    XFILE  keyFile;

    (void)certFile;
    (void)keyFile;
#endif

#ifndef NO_RSA
    if (rsaClientCertBuf == NULL || rsaClientCertBufSz == NULL ||
        rsaClientPrivKeyBuf == NULL || rsaClientPrivKeyBufSz == NULL)
        return BAD_FUNC_ARG;
#endif

#ifdef HAVE_ECC
    if (eccClientCertBuf == NULL || eccClientCertBufSz == NULL ||
        eccClientPrivKeyBuf == NULL || eccClientPrivKeyBufSz == NULL)
        return BAD_FUNC_ARG;
#endif

/* RSA */
#ifndef NO_RSA

#ifdef USE_CERT_BUFFERS_1024
    if (*rsaClientCertBufSz < (word32)sizeof_client_cert_der_1024)
        return -11709;

    XMEMCPY(rsaClientCertBuf, client_cert_der_1024,
            sizeof_client_cert_der_1024);
    *rsaClientCertBufSz = sizeof_client_cert_der_1024;

    if (rsaServerCertBuf != NULL) {
        if (*rsaServerCertBufSz < (word32)sizeof_server_cert_der_1024)
            return -11710;

        XMEMCPY(rsaServerCertBuf, server_cert_der_1024,
                sizeof_server_cert_der_1024);
        *rsaServerCertBufSz = sizeof_server_cert_der_1024;
    }

    if (rsaCaCertBuf != NULL) {
        if (*rsaCaCertBufSz < (word32)sizeof_ca_cert_der_1024)
            return -11711;

        XMEMCPY(rsaCaCertBuf, ca_cert_der_1024, sizeof_ca_cert_der_1024);
        *rsaCaCertBufSz = sizeof_ca_cert_der_1024;
    }
#elif defined(USE_CERT_BUFFERS_2048)
    if (*rsaClientCertBufSz < (word32)sizeof_client_cert_der_2048)
        return -11712;

    XMEMCPY(rsaClientCertBuf, client_cert_der_2048,
            sizeof_client_cert_der_2048);
    *rsaClientCertBufSz = sizeof_client_cert_der_2048;

    if (rsaServerCertBuf != NULL) {
        if (*rsaServerCertBufSz < (word32)sizeof_server_cert_der_2048)
            return -11713;

        XMEMCPY(rsaServerCertBuf, server_cert_der_2048,
                sizeof_server_cert_der_2048);
        *rsaServerCertBufSz = sizeof_server_cert_der_2048;
    }

    if (rsaCaCertBuf != NULL) {
        if (*rsaCaCertBufSz < (word32)sizeof_ca_cert_der_2048)
            return -11714;

        XMEMCPY(rsaCaCertBuf, ca_cert_der_2048, sizeof_ca_cert_der_2048);
        *rsaCaCertBufSz = sizeof_ca_cert_der_2048;
    }
#else
    certFile = XFOPEN(clientCert, "rb");
    if (!certFile)
        return -11715;

    *rsaClientCertBufSz = (word32)XFREAD(rsaClientCertBuf, 1,
                                        *rsaClientCertBufSz, certFile);
    XFCLOSE(certFile);

    if (rsaServerCertBuf != NULL) {
        certFile = XFOPEN(rsaServerCertDerFile, "rb");
        if (!certFile)
            return -11716;

        *rsaServerCertBufSz = (word32)XFREAD(rsaServerCertBuf, 1,
                                            *rsaServerCertBufSz, certFile);
        XFCLOSE(certFile);
    }

    if (rsaCaCertBuf != NULL) {
        certFile = XFOPEN(rsaCaCertDerFile, "rb");
        if (!certFile)
            return -11717;

        *rsaCaCertBufSz = (word32)XFREAD(rsaCaCertBuf, 1, *rsaCaCertBufSz,
                                        certFile);
        XFCLOSE(certFile);
    }
#endif

#ifdef USE_CERT_BUFFERS_1024
    if (*rsaClientPrivKeyBufSz < (word32)sizeof_client_key_der_1024)
        return -11718;

    XMEMCPY(rsaClientPrivKeyBuf, client_key_der_1024,
            sizeof_client_key_der_1024);
    *rsaClientPrivKeyBufSz = sizeof_client_key_der_1024;

    if (rsaServerPrivKeyBuf != NULL) {
        if (*rsaServerPrivKeyBufSz < (word32)sizeof_server_key_der_1024)
            return -11719;

        XMEMCPY(rsaServerPrivKeyBuf, server_key_der_1024,
                sizeof_server_key_der_1024);
        *rsaServerPrivKeyBufSz = sizeof_server_key_der_1024;
    }

    if (rsaCaPrivKeyBuf != NULL) {
        if (*rsaCaPrivKeyBufSz < (word32)sizeof_ca_key_der_1024)
            return -11720;

        XMEMCPY(rsaCaPrivKeyBuf, ca_key_der_1024, sizeof_ca_key_der_1024);
        *rsaCaPrivKeyBufSz = sizeof_ca_key_der_1024;
    }
#elif defined(USE_CERT_BUFFERS_2048)
    if (*rsaClientPrivKeyBufSz < (word32)sizeof_client_key_der_2048)
        return -11721;

    XMEMCPY(rsaClientPrivKeyBuf, client_key_der_2048,
            sizeof_client_key_der_2048);
    *rsaClientPrivKeyBufSz = sizeof_client_key_der_2048;

    if (rsaServerPrivKeyBuf != NULL) {
        if (*rsaServerPrivKeyBufSz < (word32)sizeof_server_key_der_2048)
            return -11722;

        XMEMCPY(rsaServerPrivKeyBuf, server_key_der_2048,
                sizeof_server_key_der_2048);
        *rsaServerPrivKeyBufSz = sizeof_server_key_der_2048;
    }

    if (rsaCaPrivKeyBuf != NULL) {
        if (*rsaCaPrivKeyBufSz < (word32)sizeof_ca_key_der_2048)
            return -11723;

        XMEMCPY(rsaCaPrivKeyBuf, ca_key_der_2048, sizeof_ca_key_der_2048);
        *rsaCaPrivKeyBufSz = sizeof_ca_key_der_2048;
    }
#else
    keyFile = XFOPEN(clientKey, "rb");
    if (!keyFile)
        return -11724;

    *rsaClientPrivKeyBufSz = (word32)XFREAD(rsaClientPrivKeyBuf, 1,
                                           *rsaClientPrivKeyBufSz, keyFile);
    XFCLOSE(keyFile);

    if (rsaServerPrivKeyBuf != NULL) {
        keyFile = XFOPEN(rsaServerKeyDerFile, "rb");
        if (!keyFile)
            return -11725;

        *rsaServerPrivKeyBufSz = (word32)XFREAD(rsaServerPrivKeyBuf, 1,
                                               *rsaServerPrivKeyBufSz, keyFile);
        XFCLOSE(keyFile);
    }

    if (rsaCaPrivKeyBuf != NULL) {
        keyFile = XFOPEN(rsaCaKeyFile, "rb");
        if (!keyFile)
            return -11726;

        *rsaCaPrivKeyBufSz = (word32)XFREAD(rsaCaPrivKeyBuf, 1,
                                           *rsaCaPrivKeyBufSz, keyFile);
        XFCLOSE(keyFile);
    }
#endif /* USE_CERT_BUFFERS */

#endif /* NO_RSA */

/* ECC */
#ifdef HAVE_ECC

#ifdef USE_CERT_BUFFERS_256
    if (*eccClientCertBufSz < (word32)sizeof_cliecc_cert_der_256)
        return -11727;

    XMEMCPY(eccClientCertBuf, cliecc_cert_der_256, sizeof_cliecc_cert_der_256);
    *eccClientCertBufSz = sizeof_cliecc_cert_der_256;
#else
    certFile = XFOPEN(eccClientCert, "rb");
    if (!certFile)
        return -11728;

    *eccClientCertBufSz = (word32)XFREAD(eccClientCertBuf, 1,
                                        *eccClientCertBufSz, certFile);
    XFCLOSE(certFile);
#endif /* USE_CERT_BUFFERS_256 */

#ifdef USE_CERT_BUFFERS_256
    if (*eccClientPrivKeyBufSz < (word32)sizeof_ecc_clikey_der_256)
        return -11729;

    XMEMCPY(eccClientPrivKeyBuf, ecc_clikey_der_256, sizeof_ecc_clikey_der_256);
    *eccClientPrivKeyBufSz = sizeof_ecc_clikey_der_256;
#else
    keyFile = XFOPEN(eccClientKey, "rb");
    if (!keyFile)
        return -11730;

    *eccClientPrivKeyBufSz = (word32)XFREAD(eccClientPrivKeyBuf, 1,
                                           *eccClientPrivKeyBufSz, keyFile);
    XFCLOSE(keyFile);
#endif /* USE_CERT_BUFFERS_256 */
#endif /* HAVE_ECC */

#ifdef NO_RSA
    (void)rsaClientCertBuf;
    (void)rsaClientCertBufSz;
    (void)rsaClientPrivKeyBuf;
    (void)rsaClientPrivKeyBufSz;
    (void)rsaServerCertBuf;
    (void)rsaServerCertBufSz;
    (void)rsaServerPrivKeyBuf;
    (void)rsaServerPrivKeyBufSz;
    (void)rsaCaCertBuf;
    (void)rsaCaCertBufSz;
    (void)rsaCaPrivKeyBuf;
    (void)rsaCaPrivKeyBufSz;
#endif
#ifndef HAVE_ECC
    (void)eccClientCertBuf;
    (void)eccClientCertBufSz;
    (void)eccClientPrivKeyBuf;
    (void)eccClientPrivKeyBufSz;
#endif
#ifndef NO_FILESYSTEM
    (void)certFile;
    (void)keyFile;
#endif
    return 0;
}


typedef struct {
    const byte*  content;
    word32       contentSz;
    int          contentOID;
    int          encryptOID;
    int          keyWrapOID;
    int          keyAgreeOID;
    byte*        cert;
    size_t       certSz;
    byte*        privateKey;
    word32       privateKeySz;
    byte*        optionalUkm;
    word32       optionalUkmSz;
    int          ktriOptions;    /* KTRI options flags */
    int          kariOptions;    /* KARI options flags */

    /* KEKRI specific */
    byte*        secretKey;      /* key, only for kekri RecipientInfo types */
    word32       secretKeySz;    /* size of secretKey, bytes */
    byte*        secretKeyId;    /* key identifier */
    word32       secretKeyIdSz;  /* size of key identifier, bytes */
    void*        timePtr;        /* time_t pointer */
    byte*        otherAttrOID;   /* OPTIONAL, other attribute OID */
    word32       otherAttrOIDSz; /* size of otherAttrOID, bytes */
    byte*        otherAttr;      /* OPTIONAL, other attribute, ASN.1 encoded */
    word32       otherAttrSz;    /* size of otherAttr, bytes */
    int          kekriOptions;   /* KEKRI options flags */

    /* PWRI specific */
    char*        password;
    word32       passwordSz;
    byte*        salt;
    word32       saltSz;
    int          kdfOID;
    int          hashOID;
    int          kdfIterations;
    int          pwriOptions;    /* PWRI options flags */

    /* ORI specific */
    int          isOri;
    int          oriOptions;     /* ORI options flags */

    const char*  outFileName;
} pkcs7EnvelopedVector;


static const byte asnDataOid[] = {
    0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x07, 0x01
};

/* ORI encrypt callback, responsible for encrypting content-encryption key (CEK)
 * and giving wolfCrypt the value for oriOID and oriValue to place in
 * OtherRecipientInfo.
 *
 * Returns 0 on success, negative upon error. */
static int myOriEncryptCb(PKCS7* pkcs7, byte* cek, word32 cekSz, byte* oriType,
                          word32* oriTypeSz, byte* oriValue, word32* oriValueSz,
                          void* ctx)
{
    int i;

    /* make sure buffers are large enough */
    if ((*oriValueSz < (2 + cekSz)) || (*oriTypeSz < sizeof(oriType)))
        return -11731;

    /* our simple encryption algorithm will be take the bitwise complement */
    oriValue[0] = 0x04;         /*ASN OCTET STRING */
    oriValue[1] = (byte)cekSz;  /* length */
    for (i = 0; i < (int)cekSz; i++) {
        oriValue[2 + i] = ~cek[i];
    }
    *oriValueSz = 2 + cekSz;

    /* set oriType to ASN.1 encoded data OID */
    XMEMCPY(oriType, asnDataOid, sizeof(asnDataOid));
    *oriTypeSz = sizeof(asnDataOid);

    (void)pkcs7;
    (void)ctx;

    return 0;
}


/* ORI decrypt callback, responsible for providing a decrypted content
 * encryption key (CEK) placed into decryptedKey and size placed into
 * decryptedKeySz. oriOID and oriValue are given to the callback to help
 * in decrypting the encrypted CEK.
 *
 * Returns 0 on success, negative upon error. */
static int myOriDecryptCb(PKCS7* pkcs7, byte* oriType, word32 oriTypeSz,
                          byte* oriValue, word32 oriValueSz, byte* decryptedKey,
                          word32* decryptedKeySz, void* ctx)
{
    int i;

    /* make sure oriType matches what we expect */
    if (oriTypeSz != sizeof(asnDataOid))
        return -11732;

    if (XMEMCMP(oriType, asnDataOid, sizeof(asnDataOid)) != 0)
        return -11733;

    /* make sure decrypted buffer is large enough */
    if (*decryptedKeySz < oriValueSz)
        return -11734;

    /* decrypt encrypted CEK using simple bitwise complement,
       only for example */
    for (i = 0; i < (int)oriValueSz - 2; i++) {
        decryptedKey[i] = ~oriValue[2 + i];
    }

    *decryptedKeySz = oriValueSz - 2;

    (void)pkcs7;
    (void)ctx;

    return 0;
}


#ifndef NO_AES
/* returns 0 on success */
static int myDecryptionFunc(PKCS7* pkcs7, int encryptOID, byte* iv, int ivSz,
        byte* aad, word32 aadSz, byte* authTag, word32 authTagSz,
        byte* in, int inSz, byte* out, void* usrCtx)
{
    int keyId = -1, ret, keySz;
    word32 keyIdSz = 8;
    const byte*  key;
    byte   keyIdRaw[8];
    Aes    aes;

    /* looking for KEY ID
     * fwDecryptKeyID OID "1.2.840.113549.1.9.16.2.37
     */
    const unsigned char OID[] = {
        /* 0x06, 0x0B do not pass in tag and length */
        0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D,
        0x01, 0x09, 0x10, 0x02, 0x25
    };

    const byte defKey[] = {
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08
    };

    const byte altKey[] = {
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08
    };

    /* test user context passed in */
    if (usrCtx == NULL || *(int*)usrCtx != 1) {
        return -11735;
    }

    /* if needing to find keyIdSz can call with NULL */
    ret = wc_PKCS7_GetAttributeValue(pkcs7, OID, sizeof(OID), NULL,
            &keyIdSz);
    if (ret != LENGTH_ONLY_E) {
        printf("Unexpected error %d when getting keyIdSz\n", ret);
        printf("Possibly no KEY ID attribute set\n");
        return -11736;
    }
    else {
        XMEMSET(keyIdRaw, 0, sizeof(keyIdRaw));
        ret = wc_PKCS7_GetAttributeValue(pkcs7, OID, sizeof(OID), keyIdRaw,
                &keyIdSz);
        if (ret < 0) {
            return ret;
        }

        if (keyIdSz < 3) {
            printf("keyIdSz is smaller than expected\n");
            return -11737;
        }
        if (keyIdSz > 2 + sizeof(int)) {
            printf("example case was only expecting a keyId of int size\n");
            return -11738;
        }

        /* keyIdRaw[0] OCTET TAG */
        /* keyIdRaw[1] Length */
#ifdef BIG_ENDIAN_ORDER
        if (keyIdRaw[1] == 0x01) {
            keyId = 1;
        }
#else
        keyId = *(int*)(keyIdRaw + 2);
#endif
    }


    /* Use keyID here if found to select key and decrypt in HSM or in this
     * example just select key and do software decryption */
    if (keyId == 1) {
        key = altKey;
        keySz = sizeof(altKey);
    }
    else {
        key = defKey;
        keySz = sizeof(defKey);
    }

    switch (encryptOID) {
        case AES256CBCb:
            if ((keySz != 32 ) || (ivSz  != AES_BLOCK_SIZE))
                return BAD_FUNC_ARG;
            break;

        case AES128CBCb:
            if ((keySz != 16 ) || (ivSz  != AES_BLOCK_SIZE))
                return BAD_FUNC_ARG;
            break;

        default:
            printf("Unsupported content cipher type for example");
            return ALGO_ID_E;
    };

    ret = wc_AesInit(&aes, HEAP_HINT, INVALID_DEVID);
    if (ret == 0) {
        ret = wc_AesSetKey(&aes, key, keySz, iv, AES_DECRYPTION);
        if (ret == 0)
            ret = wc_AesCbcDecrypt(&aes, out, in, inSz);
        wc_AesFree(&aes);
    }

    (void)aad;
    (void)aadSz;
    (void)authTag;
    (void)authTagSz;
    return ret;
}
#endif /* NO_AES */


static int pkcs7enveloped_run_vectors(byte* rsaCert, word32 rsaCertSz,
                                      byte* rsaPrivKey,  word32 rsaPrivKeySz,
                                      byte* eccCert, word32 eccCertSz,
                                      byte* eccPrivKey,  word32 eccPrivKeySz)
{
    int ret, testSz, i;
    int envelopedSz, decodedSz;

    byte   enveloped[2048];
    byte   decoded[2048];
    PKCS7* pkcs7;
    WC_RNG rng;
#ifdef PKCS7_OUTPUT_TEST_BUNDLES
    XFILE  pkcs7File;
#endif

    const byte data[] = { /* Hello World */
        0x48,0x65,0x6c,0x6c,0x6f,0x20,0x57,0x6f,
        0x72,0x6c,0x64
    };

#if !defined(NO_AES) && defined(WOLFSSL_AES_256) && defined(HAVE_ECC) && \
    defined(WOLFSSL_SHA512)
    byte optionalUkm[] = {
        0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07
    };
#endif /* NO_AES */

#if !defined(NO_AES) && !defined(NO_SHA) && defined(WOLFSSL_AES_128)
    /* encryption key for kekri recipient types */
    byte secretKey[] = {
        0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
        0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07
    };

    /* encryption key identifier */
    byte secretKeyId[] = {
        0x02,0x02,0x03,0x04
    };
#endif

#if !defined(NO_PWDBASED) && !defined(NO_AES) && \
    !defined(NO_SHA) && defined(WOLFSSL_AES_128)

    #ifndef HAVE_FIPS
    char password[] = "password"; /* NOTE: Password is too short for FIPS */
    #else
    char password[] = "passwordFIPS_MODE";
    #endif

    byte salt[] = {
        0x12, 0x34, 0x56, 0x78, 0x78, 0x56, 0x34, 0x12
    };
#endif

    const pkcs7EnvelopedVector testVectors[] =
    {
        /* key transport key encryption technique */
#ifndef NO_RSA
    #ifndef NO_DES3
        {data, (word32)sizeof(data), DATA, DES3b, 0, 0, rsaCert, rsaCertSz,
         rsaPrivKey, rsaPrivKeySz, NULL, 0, 0, 0, NULL, 0, NULL, 0, NULL, NULL,
         0, NULL, 0, 0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0, 0,
         "pkcs7envelopedDataDES3.der"},
    #endif

    #ifndef NO_AES
        #ifdef WOLFSSL_AES_128
        {data, (word32)sizeof(data), DATA, AES128CBCb, 0, 0, rsaCert, rsaCertSz,
         rsaPrivKey, rsaPrivKeySz, NULL, 0, 0, 0, NULL, 0, NULL, 0, NULL, NULL,
         0, NULL, 0, 0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0, 0,
         "pkcs7envelopedDataAES128CBC.der"},
        #endif
        #ifdef WOLFSSL_AES_192
        {data, (word32)sizeof(data), DATA, AES192CBCb, 0, 0, rsaCert, rsaCertSz,
         rsaPrivKey, rsaPrivKeySz, NULL, 0, 0, 0, NULL, 0, NULL, 0, NULL, NULL,
         0, NULL, 0, 0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0, 0,
         "pkcs7envelopedDataAES192CBC.der"},
        #endif
        #ifdef WOLFSSL_AES_256
        {data, (word32)sizeof(data), DATA, AES256CBCb, 0, 0, rsaCert, rsaCertSz,
         rsaPrivKey, rsaPrivKeySz, NULL, 0, 0, 0, NULL, 0, NULL, 0, NULL, NULL,
         0, NULL, 0, 0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0, 0,
         "pkcs7envelopedDataAES256CBC.der"},

        /* explicitly using SKID for SubjectKeyIdentifier */
        {data, (word32)sizeof(data), DATA, AES256CBCb, 0, 0, rsaCert, rsaCertSz,
         rsaPrivKey, rsaPrivKeySz, NULL, 0, CMS_SKID, 0, NULL, 0, NULL, 0, NULL,
         NULL, 0, NULL, 0, 0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0, 0,
         "pkcs7envelopedDataAES256CBC_SKID.der"},

        /* explicitly using IssuerAndSerialNumber for SubjectKeyIdentifier */
        {data, (word32)sizeof(data), DATA, AES256CBCb, 0, 0, rsaCert, rsaCertSz,
         rsaPrivKey, rsaPrivKeySz, NULL, 0, CMS_ISSUER_AND_SERIAL_NUMBER, 0,
         NULL, 0, NULL, 0, NULL, NULL, 0, NULL, 0, 0, NULL, 0, NULL, 0, 0, 0,
         0, 0, 0, 0, "pkcs7envelopedDataAES256CBC_IANDS.der"},
        #endif
    #endif /* NO_AES */
#endif

        /* key agreement key encryption technique*/
#ifdef HAVE_ECC
    #ifndef NO_AES
        #if !defined(NO_SHA) && defined(WOLFSSL_AES_128)
        {data, (word32)sizeof(data), DATA, AES128CBCb, AES128_WRAP,
         dhSinglePass_stdDH_sha1kdf_scheme, eccCert, eccCertSz, eccPrivKey,
         eccPrivKeySz, NULL, 0, 0, 0, NULL, 0, NULL, 0, NULL, NULL, 0, NULL, 0,
         0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0, 0,
         "pkcs7envelopedDataAES128CBC_ECDH_SHA1KDF.der"},
        #endif

        #if !defined(NO_SHA256) && defined(WOLFSSL_AES_256)
        {data, (word32)sizeof(data), DATA, AES256CBCb, AES256_WRAP,
         dhSinglePass_stdDH_sha256kdf_scheme, eccCert, eccCertSz, eccPrivKey,
         eccPrivKeySz, NULL, 0, 0, 0, NULL, 0, NULL, 0, NULL, NULL, 0, NULL, 0,
         0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0, 0,
         "pkcs7envelopedDataAES256CBC_ECDH_SHA256KDF.der"},
        #endif /* NO_SHA256 && WOLFSSL_AES_256 */

        #if defined(WOLFSSL_SHA512) && defined(WOLFSSL_AES_256)
        {data, (word32)sizeof(data), DATA, AES256CBCb, AES256_WRAP,
         dhSinglePass_stdDH_sha512kdf_scheme, eccCert, eccCertSz, eccPrivKey,
         eccPrivKeySz, NULL, 0, 0, 0, NULL, 0, NULL, 0, NULL, NULL, 0, NULL, 0,
         0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0, 0,
         "pkcs7envelopedDataAES256CBC_ECDH_SHA512KDF.der"},

        /* with optional user keying material (ukm) */
        {data, (word32)sizeof(data), DATA, AES256CBCb, AES256_WRAP,
         dhSinglePass_stdDH_sha512kdf_scheme, eccCert, eccCertSz, eccPrivKey,
         eccPrivKeySz, optionalUkm, sizeof(optionalUkm), 0, 0, NULL, 0,
         NULL, 0, NULL, NULL, 0, NULL, 0, 0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0, 0,
         "pkcs7envelopedDataAES256CBC_ECDH_SHA512KDF_ukm.der"},
        #endif /* WOLFSSL_SHA512 && WOLFSSL_AES_256 */
    #endif /* NO_AES */
#endif

        /* kekri (KEKRecipientInfo) recipient types */
#ifndef NO_AES
        #if !defined(NO_SHA) && defined(WOLFSSL_AES_128)
        {data, (word32)sizeof(data), DATA, AES128CBCb, AES128_WRAP, 0,
         NULL, 0, NULL, 0, NULL, 0, 0, 0, secretKey, sizeof(secretKey),
         secretKeyId, sizeof(secretKeyId), NULL, NULL, 0, NULL, 0,
         0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0, 0,
         "pkcs7envelopedDataAES128CBC_KEKRI.der"},
        #endif
#endif

        /* pwri (PasswordRecipientInfo) recipient types */
#if !defined(NO_PWDBASED) && !defined(NO_AES)
        #if !defined(NO_SHA) && defined(WOLFSSL_AES_128)
        {data, (word32)sizeof(data), DATA, AES128CBCb, 0, 0,
         NULL, 0, NULL, 0, NULL, 0, 0, 0, NULL, 0,
         NULL, 0, NULL, NULL, 0, NULL, 0, 0, password,
         (word32)XSTRLEN(password), salt, sizeof(salt), PBKDF2_OID, WC_SHA, 5,
         0, 0, 0, "pkcs7envelopedDataAES128CBC_PWRI.der"},
        #endif
#endif

#if !defined(NO_AES) && !defined(NO_AES_128)
        /* ori (OtherRecipientInfo) recipient types */
        {data, (word32)sizeof(data), DATA, AES128CBCb, 0, 0, NULL, 0, NULL, 0,
         NULL, 0, 0, 0, NULL, 0, NULL, 0, NULL, NULL, 0, NULL, 0, 0, NULL, 0,
         NULL, 0, 0, 0, 0, 0, 1, 0, "pkcs7envelopedDataAES128CBC_ORI.der"},
#endif
    };

    testSz = sizeof(testVectors) / sizeof(pkcs7EnvelopedVector);

#ifdef ECC_TIMING_RESISTANT
#ifndef HAVE_FIPS
        ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
        ret = wc_InitRng(&rng);
#endif
        if (ret != 0) {
            return -11760;
        }
#endif

    for (i = 0; i < testSz; i++) {
        pkcs7 = wc_PKCS7_New(HEAP_HINT,
        #ifdef WOLFSSL_ASYNC_CRYPT
            INVALID_DEVID /* async PKCS7 is not supported */
        #else
            devId
        #endif
        );
        if (pkcs7 == NULL)
            return -11739;

        if (testVectors[i].secretKey != NULL) {
            /* KEKRI recipient type */

            ret = wc_PKCS7_Init(pkcs7, pkcs7->heap, pkcs7->devId);
            if (ret != 0) {
                return -11740;
            }

            pkcs7->content      = (byte*)testVectors[i].content;
            pkcs7->contentSz    = testVectors[i].contentSz;
            pkcs7->contentOID   = testVectors[i].contentOID;
            pkcs7->encryptOID   = testVectors[i].encryptOID;
            pkcs7->ukm          = testVectors[i].optionalUkm;
            pkcs7->ukmSz        = testVectors[i].optionalUkmSz;

            ret = wc_PKCS7_AddRecipient_KEKRI(pkcs7, testVectors[i].keyWrapOID,
                    testVectors[i].secretKey, testVectors[i].secretKeySz,
                    testVectors[i].secretKeyId, testVectors[i].secretKeyIdSz,
                    testVectors[i].timePtr, testVectors[i].otherAttrOID,
                    testVectors[i].otherAttrOIDSz, testVectors[i].otherAttr,
                    testVectors[i].otherAttrSz, testVectors[i].kekriOptions);

            if (ret < 0) {
                wc_PKCS7_Free(pkcs7);
                return -11741;
            }

            /* set key, for decryption */
            ret = wc_PKCS7_SetKey(pkcs7, testVectors[i].secretKey,
                                  testVectors[i].secretKeySz);

            if (ret != 0) {
                wc_PKCS7_Free(pkcs7);
                return -11742;
            }

        } else if (testVectors[i].password != NULL) {
        #ifndef NO_PWDBASED
            /* PWRI recipient type */

            ret = wc_PKCS7_Init(pkcs7, pkcs7->heap, pkcs7->devId);
            if (ret != 0) {
                return -11743;
            }

            pkcs7->content      = (byte*)testVectors[i].content;
            pkcs7->contentSz    = testVectors[i].contentSz;
            pkcs7->contentOID   = testVectors[i].contentOID;
            pkcs7->encryptOID   = testVectors[i].encryptOID;
            pkcs7->ukm          = testVectors[i].optionalUkm;
            pkcs7->ukmSz        = testVectors[i].optionalUkmSz;

            ret = wc_PKCS7_AddRecipient_PWRI(pkcs7,
                    (byte*)testVectors[i].password,
                    testVectors[i].passwordSz, testVectors[i].salt,
                    testVectors[i].saltSz, testVectors[i].kdfOID,
                    testVectors[i].hashOID, testVectors[i].kdfIterations,
                    testVectors[i].encryptOID, testVectors[i].pwriOptions);

            if (ret < 0) {
                wc_PKCS7_Free(pkcs7);
                return -11744;
            }

            /* set password, for decryption */
            ret = wc_PKCS7_SetPassword(pkcs7, (byte*)testVectors[i].password,
                    testVectors[i].passwordSz);

            if (ret < 0) {
                wc_PKCS7_Free(pkcs7);
                return -11745;
            }
        #endif /* NO_PWDBASED */

        } else if (testVectors[i].isOri == 1) {
            /* ORI recipient type */

            ret = wc_PKCS7_Init(pkcs7, pkcs7->heap, pkcs7->devId);
            if (ret != 0) {
                return -11746;
            }

            pkcs7->content      = (byte*)testVectors[i].content;
            pkcs7->contentSz    = testVectors[i].contentSz;
            pkcs7->contentOID   = testVectors[i].contentOID;
            pkcs7->encryptOID   = testVectors[i].encryptOID;

            ret = wc_PKCS7_AddRecipient_ORI(pkcs7, myOriEncryptCb,
                                            testVectors[i].oriOptions);

            if (ret < 0) {
                wc_PKCS7_Free(pkcs7);
                return -11747;
            }

            /* set decrypt callback for decryption */
            ret = wc_PKCS7_SetOriDecryptCb(pkcs7, myOriDecryptCb);

            if (ret < 0) {
                wc_PKCS7_Free(pkcs7);
                return -11748;
            }

        } else {
            /* KTRI or KARI recipient types */

            ret = wc_PKCS7_Init(pkcs7, pkcs7->heap, pkcs7->devId);
            if (ret != 0) {
                return -11749;
            }

            ret = wc_PKCS7_InitWithCert(pkcs7, testVectors[i].cert,
                                        (word32)testVectors[i].certSz);
            if (ret != 0) {
                wc_PKCS7_Free(pkcs7);
                return -11750;
            }

            pkcs7->keyWrapOID   = testVectors[i].keyWrapOID;
            pkcs7->keyAgreeOID  = testVectors[i].keyAgreeOID;
            pkcs7->privateKey   = testVectors[i].privateKey;
            pkcs7->privateKeySz = testVectors[i].privateKeySz;
            pkcs7->content      = (byte*)testVectors[i].content;
            pkcs7->contentSz    = testVectors[i].contentSz;
            pkcs7->contentOID   = testVectors[i].contentOID;
            pkcs7->encryptOID   = testVectors[i].encryptOID;
            pkcs7->ukm          = testVectors[i].optionalUkm;
            pkcs7->ukmSz        = testVectors[i].optionalUkmSz;

            /* set SubjectIdentifier type for KTRI types */
            if (testVectors[i].ktriOptions & CMS_SKID) {

                ret = wc_PKCS7_SetSignerIdentifierType(pkcs7, CMS_SKID);
                if (ret != 0) {
                    wc_PKCS7_Free(pkcs7);
                    return -11751;
                }
            } else if (testVectors[i].ktriOptions &
                       CMS_ISSUER_AND_SERIAL_NUMBER) {

                ret = wc_PKCS7_SetSignerIdentifierType(pkcs7,
                        CMS_ISSUER_AND_SERIAL_NUMBER);
                if (ret != 0) {
                    wc_PKCS7_Free(pkcs7);
                    return -11752;
                }
            }
        }

#ifdef ECC_TIMING_RESISTANT
        pkcs7->rng = &rng;
#endif
        /* encode envelopedData */
        envelopedSz = wc_PKCS7_EncodeEnvelopedData(pkcs7, enveloped,
                                                   sizeof(enveloped));
        if (envelopedSz <= 0) {
            wc_PKCS7_Free(pkcs7);
            return -11753;
        }

        /* decode envelopedData */
        decodedSz = wc_PKCS7_DecodeEnvelopedData(pkcs7, enveloped, envelopedSz,
                                                 decoded, sizeof(decoded));
        if (decodedSz <= 0) {
            wc_PKCS7_Free(pkcs7);
            return -11754;
        }

        /* test decode result */
        if (XMEMCMP(decoded, data, sizeof(data)) != 0){
            wc_PKCS7_Free(pkcs7);
            return -11755;
        }

#ifndef NO_PKCS7_STREAM
        { /* test reading byte by byte */
            int z;
            for (z = 0; z < envelopedSz; z++) {
                decodedSz = wc_PKCS7_DecodeEnvelopedData(pkcs7, enveloped + z, 1,
                                                 decoded, sizeof(decoded));
                if (decodedSz <= 0 && decodedSz != WC_PKCS7_WANT_READ_E) {
                    printf("unexpected error %d\n", decodedSz);
                    return -11756;
                }
            }
            /* test decode result */
            if (XMEMCMP(decoded, data, sizeof(data)) != 0) {
                printf("stream read compare failed\n");
                wc_PKCS7_Free(pkcs7);
                return -11757;
            }
        }
#endif
#ifdef PKCS7_OUTPUT_TEST_BUNDLES
        /* output pkcs7 envelopedData for external testing */
        pkcs7File = XFOPEN(testVectors[i].outFileName, "wb");
        if (!pkcs7File) {
            wc_PKCS7_Free(pkcs7);
            return -11758;
        }

        ret = (int)XFWRITE(enveloped, 1, envelopedSz, pkcs7File);
        XFCLOSE(pkcs7File);
        if (ret != envelopedSz) {
            wc_PKCS7_Free(pkcs7);
            return -11759;
        }
#endif /* PKCS7_OUTPUT_TEST_BUNDLES */

        wc_PKCS7_Free(pkcs7);
        pkcs7 = NULL;
    }

#ifdef ECC_TIMING_RESISTANT
    wc_FreeRng(&rng);
#endif

    (void)eccCert;
    (void)eccCertSz;
    (void)eccPrivKey;
    (void)eccPrivKeySz;
    (void)rsaCert;
    (void)rsaCertSz;
    (void)rsaPrivKey;
    (void)rsaPrivKeySz;

    return 0;
}


int pkcs7enveloped_test(void)
{
    int ret = 0;

    byte* rsaCert    = NULL;
    byte* rsaPrivKey = NULL;
    word32 rsaCertSz    = 0;
    word32 rsaPrivKeySz = 0;

    byte* eccCert    = NULL;
    byte* eccPrivKey = NULL;
    word32 eccCertSz    = 0;
    word32 eccPrivKeySz = 0;

#ifndef NO_RSA
    /* read client RSA cert and key in DER format */
    rsaCert = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (rsaCert == NULL)
        return -11800;

    rsaPrivKey = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (rsaPrivKey == NULL) {
        XFREE(rsaCert, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        return -11801;
    }

    rsaCertSz = FOURK_BUF;
    rsaPrivKeySz = FOURK_BUF;
#endif /* NO_RSA */

#ifdef HAVE_ECC
    /* read client ECC cert and key in DER format */
    eccCert = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (eccCert == NULL) {
    #ifndef NO_RSA
        XFREE(rsaCert,    HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(rsaPrivKey, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        return -11802;
    }

    eccPrivKey =(byte*)XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (eccPrivKey == NULL) {
    #ifndef NO_RSA
        XFREE(rsaCert,    HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(rsaPrivKey, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        XFREE(eccCert,    HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        return -11803;
    }

    eccCertSz = FOURK_BUF;
    eccPrivKeySz = FOURK_BUF;
#endif /* HAVE_ECC */

    ret = pkcs7_load_certs_keys(rsaCert, &rsaCertSz, rsaPrivKey,
                                &rsaPrivKeySz, NULL, NULL, NULL, NULL,
                                NULL, NULL, NULL, NULL, eccCert, &eccCertSz,
                                eccPrivKey, &eccPrivKeySz);
    if (ret < 0) {
    #ifndef NO_RSA
        XFREE(rsaCert,    HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(rsaPrivKey, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
    #ifdef HAVE_ECC
        XFREE(eccCert,    HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(eccPrivKey, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        return -11804;
    }

    ret = pkcs7enveloped_run_vectors(rsaCert, (word32)rsaCertSz,
                                     rsaPrivKey, (word32)rsaPrivKeySz,
                                     eccCert, (word32)eccCertSz,
                                     eccPrivKey, (word32)eccPrivKeySz);

#ifndef NO_RSA
    XFREE(rsaCert,    HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(rsaPrivKey, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
#endif
#ifdef HAVE_ECC
    XFREE(eccCert,    HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(eccPrivKey, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}


#if defined(HAVE_AESGCM) || defined(HAVE_AESCCM)

typedef struct {
    const byte*  content;
    word32       contentSz;
    int          contentOID;
    int          encryptOID;
    int          keyWrapOID;
    int          keyAgreeOID;
    byte*        cert;
    size_t       certSz;
    byte*        privateKey;
    word32       privateKeySz;
    PKCS7Attrib* authAttribs;
    word32       authAttribsSz;
    PKCS7Attrib* unauthAttribs;
    word32       unauthAttribsSz;

    /* KARI / KTRI specific */
    byte*        optionalUkm;
    word32       optionalUkmSz;
    int          ktriOptions;    /* KTRI options flags */
    int          kariOptions;    /* KARI options flags */

    /* KEKRI specific */
    byte*        secretKey;      /* key, only for kekri RecipientInfo types */
    word32       secretKeySz;    /* size of secretKey, bytes */
    byte*        secretKeyId;    /* key identifier */
    word32       secretKeyIdSz;  /* size of key identifier, bytes */
    void*        timePtr;        /* time_t pointer */
    byte*        otherAttrOID;   /* OPTIONAL, other attribute OID */
    word32       otherAttrOIDSz; /* size of otherAttrOID, bytes */
    byte*        otherAttr;      /* OPTIONAL, other attribute, ASN.1 encoded */
    word32       otherAttrSz;    /* size of otherAttr, bytes */
    int          kekriOptions;   /* KEKRI options flags */

    /* PWRI specific */
    char*        password;       /* password */
    word32       passwordSz;     /* password size, bytes */
    byte*        salt;           /* KDF salt */
    word32       saltSz;         /* KDF salt size, bytes */
    int          kdfOID;         /* KDF OID */
    int          hashOID;        /* KDF hash algorithm OID */
    int          kdfIterations;  /* KDF iterations */
    int          kekEncryptOID;  /* KEK encryption algorithm OID */
    int          pwriOptions;    /* PWRI options flags */

    /* ORI specific */
    int          isOri;
    int          oriOptions;     /* ORI options flags */

    const char*  outFileName;
} pkcs7AuthEnvelopedVector;


static int pkcs7authenveloped_run_vectors(byte* rsaCert, word32 rsaCertSz,
                                          byte* rsaPrivKey,  word32 rsaPrivKeySz,
                                          byte* eccCert, word32 eccCertSz,
                                          byte* eccPrivKey,  word32 eccPrivKeySz)
{
    int ret, testSz, i;
    int envelopedSz, decodedSz;

    byte   enveloped[2048];
    byte   decoded[2048];
    WC_RNG rng;
    PKCS7* pkcs7;
#ifdef PKCS7_OUTPUT_TEST_BUNDLES
    XFILE  pkcs7File;
#endif

    const byte data[] = { /* Hello World */
        0x48,0x65,0x6c,0x6c,0x6f,0x20,0x57,0x6f,
        0x72,0x6c,0x64
    };
    byte senderNonce[PKCS7_NONCE_SZ + 2];

#ifdef HAVE_ECC
    byte senderNonceOid[] =
               { 0x06, 0x0a, 0x60, 0x86, 0x48, 0x01, 0x86, 0xF8, 0x45, 0x01,
                 0x09, 0x05 };

    PKCS7Attrib attribs[] =
    {
        { senderNonceOid, sizeof(senderNonceOid), senderNonce,
                                       sizeof(senderNonce) }
    };
#endif

#if !defined(NO_AES) && defined(WOLFSSL_AES_256) && defined(HAVE_ECC) && \
    defined(WOLFSSL_SHA512)
    byte optionalUkm[] = {
        0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07
    };
#endif /* NO_AES */

#if !defined(NO_AES) && !defined(NO_SHA) && defined(WOLFSSL_AES_128)
    /* encryption key for kekri recipient types */
    byte secretKey[] = {
        0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
        0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07
    };

    /* encryption key identifier */
    byte secretKeyId[] = {
        0x02,0x02,0x03,0x04
    };
#endif

#if !defined(NO_PWDBASED) && !defined(NO_AES) && defined(HAVE_AESGCM) && \
    !defined(NO_SHA) && defined(WOLFSSL_AES_128)

    #ifndef HAVE_FIPS
    char password[] = "password";
    #else
    char password[] = "passwordFIPS_MODE";
    #endif

    byte salt[] = {
        0x12, 0x34, 0x56, 0x78, 0x78, 0x56, 0x34, 0x12
    };
#endif

    const pkcs7AuthEnvelopedVector testVectors[] =
    {
        /* key transport key encryption technique */
#ifndef NO_RSA
    #if !defined(NO_AES) && defined(HAVE_AESGCM)
        #ifdef WOLFSSL_AES_128
        {data, (word32)sizeof(data), DATA, AES128GCMb, 0, 0, rsaCert, rsaCertSz,
         rsaPrivKey, rsaPrivKeySz, NULL, 0, NULL, 0, NULL, 0, 0, 0, NULL, 0,
         NULL, 0, NULL, NULL, 0, NULL, 0, 0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0,
         0, 0, "pkcs7authEnvelopedDataAES128GCM.der"},
        #endif
        #ifdef WOLFSSL_AES_192
        {data, (word32)sizeof(data), DATA, AES192GCMb, 0, 0, rsaCert, rsaCertSz,
         rsaPrivKey, rsaPrivKeySz, NULL, 0, NULL, 0, NULL, 0, 0, 0, NULL, 0,
         NULL, 0, NULL, NULL, 0, NULL, 0, 0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0,
         0, 0, "pkcs7authEnvelopedDataAES192GCM.der"},
        #endif
        #ifdef WOLFSSL_AES_256
        {data, (word32)sizeof(data), DATA, AES256GCMb, 0, 0, rsaCert, rsaCertSz,
         rsaPrivKey, rsaPrivKeySz, NULL, 0, NULL, 0, NULL, 0, 0, 0, NULL, 0,
         NULL, 0, NULL, NULL, 0, NULL, 0, 0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0,
         0, 0, "pkcs7authEnvelopedDataAES256GCM.der"},

        /* test with contentType set to FirmwarePkgData */
        {data, (word32)sizeof(data), FIRMWARE_PKG_DATA, AES256GCMb, 0, 0,
         rsaCert, rsaCertSz, rsaPrivKey, rsaPrivKeySz, NULL, 0, NULL, 0, NULL,
         0, 0, 0, NULL, 0, NULL, 0, NULL, NULL, 0, NULL, 0, 0, NULL, 0, NULL,
         0, 0, 0, 0, 0, 0, 0, 0,
         "pkcs7authEnvelopedDataAES256GCM_firmwarePkgData.der"},

        /* explicitly using SKID for SubjectKeyIdentifier */
        {data, (word32)sizeof(data), DATA, AES256GCMb, 0, 0, rsaCert, rsaCertSz,
         rsaPrivKey, rsaPrivKeySz, NULL, 0, NULL, 0, NULL, 0, CMS_SKID, 0,
         NULL, 0, NULL, 0, NULL, NULL, 0, NULL, 0, 0, NULL, 0, NULL, 0, 0, 0,
         0, 0, 0, 0, 0, "pkcs7authEnvelopedDataAES256GCM_SKID.der"},

        /* explicitly using IssuerAndSerialNumber for SubjectKeyIdentifier */
        {data, (word32)sizeof(data), DATA, AES256GCMb, 0, 0, rsaCert, rsaCertSz,
         rsaPrivKey, rsaPrivKeySz, NULL, 0, NULL, 0, NULL, 0,
         CMS_ISSUER_AND_SERIAL_NUMBER, 0, NULL, 0, NULL, 0, NULL, NULL, 0,
         NULL, 0, 0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0, 0, 0,
         "pkcs7authEnvelopedDataAES256GCM_IANDS.der"},
        #endif
    #endif /* NO_AES */
#endif

        /* key agreement key encryption technique*/
#ifdef HAVE_ECC
    #if !defined(NO_AES) && defined(HAVE_AESGCM)
        #if !defined(NO_SHA) && defined(WOLFSSL_AES_128)
        {data, (word32)sizeof(data), DATA, AES128GCMb, AES128_WRAP,
         dhSinglePass_stdDH_sha1kdf_scheme, eccCert, eccCertSz, eccPrivKey,
         eccPrivKeySz, NULL, 0, NULL, 0, NULL, 0, 0, 0, NULL, 0, NULL, 0,
         NULL, NULL, 0, NULL, 0, 0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0, 0, 0,
         "pkcs7authEnvelopedDataAES128GCM_ECDH_SHA1KDF.der"},
        #endif

        #if !defined(NO_SHA256) && defined(WOLFSSL_AES_256)
        {data, (word32)sizeof(data), DATA, AES256GCMb, AES256_WRAP,
         dhSinglePass_stdDH_sha256kdf_scheme, eccCert, eccCertSz, eccPrivKey,
         eccPrivKeySz, NULL, 0, NULL, 0, NULL, 0, 0, 0, NULL, 0, NULL, 0,
         NULL, NULL, 0, NULL, 0, 0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0, 0, 0,
         "pkcs7authEnvelopedDataAES256GCM_ECDH_SHA256KDF.der"},

        /* with authenticated attributes */
        {data, (word32)sizeof(data), DATA, AES256GCMb, AES256_WRAP,
         dhSinglePass_stdDH_sha256kdf_scheme, eccCert, eccCertSz, eccPrivKey,
         eccPrivKeySz, attribs, (sizeof(attribs) / sizeof(PKCS7Attrib)),
         NULL, 0, NULL, 0, 0, 0, NULL, 0,
         NULL, 0, NULL, NULL, 0, NULL, 0, 0, NULL, 0, NULL, 0, 0, 0, 0, 0,
         0, 0, 0,
         "pkcs7authEnvelopedDataAES256GCM_ECDH_SHA256KDF_authAttribs.der"},

        /* with unauthenticated attributes */
        {data, (word32)sizeof(data), DATA, AES256GCMb, AES256_WRAP,
         dhSinglePass_stdDH_sha256kdf_scheme, eccCert, eccCertSz, eccPrivKey,
         eccPrivKeySz, NULL, 0, attribs,
         (sizeof(attribs) / sizeof(PKCS7Attrib)), NULL, 0, 0, 0, NULL, 0,
         NULL, 0, NULL, NULL, 0, NULL, 0, 0, NULL, 0, NULL, 0, 0, 0, 0, 0,
         0, 0, 0,
         "pkcs7authEnvelopedDataAES256GCM_ECDH_SHA256KDF_unauthAttribs.der"},

        /* with authenticated AND unauthenticated attributes */
        {data, (word32)sizeof(data), DATA, AES256GCMb, AES256_WRAP,
         dhSinglePass_stdDH_sha256kdf_scheme, eccCert, eccCertSz, eccPrivKey,
         eccPrivKeySz, attribs, (sizeof(attribs) / sizeof(PKCS7Attrib)),
         attribs, (sizeof(attribs) / sizeof(PKCS7Attrib)), NULL, 0, 0, 0,
         NULL, 0, NULL, 0, NULL, NULL, 0, NULL, 0, 0, NULL, 0, NULL, 0, 0,
         0, 0, 0, 0, 0, 0,
         "pkcs7authEnvelopedDataAES256GCM_ECDH_SHA256KDF_bothAttribs.der"},

        /* with authenticated AND unauthenticated attributes AND
         * contentType of FirmwarePkgData */
        {data, (word32)sizeof(data), FIRMWARE_PKG_DATA, AES256GCMb, AES256_WRAP,
         dhSinglePass_stdDH_sha256kdf_scheme, eccCert, eccCertSz, eccPrivKey,
         eccPrivKeySz, attribs, (sizeof(attribs) / sizeof(PKCS7Attrib)),
         attribs, (sizeof(attribs) / sizeof(PKCS7Attrib)), NULL, 0, 0, 0,
         NULL, 0, NULL, 0, NULL, NULL, 0, NULL, 0, 0, NULL, 0, NULL, 0, 0,
         0, 0, 0, 0, 0, 0,
         "pkcs7authEnvelopedDataAES256GCM_ECDH_SHA256KDF_fw_bothAttribs.der"},
        #endif /* NO_SHA256 && WOLFSSL_AES_256 */

        #if defined(WOLFSSL_SHA512) && defined(WOLFSSL_AES_256)
        {data, (word32)sizeof(data), DATA, AES256GCMb, AES256_WRAP,
         dhSinglePass_stdDH_sha512kdf_scheme, eccCert, eccCertSz, eccPrivKey,
         eccPrivKeySz, NULL, 0, NULL, 0, NULL, 0, 0, 0, NULL, 0, NULL, 0, NULL,
         NULL, 0, NULL, 0, 0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0, 0, 0,
         "pkcs7authEnvelopedDataAES256GCM_ECDH_SHA512KDF.der"},

        /* with optional user keying material (ukm) */
        {data, (word32)sizeof(data), DATA, AES256GCMb, AES256_WRAP,
         dhSinglePass_stdDH_sha512kdf_scheme, eccCert, eccCertSz, eccPrivKey,
         eccPrivKeySz, NULL, 0, NULL, 0, optionalUkm, sizeof(optionalUkm), 0,
         0, NULL, 0, NULL, 0, NULL, NULL, 0, NULL, 0, 0, NULL, 0, NULL, 0, 0,
         0, 0, 0, 0, 0, 0,
         "pkcs7authEnvelopedDataAES256GCM_ECDH_SHA512KDF_ukm.der"},
        #endif /* WOLFSSL_SHA512 && WOLFSSL_AES_256 */
    #endif /* NO_AES */
#endif

        /* kekri (KEKRecipientInfo) recipient types */
#if !defined(NO_AES) && defined(HAVE_AESGCM)
        #if !defined(NO_SHA) && defined(WOLFSSL_AES_128)
        {data, (word32)sizeof(data), DATA, AES128GCMb, AES128_WRAP, 0,
         NULL, 0, NULL, 0, NULL, 0, NULL, 0, NULL, 0, 0, 0,
         secretKey, sizeof(secretKey), secretKeyId, sizeof(secretKeyId),
         NULL, NULL, 0, NULL, 0, 0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0, 0, 0,
         "pkcs7authEnvelopedDataAES128GCM_KEKRI.der"},
        #endif
#endif

        /* pwri (PasswordRecipientInfo) recipient types */
#if !defined(NO_PWDBASED) && !defined(NO_AES) && defined(HAVE_AESGCM)
        #if !defined(NO_SHA) && defined(WOLFSSL_AES_128)
        {data, (word32)sizeof(data), DATA, AES128GCMb, 0, 0,
         NULL, 0, NULL, 0, NULL, 0, NULL, 0, NULL, 0, 0, 0, NULL, 0,
         NULL, 0, NULL, NULL, 0, NULL, 0, 0, password,
         (word32)XSTRLEN(password), salt, sizeof(salt), PBKDF2_OID, WC_SHA, 5,
         AES128CBCb, 0, 0, 0, "pkcs7authEnvelopedDataAES128GCM_PWRI.der"},
        #endif
#endif

#if !defined(NO_AES) && defined(HAVE_AESGCM)
        #ifdef WOLFSSL_AES_128
        /* ori (OtherRecipientInfo) recipient types */
        {data, (word32)sizeof(data), DATA, AES128GCMb, 0, 0, NULL, 0, NULL, 0,
         NULL, 0, NULL, 0, NULL, 0, 0, 0, NULL, 0, NULL, 0, NULL, NULL, 0,
         NULL, 0, 0, NULL, 0, NULL, 0, 0, 0, 0, 0, 0, 1, 0,
         "pkcs7authEnvelopedDataAES128GCM_ORI.der"},
        #endif
#endif
    };

    testSz = sizeof(testVectors) / sizeof(pkcs7AuthEnvelopedVector);


    /* generate senderNonce */
    {
#ifndef HAVE_FIPS
        ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
        ret = wc_InitRng(&rng);
#endif
        if (ret != 0) {
            return -11805;
        }

        senderNonce[0] = 0x04;
        senderNonce[1] = PKCS7_NONCE_SZ;

        ret = wc_RNG_GenerateBlock(&rng, &senderNonce[2], PKCS7_NONCE_SZ);
        if (ret != 0) {
            wc_FreeRng(&rng);
            return -11806;
        }
    }

    for (i = 0; i < testSz; i++) {
        pkcs7 = wc_PKCS7_New(HEAP_HINT,
        #ifdef WOLFSSL_ASYNC_CRYPT
            INVALID_DEVID /* async PKCS7 is not supported */
        #else
            devId
        #endif
        );
        if (pkcs7 == NULL)
            return -11807;

        if (testVectors[i].secretKey != NULL) {
            /* KEKRI recipient type */

            ret = wc_PKCS7_Init(pkcs7, pkcs7->heap, pkcs7->devId);
            if (ret != 0) {
                return -11808;
            }

            pkcs7->content         = (byte*)testVectors[i].content;
            pkcs7->contentSz       = testVectors[i].contentSz;
            pkcs7->contentOID      = testVectors[i].contentOID;
            pkcs7->encryptOID      = testVectors[i].encryptOID;
            pkcs7->ukm             = testVectors[i].optionalUkm;
            pkcs7->ukmSz           = testVectors[i].optionalUkmSz;
            pkcs7->authAttribs     = testVectors[i].authAttribs;
            pkcs7->authAttribsSz   = testVectors[i].authAttribsSz;
            pkcs7->unauthAttribs   = testVectors[i].unauthAttribs;
            pkcs7->unauthAttribsSz = testVectors[i].unauthAttribsSz;

            ret = wc_PKCS7_AddRecipient_KEKRI(pkcs7, testVectors[i].keyWrapOID,
                    testVectors[i].secretKey, testVectors[i].secretKeySz,
                    testVectors[i].secretKeyId, testVectors[i].secretKeyIdSz,
                    testVectors[i].timePtr, testVectors[i].otherAttrOID,
                    testVectors[i].otherAttrOIDSz, testVectors[i].otherAttr,
                    testVectors[i].otherAttrSz, testVectors[i].kekriOptions);

            if (ret < 0) {
                wc_PKCS7_Free(pkcs7);
                return -11809;
            }

            /* set key, for decryption */
            ret = wc_PKCS7_SetKey(pkcs7, testVectors[i].secretKey,
                                  testVectors[i].secretKeySz);

            if (ret != 0) {
                wc_PKCS7_Free(pkcs7);
                return -11810;
            }

        } else if (testVectors[i].password != NULL) {
        #ifndef NO_PWDBASED
            /* PWRI recipient type */

            ret = wc_PKCS7_Init(pkcs7, pkcs7->heap, pkcs7->devId);
            if (ret != 0) {
                return -11811;
            }

            pkcs7->content         = (byte*)testVectors[i].content;
            pkcs7->contentSz       = testVectors[i].contentSz;
            pkcs7->contentOID      = testVectors[i].contentOID;
            pkcs7->encryptOID      = testVectors[i].encryptOID;
            pkcs7->ukm             = testVectors[i].optionalUkm;
            pkcs7->ukmSz           = testVectors[i].optionalUkmSz;
            pkcs7->authAttribs     = testVectors[i].authAttribs;
            pkcs7->authAttribsSz   = testVectors[i].authAttribsSz;
            pkcs7->unauthAttribs   = testVectors[i].unauthAttribs;
            pkcs7->unauthAttribsSz = testVectors[i].unauthAttribsSz;

            ret = wc_PKCS7_AddRecipient_PWRI(pkcs7,
                    (byte*)testVectors[i].password,
                    testVectors[i].passwordSz, testVectors[i].salt,
                    testVectors[i].saltSz, testVectors[i].kdfOID,
                    testVectors[i].hashOID, testVectors[i].kdfIterations,
                    testVectors[i].kekEncryptOID, testVectors[i].pwriOptions);

            if (ret < 0) {
                wc_PKCS7_Free(pkcs7);
                return -11812;
            }

            /* set password, for decryption */
            ret = wc_PKCS7_SetPassword(pkcs7, (byte*)testVectors[i].password,
                    testVectors[i].passwordSz);

            if (ret < 0) {
                wc_PKCS7_Free(pkcs7);
                return -11813;
            }

        #endif /* NO_PWDBASED */
        } else if (testVectors[i].isOri == 1) {
            /* ORI recipient type */

            ret = wc_PKCS7_Init(pkcs7, pkcs7->heap, pkcs7->devId);
            if (ret != 0) {
                return -11814;
            }

            pkcs7->content         = (byte*)testVectors[i].content;
            pkcs7->contentSz       = testVectors[i].contentSz;
            pkcs7->contentOID      = testVectors[i].contentOID;
            pkcs7->encryptOID      = testVectors[i].encryptOID;
            pkcs7->authAttribs     = testVectors[i].authAttribs;
            pkcs7->authAttribsSz   = testVectors[i].authAttribsSz;
            pkcs7->unauthAttribs   = testVectors[i].unauthAttribs;
            pkcs7->unauthAttribsSz = testVectors[i].unauthAttribsSz;

            ret = wc_PKCS7_AddRecipient_ORI(pkcs7, myOriEncryptCb,
                                            testVectors[i].oriOptions);

            if (ret < 0) {
                wc_PKCS7_Free(pkcs7);
                return -11815;
            }

            /* set decrypt callback for decryption */
            ret = wc_PKCS7_SetOriDecryptCb(pkcs7, myOriDecryptCb);

            if (ret < 0) {
                wc_PKCS7_Free(pkcs7);
                return -11816;
            }

        } else {
            /* KTRI or KARI recipient types */

            ret = wc_PKCS7_InitWithCert(pkcs7, testVectors[i].cert,
                                        (word32)testVectors[i].certSz);
            if (ret != 0) {
                wc_PKCS7_Free(pkcs7);
                return -11817;
            }

            pkcs7->keyWrapOID      = testVectors[i].keyWrapOID;
            pkcs7->keyAgreeOID     = testVectors[i].keyAgreeOID;
            pkcs7->privateKey      = testVectors[i].privateKey;
            pkcs7->privateKeySz    = testVectors[i].privateKeySz;
            pkcs7->content         = (byte*)testVectors[i].content;
            pkcs7->contentSz       = testVectors[i].contentSz;
            pkcs7->contentOID      = testVectors[i].contentOID;
            pkcs7->encryptOID      = testVectors[i].encryptOID;
            pkcs7->ukm             = testVectors[i].optionalUkm;
            pkcs7->ukmSz           = testVectors[i].optionalUkmSz;
            pkcs7->authAttribs     = testVectors[i].authAttribs;
            pkcs7->authAttribsSz   = testVectors[i].authAttribsSz;
            pkcs7->unauthAttribs   = testVectors[i].unauthAttribs;
            pkcs7->unauthAttribsSz = testVectors[i].unauthAttribsSz;

            /* set SubjectIdentifier type for KTRI types */
            if (testVectors[i].ktriOptions & CMS_SKID) {

                ret = wc_PKCS7_SetSignerIdentifierType(pkcs7, CMS_SKID);
                if (ret != 0) {
                    wc_PKCS7_Free(pkcs7);
                    return -11818;
                }
            } else if (testVectors[i].ktriOptions &
                       CMS_ISSUER_AND_SERIAL_NUMBER) {

                ret = wc_PKCS7_SetSignerIdentifierType(pkcs7,
                        CMS_ISSUER_AND_SERIAL_NUMBER);
                if (ret != 0) {
                    wc_PKCS7_Free(pkcs7);
                    return -11819;
                }
            }
        }

#ifdef ECC_TIMING_RESISTANT
        pkcs7->rng = &rng;
#endif

        /* encode envelopedData */
        envelopedSz = wc_PKCS7_EncodeAuthEnvelopedData(pkcs7, enveloped,
                                                       sizeof(enveloped));
        if (envelopedSz <= 0) {
            wc_PKCS7_Free(pkcs7);
            return -11820;
        }
#ifndef NO_PKCS7_STREAM
        { /* test reading byte by byte */
            int z;
            for (z = 0; z < envelopedSz; z++) {
                decodedSz = wc_PKCS7_DecodeAuthEnvelopedData(pkcs7,
                        enveloped + z, 1, decoded, sizeof(decoded));
                if (decodedSz <= 0 && decodedSz != WC_PKCS7_WANT_READ_E) {
                    printf("unexpected error %d\n", decodedSz);
                    return -11821;
                }
            }
            /* test decode result */
            if (XMEMCMP(decoded, data, sizeof(data)) != 0) {
                printf("stream read compare failed\n");
                wc_PKCS7_Free(pkcs7);
                return -11822;
            }
        }
#endif
        /* decode envelopedData */
        decodedSz = wc_PKCS7_DecodeAuthEnvelopedData(pkcs7, enveloped,
                                                     envelopedSz, decoded,
                                                     sizeof(decoded));
        if (decodedSz <= 0) {
            wc_PKCS7_Free(pkcs7);
            return -11823;
        }

        /* test decode result */
        if (XMEMCMP(decoded, data, sizeof(data)) != 0){
            wc_PKCS7_Free(pkcs7);
            return -11824;
        }

#ifdef PKCS7_OUTPUT_TEST_BUNDLES
        /* output pkcs7 envelopedData for external testing */
        pkcs7File = XFOPEN(testVectors[i].outFileName, "wb");
        if (!pkcs7File) {
            wc_PKCS7_Free(pkcs7);
            return -11825;
        }

        ret = (int)XFWRITE(enveloped, 1, envelopedSz, pkcs7File);
        XFCLOSE(pkcs7File);
        if (ret != envelopedSz) {
            wc_PKCS7_Free(pkcs7);
            return -11826;
        }
#endif /* PKCS7_OUTPUT_TEST_BUNDLES */

        wc_PKCS7_Free(pkcs7);
        pkcs7 = NULL;
    }

    wc_FreeRng(&rng);

#if !defined(HAVE_ECC) || defined(NO_AES)
    (void)eccCert;
    (void)eccCertSz;
    (void)eccPrivKey;
    (void)eccPrivKeySz;
    (void)secretKey;
    (void)secretKeyId;
#endif
#ifdef NO_RSA
    (void)rsaCert;
    (void)rsaCertSz;
    (void)rsaPrivKey;
    (void)rsaPrivKeySz;
#endif
    return 0;
}


int pkcs7authenveloped_test(void)
{
    int ret = 0;

    byte* rsaCert    = NULL;
    byte* rsaPrivKey = NULL;
    word32 rsaCertSz    = 0;
    word32 rsaPrivKeySz = 0;

    byte* eccCert    = NULL;
    byte* eccPrivKey = NULL;
    word32 eccCertSz    = 0;
    word32 eccPrivKeySz = 0;

#ifndef NO_RSA
    /* read client RSA cert and key in DER format */
    rsaCert = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (rsaCert == NULL)
        return -11900;

    rsaPrivKey = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (rsaPrivKey == NULL) {
        XFREE(rsaCert, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        return -11901;
    }

    rsaCertSz = FOURK_BUF;
    rsaPrivKeySz = FOURK_BUF;
#endif /* NO_RSA */

#ifdef HAVE_ECC
    /* read client ECC cert and key in DER format */
    eccCert = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (eccCert == NULL) {
    #ifndef NO_RSA
        XFREE(rsaCert,    HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(rsaPrivKey, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        return -11902;
    }

    eccPrivKey =(byte*)XMALLOC(FOURK_BUF, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (eccPrivKey == NULL) {
    #ifndef NO_RSA
        XFREE(rsaCert,    HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(rsaPrivKey, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        XFREE(eccCert,    HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        return -11903;
    }

    eccCertSz = FOURK_BUF;
    eccPrivKeySz = FOURK_BUF;
#endif /* HAVE_ECC */

    ret = pkcs7_load_certs_keys(rsaCert, &rsaCertSz, rsaPrivKey,
                                &rsaPrivKeySz, NULL, NULL, NULL, NULL,
                                NULL, NULL, NULL, NULL, eccCert, &eccCertSz,
                                eccPrivKey, &eccPrivKeySz);
    if (ret < 0) {
    #ifndef NO_RSA
        XFREE(rsaCert,    HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(rsaPrivKey, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
    #ifdef HAVE_ECC
        XFREE(eccCert,    HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(eccPrivKey, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        return -11904;
    }

    ret = pkcs7authenveloped_run_vectors(rsaCert, (word32)rsaCertSz,
                                         rsaPrivKey, (word32)rsaPrivKeySz,
                                         eccCert, (word32)eccCertSz,
                                         eccPrivKey, (word32)eccPrivKeySz);

#ifndef NO_RSA
    XFREE(rsaCert,    HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(rsaPrivKey, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
#endif
#ifdef HAVE_ECC
    XFREE(eccCert,    HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(eccPrivKey, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#endif /* HAVE_AESGCM || HAVE_AESCCM */
#ifndef NO_AES
static const byte p7DefKey[] = {
    0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
    0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
    0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
    0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08
};

static const byte p7AltKey[] = {
    0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
    0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08
};

static int myCEKwrapFunc(PKCS7* pkcs7, byte* cek, word32 cekSz, byte* keyId,
        word32 keyIdSz, byte* orginKey, word32 orginKeySz,
        byte* out, word32 outSz, int keyWrapAlgo, int type, int direction)
{
    int ret;

    if (cek == NULL || out == NULL)
        return BAD_FUNC_ARG;

    /* test case sanity checks */
    if (keyIdSz != 1) {
        return -11905;
    }

    if (keyId[0] != 0x00) {
        return -11906;
    }

    if (type != (int)PKCS7_KEKRI) {
        return -11907;
    }

    switch (keyWrapAlgo) {
        case AES256_WRAP:
            ret = wc_AesKeyUnWrap(p7DefKey, sizeof(p7DefKey), cek, cekSz,
                                      out, outSz, NULL);
            if (ret <= 0)
                return ret;
            break;

        default:
            WOLFSSL_MSG("Unsupported key wrap algorithm in example");
            return BAD_KEYWRAP_ALG_E;
    };

    (void)pkcs7;
    (void)direction;
    (void)orginKey; /* used with KAKRI */
    (void)orginKeySz;
    return ret;
}


/* returns key size on success */
static int getFirmwareKey(PKCS7* pkcs7, byte* key, word32 keySz)
{
    int    ret;
    word32 atrSz;
    byte   atr[256];

    /* Additionally can look for fwWrappedFirmwareKey
     * 1.2.840.113529.1.9.16.1.16 */
    const unsigned char fwWrappedFirmwareKey[] = {
        /* 0x06, 0x0B */
        0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D,
        0x01, 0x09, 0x10, 0x02, 0x27
    };

    /* find keyID in fwWrappedFirmwareKey */
    ret = wc_PKCS7_GetAttributeValue(pkcs7, fwWrappedFirmwareKey,
            sizeof(fwWrappedFirmwareKey), NULL, &atrSz);
    if (ret == LENGTH_ONLY_E) {
        XMEMSET(atr, 0, sizeof(atr));
        ret = wc_PKCS7_GetAttributeValue(pkcs7, fwWrappedFirmwareKey,
                sizeof(fwWrappedFirmwareKey), atr, &atrSz);

        /* keyIdRaw[0] OCTET TAG */
        /* keyIdRaw[1] Length */

        if (ret > 0) {
            PKCS7* envPkcs7;

            envPkcs7 = wc_PKCS7_New(NULL, 0);
            if (envPkcs7 == NULL) {
                return MEMORY_E;
            }

            wc_PKCS7_Init(envPkcs7, NULL, 0);
            ret = wc_PKCS7_SetWrapCEKCb(envPkcs7, myCEKwrapFunc);
            if (ret == 0) {
                /* expecting FIRMWARE_PKG_DATA content */
                envPkcs7->contentOID = FIRMWARE_PKG_DATA;
                ret = wc_PKCS7_DecodeEnvelopedData(envPkcs7, atr, atrSz,
                    key, keySz);
            }
            wc_PKCS7_Free(envPkcs7);
        }
    }

    return ret;
}

/* create a KEKRI enveloped data
 * return size on success */
static int envelopedData_encrypt(byte* in, word32 inSz, byte* out,
        word32 outSz)
{
    int ret;
    PKCS7* pkcs7;
    const byte keyId[] = { 0x00 };

    pkcs7 = wc_PKCS7_New(NULL, INVALID_DEVID);
    if (pkcs7 == NULL)
        return -11908;

    pkcs7->content     = in;
    pkcs7->contentSz   = inSz;
    pkcs7->contentOID  = FIRMWARE_PKG_DATA;
    pkcs7->encryptOID  = AES256CBCb;
    pkcs7->ukm         = NULL;
    pkcs7->ukmSz       = 0;

    /* add recipient (KEKRI type) */
    ret = wc_PKCS7_AddRecipient_KEKRI(pkcs7, AES256_WRAP, (byte*)p7DefKey,
                                      sizeof(p7DefKey), (byte*)keyId,
                                      sizeof(keyId), NULL, NULL, 0, NULL, 0, 0);
    if (ret < 0) {
        printf("wc_PKCS7_AddRecipient_KEKRI() failed, ret = %d\n", ret);
        wc_PKCS7_Free(pkcs7);
        return -11909;
    }

    /* encode envelopedData, returns size */
    ret = wc_PKCS7_EncodeEnvelopedData(pkcs7, out, outSz);
    if (ret <= 0) {
        printf("wc_PKCS7_EncodeEnvelopedData() failed, ret = %d\n", ret);
        wc_PKCS7_Free(pkcs7);
        return -11910;

    }

    wc_PKCS7_Free(pkcs7);

    return ret;
}


/*
 * keyHint is the KeyID to be set in the fwDecryptKeyID attribute
 * returns size of buffer output on success
 */
static int generateBundle(byte* out, word32 *outSz, const byte* encryptKey,
        word32 encryptKeySz, byte keyHint, byte* cert, word32 certSz,
        byte* key, word32 keySz)
{
    int ret, attribNum = 1;
    PKCS7* pkcs7;

    /* KEY ID
     * fwDecryptKeyID OID 1.2.840.113549.1.9.16.2.37
     */
    const unsigned char fwDecryptKeyID[] = {
        0x06, 0x0B,
        0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D,
        0x01, 0x09, 0x10, 0x02, 0x25
    };

    /* fwWrappedFirmwareKey 1.2.840.113529.1.9.16.1.16 */
    const unsigned char fwWrappedFirmwareKey[] = {
        0x06, 0x0B, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D,
        0x01, 0x09, 0x10, 0x02, 0x27
    };

    byte keyID[] = { 0x04, 0x01, 0x00 };
    byte env[256];
    char data[] = "Test of wolfSSL PKCS7 decrypt callback";

    PKCS7Attrib attribs[] =
    {
        { fwDecryptKeyID, sizeof(fwDecryptKeyID), keyID, sizeof(keyID) },
        { fwWrappedFirmwareKey, sizeof(fwWrappedFirmwareKey), env, 0 }
    };

    keyID[2] = keyHint;

    /* If using keyHint 0 then create a bundle with fwWrappedFirmwareKey */
    if (keyHint == 0) {
        ret = envelopedData_encrypt((byte*)p7DefKey, sizeof(p7DefKey), env,
                sizeof(env));
        if (ret <= 0) {
            return ret;
        }
        attribs[1].valueSz = ret;
        attribNum++;
    }

    /* init PKCS7 */
    pkcs7 = wc_PKCS7_New(NULL, INVALID_DEVID);
    if (pkcs7 == NULL)
        return -11911;

    ret = wc_PKCS7_InitWithCert(pkcs7, cert, certSz);
    if (ret != 0) {
        printf("ERROR: wc_PKCS7_InitWithCert() failed, ret = %d\n", ret);
        wc_PKCS7_Free(pkcs7);
        return -11912;
    }

    ret = wc_PKCS7_SetSignerIdentifierType(pkcs7, CMS_SKID);
    if (ret != 0) {
        wc_PKCS7_Free(pkcs7);
        return -11913;
    }

    /* encode Signed Encrypted FirmwarePkgData */
    if (encryptKeySz == 16) {
        ret = wc_PKCS7_EncodeSignedEncryptedFPD(pkcs7, (byte*)encryptKey,
                encryptKeySz, key, keySz, AES128CBCb, RSAk, SHA256h,
                (byte*)data, sizeof(data), NULL, 0,
                attribs, attribNum, out, *outSz);
    }
    else {
        ret = wc_PKCS7_EncodeSignedEncryptedFPD(pkcs7, (byte*)encryptKey,
                encryptKeySz, key, keySz, AES256CBCb, RSAk, SHA256h,
                (byte*)data, sizeof(data), NULL, 0,
                attribs, attribNum, out, *outSz);
    }
    if (ret <= 0) {
        printf("ERROR: wc_PKCS7_EncodeSignedEncryptedFPD() failed, "
                "ret = %d\n", ret);
        wc_PKCS7_Free(pkcs7);
        return -11914;

    } else {
        *outSz = ret;
    }

    wc_PKCS7_Free(pkcs7);

    return ret;
}


/* test verification and decryption of PKCS7 bundle
 * return 0 on success
 */
static int verifyBundle(byte* derBuf, word32 derSz, int keyHint)
{
    int ret = 0;
    int usrCtx = 1; /* test value to pass as user context to callback */
    PKCS7* pkcs7;
    byte*  sid;
    word32 sidSz;
    byte key[256];
    word32 keySz = sizeof(key);

    byte decoded[FOURK_BUF/2];
    int  decodedSz = FOURK_BUF/2;

    const byte expectedSid[] = {
        0x33, 0xD8, 0x45, 0x66, 0xD7, 0x68, 0x87, 0x18,
        0x7E, 0x54, 0x0D, 0x70, 0x27, 0x91, 0xC7, 0x26,
        0xD7, 0x85, 0x65, 0xC0
    };

    pkcs7 = wc_PKCS7_New(HEAP_HINT, INVALID_DEVID);
    if (pkcs7 == NULL) {
        return MEMORY_E;
    }

    /* Test verify */
    ret = wc_PKCS7_Init(pkcs7, HEAP_HINT, INVALID_DEVID);
    if (ret != 0) {
        wc_PKCS7_Free(pkcs7);
        return ret;
    }
    ret = wc_PKCS7_InitWithCert(pkcs7, NULL, 0);
    if (ret != 0) {
        wc_PKCS7_Free(pkcs7);
        return ret;
    }
    ret = wc_PKCS7_VerifySignedData(pkcs7, derBuf, derSz);
    if (ret != 0) {
        wc_PKCS7_Free(pkcs7);
        return ret;
    }

    /* Get size of SID and print it out */
    ret = wc_PKCS7_GetSignerSID(pkcs7, NULL, &sidSz);
    if (ret != LENGTH_ONLY_E) {
        wc_PKCS7_Free(pkcs7);
        return ret;
    }

    sid = (byte*)XMALLOC(sidSz, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (sid == NULL) {
        wc_PKCS7_Free(pkcs7);
        return ret;
    }

    ret = wc_PKCS7_GetSignerSID(pkcs7, sid, &sidSz);
    if (ret != 0) {
        wc_PKCS7_Free(pkcs7);
        XFREE(sid, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        return ret;
    }
    ret = XMEMCMP(sid, expectedSid, sidSz);
    XFREE(sid, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (ret != 0) {
        wc_PKCS7_Free(pkcs7);
        return ret;
    }

    /* get expected fwWrappedFirmwareKey */
    if (keyHint == 0) {
        ret = getFirmwareKey(pkcs7, key, keySz);
        if (ret < 0) {
            wc_PKCS7_Free(pkcs7);
            return ret;
        }
        pkcs7->encryptionKey = key;
        pkcs7->encryptionKeySz = ret;
    }
    else {
        decodedSz = sizeof(decoded);
        ret = wc_PKCS7_SetDecodeEncryptedCb(pkcs7, myDecryptionFunc);
        if (ret != 0) {
            wc_PKCS7_Free(pkcs7);
            return ret;
        }

        ret = wc_PKCS7_SetDecodeEncryptedCtx(pkcs7, (void*)&usrCtx);
        if (ret != 0) {
            wc_PKCS7_Free(pkcs7);
            return ret;
        }
    }

    decodedSz = wc_PKCS7_DecodeEncryptedData(pkcs7, pkcs7->content,
            pkcs7->contentSz, decoded, decodedSz);
    if (decodedSz < 0) {
        ret = decodedSz;
        wc_PKCS7_Free(pkcs7);
        return ret;
    }

    wc_PKCS7_Free(pkcs7);
    return 0;
}


int pkcs7callback_test(byte* cert, word32 certSz, byte* key, word32 keySz)
{

    int ret = 0;
    byte derBuf[FOURK_BUF];
    word32 derSz = sizeof(derBuf);

    /* Doing default generation and verify */
    ret = generateBundle(derBuf, &derSz, p7DefKey, sizeof(p7DefKey), 0, cert,
            certSz, key, keySz);
    if (ret <= 0) {
        return -11915;
    }

    ret = verifyBundle(derBuf, derSz, 0);
    if (ret != 0) {
        return -11916;
    }

    /* test choosing other key with keyID */
    derSz = sizeof(derBuf);
    ret = generateBundle(derBuf, &derSz, p7AltKey, sizeof(p7AltKey), 1,
            cert, certSz, key, keySz);
    if (ret <= 0) {
        return -11917;
    }

    ret = verifyBundle(derBuf, derSz, 1);
    if (ret != 0) {
        return -11918;
    }

    /* test fail case with wrong keyID */
    derSz = sizeof(derBuf);
    ret = generateBundle(derBuf, &derSz, p7DefKey, sizeof(p7DefKey), 1,
            cert, certSz, key, keySz);
    if (ret <= 0) {
        return -11919;
    }

    ret = verifyBundle(derBuf, derSz, 1);
    if (ret == 0) {
        return -11920;
    }

    return 0;
}
#endif /* NO_AES */

#ifndef NO_PKCS7_ENCRYPTED_DATA

typedef struct {
    const byte*  content;
    word32       contentSz;
    int          contentOID;
    int          encryptOID;
    byte*        encryptionKey;
    word32       encryptionKeySz;
    PKCS7Attrib* attribs;
    word32       attribsSz;
    const char*  outFileName;
} pkcs7EncryptedVector;


int pkcs7encrypted_test(void)
{
    int ret = 0;
    int i, testSz;
    int encryptedSz, decodedSz, attribIdx;
    PKCS7* pkcs7;
    byte  encrypted[2048];
    byte  decoded[2048];
#ifdef PKCS7_OUTPUT_TEST_BUNDLES
    XFILE pkcs7File;
#endif

    PKCS7Attrib* expectedAttrib;
    PKCS7DecodedAttrib* decodedAttrib;

    const byte data[] = { /* Hello World */
        0x48,0x65,0x6c,0x6c,0x6f,0x20,0x57,0x6f,
        0x72,0x6c,0x64
    };

#ifndef NO_DES3
    byte desKey[] = {
        0x01,0x23,0x45,0x67,0x89,0xab,0xcd,0xef
    };
    byte des3Key[] = {
        0x01,0x23,0x45,0x67,0x89,0xab,0xcd,0xef,
        0xfe,0xde,0xba,0x98,0x76,0x54,0x32,0x10,
        0x89,0xab,0xcd,0xef,0x01,0x23,0x45,0x67
    };
#endif

#ifndef NO_AES
#ifdef WOLFSSL_AES_128
    byte aes128Key[] = {
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08
    };
#endif
#ifdef WOLFSSL_AES_192
    byte aes192Key[] = {
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08
    };
#endif
#ifdef WOLFSSL_AES_256
    byte aes256Key[] = {
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08
    };
#endif

#ifdef WOLFSSL_AES_256
    /* Attribute example from RFC 4134, Section 7.2
     * OID = 1.2.5555
     * OCTET STRING = 'This is a test General ASN Attribute, number 1.' */
    static byte genAttrOid[] = { 0x06, 0x03, 0x2a, 0xab, 0x33 };
    static byte genAttr[] = { 0x04, 47,
                              0x54, 0x68, 0x69, 0x73, 0x20, 0x69, 0x73, 0x20,
                              0x61, 0x20, 0x74, 0x65, 0x73, 0x74, 0x20, 0x47,
                              0x65, 0x6e, 0x65, 0x72, 0x61, 0x6c, 0x20, 0x41,
                              0x53, 0x4e, 0x20, 0x41, 0x74, 0x74, 0x72, 0x69,
                              0x62, 0x75, 0x74, 0x65, 0x2c, 0x20, 0x6e, 0x75,
                              0x6d, 0x62, 0x65, 0x72, 0x20, 0x31, 0x2e };

    static byte genAttrOid2[] = { 0x06, 0x03, 0x2a, 0xab, 0x34 };
    static byte genAttr2[] = { 0x04, 47,
                              0x54, 0x68, 0x69, 0x73, 0x20, 0x69, 0x73, 0x20,
                              0x61, 0x20, 0x74, 0x65, 0x73, 0x74, 0x20, 0x47,
                              0x65, 0x6e, 0x65, 0x72, 0x61, 0x6c, 0x20, 0x41,
                              0x53, 0x4e, 0x20, 0x41, 0x74, 0x74, 0x72, 0x69,
                              0x62, 0x75, 0x74, 0x65, 0x2c, 0x20, 0x6e, 0x75,
                              0x6d, 0x62, 0x65, 0x72, 0x20, 0x32, 0x2e };

    PKCS7Attrib attribs[] =
    {
        { genAttrOid, sizeof(genAttrOid), genAttr, sizeof(genAttr) }
    };

    PKCS7Attrib multiAttribs[] =
    {
        { genAttrOid, sizeof(genAttrOid), genAttr, sizeof(genAttr) },
        { genAttrOid2, sizeof(genAttrOid2), genAttr2, sizeof(genAttr2) }
    };
#endif
#endif /* NO_AES */

    const pkcs7EncryptedVector testVectors[] =
    {
#ifndef NO_DES3
        {data, (word32)sizeof(data), DATA, DES3b, des3Key, sizeof(des3Key),
         NULL, 0, "pkcs7encryptedDataDES3.der"},

        {data, (word32)sizeof(data), DATA, DESb, desKey, sizeof(desKey),
         NULL, 0, "pkcs7encryptedDataDES.der"},
#endif /* NO_DES3 */

#ifndef NO_AES
    #ifdef WOLFSSL_AES_128
        {data, (word32)sizeof(data), DATA, AES128CBCb, aes128Key,
         sizeof(aes128Key), NULL, 0, "pkcs7encryptedDataAES128CBC.der"},
    #endif
    #ifdef WOLFSSL_AES_192
        {data, (word32)sizeof(data), DATA, AES192CBCb, aes192Key,
         sizeof(aes192Key), NULL, 0, "pkcs7encryptedDataAES192CBC.der"},
    #endif
    #ifdef WOLFSSL_AES_256
        {data, (word32)sizeof(data), DATA, AES256CBCb, aes256Key,
         sizeof(aes256Key), NULL, 0, "pkcs7encryptedDataAES256CBC.der"},

        /* test with optional unprotected attributes */
        {data, (word32)sizeof(data), DATA, AES256CBCb, aes256Key,
         sizeof(aes256Key), attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7encryptedDataAES256CBC_attribs.der"},

        /* test with multiple optional unprotected attributes */
        {data, (word32)sizeof(data), DATA, AES256CBCb, aes256Key,
         sizeof(aes256Key), multiAttribs,
         (sizeof(multiAttribs)/sizeof(PKCS7Attrib)),
         "pkcs7encryptedDataAES256CBC_multi_attribs.der"},

        /* test with contentType set to FirmwarePkgData */
        {data, (word32)sizeof(data), FIRMWARE_PKG_DATA, AES256CBCb, aes256Key,
         sizeof(aes256Key), NULL, 0,
         "pkcs7encryptedDataAES256CBC_firmwarePkgData.der"},
    #endif
#endif /* NO_AES */
    };

    testSz = sizeof(testVectors) / sizeof(pkcs7EncryptedVector);

    for (i = 0; i < testSz; i++) {
        pkcs7 = wc_PKCS7_New(HEAP_HINT, devId);
        if (pkcs7 == NULL)
            return -12000;

        pkcs7->content              = (byte*)testVectors[i].content;
        pkcs7->contentSz            = testVectors[i].contentSz;
        pkcs7->contentOID           = testVectors[i].contentOID;
        pkcs7->encryptOID           = testVectors[i].encryptOID;
        pkcs7->encryptionKey        = testVectors[i].encryptionKey;
        pkcs7->encryptionKeySz      = testVectors[i].encryptionKeySz;
        pkcs7->unprotectedAttribs   = testVectors[i].attribs;
        pkcs7->unprotectedAttribsSz = testVectors[i].attribsSz;

        /* encode encryptedData */
        encryptedSz = wc_PKCS7_EncodeEncryptedData(pkcs7, encrypted,
                                                   sizeof(encrypted));
        if (encryptedSz <= 0) {
            wc_PKCS7_Free(pkcs7);
            return -12001;
        }

        /* decode encryptedData */
#ifndef NO_PKCS7_STREAM
        { /* test reading byte by byte */
            int z;
            for (z = 0; z < encryptedSz; z++) {
                decodedSz = wc_PKCS7_DecodeEncryptedData(pkcs7, encrypted + z, 1,
                                                 decoded, sizeof(decoded));
                if (decodedSz <= 0 && decodedSz != WC_PKCS7_WANT_READ_E) {
                    printf("unexpected error %d\n", decodedSz);
                    return -12002;
                }
            }
            /* test decode result */
            if (XMEMCMP(decoded, data, sizeof(data)) != 0) {
                printf("stream read failed\n");
                wc_PKCS7_Free(pkcs7);
                return -12003;
            }
        }
#endif
        decodedSz = wc_PKCS7_DecodeEncryptedData(pkcs7, encrypted, encryptedSz,
                                                 decoded, sizeof(decoded));
        if (decodedSz <= 0){
            wc_PKCS7_Free(pkcs7);
            return -12004;
        }

        /* test decode result */
        if (XMEMCMP(decoded, data, sizeof(data)) != 0) {
            wc_PKCS7_Free(pkcs7);
            return -12005;
        }

        /* verify decoded unprotected attributes */
        if (pkcs7->decodedAttrib != NULL) {
            decodedAttrib = pkcs7->decodedAttrib;
            attribIdx = 1;

            while (decodedAttrib != NULL) {

                /* expected attribute, stored list is reversed */
                expectedAttrib = &(pkcs7->unprotectedAttribs
                        [pkcs7->unprotectedAttribsSz - attribIdx]);

                /* verify oid */
                if (XMEMCMP(decodedAttrib->oid, expectedAttrib->oid,
                            decodedAttrib->oidSz) != 0) {
                    wc_PKCS7_Free(pkcs7);
                    return -12006;
                }

                /* verify value */
                if (XMEMCMP(decodedAttrib->value, expectedAttrib->value,
                            decodedAttrib->valueSz) != 0) {
                    wc_PKCS7_Free(pkcs7);
                    return -12007;
                }

                decodedAttrib = decodedAttrib->next;
                attribIdx++;
            }
        }

#ifdef PKCS7_OUTPUT_TEST_BUNDLES
        /* output pkcs7 envelopedData for external testing */
        pkcs7File = XFOPEN(testVectors[i].outFileName, "wb");
        if (!pkcs7File) {
            wc_PKCS7_Free(pkcs7);
            return -12008;
        }

        ret = (int)XFWRITE(encrypted, encryptedSz, 1, pkcs7File);
        XFCLOSE(pkcs7File);

        if (ret > 0)
            ret = 0;
#endif

        wc_PKCS7_Free(pkcs7);
    }

    return ret;
}

#endif /* NO_PKCS7_ENCRYPTED_DATA */


#if defined(HAVE_LIBZ) && !defined(NO_PKCS7_COMPRESSED_DATA)

typedef struct {
    const byte*  content;
    word32       contentSz;
    int          contentOID;
    const char*  outFileName;
} pkcs7CompressedVector;


int pkcs7compressed_test(void)
{
    int ret = 0;
    int i, testSz;
    int compressedSz, decodedSz;
    PKCS7* pkcs7;
    byte  compressed[2048];
    byte  decoded[2048];
#ifdef PKCS7_OUTPUT_TEST_BUNDLES
    XFILE pkcs7File;
#endif

    const byte data[] = { /* Hello World */
        0x48,0x65,0x6c,0x6c,0x6f,0x20,0x57,0x6f,
        0x72,0x6c,0x64
    };

    const pkcs7CompressedVector testVectors[] =
    {
        {data, (word32)sizeof(data), DATA,
            "pkcs7compressedData_data_zlib.der"},
        {data, (word32)sizeof(data), FIRMWARE_PKG_DATA,
            "pkcs7compressedData_firmwarePkgData_zlib.der"},
    };

    testSz = sizeof(testVectors) / sizeof(pkcs7CompressedVector);

    for (i = 0; i < testSz; i++) {
        pkcs7 = wc_PKCS7_New(HEAP_HINT, devId);
        if (pkcs7 == NULL)
            return -12100;

        pkcs7->content              = (byte*)testVectors[i].content;
        pkcs7->contentSz            = testVectors[i].contentSz;
        pkcs7->contentOID           = testVectors[i].contentOID;

        /* encode compressedData */
        compressedSz = wc_PKCS7_EncodeCompressedData(pkcs7, compressed,
                                                   sizeof(compressed));
        if (compressedSz <= 0) {
            wc_PKCS7_Free(pkcs7);
            return -12101;
        }

        /* decode compressedData */
        decodedSz = wc_PKCS7_DecodeCompressedData(pkcs7, compressed,
                                                  compressedSz, decoded,
                                                  sizeof(decoded));
        if (decodedSz <= 0){
            wc_PKCS7_Free(pkcs7);
            return -12102;
        }

        /* test decode result */
        if (XMEMCMP(decoded, testVectors[i].content,
                    testVectors[i].contentSz) != 0) {
            wc_PKCS7_Free(pkcs7);
            return -12103;
        }

        /* make sure content type is the same */
        if (testVectors[i].contentOID != pkcs7->contentOID)
            return -12104;

#ifdef PKCS7_OUTPUT_TEST_BUNDLES
        /* output pkcs7 compressedData for external testing */
        pkcs7File = XFOPEN(testVectors[i].outFileName, "wb");
        if (!pkcs7File) {
            wc_PKCS7_Free(pkcs7);
            return -12105;
        }

        ret = (int)XFWRITE(compressed, compressedSz, 1, pkcs7File);
        XFCLOSE(pkcs7File);

        if (ret > 0)
            ret = 0;
#endif

        wc_PKCS7_Free(pkcs7);
    }

    return ret;
} /* pkcs7compressed_test() */

#endif /* HAVE_LIBZ */


typedef struct {
    const byte*  content;
    word32       contentSz;
    int          hashOID;
    int          signOID;
    byte*        privateKey;
    word32       privateKeySz;
    byte*        cert;
    size_t       certSz;
    byte*        caCert;
    size_t       caCertSz;
    PKCS7Attrib* signedAttribs;
    word32       signedAttribsSz;
    const char*  outFileName;
    int          contentOID;
    byte*        contentType;
    word32       contentTypeSz;
    int          sidType;
    int          encryptOID;   /* for single-shot encrypt alg OID */
    int          encCompFlag;  /* for single-shot. 1 = enc, 2 = comp, 3 = both*/
    byte*        encryptKey;   /* for single-shot, encryptedData */
    word32       encryptKeySz; /* for single-shot, encryptedData */
    PKCS7Attrib* unprotectedAttribs;   /* for single-shot, encryptedData */
    word32       unprotectedAttribsSz; /* for single-shot, encryptedData */
    word16       detachedSignature;    /* generate detached signature (0:1) */
} pkcs7SignedVector;


static int pkcs7signed_run_vectors(
                        byte* rsaClientCertBuf, word32 rsaClientCertBufSz,
                        byte* rsaClientPrivKeyBuf, word32 rsaClientPrivKeyBufSz,
                        byte* rsaServerCertBuf, word32 rsaServerCertBufSz,
                        byte* rsaServerPrivKeyBuf, word32 rsaServerPrivKeyBufSz,
                        byte* rsaCaCertBuf, word32 rsaCaCertBufSz,
                        byte* rsaCaPrivKeyBuf, word32 rsaCaPrivKeyBufSz,
                        byte* eccClientCertBuf, word32 eccClientCertBufSz,
                        byte* eccClientPrivKeyBuf, word32 eccClientPrivKeyBufSz)
{
    int ret, testSz, i;
    int encodedSz;
    byte*  out;
    word32 outSz;
    WC_RNG rng;
    PKCS7* pkcs7;
#ifdef PKCS7_OUTPUT_TEST_BUNDLES
    XFILE  file;
#endif

    const byte data[] = { /* Hello World */
        0x48,0x65,0x6c,0x6c,0x6f,0x20,0x57,0x6f,
        0x72,0x6c,0x64
    };

    static byte transIdOid[] =
               { 0x06, 0x0a, 0x60, 0x86, 0x48, 0x01, 0x86, 0xF8, 0x45, 0x01,
                 0x09, 0x07 };
    static byte messageTypeOid[] =
               { 0x06, 0x0a, 0x60, 0x86, 0x48, 0x01, 0x86, 0xF8, 0x45, 0x01,
                 0x09, 0x02 };
    static byte senderNonceOid[] =
               { 0x06, 0x0a, 0x60, 0x86, 0x48, 0x01, 0x86, 0xF8, 0x45, 0x01,
                 0x09, 0x05 };
#ifndef NO_SHA
    static byte transId[(WC_SHA_DIGEST_SIZE + 1) * 2 + 1];
#else
    static byte transId[(WC_SHA256_DIGEST_SIZE + 1) * 2 + 1];
#endif
    static byte messageType[] = { 0x13, 2, '1', '9' };
    static byte senderNonce[PKCS7_NONCE_SZ + 2];

    PKCS7Attrib attribs[] =
    {
        { transIdOid, sizeof(transIdOid), transId,
                               sizeof(transId) - 1 }, /* take off the null */
        { messageTypeOid, sizeof(messageTypeOid), messageType,
                                       sizeof(messageType) },
        { senderNonceOid, sizeof(senderNonceOid), senderNonce,
                                       sizeof(senderNonce) }
    };

    /* for testing custom contentType, FirmwarePkgData */
    byte customContentType[] = { 0x06, 0x0B, 0x2A, 0x86,
                                 0x48, 0x86, 0xF7, 0x0D,
                                 0x01, 0x09, 0x10, 0x01, 0x10 };

    const pkcs7SignedVector testVectors[] =
    {
#ifndef NO_RSA
    #ifndef NO_SHA
        /* RSA with SHA */
        {data, (word32)sizeof(data), SHAh, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_RSA_SHA.der", 0, NULL, 0, 0, 0, 0, NULL, 0, NULL,
         0, 0},

        /* RSA with SHA, no signed attributes */
        {data, (word32)sizeof(data), SHAh, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz,
         NULL, 0, NULL, 0,
         "pkcs7signedData_RSA_SHA_noattr.der", 0, NULL, 0, 0, 0, 0, NULL, 0,
         NULL, 0, 0},
    #endif
    #ifdef WOLFSSL_SHA224
        /* RSA with SHA224 */
        {data, (word32)sizeof(data), SHA224h, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_RSA_SHA224.der", 0, NULL, 0, 0, 0, 0, NULL, 0,
         NULL, 0, 0},
    #endif
    #ifndef NO_SHA256
        /* RSA with SHA256 */
        {data, (word32)sizeof(data), SHA256h, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_RSA_SHA256.der", 0, NULL, 0, 0, 0, 0, NULL, 0,
         NULL, 0, 0},

        /* RSA with SHA256, detached signature */
        {data, (word32)sizeof(data), SHA256h, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_RSA_SHA256_detachedSig.der", 0, NULL, 0, 0, 0, 0,
         NULL, 0, NULL, 0, 1},

        /* RSA with SHA256 and SubjectKeyIdentifier in SignerIdentifier */
        {data, (word32)sizeof(data), SHA256h, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_RSA_SHA256_SKID.der", 0, NULL, 0, CMS_SKID, 0, 0,
        NULL, 0, NULL, 0, 0},

        /* RSA with SHA256 and custom contentType */
        {data, (word32)sizeof(data), SHA256h, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_RSA_SHA256_custom_contentType.der", 0,
         customContentType, sizeof(customContentType), 0, 0, 0, NULL, 0,
         NULL, 0, 0},

        /* RSA with SHA256 and FirmwarePkgData contentType */
        {data, (word32)sizeof(data), SHA256h, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_RSA_SHA256_firmwarePkgData.der",
         FIRMWARE_PKG_DATA, NULL, 0, 0, 0, 0, NULL, 0, NULL, 0, 0},

        /* RSA with SHA256 using server cert and ca cert */
        {data, (word32)sizeof(data), SHA256h, RSAk, rsaServerPrivKeyBuf,
         rsaServerPrivKeyBufSz, rsaServerCertBuf, rsaServerCertBufSz,
         rsaCaCertBuf, rsaCaCertBufSz,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_RSA_SHA256_with_ca_cert.der", 0, NULL, 0, 0, 0, 0,
        NULL, 0, NULL, 0, 0},
    #endif
    #if defined(WOLFSSL_SHA384)
        /* RSA with SHA384 */
        {data, (word32)sizeof(data), SHA384h, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_RSA_SHA384.der", 0, NULL, 0, 0, 0, 0, NULL, 0,
         NULL, 0, 0},
    #endif
    #if defined(WOLFSSL_SHA512)
        /* RSA with SHA512 */
        {data, (word32)sizeof(data), SHA512h, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_RSA_SHA512.der", 0, NULL, 0, 0, 0, 0, NULL, 0,
         NULL, 0, 0},
    #endif
#endif /* NO_RSA */

#ifdef HAVE_ECC
    #ifndef NO_SHA
        /* ECDSA with SHA */
        {data, (word32)sizeof(data), SHAh, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_ECDSA_SHA.der", 0, NULL, 0, 0, 0, 0, NULL, 0,
         NULL, 0, 0},

        /* ECDSA with SHA, no signed attributes */
        {data, (word32)sizeof(data), SHAh, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz,
         NULL, 0, NULL, 0,
         "pkcs7signedData_ECDSA_SHA_noattr.der", 0, NULL, 0, 0, 0, 0, NULL, 0,
         NULL, 0, 0},
    #endif
    #ifdef WOLFSSL_SHA224
        /* ECDSA with SHA224 */
        {data, (word32)sizeof(data), SHA224h, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_ECDSA_SHA224.der", 0, NULL, 0, 0, 0, 0, NULL, 0,
         NULL, 0, 0},
    #endif
    #ifndef NO_SHA256
        /* ECDSA with SHA256 */
        {data, (word32)sizeof(data), SHA256h, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_ECDSA_SHA256.der", 0, NULL, 0, 0, 0, 0, NULL, 0,
         NULL, 0, 0},

        /* ECDSA with SHA256 and SubjectKeyIdentifier in SigherIdentifier */
        {data, (word32)sizeof(data), SHA256h, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_ECDSA_SHA256_SKID.der", 0, NULL, 0, CMS_SKID, 0, 0,
        NULL, 0, NULL, 0, 0},

        /* ECDSA with SHA256 and custom contentType */
        {data, (word32)sizeof(data), SHA256h, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_ECDSA_SHA256_custom_contentType.der", 0,
         customContentType, sizeof(customContentType), 0, 0, 0, NULL, 0,
         NULL, 0, 0},

        /* ECDSA with SHA256 and FirmwarePkgData contentType */
        {data, (word32)sizeof(data), SHA256h, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_ECDSA_SHA256_firmwarePkgData.der",
         FIRMWARE_PKG_DATA, NULL, 0, 0, 0, 0, NULL, 0, NULL, 0, 0},
    #endif
    #ifdef WOLFSSL_SHA384
        /* ECDSA with SHA384 */
        {data, (word32)sizeof(data), SHA384h, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_ECDSA_SHA384.der", 0, NULL, 0, 0, 0, 0, NULL, 0,
         NULL, 0, 0},
    #endif
    #ifdef WOLFSSL_SHA512
        /* ECDSA with SHA512 */
        {data, (word32)sizeof(data), SHA512h, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedData_ECDSA_SHA512.der", 0, NULL, 0, 0, 0, 0, NULL, 0,
         NULL, 0, 0},
    #endif
#endif /* HAVE_ECC */
    };

    testSz = sizeof(testVectors) / sizeof(pkcs7SignedVector);

    outSz = FOURK_BUF;
    out = (byte*)XMALLOC(outSz, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (out == NULL)
        return -12106;

    XMEMSET(out, 0, outSz);

    ret = wc_PKCS7_PadData((byte*)data, sizeof(data), out, outSz, 16);
    if (ret < 0) {
        XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        return -12107;
    }

#ifndef HAVE_FIPS
    ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
    ret = wc_InitRng(&rng);
#endif
    if (ret != 0) {
        XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        return -12108;
    }

    for (i = 0; i < testSz; i++) {
        pkcs7 = wc_PKCS7_New(HEAP_HINT, devId);
        if (pkcs7 == NULL)
            return -12109;

        ret = wc_PKCS7_InitWithCert(pkcs7, testVectors[i].cert,
                                    (word32)testVectors[i].certSz);

        if (ret != 0) {
            XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
            wc_PKCS7_Free(pkcs7);
            return -12110;
        }

        /* load CA certificate, if present */
        if (testVectors[i].caCert != NULL) {
            ret = wc_PKCS7_AddCertificate(pkcs7, testVectors[i].caCert,
                                          (word32)testVectors[i].caCertSz);
            if (ret != 0) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12111;
            }
        }

        pkcs7->rng             = &rng;
        pkcs7->content         = (byte*)testVectors[i].content;
        pkcs7->contentSz       = testVectors[i].contentSz;
        pkcs7->contentOID      = testVectors[i].contentOID;
        pkcs7->hashOID         = testVectors[i].hashOID;
        pkcs7->encryptOID      = testVectors[i].signOID;
        pkcs7->privateKey      = testVectors[i].privateKey;
        pkcs7->privateKeySz    = testVectors[i].privateKeySz;
        pkcs7->signedAttribs   = testVectors[i].signedAttribs;
        pkcs7->signedAttribsSz = testVectors[i].signedAttribsSz;

        /* optional custom contentType, default is DATA,
           overrides contentOID if set */
        if (testVectors[i].contentType != NULL) {
            ret = wc_PKCS7_SetContentType(pkcs7, testVectors[i].contentType,
                                          testVectors[i].contentTypeSz);
            if (ret != 0) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12112;
            }
        }

        /* set SignerIdentifier to use SubjectKeyIdentifier if desired,
           default is IssuerAndSerialNumber */
        if (testVectors[i].sidType == CMS_SKID) {
            ret = wc_PKCS7_SetSignerIdentifierType(pkcs7, CMS_SKID);
            if (ret != 0) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12113;
            }
        }

        /* generate senderNonce */
        {
            senderNonce[0] = 0x04;
            senderNonce[1] = PKCS7_NONCE_SZ;

            ret = wc_RNG_GenerateBlock(&rng, &senderNonce[2], PKCS7_NONCE_SZ);
            if (ret != 0) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12114;
            }
        }

        /* generate transactionID (used with SCEP) */
        {
        #ifndef NO_SHA
            wc_Sha sha;
            byte digest[WC_SHA_DIGEST_SIZE];
        #else
            wc_Sha256 sha;
            byte digest[WC_SHA256_DIGEST_SIZE];
        #endif
            int j,k;

            transId[0] = 0x13;
            transId[1] = sizeof(digest) * 2;

        #ifndef NO_SHA
            ret = wc_InitSha_ex(&sha, HEAP_HINT, devId);
            if (ret != 0) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12115;
            }
            wc_ShaUpdate(&sha, pkcs7->publicKey, pkcs7->publicKeySz);
            wc_ShaFinal(&sha, digest);
            wc_ShaFree(&sha);
        #else
            ret = wc_InitSha256_ex(&sha, HEAP_HINT, devId);
            if (ret != 0) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12116;
            }
            wc_Sha256Update(&sha, pkcs7->publicKey, pkcs7->publicKeySz);
            wc_Sha256Final(&sha, digest);
            wc_Sha256Free(&sha);
        #endif

            for (j = 0, k = 2; j < (int)sizeof(digest); j++, k += 2) {
                XSNPRINTF((char*)&transId[k], 3, "%02x", digest[j]);
            }
        }

        /* enable detached signature generation, if set */
        if (testVectors[i].detachedSignature == 1) {
            ret = wc_PKCS7_SetDetached(pkcs7, 1);
            if (ret != 0) {
            XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
            wc_PKCS7_Free(pkcs7);
            return -12117;
            }
        }

        encodedSz = wc_PKCS7_EncodeSignedData(pkcs7, out, outSz);
        if (encodedSz < 0) {
            XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
            wc_PKCS7_Free(pkcs7);
            return -12118;
        }

    #ifdef PKCS7_OUTPUT_TEST_BUNDLES
        /* write PKCS#7 to output file for more testing */
        file = XFOPEN(testVectors[i].outFileName, "wb");
        if (!file) {
            XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
            wc_PKCS7_Free(pkcs7);
            return -12119;
        }
        ret = (int)XFWRITE(out, 1, encodedSz, file);
        XFCLOSE(file);
        if (ret != (int)encodedSz) {
            XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
            wc_PKCS7_Free(pkcs7);
            return -12120;
        }
    #endif /* PKCS7_OUTPUT_TEST_BUNDLES */

        wc_PKCS7_Free(pkcs7);

        pkcs7 = wc_PKCS7_New(HEAP_HINT, devId);
        if (pkcs7 == NULL)
            return -12121;
        wc_PKCS7_InitWithCert(pkcs7, NULL, 0);

        if (testVectors[i].detachedSignature == 1) {
            /* set content for verifying detached signatures */
            pkcs7->content         = (byte*)testVectors[i].content;
            pkcs7->contentSz       = testVectors[i].contentSz;
        }

        ret = wc_PKCS7_VerifySignedData(pkcs7, out, outSz);
        if (ret < 0) {
            XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
            wc_PKCS7_Free(pkcs7);
            return -12122;
        }

        /* verify contentType extracted successfully for custom content types */
        if (testVectors[i].contentTypeSz > 0) {
            if (pkcs7->contentTypeSz != testVectors[i].contentTypeSz) {
                return -12123;
            } else if (XMEMCMP(pkcs7->contentType, testVectors[i].contentType,
                       pkcs7->contentTypeSz) != 0) {
                return -12124;
            }
        }

        if (pkcs7->singleCert == NULL || pkcs7->singleCertSz == 0) {
            XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
            wc_PKCS7_Free(pkcs7);
            return -12125;
        }

        {
            /* check getting signed attributes */
        #ifndef NO_SHA
            byte buf[(WC_SHA_DIGEST_SIZE + 1) * 2 + 1];
        #else
            byte buf[(WC_SHA256_DIGEST_SIZE + 1) * 2 + 1];
        #endif
            byte* oidPt = transIdOid + 2;  /* skip object id tag and size */
            int oidSz = (int)sizeof(transIdOid) - 2;
            int bufSz = 0;

            if (testVectors[i].signedAttribs != NULL &&
                    wc_PKCS7_GetAttributeValue(pkcs7, oidPt, oidSz,
                    NULL, (word32*)&bufSz) != LENGTH_ONLY_E) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12126;
            }

            if (bufSz > (int)sizeof(buf)) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12127;
            }

            bufSz = wc_PKCS7_GetAttributeValue(pkcs7, oidPt, oidSz,
                    buf, (word32*)&bufSz);
            if ((testVectors[i].signedAttribs != NULL && bufSz < 0) ||
                (testVectors[i].signedAttribs == NULL && bufSz > 0)) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12128;
            }
        }

    #ifdef PKCS7_OUTPUT_TEST_BUNDLES
        file = XFOPEN("./pkcs7cert.der", "wb");
        if (!file) {
            XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
            wc_PKCS7_Free(pkcs7);
            return -12129;
        }
        ret = (int)XFWRITE(pkcs7->singleCert, 1, pkcs7->singleCertSz, file);
        XFCLOSE(file);
    #endif /* PKCS7_OUTPUT_TEST_BUNDLES */

        wc_PKCS7_Free(pkcs7);
    }

    XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    wc_FreeRng(&rng);

    if (ret > 0)
        return 0;

    (void)rsaClientCertBuf;
    (void)rsaClientCertBufSz;
    (void)rsaClientPrivKeyBuf;
    (void)rsaClientPrivKeyBufSz;
    (void)rsaServerCertBuf;
    (void)rsaServerCertBufSz;
    (void)rsaServerPrivKeyBuf;
    (void)rsaServerPrivKeyBufSz;
    (void)rsaCaCertBuf;
    (void)rsaCaCertBufSz;
    (void)rsaCaPrivKeyBuf;
    (void)rsaCaPrivKeyBufSz;
    (void)eccClientCertBuf;
    (void)eccClientCertBufSz;
    (void)eccClientPrivKeyBuf;
    (void)eccClientPrivKeyBufSz;

    return ret;
}


static int pkcs7signed_run_SingleShotVectors(
                        byte* rsaClientCertBuf, word32 rsaClientCertBufSz,
                        byte* rsaClientPrivKeyBuf, word32 rsaClientPrivKeyBufSz,
                        byte* rsaServerCertBuf, word32 rsaServerCertBufSz,
                        byte* rsaServerPrivKeyBuf, word32 rsaServerPrivKeyBufSz,
                        byte* rsaCaCertBuf, word32 rsaCaCertBufSz,
                        byte* rsaCaPrivKeyBuf, word32 rsaCaPrivKeyBufSz,
                        byte* eccClientCertBuf, word32 eccClientCertBufSz,
                        byte* eccClientPrivKeyBuf, word32 eccClientPrivKeyBufSz)
{
    int ret, testSz, i;
    int encodedSz;
    byte*  out;
    word32 outSz;
    WC_RNG rng;
    PKCS7* pkcs7;
#ifdef PKCS7_OUTPUT_TEST_BUNDLES
    XFILE  file;
#endif

    const byte data[] = { /* Hello World */
        0x48,0x65,0x6c,0x6c,0x6f,0x20,0x57,0x6f,
        0x72,0x6c,0x64
    };

#if defined(WOLFSSL_AES_256) && !defined(NO_PKCS7_ENCRYPTED_DATA)
    byte aes256Key[] = {
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
        0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08
    };
#endif

    static byte messageTypeOid[] =
               { 0x06, 0x0a, 0x60, 0x86, 0x48, 0x01, 0x86, 0xF8, 0x45, 0x01,
                 0x09, 0x02 };
    static byte messageType[] = { 0x13, 2, '1', '9' };

    PKCS7Attrib attribs[] =
    {
        { messageTypeOid, sizeof(messageTypeOid), messageType,
                                       sizeof(messageType) },
    };

    const pkcs7SignedVector testVectors[] =
    {
#ifndef NO_RSA
    #ifndef NO_SHA256
        /* Signed FirmwarePkgData, RSA, SHA256, no attribs */
        {data, (word32)sizeof(data), SHA256h, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         NULL, 0,
         "pkcs7signedFirmwarePkgData_RSA_SHA256_noattr.der", 0, NULL, 0, 0,
         0, 0, NULL, 0, NULL, 0, 0},

        /* Signed FirmwarePkgData, RSA, SHA256, attrs */
        {data, (word32)sizeof(data), SHA256h, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedFirmwarePkgData_RSA_SHA256.der", 0, NULL, 0, 0, 0, 0,
        NULL, 0, NULL, 0, 0},

        /* Signed FirmwarePkgData, RSA, SHA256, SubjectKeyIdentifier, attrs */
        {data, (word32)sizeof(data), SHA256h, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedFirmwarePkgData_RSA_SHA256_SKID.der", 0, NULL,
         0, CMS_SKID, 0, 0, NULL, 0, NULL, 0, 0},

        /* Signed FirmwraePkgData, RSA, SHA256, server cert and ca cert, attr */
        {data, (word32)sizeof(data), SHA256h, RSAk, rsaServerPrivKeyBuf,
         rsaServerPrivKeyBufSz, rsaServerCertBuf, rsaServerCertBufSz,
         rsaCaCertBuf, rsaCaCertBufSz,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedFirmwarePkgData_RSA_SHA256_with_ca_cert.der", 0, NULL,
         0, 0, 0, 0, NULL, 0, NULL, 0, 0},

    #if defined(WOLFSSL_AES_256) && !defined(NO_PKCS7_ENCRYPTED_DATA)
        /* Signed Encrypted FirmwarePkgData, RSA, SHA256, no attribs */
        {data, (word32)sizeof(data), SHA256h, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         NULL, 0,
         "pkcs7signedEncryptedFirmwarePkgData_RSA_SHA256_noattr.der", 0,
         NULL, 0, 0, AES256CBCb, 1, aes256Key, sizeof(aes256Key), NULL, 0, 0},

        /* Signed Encrypted FirmwarePkgData, RSA, SHA256, attribs */
        {data, (word32)sizeof(data), SHA256h, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedEncryptedFirmwarePkgData_RSA_SHA256.der", 0,
         NULL, 0, 0, AES256CBCb, 1, aes256Key, sizeof(aes256Key),
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)), 0},
    #endif /* WOLFSSL_AES_256 && !NO_PKCS7_ENCRYPTED_DATA */

    #if defined(HAVE_LIBZ) && !defined(NO_PKCS7_COMPRESSED_DATA)
        /* Signed Compressed FirmwarePkgData, RSA, SHA256, no attribs */
        {data, (word32)sizeof(data), SHA256h, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         NULL, 0,
         "pkcs7signedCompressedFirmwarePkgData_RSA_SHA256_noattr.der", 0,
         NULL, 0, 0, 0, 2, NULL, 0, NULL, 0, 0},

        /* Signed Compressed FirmwarePkgData, RSA, SHA256, attribs */
        {data, (word32)sizeof(data), SHA256h, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedCompressedFirmwarePkgData_RSA_SHA256.der", 0,
         NULL, 0, 0, 0, 2, NULL, 0, NULL, 0, 0},

    #ifndef NO_PKCS7_ENCRYPTED_DATA
        /* Signed Encrypted Compressed FirmwarePkgData, RSA, SHA256,
           no attribs */
        {data, (word32)sizeof(data), SHA256h, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         NULL, 0,
         "pkcs7signedEncryptedCompressedFirmwarePkgData_RSA_SHA256_noattr.der",
         0, NULL, 0, 0, AES256CBCb, 3, aes256Key, sizeof(aes256Key), NULL,
         0, 0},

        /* Signed Encrypted Compressed FirmwarePkgData, RSA, SHA256,
           attribs */
        {data, (word32)sizeof(data), SHA256h, RSAk, rsaClientPrivKeyBuf,
         rsaClientPrivKeyBufSz, rsaClientCertBuf, rsaClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedEncryptedCompressedFirmwarePkgData_RSA_SHA256.der",
         0, NULL, 0, 0, AES256CBCb, 3, aes256Key, sizeof(aes256Key),
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)), 0},
    #endif /* !NO_PKCS7_ENCRYPTED_DATA */

    #endif /* HAVE_LIBZ && !NO_PKCS7_COMPRESSED_DATA */

    #endif /* NO_SHA256 */
#endif /* NO_RSA */

#ifdef HAVE_ECC
    #ifndef NO_SHA256
        /* Signed FirmwarePkgData, ECDSA, SHA256, no attribs */
        {data, (word32)sizeof(data), SHA256h, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz, NULL, 0,
         NULL, 0,
         "pkcs7signedFirmwarePkgData_ECDSA_SHA256_noattr.der", 0, NULL,
         0, 0, 0, 0, NULL, 0, NULL, 0, 0},

        /* Signed FirmwarePkgData, ECDSA, SHA256, attribs */
        {data, (word32)sizeof(data), SHA256h, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedFirmwarePkgData_ECDSA_SHA256.der", 0, NULL,
         0, 0, 0, 0, NULL, 0, NULL, 0, 0},

        /* Signed FirmwarePkgData, ECDSA, SHA256, SubjectKeyIdentifier, attr */
        {data, (word32)sizeof(data), SHA256h, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedFirmwarePkgData_ECDSA_SHA256_SKID.der", 0, NULL,
         0, CMS_SKID, 0, 0, NULL, 0, NULL, 0, 0},

    #if defined(WOLFSSL_AES_256) && !defined(NO_PKCS7_ENCRYPTED_DATA)
        /* Signed Encrypted FirmwarePkgData, ECDSA, SHA256, no attribs */
        {data, (word32)sizeof(data), SHA256h, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz, NULL, 0,
         NULL, 0,
         "pkcs7signedEncryptedFirmwarePkgData_ECDSA_SHA256_noattr.der", 0, NULL,
         0, 0, AES256CBCb, 1, aes256Key, sizeof(aes256Key), NULL, 0, 0},

        /* Signed Encrypted FirmwarePkgData, ECDSA, SHA256, attribs */
        {data, (word32)sizeof(data), SHA256h, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedEncryptedFirmwarePkgData_ECDSA_SHA256.der", 0, NULL,
         0, 0, AES256CBCb, 1, aes256Key, sizeof(aes256Key),
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)), 0},
    #endif /* WOLFSSL_AES_256 && !NO_PKCS7_ENCRYPTED_DATA */

    #if defined(HAVE_LIBZ) && !defined(NO_PKCS7_COMPRESSED_DATA)
        /* Signed Compressed FirmwarePkgData, ECDSA, SHA256, no attribs */
        {data, (word32)sizeof(data), SHA256h, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz, NULL, 0,
         NULL, 0,
         "pkcs7signedCompressedFirmwarePkgData_ECDSA_SHA256_noattr.der", 0, NULL,
         0, 0, 0, 2, NULL, 0, NULL, 0, 0},

        /* Signed Compressed FirmwarePkgData, ECDSA, SHA256, attrib */
        {data, (word32)sizeof(data), SHA256h, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
         "pkcs7signedCompressedFirmwarePkgData_ECDSA_SHA256.der", 0, NULL,
         0, 0, 0, 2, NULL, 0, NULL, 0, 0},

    #ifndef NO_PKCS7_ENCRYPTED_DATA
        /* Signed Encrypted Compressed FirmwarePkgData, ECDSA, SHA256,
           no attribs */
        {data, (word32)sizeof(data), SHA256h, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz, NULL, 0,
         NULL, 0,
        "pkcs7signedEncryptedCompressedFirmwarePkgData_ECDSA_SHA256_noattr.der",
         0, NULL, 0, 0, AES256CBCb, 3, aes256Key, sizeof(aes256Key), NULL,
         0, 0},

        /* Signed Encrypted Compressed FirmwarePkgData, ECDSA, SHA256,
           attribs */
        {data, (word32)sizeof(data), SHA256h, ECDSAk, eccClientPrivKeyBuf,
         eccClientPrivKeyBufSz, eccClientCertBuf, eccClientCertBufSz, NULL, 0,
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)),
        "pkcs7signedEncryptedCompressedFirmwarePkgData_ECDSA_SHA256.der",
         0, NULL, 0, 0, AES256CBCb, 3, aes256Key, sizeof(aes256Key),
         attribs, (sizeof(attribs)/sizeof(PKCS7Attrib)), 0},
    #endif /* !NO_PKCS7_ENCRYPTED_DATA */

    #endif /* HAVE_LIBZ && !NO_PKCS7_COMPRESSED_DATA */

    #endif /* NO_SHA256 */
#endif /* HAVE_ECC */
    };

    testSz = sizeof(testVectors) / sizeof(pkcs7SignedVector);

    outSz = FOURK_BUF;
    out = (byte*)XMALLOC(outSz, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    if (out == NULL)
        return -12130;

    XMEMSET(out, 0, outSz);

    ret = wc_PKCS7_PadData((byte*)data, sizeof(data), out, outSz, 16);
    if (ret < 0) {
        XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        return -12131;
    }

#ifndef HAVE_FIPS
    ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
    ret = wc_InitRng(&rng);
#endif
    if (ret != 0) {
        XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
        return -12132;
    }

    for (i = 0; i < testSz; i++) {
        pkcs7 = wc_PKCS7_New(HEAP_HINT, devId);
        if (pkcs7 == NULL)
            return -12133;

        ret = wc_PKCS7_InitWithCert(pkcs7, testVectors[i].cert,
                                    (word32)testVectors[i].certSz);

        if (ret != 0) {
            XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
            wc_PKCS7_Free(pkcs7);
            return -12134;
        }

        /* load CA certificate, if present */
        if (testVectors[i].caCert != NULL) {
            ret = wc_PKCS7_AddCertificate(pkcs7, testVectors[i].caCert,
                                          (word32)testVectors[i].caCertSz);
            if (ret != 0) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12135;
            }
        }

        /* set SignerIdentifier to use SubjectKeyIdentifier if desired,
           default is IssuerAndSerialNumber */
        if (testVectors[i].sidType == CMS_SKID) {
            ret = wc_PKCS7_SetSignerIdentifierType(pkcs7, CMS_SKID);
            if (ret != 0) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12136;
            }
        }

        if (testVectors[i].encCompFlag == 0) {

            /* encode Signed FirmwarePkgData */
            encodedSz = wc_PKCS7_EncodeSignedFPD(pkcs7,
                    testVectors[i].privateKey, testVectors[i].privateKeySz,
                    testVectors[i].signOID, testVectors[i].hashOID,
                    (byte*)testVectors[i].content, testVectors[i].contentSz,
                    testVectors[i].signedAttribs,
                    testVectors[i].signedAttribsSz, out, outSz);

            if (encodedSz < 0) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12137;
            }

    #ifndef NO_PKCS7_ENCRYPTED_DATA

        } else if (testVectors[i].encCompFlag == 1) {

            /* encode Signed Encrypted FirmwarePkgData */
            encodedSz = wc_PKCS7_EncodeSignedEncryptedFPD(pkcs7,
                    testVectors[i].encryptKey, testVectors[i].encryptKeySz,
                    testVectors[i].privateKey, testVectors[i].privateKeySz,
                    testVectors[i].encryptOID, testVectors[i].signOID,
                    testVectors[i].hashOID, (byte*)testVectors[i].content,
                    testVectors[i].contentSz, testVectors[i].unprotectedAttribs,
                    testVectors[i].unprotectedAttribsSz,
                    testVectors[i].signedAttribs,
                    testVectors[i].signedAttribsSz, out, outSz);

            if (encodedSz <= 0) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12138;
            }
    #endif

    #if defined(HAVE_LIBZ) && !defined(NO_PKCS7_COMPRESSED_DATA)
        } else if (testVectors[i].encCompFlag == 2) {

            /* encode Signed Compressed FirmwarePkgData */
            encodedSz = wc_PKCS7_EncodeSignedCompressedFPD(pkcs7,
                    testVectors[i].privateKey, testVectors[i].privateKeySz,
                    testVectors[i].signOID, testVectors[i].hashOID,
                    (byte*)testVectors[i].content, testVectors[i].contentSz,
                    testVectors[i].signedAttribs,
                    testVectors[i].signedAttribsSz, out, outSz);

            if (encodedSz <= 0) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12139;
            }

        #ifndef NO_PKCS7_ENCRYPTED_DATA
        } else if (testVectors[i].encCompFlag == 3) {

            /* encode Signed Encrypted Compressed FirmwarePkgData */
            encodedSz = wc_PKCS7_EncodeSignedEncryptedCompressedFPD(pkcs7,
                    testVectors[i].encryptKey, testVectors[i].encryptKeySz,
                    testVectors[i].privateKey, testVectors[i].privateKeySz,
                    testVectors[i].encryptOID, testVectors[i].signOID,
                    testVectors[i].hashOID, (byte*)testVectors[i].content,
                    testVectors[i].contentSz, testVectors[i].unprotectedAttribs,
                    testVectors[i].unprotectedAttribsSz,
                    testVectors[i].signedAttribs,
                    testVectors[i].signedAttribsSz, out, outSz);

            if (encodedSz <= 0) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12140;
            }

        #endif /* NO_PKCS7_ENCRYPTED_DATA */
    #endif /* HAVE_LIBZ && !NO_PKCS7_COMPRESSED_DATA */

        } else {
            /* unsupported SignedData single-shot combination */
            XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
            wc_PKCS7_Free(pkcs7);
            return -12141;
        }

    #ifdef PKCS7_OUTPUT_TEST_BUNDLES
        /* write PKCS#7 to output file for more testing */
        file = XFOPEN(testVectors[i].outFileName, "wb");
        if (!file) {
            XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
            wc_PKCS7_Free(pkcs7);
            return -12142;
        }
        ret = (int)XFWRITE(out, 1, encodedSz, file);
        XFCLOSE(file);
        if (ret != (int)encodedSz) {
            XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
            wc_PKCS7_Free(pkcs7);
            return -12143;
        }
    #endif /* PKCS7_OUTPUT_TEST_BUNDLES */

        wc_PKCS7_Free(pkcs7);

        pkcs7 = wc_PKCS7_New(HEAP_HINT, devId);
        if (pkcs7 == NULL)
            return -12144;
        wc_PKCS7_InitWithCert(pkcs7, NULL, 0);

        ret = wc_PKCS7_VerifySignedData(pkcs7, out, outSz);
        if (ret < 0) {
            XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
            wc_PKCS7_Free(pkcs7);
            return -12145;
        }
#ifndef NO_PKCS7_STREAM
        {
            word32 z;
            for (z = 0; z < outSz && ret != 0; z++) {
                ret = wc_PKCS7_VerifySignedData(pkcs7, out + z, 1);
                if (ret < 0 && ret != WC_PKCS7_WANT_READ_E) {
                    XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                    wc_PKCS7_Free(pkcs7);
                    printf("unexpected error %d\n", ret);
                    return -12146;
                }
            }
        }
#endif

        if (pkcs7->singleCert == NULL || pkcs7->singleCertSz == 0) {
            XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
            wc_PKCS7_Free(pkcs7);
            return -12147;
        }

        if (testVectors[i].encCompFlag == 0) {
            /* verify decoded content matches expected */
            if ((pkcs7->contentSz != testVectors[i].contentSz) ||
                XMEMCMP(pkcs7->content, testVectors[i].content,
                        pkcs7->contentSz)) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12148;
            }

        }
    #ifndef NO_PKCS7_ENCRYPTED_DATA
        else if (testVectors[i].encCompFlag == 1) {

            /* decrypt inner encryptedData */
            pkcs7->encryptionKey = testVectors[i].encryptKey;
            pkcs7->encryptionKeySz = testVectors[i].encryptKeySz;

            ret = wc_PKCS7_DecodeEncryptedData(pkcs7, pkcs7->content,
                                               pkcs7->contentSz, out, outSz);
            if (ret < 0) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12149;
            }

            /* compare decrypted to expected */
            if (((word32)ret != testVectors[i].contentSz) ||
                XMEMCMP(out, testVectors[i].content, ret)) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12150;
            }
        }
    #endif
    #if defined(HAVE_LIBZ) && !defined(NO_PKCS7_COMPRESSED_DATA)
        else if (testVectors[i].encCompFlag == 2) {

            /* decompress inner compressedData */
            ret = wc_PKCS7_DecodeCompressedData(pkcs7, pkcs7->content,
                                                pkcs7->contentSz, out, outSz);
            if (ret < 0) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12151;
            }

            /* compare decompressed to expected */
            if (((word32)ret != testVectors[i].contentSz) ||
                XMEMCMP(out, testVectors[i].content, ret)) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12152;
            }
        }
    #ifndef NO_PKCS7_ENCRYPTED_DATA
        else if (testVectors[i].encCompFlag == 3) {

            byte* encryptedTmp;
            int encryptedTmpSz;

            encryptedTmpSz = FOURK_BUF;
            encryptedTmp = (byte*)XMALLOC(encryptedTmpSz, HEAP_HINT,
                                          DYNAMIC_TYPE_TMP_BUFFER);
            if (encryptedTmp == NULL) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12153;
            }

            XMEMSET(encryptedTmp, 0, encryptedTmpSz);

            /* decrypt inner encryptedData */
            pkcs7->encryptionKey = testVectors[i].encryptKey;
            pkcs7->encryptionKeySz = testVectors[i].encryptKeySz;

            encryptedTmpSz = wc_PKCS7_DecodeEncryptedData(pkcs7, pkcs7->content,
                                               pkcs7->contentSz, encryptedTmp,
                                               encryptedTmpSz);

            if (encryptedTmpSz < 0) {
                XFREE(encryptedTmp, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12154;
            }

            /* decompress inner compressedData */
            ret = wc_PKCS7_DecodeCompressedData(pkcs7, encryptedTmp,
                                                encryptedTmpSz, out, outSz);
            if (ret < 0) {
                XFREE(encryptedTmp, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12155;
            }

            XFREE(encryptedTmp, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);

            /* compare decompressed to expected */
            if (((word32)ret != testVectors[i].contentSz) ||
                XMEMCMP(out, testVectors[i].content, ret)) {
                XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
                wc_PKCS7_Free(pkcs7);
                return -12156;
            }
        }
    #endif /* NO_PKCS7_ENCRYPTED_DATA */
    #endif /* HAVE_LIBZ && !NO_PKCS7_COMPRESSED_DATA */

        wc_PKCS7_Free(pkcs7);
    }

    XFREE(out, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    wc_FreeRng(&rng);

    if (ret > 0)
        return 0;

    (void)eccClientCertBuf;
    (void)eccClientCertBufSz;
    (void)eccClientPrivKeyBuf;
    (void)eccClientPrivKeyBufSz;

    (void)rsaClientCertBuf;
    (void)rsaClientCertBufSz;
    (void)rsaClientPrivKeyBuf;
    (void)rsaClientPrivKeyBufSz;
    (void)rsaServerCertBuf;
    (void)rsaServerCertBufSz;
    (void)rsaServerPrivKeyBuf;
    (void)rsaServerPrivKeyBufSz;
    (void)rsaCaCertBuf;
    (void)rsaCaCertBufSz;
    (void)rsaCaPrivKeyBuf;
    (void)rsaCaPrivKeyBufSz;

    return ret;
}


int pkcs7signed_test(void)
{
    int ret = 0;

    byte* rsaClientCertBuf    = NULL;
    byte* rsaServerCertBuf    = NULL;
    byte* rsaCaCertBuf        = NULL;
    byte* eccClientCertBuf    = NULL;
    byte* rsaClientPrivKeyBuf = NULL;
    byte* rsaServerPrivKeyBuf = NULL;
    byte* rsaCaPrivKeyBuf     = NULL;
    byte* eccClientPrivKeyBuf = NULL;

    word32 rsaClientCertBufSz    = 0;
    word32 rsaServerCertBufSz    = 0;
    word32 rsaCaCertBufSz        = 0;
    word32 eccClientCertBufSz    = 0;
    word32 rsaClientPrivKeyBufSz = 0;
    word32 rsaServerPrivKeyBufSz = 0;
    word32 rsaCaPrivKeyBufSz     = 0;
    word32 eccClientPrivKeyBufSz = 0;

#ifndef NO_RSA
    /* read client RSA cert and key in DER format */
    rsaClientCertBuf = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT,
                                      DYNAMIC_TYPE_TMP_BUFFER);
    if (rsaClientCertBuf == NULL)
        ret = -12200;

    rsaClientPrivKeyBuf = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT,
                                         DYNAMIC_TYPE_TMP_BUFFER);
    if (ret == 0 && rsaClientPrivKeyBuf == NULL) {
        ret = -12201;
    }

    rsaClientCertBufSz = FOURK_BUF;
    rsaClientPrivKeyBufSz = FOURK_BUF;

    /* read server RSA cert and key in DER format */
    rsaServerCertBuf = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT,
                                      DYNAMIC_TYPE_TMP_BUFFER);
    if (ret == 0 && rsaServerCertBuf == NULL)
        ret = -12202;

    rsaServerPrivKeyBuf = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT,
                                         DYNAMIC_TYPE_TMP_BUFFER);
    if (ret == 0 && rsaServerPrivKeyBuf == NULL) {
        ret = -12203;
    }

    rsaServerCertBufSz = FOURK_BUF;
    rsaServerPrivKeyBufSz = FOURK_BUF;

    /* read CA RSA cert and key in DER format, for use with server cert */
    rsaCaCertBuf = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT,
                                  DYNAMIC_TYPE_TMP_BUFFER);
    if (ret == 0 && rsaCaCertBuf == NULL)
        ret = -12204;

    rsaCaPrivKeyBuf = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT,
                                     DYNAMIC_TYPE_TMP_BUFFER);
    if (ret == 0 && rsaCaPrivKeyBuf == NULL) {
        ret = -12205;
    }

    rsaCaCertBufSz = FOURK_BUF;
    rsaCaPrivKeyBufSz = FOURK_BUF;
#endif /* NO_RSA */

#ifdef HAVE_ECC
    /* read client ECC cert and key in DER format */
    eccClientCertBuf = (byte*)XMALLOC(FOURK_BUF, HEAP_HINT,
                                      DYNAMIC_TYPE_TMP_BUFFER);
    if (ret == 0 && eccClientCertBuf == NULL) {
        ret = -12206;
    }

    eccClientPrivKeyBuf =(byte*)XMALLOC(FOURK_BUF, HEAP_HINT,
                                        DYNAMIC_TYPE_TMP_BUFFER);
    if (ret == 0 && eccClientPrivKeyBuf == NULL) {
        ret = -12207;
    }

    eccClientCertBufSz = FOURK_BUF;
    eccClientPrivKeyBufSz = FOURK_BUF;
#endif /* HAVE_ECC */

    if (ret >= 0)
        ret = pkcs7_load_certs_keys(rsaClientCertBuf, &rsaClientCertBufSz,
                                rsaClientPrivKeyBuf, &rsaClientPrivKeyBufSz,
                                rsaServerCertBuf, &rsaServerCertBufSz,
                                rsaServerPrivKeyBuf, &rsaServerPrivKeyBufSz,
                                rsaCaCertBuf, &rsaCaCertBufSz,
                                rsaCaPrivKeyBuf, &rsaCaPrivKeyBufSz,
                                eccClientCertBuf, &eccClientCertBufSz,
                                eccClientPrivKeyBuf, &eccClientPrivKeyBufSz);
    if (ret < 0) {
        ret = -12208;
    }

    if (ret >= 0)
        ret = pkcs7signed_run_vectors(rsaClientCertBuf, (word32)rsaClientCertBufSz,
                            rsaClientPrivKeyBuf, (word32)rsaClientPrivKeyBufSz,
                            rsaServerCertBuf, (word32)rsaServerCertBufSz,
                            rsaServerPrivKeyBuf, (word32)rsaServerPrivKeyBufSz,
                            rsaCaCertBuf, (word32)rsaCaCertBufSz,
                            rsaCaPrivKeyBuf, (word32)rsaCaPrivKeyBufSz,
                            eccClientCertBuf, (word32)eccClientCertBufSz,
                            eccClientPrivKeyBuf, (word32)eccClientPrivKeyBufSz);

    if (ret >= 0)
        ret = pkcs7signed_run_SingleShotVectors(
                            rsaClientCertBuf, (word32)rsaClientCertBufSz,
                            rsaClientPrivKeyBuf, (word32)rsaClientPrivKeyBufSz,
                            rsaServerCertBuf, (word32)rsaServerCertBufSz,
                            rsaServerPrivKeyBuf, (word32)rsaServerPrivKeyBufSz,
                            rsaCaCertBuf, (word32)rsaCaCertBufSz,
                            rsaCaPrivKeyBuf, (word32)rsaCaPrivKeyBufSz,
                            eccClientCertBuf, (word32)eccClientCertBufSz,
                            eccClientPrivKeyBuf, (word32)eccClientPrivKeyBufSz);

#ifndef NO_AES
    if (ret >= 0)
        ret = pkcs7callback_test(
                            rsaClientCertBuf, (word32)rsaClientCertBufSz,
                            rsaClientPrivKeyBuf, (word32)rsaClientPrivKeyBufSz);
#endif

    XFREE(rsaClientCertBuf,    HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(rsaClientPrivKeyBuf, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(rsaServerCertBuf,    HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(rsaServerPrivKeyBuf, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(rsaCaCertBuf,        HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(rsaCaPrivKeyBuf,     HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(eccClientCertBuf,    HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(eccClientPrivKeyBuf, HEAP_HINT, DYNAMIC_TYPE_TMP_BUFFER);

    return ret;
}

#endif /* HAVE_PKCS7 */

#ifdef HAVE_VALGRIND
/* Need a static build to have access to symbols. */

/* Maximum number of bytes in a number to test. */
#define MP_MAX_TEST_BYTE_LEN      16

#if defined(HAVE_ECC) || defined(WOLFSSL_KEY_GEN)
static int randNum(mp_int* n, int len, WC_RNG* rng, void* heap)
{
    byte d[MP_MAX_TEST_BYTE_LEN];
    int  ret;

    (void)heap;

    do {
        ret = wc_RNG_GenerateBlock(rng, d, len);
        if (ret != 0)
            return ret;
        ret = mp_read_unsigned_bin(n, d, len);
        if (ret != 0)
            return ret;
    } while (mp_iszero(n));

    return 0;
}
#endif

int mp_test(void)
{
    WC_RNG rng;
    int    ret;
#if defined(HAVE_ECC) || defined(WOLFSSL_KEY_GEN)
    int    i, j, k;
    mp_digit d;
#endif
    mp_int a, b, r1, r2, p;

    ret = mp_init_multi(&a, &b, &r1, &r2, NULL, NULL);
    if (ret != 0)
        return -12300;

    mp_init_copy(&p, &a);

#ifndef HAVE_FIPS
    ret = wc_InitRng_ex(&rng, HEAP_HINT, devId);
#else
    ret = wc_InitRng(&rng);
#endif
    if (ret != 0)
        goto done;

#if defined(HAVE_ECC) || defined(WOLFSSL_KEY_GEN)
    mp_set_int(&a, 0);
    if (a.used != 0 || a.dp[0] != 0)
        return -12301;

    for (j = 1; j <= MP_MAX_TEST_BYTE_LEN; j++) {
        for (i = 0; i < 4 * j; i++) {
            /* New values to use. */
            ret = randNum(&p, j, &rng, NULL);
            if (ret != 0)
                return -12302;
            ret = randNum(&a, j, &rng, NULL);
            if (ret != 0)
                return -12303;
            ret = randNum(&b, j, &rng, NULL);
            if (ret != 0)
                return -12304;
            ret = wc_RNG_GenerateBlock(&rng, (byte*)&d, sizeof(d));
            if (ret != 0)
                return -12305;
            d &= MP_MASK;

            /* Ensure sqrmod produce same result as mulmod. */
            ret = mp_sqrmod(&a, &p, &r1);
            if (ret != 0)
                return -12306;
            ret = mp_mulmod(&a, &a, &p, &r2);
            if (ret != 0)
                return -12307;
            if (mp_cmp(&r1, &r2) != 0)
                return -12308;

            /* Ensure add with mod produce same result as sub with mod. */
            ret = mp_addmod(&a, &b, &p, &r1);
            if (ret != 0)
                return -12309;
            b.sign ^= 1;
            ret = mp_submod(&a, &b, &p, &r2);
            if (ret != 0)
                return -12310;
            if (mp_cmp(&r1, &r2) != 0)
                return -12311;

            /* Ensure add digit produce same result as sub digit. */
            ret = mp_add_d(&a, d, &r1);
            if (ret != 0)
                return -12312;
            ret = mp_sub_d(&r1, d, &r2);
            if (ret != 0)
                return -12313;
            if (mp_cmp(&a, &r2) != 0)
                return -12314;

            /* Invert - if p is even it will use the slow impl.
             *        - if p and a are even it will fail.
             */
            ret = mp_invmod(&a, &p, &r1);
            if (ret != 0 && ret != MP_VAL)
                return -12315;
            ret = 0;

            /* Shift up and down number all bits in a digit. */
            for (k = 0; k < DIGIT_BIT; k++) {
                mp_mul_2d(&a, k, &r1);
                mp_div_2d(&r1, k, &r2, &p);
                if (mp_cmp(&a, &r2) != 0)
                    return -12316;
                if (!mp_iszero(&p))
                    return -12317;
                mp_rshb(&r1, k);
                if (mp_cmp(&a, &r1) != 0)
                    return -12318;
            }
        }
    }

    /* Check that setting a 32-bit digit works. */
    d &= 0xffffffff;
    mp_set_int(&a, d);
    if (a.used != 1 || a.dp[0] != d)
        return -12319;

    /* Check setting a bit and testing a bit works. */
    for (i = 0; i < MP_MAX_TEST_BYTE_LEN * 8; i++) {
        mp_zero(&a);
        mp_set_bit(&a, i);
        if (!mp_is_bit_set(&a, i))
            return -12320;
    }
#endif

done:
    mp_clear(&p);
    mp_clear(&r2);
    mp_clear(&r1);
    mp_clear(&b);
    mp_clear(&a);
    wc_FreeRng(&rng);
    return ret;
}
#endif


#if defined(WOLFSSL_PUBLIC_MP) && defined(WOLFSSL_KEY_GEN)

typedef struct pairs_t {
    const unsigned char* coeff;
    int coeffSz;
    int exp;
} pairs_t;


/*
n =p1p2p3, where pi = ki(p1−1)+1 with (k2,k3) = (173,293)
p1 = 2^192 * 0x000000000000e24fd4f6d6363200bf2323ec46285cac1d3a
   + 2^0   * 0x0b2488b0c29d96c5e67f8bec15b54b189ae5636efe89b45b
*/

static const unsigned char c192a[] =
{
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe2, 0x4f,
    0xd4, 0xf6, 0xd6, 0x36, 0x32, 0x00, 0xbf, 0x23,
    0x23, 0xec, 0x46, 0x28, 0x5c, 0xac, 0x1d, 0x3a
};
static const unsigned char c0a[] =
{
    0x0b, 0x24, 0x88, 0xb0, 0xc2, 0x9d, 0x96, 0xc5,
    0xe6, 0x7f, 0x8b, 0xec, 0x15, 0xb5, 0x4b, 0x18,
    0x9a, 0xe5, 0x63, 0x6e, 0xfe, 0x89, 0xb4, 0x5b
};

static const pairs_t ecPairsA[] =
{
    {c192a, sizeof(c192a), 192},
    {c0a, sizeof(c0a), 0}
};

static const int kA[] = {173, 293};

static const unsigned char controlPrime[] = {
    0xe1, 0x76, 0x45, 0x80, 0x59, 0xb6, 0xd3, 0x49,
    0xdf, 0x0a, 0xef, 0x12, 0xd6, 0x0f, 0xf0, 0xb7,
    0xcb, 0x2a, 0x37, 0xbf, 0xa7, 0xf8, 0xb5, 0x4d,
    0xf5, 0x31, 0x35, 0xad, 0xe4, 0xa3, 0x94, 0xa1,
    0xdb, 0xf1, 0x96, 0xad, 0xb5, 0x05, 0x64, 0x85,
    0x83, 0xfc, 0x1b, 0x5b, 0x29, 0xaa, 0xbe, 0xf8,
    0x26, 0x3f, 0x76, 0x7e, 0xad, 0x1c, 0xf0, 0xcb,
    0xd7, 0x26, 0xb4, 0x1b, 0x05, 0x8e, 0x56, 0x86,
    0x7e, 0x08, 0x62, 0x21, 0xc1, 0x86, 0xd6, 0x47,
    0x79, 0x3e, 0xb7, 0x5d, 0xa4, 0xc6, 0x3a, 0xd7,
    0xb1, 0x74, 0x20, 0xf6, 0x50, 0x97, 0x41, 0x04,
    0x53, 0xed, 0x3f, 0x26, 0xd6, 0x6f, 0x91, 0xfa,
    0x68, 0x26, 0xec, 0x2a, 0xdc, 0x9a, 0xf1, 0xe7,
    0xdc, 0xfb, 0x73, 0xf0, 0x79, 0x43, 0x1b, 0x21,
    0xa3, 0x59, 0x04, 0x63, 0x52, 0x07, 0xc9, 0xd7,
    0xe6, 0xd1, 0x1b, 0x5d, 0x5e, 0x96, 0xfa, 0x53
};

static const unsigned char testOne[] = { 1 };


static int GenerateNextP(mp_int* p1, mp_int* p2, int k)
{
    int ret;
    mp_int ki;

    ret = mp_init(&ki);
    if (ret == 0)
        ret = mp_set(&ki, k);
    if (ret == 0)
        ret = mp_sub_d(p1, 1, p2);
    if (ret == 0)
        ret = mp_mul(p2, &ki, p2);
    if (ret == 0)
        ret = mp_add_d(p2, 1, p2);
    mp_clear(&ki);

    return ret;
}


static int GenerateP(mp_int* p1, mp_int* p2, mp_int* p3,
                const pairs_t* ecPairs, int ecPairsSz,
                const int* k)
{
    mp_int x,y;
    int ret, i;

    ret = mp_init(&x);
    if (ret == 0) {
        ret = mp_init(&y);
        if (ret != 0) {
            mp_clear(&x);
            return MP_MEM;
        }
    }
    for (i = 0; ret == 0 && i < ecPairsSz; i++) {
        ret = mp_read_unsigned_bin(&x, ecPairs[i].coeff, ecPairs[i].coeffSz);
        /* p1 = 2^exp */
        if (ret == 0)
            ret = mp_2expt(&y, ecPairs[i].exp);
        /* p1 = p1 * m */
        if (ret == 0)
            ret = mp_mul(&x, &y, &x);
        /* p1 +=  */
        if (ret == 0)
            ret = mp_add(p1, &x, p1);
        mp_zero(&x);
        mp_zero(&y);
    }
    mp_clear(&x);
    mp_clear(&y);

    if (ret == 0)
        ret = GenerateNextP(p1, p2, k[0]);
    if (ret == 0)
        ret = GenerateNextP(p1, p3, k[1]);

    return ret;
}

int prime_test(void)
{
    mp_int n, p1, p2, p3;
    int ret, isPrime = 0;
    WC_RNG rng;

    ret = wc_InitRng(&rng);
    if (ret == 0)
        ret = mp_init_multi(&n, &p1, &p2, &p3, NULL, NULL);
    if (ret == 0)
        ret = GenerateP(&p1, &p2, &p3,
                ecPairsA, sizeof(ecPairsA) / sizeof(ecPairsA[0]), kA);
    if (ret == 0)
        ret = mp_mul(&p1, &p2, &n);
    if (ret == 0)
        ret = mp_mul(&n, &p3, &n);
    if (ret != 0)
        return -12400;

    /* Check the old prime test using the number that false positives.
     * This test result should indicate as not prime. */
    ret = mp_prime_is_prime(&n, 40, &isPrime);
    if (ret != 0)
        return -12401;
    if (isPrime)
        return -12402;

    /* This test result should fail. It should indicate the value as prime. */
    ret = mp_prime_is_prime(&n, 8, &isPrime);
    if (ret != 0)
        return -12403;
    if (!isPrime)
        return -12404;

    /* This test result should indicate the value as not prime. */
    ret = mp_prime_is_prime_ex(&n, 8, &isPrime, &rng);
    if (ret != 0)
        return -12405;
    if (isPrime)
        return -12406;

    ret = mp_read_unsigned_bin(&n, controlPrime, sizeof(controlPrime));
    if (ret != 0)
        return -12407;

    /* This test result should indicate the value as prime. */
    ret = mp_prime_is_prime_ex(&n, 8, &isPrime, &rng);
    if (ret != 0)
        return -12408;
    if (!isPrime)
        return -12409;

    /* This test result should indicate the value as prime. */
    isPrime = -1;
    ret = mp_prime_is_prime(&n, 8, &isPrime);
    if (ret != 0)
        return -12410;
    if (!isPrime)
        return -12411;

    ret = mp_read_unsigned_bin(&n, testOne, sizeof(testOne));
    if (ret != 0)
        return -12412;

    /* This test result should indicate the value as not prime. */
    ret = mp_prime_is_prime_ex(&n, 8, &isPrime, &rng);
    if (ret != 0)
        return -12413;
    if (isPrime)
        return -12414;

    ret = mp_prime_is_prime(&n, 8, &isPrime);
    if (ret != 0)
        return -12415;
    if (isPrime)
        return -12416;

    mp_clear(&p3);
    mp_clear(&p2);
    mp_clear(&p1);
    mp_clear(&n);
    wc_FreeRng(&rng);

    return 0;
}

#endif /* WOLFSSL_PUBLIC_MP */


#if defined(ASN_BER_TO_DER) && \
    (defined(WOLFSSL_TEST_CERT) || defined(OPENSSL_EXTRA) || \
     defined(OPENSSL_EXTRA_X509_SMALL))
/* wc_BerToDer is only public facing in the case of test cert or opensslextra */
typedef struct berDerTestData {
    const byte *in;
    word32 inSz;
    const byte *out;
    word32 outSz;
} berDerTestData;

int berder_test(void)
{
    int ret;
    int i;
    word32 len = 0, l;
    byte out[32];
    static const byte good1_in[] = { 0x30, 0x80, 0x00, 0x00 };
    static const byte good1_out[] = { 0x30, 0x00 };
    static const byte good2_in[] = { 0x30, 0x80, 0x02, 0x01, 0x01, 0x00, 0x00 };
    static const byte good2_out[] = { 0x30, 0x03, 0x02, 0x01, 0x01 };
    static const byte good3_in[] = {
        0x24, 0x80, 0x04, 0x01, 0x01, 0x00, 0x00
    };
    static const byte good3_out[] = { 0x04, 0x1, 0x01 };
    static const byte good4_in[] = {
        0x30, 0x80,
          0x02, 0x01, 0x01,
          0x30, 0x80,
            0x24, 0x80,
              0x04, 0x01, 0x01,
              0x04, 0x02, 0x02, 0x03,
              0x00, 0x00,
            0x06, 0x01, 0x01,
            0x00, 0x00,
          0x31, 0x80,
            0x06, 0x01, 0x01,
            0x00, 0x00,
          0x00, 0x00,
    };
    static const byte good4_out[] = {
        0x30, 0x12,
          0x02, 0x01, 0x01,
          0x30, 0x08,
            0x04, 0x03, 0x01, 0x02, 0x03,
            0x06, 0x01, 0x01,
          0x31, 0x03,
            0x06, 0x01, 0x01
    };
    static const byte good5_in[] = { 0x30, 0x03, 0x02, 0x01, 0x01 };

    berDerTestData testData[] = {
        { good1_in, sizeof(good1_in), good1_out, sizeof(good1_out) },
        { good2_in, sizeof(good2_in), good2_out, sizeof(good2_out) },
        { good3_in, sizeof(good3_in), good3_out, sizeof(good3_out) },
        { good4_in, sizeof(good4_in), good4_out, sizeof(good4_out) },
        { good5_in, sizeof(good5_in), good5_in , sizeof(good5_in ) },
    };

    for (i = 0; i < (int)(sizeof(testData) / sizeof(*testData)); i++) {
        ret = wc_BerToDer(testData[i].in, testData[i].inSz, NULL, &len);
        if (ret != LENGTH_ONLY_E)
            return -12500 - i;
        if (len != testData[i].outSz)
            return -12510 - i;
        len = testData[i].outSz;
        ret = wc_BerToDer(testData[i].in, testData[i].inSz, out, &len);
        if (ret != 0)
            return -12520 - i;
        if (XMEMCMP(out, testData[i].out, len) != 0)
            return -12530 - i;

        for (l = 1; l < testData[i].inSz; l++) {
            ret = wc_BerToDer(testData[i].in, l, NULL, &len);
            if (ret != ASN_PARSE_E)
                 return -12540;
            len = testData[i].outSz;
            ret = wc_BerToDer(testData[i].in, l, out, &len);
            if (ret != ASN_PARSE_E)
                 return -12541;
        }

        for (l = 0; l < testData[i].outSz-1; l++) {
            ret = wc_BerToDer(testData[i].in, testData[i].inSz, out, &l);
            if (ret != BUFFER_E)
                 return -12542;
        }
    }

    ret = wc_BerToDer(NULL, 4, NULL, NULL);
    if (ret != BAD_FUNC_ARG)
        return -12543;
    ret = wc_BerToDer(out, 4, NULL, NULL);
    if (ret != BAD_FUNC_ARG)
        return -12544;
    ret = wc_BerToDer(NULL, 4, NULL, &len);
    if (ret != BAD_FUNC_ARG)
        return -12545;
    ret = wc_BerToDer(NULL, 4, out, NULL);
    if (ret != BAD_FUNC_ARG)
        return -12546;
    ret = wc_BerToDer(out, 4, out, NULL);
    if (ret != BAD_FUNC_ARG)
        return -12547;
    ret = wc_BerToDer(NULL, 4, out, &len);
    if (ret != BAD_FUNC_ARG)
        return -12548;

    for (l = 1; l < sizeof(good4_out); l++) {
        len = l;
        ret = wc_BerToDer(good4_in, sizeof(good4_in), out, &len);
        if (ret != BUFFER_E)
            return -12549;
    }

    return 0;
}
#endif

#ifdef DEBUG_WOLFSSL
static THREAD_LS_T int log_cnt = 0;
static void my_Logging_cb(const int logLevel, const char *const logMessage)
{
    (void)logLevel;
    (void)logMessage;
    log_cnt++;
}
#endif /* DEBUG_WOLFSSL */

int logging_test(void)
{
#ifdef DEBUG_WOLFSSL
    const char* msg = "Testing, testing. 1, 2, 3, 4 ...";
    byte        a[8] = { 1, 2, 3, 4, 5, 6, 7, 8 };
    byte        b[256];
    int         i;

    for (i = 0; i < (int)sizeof(b); i++)
        b[i] = i;

    if (wolfSSL_Debugging_ON() != 0)
        return -12600;

    if (wolfSSL_SetLoggingCb(my_Logging_cb) != 0)
        return -12601;

    WOLFSSL_MSG(msg);
    WOLFSSL_BUFFER(a, sizeof(a));
    WOLFSSL_BUFFER(b, sizeof(b));
    WOLFSSL_BUFFER(NULL, 0);
    WOLFSSL_ERROR(MEMORY_E);
    WOLFSSL_ERROR_MSG(msg);

    /* turn off logs */
    wolfSSL_Debugging_OFF();

    /* capture log count */
    i = log_cnt;

    /* validate no logs are output when disabled */
    WOLFSSL_MSG(msg);
    WOLFSSL_BUFFER(a, sizeof(a));
    WOLFSSL_BUFFER(b, sizeof(b));
    WOLFSSL_BUFFER(NULL, 0);
    WOLFSSL_ERROR(MEMORY_E);
    WOLFSSL_ERROR_MSG(msg);

    /* check the logs were disabled */
    if (i != log_cnt)
        return -12602;

    /* restore callback and leave logging enabled */
    wolfSSL_SetLoggingCb(NULL);
    wolfSSL_Debugging_ON();

    /* suppress unused args */
    (void)a;
    (void)b;

#else
    if (wolfSSL_Debugging_ON() != NOT_COMPILED_IN)
        return -12603;
    wolfSSL_Debugging_OFF();
    if (wolfSSL_SetLoggingCb(NULL) != NOT_COMPILED_IN)
        return -12604;
#endif /* DEBUG_WOLFSSL */
    return 0;
}


int mutex_test(void)
{
#ifdef WOLFSSL_PTHREADS
    wolfSSL_Mutex m;
#endif
#ifndef WOLFSSL_NO_MALLOC
    wolfSSL_Mutex *mm = wc_InitAndAllocMutex();
    if (mm == NULL)
        return -12700;
    wc_FreeMutex(mm);
    XFREE(mm, NULL, DYNAMIC_TYPE_MUTEX);
#endif

    /* Can optionally enable advanced pthread tests using "ENABLE_PTHREAD_LOCKFREE_TESTS" */
#ifdef WOLFSSL_PTHREADS
    if (wc_InitMutex(&m) != 0)
        return -12701;
    if (wc_LockMutex(&m) != 0)
        return -12702;
#if !defined(WOLFSSL_SOLARIS) && defined(ENABLE_PTHREAD_LOCKFREE_TESTS)
    /* trying to free a locked mutex is not portable behavior with pthread */
    /* Attempting to destroy a locked mutex results in undefined behavior */
    if (wc_FreeMutex(&m) != BAD_MUTEX_E)
        return -12703;
#endif
    if (wc_UnLockMutex(&m) != 0)
        return -12704;
    if (wc_FreeMutex(&m) != 0)
        return -12705;
#if !defined(WOLFSSL_SOLARIS) && defined(ENABLE_PTHREAD_LOCKFREE_TESTS)
    /* Trying to use a pthread after free'ing is not portable behavior */
    if (wc_LockMutex(&m) != BAD_MUTEX_E)
        return -12706;
    if (wc_UnLockMutex(&m) != BAD_MUTEX_E)
        return -12707;
#endif
#endif

    return 0;
}

#if defined(USE_WOLFSSL_MEMORY) && !defined(FREERTOS)

#ifndef WOLFSSL_NO_MALLOC
static int malloc_cnt = 0;
static int realloc_cnt = 0;
static int free_cnt = 0;

static void *my_Malloc_cb(size_t size)
{
    malloc_cnt++;
    #ifndef WOLFSSL_NO_MALLOC
        return malloc(size);
    #else
        WOLFSSL_MSG("No malloc available");
        (void)size;
        return NULL;
    #endif
}
static void my_Free_cb(void *ptr)
{
    free_cnt++;
    #ifndef WOLFSSL_NO_MALLOC
        free(ptr);
    #else
        WOLFSSL_MSG("No free available");
        (void)ptr;
    #endif
}
static void *my_Realloc_cb(void *ptr, size_t size)
{
    realloc_cnt++;
    #ifndef WOLFSSL_NO_MALLOC
        return realloc(ptr, size);
    #else
        WOLFSSL_MSG("No realloc available");
        (void)ptr;
        (void)size;
        return NULL;
    #endif
}
#endif /* !WOLFSSL_NO_MALLOC */

int memcb_test(void)
{
    int ret = 0;
#ifndef WOLFSSL_NO_MALLOC
    byte* b = NULL;
#endif
    wolfSSL_Malloc_cb  mc;
    wolfSSL_Free_cb    fc;
    wolfSSL_Realloc_cb rc;

    /* Save existing memory callbacks */
    if (wolfSSL_GetAllocators(&mc, &fc, &rc) != 0)
        return -12800;

#ifndef WOLFSSL_NO_MALLOC
    /* test realloc */
    b = (byte*)XREALLOC(b, 1024, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (b == NULL) {
        ERROR_OUT(-12801, exit_memcb);
    }
    XFREE(b, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    b = NULL;

    /* Use API. */
    if (wolfSSL_SetAllocators((wolfSSL_Malloc_cb)(void*)&my_Malloc_cb,
                              (wolfSSL_Free_cb)(void*)&my_Free_cb,
                              (wolfSSL_Realloc_cb)(void*)&my_Realloc_cb) != 0) {
        ERROR_OUT(-12802, exit_memcb);
    }

    b = (byte*)XMALLOC(1024, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    b = (byte*)XREALLOC(b, 1024, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(b, NULL, DYNAMIC_TYPE_TMP_BUFFER);

#ifndef WOLFSSL_STATIC_MEMORY
    if (malloc_cnt != 1 || free_cnt != 1 || realloc_cnt != 1)
#else
    if (malloc_cnt != 0 || free_cnt != 0 || realloc_cnt != 0)
#endif
        ret = -12803;
#endif /* !WOLFSSL_NO_MALLOC */

#ifndef WOLFSSL_NO_MALLOC
exit_memcb:
#endif

    /* restore memory callbacks */
    wolfSSL_SetAllocators(mc, fc, rc);

    return ret;
}
#endif /* USE_WOLFSSL_MEMORY && !WOLFSSL_NO_MALLOC */


#ifdef WOLFSSL_IMX6_CAAM_BLOB
int blob_test(void)
{
    int ret = 0;
    byte out[112];
    byte blob[112];
    word32 outSz;

    const byte iv[] =
        {
            0xf0,0xf1,0xf2,0xf3,0xf4,0xf5,0xf6,0xf7,
            0xf8,0xf9,0xfa,0xfb,0xfc,0xfd,0xfe,0xff
        };

    const byte text[] =
        {
            0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
            0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a,
            0xae,0x2d,0x8a,0x57,0x1e,0x03,0xac,0x9c,
            0x9e,0xb7,0x6f,0xac,0x45,0xaf,0x8e,0x51,
            0x30,0xc8,0x1c,0x46,0xa3,0x5c,0xe4,0x11,
            0xe5,0xfb,0xc1,0x19,0x1a,0x0a,0x52,0xef,
            0xf6,0x9f,0x24,0x45,0xdf,0x4f,0x9b,0x17,
            0xad,0x2b,0x41,0x7b,0xe6,0x6c,0x37,0x10
        };


    XMEMSET(blob, 0, sizeof(blob));
    outSz = sizeof(blob);
    ret = wc_caamCreateBlob((byte*)iv, sizeof(iv), blob, &outSz);
    if (ret != 0) {
        ERROR_OUT(-12900, exit_blob);
    }

    blob[outSz - 2] += 1;
    ret = wc_caamOpenBlob(blob, outSz, out, &outSz);
    if (ret == 0) { /* should fail with altered blob */
        ERROR_OUT(-12901, exit_blob);
    }

    XMEMSET(blob, 0, sizeof(blob));
    outSz = sizeof(blob);
    ret = wc_caamCreateBlob((byte*)iv, sizeof(iv), blob, &outSz);
    if (ret != 0) {
        ERROR_OUT(-12902, exit_blob);
    }

    ret = wc_caamOpenBlob(blob, outSz, out, &outSz);
    if (ret != 0) {
        ERROR_OUT(-12903, exit_blob);
    }

    if (XMEMCMP(out, iv, sizeof(iv))) {
        ERROR_OUT(-12904, exit_blob);
    }

    XMEMSET(blob, 0, sizeof(blob));
    outSz = sizeof(blob);
    ret = wc_caamCreateBlob((byte*)text, sizeof(text), blob, &outSz);
    if (ret != 0) {
        ERROR_OUT(-12905, exit_blob);
    }

    ret = wc_caamOpenBlob(blob, outSz, out, &outSz);
    if (ret != 0) {
        ERROR_OUT(-12906, exit_blob);
    }

    if (XMEMCMP(out, text, sizeof(text))) {
        ERROR_OUT(-12907, exit_blob);
    }

    exit_blob:

    return ret;
}
#endif /* WOLFSSL_IMX6_CAAM_BLOB */

#ifdef WOLF_CRYPTO_CB

/* Example custom context for crypto callback */
typedef struct {
    int exampleVar; /* example, not used */
} myCryptoDevCtx;


/* Example crypto dev callback function that calls software version */
static int myCryptoDevCb(int devIdArg, wc_CryptoInfo* info, void* ctx)
{
    int ret = NOT_COMPILED_IN; /* return this to bypass HW and use SW */
    myCryptoDevCtx* myCtx = (myCryptoDevCtx*)ctx;

    if (info == NULL)
        return BAD_FUNC_ARG;

#ifdef DEBUG_WOLFSSL
    printf("CryptoDevCb: Algo Type %d\n", info->algo_type);
#endif

    if (info->algo_type == WC_ALGO_TYPE_RNG) {
    #ifndef WC_NO_RNG
        /* set devId to invalid, so software is used */
        info->rng.rng->devId = INVALID_DEVID;

        ret = wc_RNG_GenerateBlock(info->rng.rng,
            info->rng.out, info->rng.sz);

        /* reset devId */
        info->rng.rng->devId = devIdArg;
    #endif
    }
    else if (info->algo_type == WC_ALGO_TYPE_SEED) {
    #ifndef WC_NO_RNG
        static byte seed[sizeof(word32)] = { 0x00, 0x00, 0x00, 0x01 };
        word32* seedWord32 = (word32*)seed;
        word32 len;

        /* wc_GenerateSeed is a local symbol so we need to fake the entropy. */
        while (info->seed.sz > 0) {
            len = (word32)sizeof(seed);
            if (info->seed.sz < len)
                len = info->seed.sz;
            XMEMCPY(info->seed.seed, seed, sizeof(seed));
            info->seed.seed += len;
            info->seed.sz -= len;
            (*seedWord32)++;
        }

        ret = 0;
    #endif
    }
    else if (info->algo_type == WC_ALGO_TYPE_PK) {
    #ifdef DEBUG_WOLFSSL
        printf("CryptoDevCb: Pk Type %d\n", info->pk.type);
    #endif

    #ifndef NO_RSA
        if (info->pk.type == WC_PK_TYPE_RSA) {
            /* set devId to invalid, so software is used */
            info->pk.rsa.key->devId = INVALID_DEVID;

            switch (info->pk.rsa.type) {
                case RSA_PUBLIC_ENCRYPT:
                case RSA_PUBLIC_DECRYPT:
                    /* perform software based RSA public op */
                    ret = wc_RsaFunction(
                        info->pk.rsa.in, info->pk.rsa.inLen,
                        info->pk.rsa.out, info->pk.rsa.outLen,
                        info->pk.rsa.type, info->pk.rsa.key, info->pk.rsa.rng);
                    break;
                case RSA_PRIVATE_ENCRYPT:
                case RSA_PRIVATE_DECRYPT:
                    /* perform software based RSA private op */
                    ret = wc_RsaFunction(
                        info->pk.rsa.in, info->pk.rsa.inLen,
                        info->pk.rsa.out, info->pk.rsa.outLen,
                        info->pk.rsa.type, info->pk.rsa.key, info->pk.rsa.rng);
                    break;
            }

            /* reset devId */
            info->pk.rsa.key->devId = devIdArg;
        }
    #ifdef WOLFSSL_KEY_GEN
        else if (info->pk.type == WC_PK_TYPE_RSA_KEYGEN) {
            info->pk.rsakg.key->devId = INVALID_DEVID;

            ret = wc_MakeRsaKey(info->pk.rsakg.key, info->pk.rsakg.size,
                info->pk.rsakg.e, info->pk.rsakg.rng);

            /* reset devId */
            info->pk.rsakg.key->devId = devIdArg;
        }
    #endif
    #endif /* !NO_RSA */
    #ifdef HAVE_ECC
        if (info->pk.type == WC_PK_TYPE_EC_KEYGEN) {
            /* set devId to invalid, so software is used */
            info->pk.eckg.key->devId = INVALID_DEVID;

            ret = wc_ecc_make_key_ex(info->pk.eckg.rng, info->pk.eckg.size,
                info->pk.eckg.key, info->pk.eckg.curveId);

            /* reset devId */
            info->pk.eckg.key->devId = devIdArg;
        }
        else if (info->pk.type == WC_PK_TYPE_ECDSA_SIGN) {
            /* set devId to invalid, so software is used */
            info->pk.eccsign.key->devId = INVALID_DEVID;

            ret = wc_ecc_sign_hash(
                info->pk.eccsign.in, info->pk.eccsign.inlen,
                info->pk.eccsign.out, info->pk.eccsign.outlen,
                info->pk.eccsign.rng, info->pk.eccsign.key);

            /* reset devId */
            info->pk.eccsign.key->devId = devIdArg;
        }
        else if (info->pk.type == WC_PK_TYPE_ECDSA_VERIFY) {
            /* set devId to invalid, so software is used */
            info->pk.eccverify.key->devId = INVALID_DEVID;

            ret = wc_ecc_verify_hash(
                info->pk.eccverify.sig, info->pk.eccverify.siglen,
                info->pk.eccverify.hash, info->pk.eccverify.hashlen,
                info->pk.eccverify.res, info->pk.eccverify.key);

            /* reset devId */
            info->pk.eccverify.key->devId = devIdArg;
        }
        else if (info->pk.type == WC_PK_TYPE_ECDH) {
            /* set devId to invalid, so software is used */
            info->pk.ecdh.private_key->devId = INVALID_DEVID;

            ret = wc_ecc_shared_secret(
                info->pk.ecdh.private_key, info->pk.ecdh.public_key,
                info->pk.ecdh.out, info->pk.ecdh.outlen);

            /* reset devId */
            info->pk.ecdh.private_key->devId = devIdArg;
        }
    #endif /* HAVE_ECC */
    }
    else if (info->algo_type == WC_ALGO_TYPE_CIPHER) {
#if !defined(NO_AES) || !defined(NO_DES3)
    #ifdef HAVE_AESGCM
        if (info->cipher.type == WC_CIPHER_AES_GCM) {
            if (info->cipher.enc) {
                /* set devId to invalid, so software is used */
                info->cipher.aesgcm_enc.aes->devId = INVALID_DEVID;

                ret = wc_AesGcmEncrypt(
                    info->cipher.aesgcm_enc.aes,
                    info->cipher.aesgcm_enc.out,
                    info->cipher.aesgcm_enc.in,
                    info->cipher.aesgcm_enc.sz,
                    info->cipher.aesgcm_enc.iv,
                    info->cipher.aesgcm_enc.ivSz,
                    info->cipher.aesgcm_enc.authTag,
                    info->cipher.aesgcm_enc.authTagSz,
                    info->cipher.aesgcm_enc.authIn,
                    info->cipher.aesgcm_enc.authInSz);

                /* reset devId */
                info->cipher.aesgcm_enc.aes->devId = devIdArg;
            }
            else {
                /* set devId to invalid, so software is used */
                info->cipher.aesgcm_dec.aes->devId = INVALID_DEVID;

                ret = wc_AesGcmDecrypt(
                    info->cipher.aesgcm_dec.aes,
                    info->cipher.aesgcm_dec.out,
                    info->cipher.aesgcm_dec.in,
                    info->cipher.aesgcm_dec.sz,
                    info->cipher.aesgcm_dec.iv,
                    info->cipher.aesgcm_dec.ivSz,
                    info->cipher.aesgcm_dec.authTag,
                    info->cipher.aesgcm_dec.authTagSz,
                    info->cipher.aesgcm_dec.authIn,
                    info->cipher.aesgcm_dec.authInSz);

                /* reset devId */
                info->cipher.aesgcm_dec.aes->devId = devIdArg;
            }
        }
    #endif /* HAVE_AESGCM */
    #ifdef HAVE_AES_CBC
        if (info->cipher.type == WC_CIPHER_AES_CBC) {
            if (info->cipher.enc) {
                /* set devId to invalid, so software is used */
                info->cipher.aescbc.aes->devId = INVALID_DEVID;

                ret = wc_AesCbcEncrypt(
                    info->cipher.aescbc.aes,
                    info->cipher.aescbc.out,
                    info->cipher.aescbc.in,
                    info->cipher.aescbc.sz);

                /* reset devId */
                info->cipher.aescbc.aes->devId = devIdArg;
            }
            else {
                /* set devId to invalid, so software is used */
                info->cipher.aescbc.aes->devId = INVALID_DEVID;

                ret = wc_AesCbcDecrypt(
                    info->cipher.aescbc.aes,
                    info->cipher.aescbc.out,
                    info->cipher.aescbc.in,
                    info->cipher.aescbc.sz);

                /* reset devId */
                info->cipher.aescbc.aes->devId = devIdArg;
            }
        }
    #endif /* HAVE_AES_CBC */
    #ifndef NO_DES3
        if (info->cipher.type == WC_CIPHER_DES3) {
            if (info->cipher.enc) {
                /* set devId to invalid, so software is used */
                info->cipher.des3.des->devId = INVALID_DEVID;

                ret = wc_Des3_CbcEncrypt(
                    info->cipher.des3.des,
                    info->cipher.des3.out,
                    info->cipher.des3.in,
                    info->cipher.des3.sz);

                /* reset devId */
                info->cipher.des3.des->devId = devIdArg;
            }
            else {
                /* set devId to invalid, so software is used */
                info->cipher.des3.des->devId = INVALID_DEVID;

                ret = wc_Des3_CbcDecrypt(
                    info->cipher.des3.des,
                    info->cipher.des3.out,
                    info->cipher.des3.in,
                    info->cipher.des3.sz);

                /* reset devId */
                info->cipher.des3.des->devId = devIdArg;
            }
        }
    #endif /* !NO_DES3 */
#endif /* !NO_AES || !NO_DES3 */
    }
#if !defined(NO_SHA) || !defined(NO_SHA256)
    else if (info->algo_type == WC_ALGO_TYPE_HASH) {
    #if !defined(NO_SHA)
        if (info->hash.type == WC_HASH_TYPE_SHA) {
            if (info->hash.sha1 == NULL)
                return NOT_COMPILED_IN;

            /* set devId to invalid, so software is used */
            info->hash.sha1->devId = INVALID_DEVID;

            if (info->hash.in != NULL) {
                ret = wc_ShaUpdate(
                    info->hash.sha1,
                    info->hash.in,
                    info->hash.inSz);
            }
            if (info->hash.digest != NULL) {
                ret = wc_ShaFinal(
                    info->hash.sha1,
                    info->hash.digest);
            }

            /* reset devId */
            info->hash.sha1->devId = devIdArg;
        }
        else
    #endif
    #if !defined(NO_SHA256)
        if (info->hash.type == WC_HASH_TYPE_SHA256) {
            if (info->hash.sha256 == NULL)
                return NOT_COMPILED_IN;

            /* set devId to invalid, so software is used */
            info->hash.sha256->devId = INVALID_DEVID;

            if (info->hash.in != NULL) {
                ret = wc_Sha256Update(
                    info->hash.sha256,
                    info->hash.in,
                    info->hash.inSz);
            }
            if (info->hash.digest != NULL) {
                ret = wc_Sha256Final(
                    info->hash.sha256,
                    info->hash.digest);
            }

            /* reset devId */
            info->hash.sha256->devId = devIdArg;
        }
        else
    #endif
        {
        }
    }
#endif /* !NO_SHA || !NO_SHA256 */
#ifndef NO_HMAC
    else if (info->algo_type == WC_ALGO_TYPE_HMAC) {
        if (info->hmac.hmac == NULL)
            return NOT_COMPILED_IN;

        /* set devId to invalid, so software is used */
        info->hmac.hmac->devId = INVALID_DEVID;

        if (info->hash.in != NULL) {
            ret = wc_HmacUpdate(
                info->hmac.hmac,
                info->hmac.in,
                info->hmac.inSz);
        }
        else if (info->hash.digest != NULL) {
            ret = wc_HmacFinal(
                info->hmac.hmac,
                info->hmac.digest);
        }

        /* reset devId */
        info->hmac.hmac->devId = devIdArg;
    }
#endif

    (void)devIdArg;
    (void)myCtx;

    return ret;
}

int cryptocb_test(void)
{
    int ret = 0;
    myCryptoDevCtx myCtx;

    /* example data for callback */
    myCtx.exampleVar = 1;

    /* set devId to something other than INVALID_DEVID */
    devId = 1;
    ret = wc_CryptoCb_RegisterDevice(devId, myCryptoDevCb, &myCtx);

#ifndef WC_NO_RNG
    if (ret == 0)
        ret = random_test();
#endif /* WC_NO_RNG */
#ifndef NO_RSA
    if (ret == 0)
        ret = rsa_test();
#endif
#ifdef HAVE_ECC
    if (ret == 0)
        ret = ecc_test();
#endif
#ifndef NO_AES
    #ifdef HAVE_AESGCM
    if (ret == 0)
        ret = aesgcm_test();
    #endif
    #ifdef HAVE_AES_CBC
    if (ret == 0)
        ret = aes_test();
    #endif
#endif /* !NO_AES */
#ifndef NO_DES3
    if (ret == 0)
        ret = des3_test();
#endif /* !NO_DES3 */
#if !defined(NO_SHA) || !defined(NO_SHA256)
    #ifndef NO_SHA
    if (ret == 0)
        ret = sha_test();
    #endif
    #ifndef NO_SHA256
    if (ret == 0)
        ret = sha256_test();
    #endif
#endif
#ifndef NO_HMAC
    #ifndef NO_SHA
    if (ret == 0)
        ret = hmac_sha_test();
    #endif
    #ifndef NO_SHA256
    if (ret == 0)
        ret = hmac_sha256_test();
    #endif
#endif
#ifndef NO_PWDBASED
    #if defined(HAVE_PBKDF2) && !defined(NO_SHA256)
    if (ret == 0)
        ret = pbkdf2_test();
    #endif
#endif

    /* reset devId */
    devId = INVALID_DEVID;

    return ret;
}
#endif /* WOLF_CRYPTO_CB */

#ifdef WOLFSSL_CERT_PIV
int certpiv_test(void)
{
    int ret;
    wc_CertPIV piv;

    /* Template for Identiv PIV cert, nonce and signature */
    const byte pivCertIdentiv[] = {
        0x0A, 0x0D,
            0x53, 0x04,       /* NIST PIV Cert */
            0x70, 0x02,       /* Certificate */
                0x30, 0x00,
            0x71, 0x01, 0x00, /* Cert Info */
            0xFE, 0x00,       /* Error Detection */
        0x0B, 0x01, 0x00,     /* Nonce */
        0x0C, 0x01, 0x00,     /* Signed Nonce */
    };

    const byte pivCert[] = {
        0x53, 0x04,       /* NIST PIV Cert */
        0x70, 0x02,       /* Certificate */
            0x30, 0x00,
        0x71, 0x01, 0x00, /* Cert Info */
        0xFE, 0x00,       /* Error Detection */
    };

    /* Test with identiv 0x0A, 0x0B and 0x0C markers */
    ret = wc_ParseCertPIV(&piv, pivCertIdentiv, sizeof(pivCertIdentiv));
    if (ret == 0) {
        /* Test with NIST PIV format */
        ret = wc_ParseCertPIV(&piv, pivCert, sizeof(pivCert));
    }

    return ret;
}
#endif /* WOLFSSL_CERT_PIV */


#undef ERROR_OUT

#else
    #ifndef NO_MAIN_DRIVER
        int main() { return 0; }
    #endif
#endif /* NO_CRYPT_TEST */
