/* test.c
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

#ifdef XMALLOC_USER
    #include <stdlib.h>  /* we're using malloc / free direct here */
#endif

#ifndef NO_CRYPT_TEST

#ifdef WOLFSSL_TEST_CERT
    #include <wolfssl/wolfcrypt/asn.h>
#else
    #include <wolfssl/wolfcrypt/asn_public.h>
#endif
#include <wolfssl/wolfcrypt/md2.h>
#include <wolfssl/wolfcrypt/md5.h>
#include <wolfssl/wolfcrypt/md4.h>
#include <wolfssl/wolfcrypt/sha.h>
#include <wolfssl/wolfcrypt/sha256.h>
#include <wolfssl/wolfcrypt/sha512.h>
#include <wolfssl/wolfcrypt/arc4.h>
#include <wolfssl/wolfcrypt/random.h>
#include <wolfssl/wolfcrypt/coding.h>
#include <wolfssl/wolfcrypt/rsa.h>
#include <wolfssl/wolfcrypt/des3.h>
#include <wolfssl/wolfcrypt/aes.h>
#include <wolfssl/wolfcrypt/poly1305.h>
#include <wolfssl/wolfcrypt/camellia.h>
#include <wolfssl/wolfcrypt/hmac.h>
#include <wolfssl/wolfcrypt/dh.h>
#include <wolfssl/wolfcrypt/dsa.h>
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
#ifdef HAVE_BLAKE2
    #include <wolfssl/wolfcrypt/blake2.h>
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

#ifdef _MSC_VER
    /* 4996 warning to use MS extensions e.g., strcpy_s instead of strncpy */
    #pragma warning(disable: 4996)
#endif

#ifdef OPENSSL_EXTRA
    #include <wolfssl/openssl/evp.h>
    #include <wolfssl/openssl/rand.h>
    #include <wolfssl/openssl/hmac.h>
    #include <wolfssl/openssl/des.h>
#endif


#if defined(USE_CERT_BUFFERS_1024) || defined(USE_CERT_BUFFERS_2048) \
                                   || !defined(NO_DH)
    /* include test cert and key buffers for use with NO_FILESYSTEM */
    #if defined(WOLFSSL_MDK_ARM)
        #include "cert_data.h"
                        /* use certs_test.c for initial data, so other
                                               commands can share the data. */
    #else
        #include <wolfssl/certs_test.h>
    #endif
#endif

#if defined(WOLFSSL_MDK_ARM)
        #include <stdio.h>
        #include <stdlib.h>
    extern FILE * wolfSSL_fopen(const char *fname, const char *mode) ;
    #define fopen wolfSSL_fopen
#endif

#ifdef HAVE_NTRU
    #include "ntru_crypto.h"
#endif
#ifdef HAVE_CAVIUM
    #include "cavium_sysdep.h"
    #include "cavium_common.h"
    #include "cavium_ioctl.h"
#endif

#ifdef FREESCALE_MQX
    #include <mqx.h>
    #include <fio.h>
    #include <stdlib.h>
#else
    #include <stdio.h>
#endif


#ifdef THREADX
    /* since just testing, use THREADX log printf instead */
    int dc_log_printf(char*, ...);
        #undef printf
        #define printf dc_log_printf
#endif

#include "wolfcrypt/test/test.h"


typedef struct testVector {
    const char*  input;
    const char*  output;
    size_t inLen;
    size_t outLen;
} testVector;

int  md2_test(void);
int  md5_test(void);
int  md4_test(void);
int  sha_test(void);
int  sha256_test(void);
int  sha512_test(void);
int  sha384_test(void);
int  hmac_md5_test(void);
int  hmac_sha_test(void);
int  hmac_sha256_test(void);
int  hmac_sha384_test(void);
int  hmac_sha512_test(void);
int  hmac_blake2b_test(void);
int  hkdf_test(void);
int  arc4_test(void);
int  hc128_test(void);
int  rabbit_test(void);
int  chacha_test(void);
int  chacha20_poly1305_aead_test(void);
int  des_test(void);
int  des3_test(void);
int  aes_test(void);
int  poly1305_test(void);
int  aesgcm_test(void);
int  gmac_test(void);
int  aesccm_test(void);
int  camellia_test(void);
int  rsa_test(void);
int  dh_test(void);
int  dsa_test(void);
int  random_test(void);
int  pwdbased_test(void);
int  ripemd_test(void);
int  openssl_test(void);   /* test mini api */
int pbkdf1_test(void);
int pkcs12_test(void);
int pbkdf2_test(void);
#ifdef HAVE_ECC
    int  ecc_test(void);
    #ifdef HAVE_ECC_ENCRYPT
        int  ecc_encrypt_test(void);
    #endif
#endif
#ifdef HAVE_CURVE25519
    int  curve25519_test(void);
#endif
#ifdef HAVE_ED25519
    int  ed25519_test(void);
#endif
#ifdef HAVE_BLAKE2
    int  blake2b_test(void);
#endif
#ifdef HAVE_LIBZ
    int compress_test(void);
#endif
#ifdef HAVE_PKCS7
    int pkcs7enveloped_test(void);
    int pkcs7signed_test(void);
#endif


/* General big buffer size for many tests. */ 
#define FOURK_BUF 4096


static int err_sys(const char* msg, int es)

{
    printf("%s error = %d\n", msg, es);
    return -1; /* error state */
}

/* func_args from test.h, so don't have to pull in other junk */
typedef struct func_args {
    int    argc;
    char** argv;
    int    return_code;
} func_args;


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


int wolfcrypt_test(void* args)
{
    int ret = 0;

    ((func_args*)args)->return_code = -1; /* error state */

#ifdef HAVE_FIPS
    wolfCrypt_SetCb_fips(myFipsCb);
#endif

#if !defined(NO_BIG_INT)
    if (CheckCtcSettings() != 1)
        return err_sys("Build vs runtime math mismatch\n", -1234);

#ifdef USE_FAST_MATH
    if (CheckFastMathSettings() != 1)
        return err_sys("Build vs runtime fastmath FP_MAX_BITS mismatch\n",
                       -1235);
#endif /* USE_FAST_MATH */
#endif /* !NO_BIG_INT */


#ifndef NO_MD5
    if ( (ret = md5_test()) != 0)
        return err_sys("MD5      test failed!\n", ret);
    else
        printf( "MD5      test passed!\n");
#endif

#ifdef WOLFSSL_MD2
    if ( (ret = md2_test()) != 0)
        return err_sys("MD2      test failed!\n", ret);
    else
        printf( "MD2      test passed!\n");
#endif

#ifndef NO_MD4
    if ( (ret = md4_test()) != 0)
        return err_sys("MD4      test failed!\n", ret);
    else
        printf( "MD4      test passed!\n");
#endif

#ifndef NO_SHA
    if ( (ret = sha_test()) != 0)
        return err_sys("SHA      test failed!\n", ret);
    else
        printf( "SHA      test passed!\n");
#endif

#ifndef NO_SHA256
    if ( (ret = sha256_test()) != 0)
        return err_sys("SHA-256  test failed!\n", ret);
    else
        printf( "SHA-256  test passed!\n");
#endif

#ifdef WOLFSSL_SHA384
    if ( (ret = sha384_test()) != 0)
        return err_sys("SHA-384  test failed!\n", ret);
    else
        printf( "SHA-384  test passed!\n");
#endif

#ifdef WOLFSSL_SHA512
    if ( (ret = sha512_test()) != 0)
        return err_sys("SHA-512  test failed!\n", ret);
    else
        printf( "SHA-512  test passed!\n");
#endif

#ifdef WOLFSSL_RIPEMD
    if ( (ret = ripemd_test()) != 0)
        return err_sys("RIPEMD   test failed!\n", ret);
    else
        printf( "RIPEMD   test passed!\n");
#endif

#ifdef HAVE_BLAKE2
    if ( (ret = blake2b_test()) != 0)
        return err_sys("BLAKE2b  test failed!\n", ret);
    else
        printf( "BLAKE2b  test passed!\n");
#endif

#ifndef NO_HMAC
    #ifndef NO_MD5
        if ( (ret = hmac_md5_test()) != 0)
            return err_sys("HMAC-MD5 test failed!\n", ret);
        else
            printf( "HMAC-MD5 test passed!\n");
    #endif

    #ifndef NO_SHA
    if ( (ret = hmac_sha_test()) != 0)
        return err_sys("HMAC-SHA test failed!\n", ret);
    else
        printf( "HMAC-SHA test passed!\n");
    #endif

    #ifndef NO_SHA256
        if ( (ret = hmac_sha256_test()) != 0)
            return err_sys("HMAC-SHA256 test failed!\n", ret);
        else
            printf( "HMAC-SHA256 test passed!\n");
    #endif

    #ifdef WOLFSSL_SHA384
        if ( (ret = hmac_sha384_test()) != 0)
            return err_sys("HMAC-SHA384 test failed!\n", ret);
        else
            printf( "HMAC-SHA384 test passed!\n");
    #endif

    #ifdef WOLFSSL_SHA512
        if ( (ret = hmac_sha512_test()) != 0)
            return err_sys("HMAC-SHA512 test failed!\n", ret);
        else
            printf( "HMAC-SHA512 test passed!\n");
    #endif

    #ifdef HAVE_BLAKE2
        if ( (ret = hmac_blake2b_test()) != 0)
            return err_sys("HMAC-BLAKE2 test failed!\n", ret);
        else
            printf( "HMAC-BLAKE2 test passed!\n");
    #endif

    #ifdef HAVE_HKDF
        if ( (ret = hkdf_test()) != 0)
            return err_sys("HMAC-KDF    test failed!\n", ret);
        else
            printf( "HMAC-KDF    test passed!\n");
    #endif

#endif

#ifdef HAVE_AESGCM
    if ( (ret = gmac_test()) != 0)
        return err_sys("GMAC     test passed!\n", ret);
    else
        printf( "GMAC     test passed!\n");
#endif

#ifndef NO_RC4
    if ( (ret = arc4_test()) != 0)
        return err_sys("ARC4     test failed!\n", ret);
    else
        printf( "ARC4     test passed!\n");
#endif

#ifndef NO_HC128
    if ( (ret = hc128_test()) != 0)
        return err_sys("HC-128   test failed!\n", ret);
    else
        printf( "HC-128   test passed!\n");
#endif

#ifndef NO_RABBIT
    if ( (ret = rabbit_test()) != 0)
        return err_sys("Rabbit   test failed!\n", ret);
    else
        printf( "Rabbit   test passed!\n");
#endif

#ifdef HAVE_CHACHA
    if ( (ret = chacha_test()) != 0)
        return err_sys("Chacha   test failed!\n", ret);
    else
        printf( "Chacha   test passed!\n");
#endif

#ifdef HAVE_POLY1305
    if ( (ret = poly1305_test()) != 0)
        return err_sys("POLY1305 test failed!\n", ret);
    else
        printf( "POLY1305 test passed!\n");
#endif

#if defined(HAVE_CHACHA) && defined(HAVE_POLY1305)
    if ( (ret = chacha20_poly1305_aead_test()) != 0)
        return err_sys("ChaCha20-Poly1305 AEAD test failed!\n", ret);
    else
        printf( "ChaCha20-Poly1305 AEAD test passed!\n");
#endif

#ifndef NO_DES3
    if ( (ret = des_test()) != 0)
        return err_sys("DES      test failed!\n", ret);
    else
        printf( "DES      test passed!\n");
#endif

#ifndef NO_DES3
    if ( (ret = des3_test()) != 0)
        return err_sys("DES3     test failed!\n", ret);
    else
        printf( "DES3     test passed!\n");
#endif

#ifndef NO_AES
    if ( (ret = aes_test()) != 0)
        return err_sys("AES      test failed!\n", ret);
    else
        printf( "AES      test passed!\n");

#ifdef HAVE_AESGCM
    if ( (ret = aesgcm_test()) != 0)
        return err_sys("AES-GCM  test failed!\n", ret);
    else
        printf( "AES-GCM  test passed!\n");
#endif

#ifdef HAVE_AESCCM
    if ( (ret = aesccm_test()) != 0)
        return err_sys("AES-CCM  test failed!\n", ret);
    else
        printf( "AES-CCM  test passed!\n");
#endif
#endif

#ifdef HAVE_CAMELLIA
    if ( (ret = camellia_test()) != 0)
        return err_sys("CAMELLIA test failed!\n", ret);
    else
        printf( "CAMELLIA test passed!\n");
#endif

    if ( (ret = random_test()) != 0)
        return err_sys("RANDOM   test failed!\n", ret);
    else
        printf( "RANDOM   test passed!\n");

#ifndef NO_RSA
    if ( (ret = rsa_test()) != 0)
        return err_sys("RSA      test failed!\n", ret);
    else
        printf( "RSA      test passed!\n");
#endif

#ifndef NO_DH
    if ( (ret = dh_test()) != 0)
        return err_sys("DH       test failed!\n", ret);
    else
        printf( "DH       test passed!\n");
#endif

#ifndef NO_DSA
    if ( (ret = dsa_test()) != 0)
        return err_sys("DSA      test failed!\n", ret);
    else
        printf( "DSA      test passed!\n");
#endif

#ifndef NO_PWDBASED
    if ( (ret = pwdbased_test()) != 0)
        return err_sys("PWDBASED test failed!\n", ret);
    else
        printf( "PWDBASED test passed!\n");
#endif

#ifdef OPENSSL_EXTRA
    if ( (ret = openssl_test()) != 0)
        return err_sys("OPENSSL  test failed!\n", ret);
    else
        printf( "OPENSSL  test passed!\n");
#endif

#ifdef HAVE_ECC
    if ( (ret = ecc_test()) != 0)
        return err_sys("ECC      test failed!\n", ret);
    else
        printf( "ECC      test passed!\n");
    #ifdef HAVE_ECC_ENCRYPT
        if ( (ret = ecc_encrypt_test()) != 0)
            return err_sys("ECC Enc  test failed!\n", ret);
        else
            printf( "ECC Enc  test passed!\n");
    #endif
#endif

#ifdef HAVE_CURVE25519
    if ( (ret = curve25519_test()) != 0)
        return err_sys("CURVE25519 test failed!\n", ret);
    else
        printf( "CURVE25519 test passed!\n");
#endif

#ifdef HAVE_ED25519
    if ( (ret = ed25519_test()) != 0)
        return err_sys("ED25519  test failed!\n", ret);
    else
        printf( "ED25519  test passed!\n");
#endif

#ifdef HAVE_LIBZ
    if ( (ret = compress_test()) != 0)
        return err_sys("COMPRESS test failed!\n", ret);
    else
        printf( "COMPRESS test passed!\n");
#endif

#ifdef HAVE_PKCS7
    if ( (ret = pkcs7enveloped_test()) != 0)
        return err_sys("PKCS7enveloped test failed!\n", ret);
    else
        printf( "PKCS7enveloped test passed!\n");

    if ( (ret = pkcs7signed_test()) != 0)
        return err_sys("PKCS7signed    test failed!\n", ret);
    else
        printf( "PKCS7signed    test passed!\n");
#endif

    ((func_args*)args)->return_code = ret;

    return ret;
}


#ifndef NO_MAIN_DRIVER

#ifdef HAVE_CAVIUM

static int OpenNitroxDevice(int dma_mode,int dev_id)
{
   Csp1CoreAssignment core_assign;
   Uint32             device;

   if (CspInitialize(CAVIUM_DIRECT,CAVIUM_DEV_ID))
      return -1;
   if (Csp1GetDevType(&device))
      return -1;
   if (device != NPX_DEVICE) {
      if (ioctl(gpkpdev_hdlr[CAVIUM_DEV_ID], IOCTL_CSP1_GET_CORE_ASSIGNMENT,
                (Uint32 *)&core_assign)!= 0)
         return -1;
   }
   CspShutdown(CAVIUM_DEV_ID);

   return CspInitialize(dma_mode, dev_id);
}

#endif /* HAVE_CAVIUM */

    /* so overall tests can pull in test function */

    int main(int argc, char** argv)
    {

        func_args args;


#ifdef HAVE_CAVIUM
        int ret = OpenNitroxDevice(CAVIUM_DIRECT, CAVIUM_DEV_ID);
        if (ret != 0) {
            err_sys("Cavium OpenNitroxDevice failed", -1236);
            return -1236;
        }
#endif /* HAVE_CAVIUM */

        args.argc = argc;
        args.argv = argv;

        wolfcrypt_test(&args);

#ifdef HAVE_CAVIUM
        CspShutdown(CAVIUM_DEV_ID);
#endif

        return args.return_code;
    }

#endif /* NO_MAIN_DRIVER */


#ifdef WOLFSSL_MD2
int md2_test()
{
    Md2  md2;
    byte hash[MD2_DIGEST_SIZE];

    testVector a, b, c, d, e, f, g;
    testVector test_md2[7];
    int times = sizeof(test_md2) / sizeof(testVector), i;

    a.input  = "";
    a.output = "\x83\x50\xe5\xa3\xe2\x4c\x15\x3d\xf2\x27\x5c\x9f\x80\x69"
               "\x27\x73";
    a.inLen  = strlen(a.input);
    a.outLen = MD2_DIGEST_SIZE;

    b.input  = "a";
    b.output = "\x32\xec\x01\xec\x4a\x6d\xac\x72\xc0\xab\x96\xfb\x34\xc0"
               "\xb5\xd1";
    b.inLen  = strlen(b.input);
    b.outLen = MD2_DIGEST_SIZE;

    c.input  = "abc";
    c.output = "\xda\x85\x3b\x0d\x3f\x88\xd9\x9b\x30\x28\x3a\x69\xe6\xde"
               "\xd6\xbb";
    c.inLen  = strlen(c.input);
    c.outLen = MD2_DIGEST_SIZE;

    d.input  = "message digest";
    d.output = "\xab\x4f\x49\x6b\xfb\x2a\x53\x0b\x21\x9f\xf3\x30\x31\xfe"
               "\x06\xb0";
    d.inLen  = strlen(d.input);
    d.outLen = MD2_DIGEST_SIZE;

    e.input  = "abcdefghijklmnopqrstuvwxyz";
    e.output = "\x4e\x8d\xdf\xf3\x65\x02\x92\xab\x5a\x41\x08\xc3\xaa\x47"
               "\x94\x0b";
    e.inLen  = strlen(e.input);
    e.outLen = MD2_DIGEST_SIZE;

    f.input  = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz012345"
               "6789";
    f.output = "\xda\x33\xde\xf2\xa4\x2d\xf1\x39\x75\x35\x28\x46\xc3\x03"
               "\x38\xcd";
    f.inLen  = strlen(f.input);
    f.outLen = MD2_DIGEST_SIZE;

    g.input  = "1234567890123456789012345678901234567890123456789012345678"
               "9012345678901234567890";
    g.output = "\xd5\x97\x6f\x79\xd8\x3d\x3a\x0d\xc9\x80\x6c\x3c\x66\xf3"
               "\xef\xd8";
    g.inLen  = strlen(g.input);
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

        if (memcmp(hash, test_md2[i].output, MD2_DIGEST_SIZE) != 0)
            return -155 - i;
    }

    return 0;
}
#endif

#ifndef NO_MD5
int md5_test(void)
{
    Md5  md5;
    byte hash[MD5_DIGEST_SIZE];

    testVector a, b, c, d, e;
    testVector test_md5[5];
    int times = sizeof(test_md5) / sizeof(testVector), i;

    a.input  = "abc";
    a.output = "\x90\x01\x50\x98\x3c\xd2\x4f\xb0\xd6\x96\x3f\x7d\x28\xe1\x7f"
               "\x72";
    a.inLen  = strlen(a.input);
    a.outLen = MD5_DIGEST_SIZE;

    b.input  = "message digest";
    b.output = "\xf9\x6b\x69\x7d\x7c\xb7\x93\x8d\x52\x5a\x2f\x31\xaa\xf1\x61"
               "\xd0";
    b.inLen  = strlen(b.input);
    b.outLen = MD5_DIGEST_SIZE;

    c.input  = "abcdefghijklmnopqrstuvwxyz";
    c.output = "\xc3\xfc\xd3\xd7\x61\x92\xe4\x00\x7d\xfb\x49\x6c\xca\x67\xe1"
               "\x3b";
    c.inLen  = strlen(c.input);
    c.outLen = MD5_DIGEST_SIZE;

    d.input  = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz012345"
               "6789";
    d.output = "\xd1\x74\xab\x98\xd2\x77\xd9\xf5\xa5\x61\x1c\x2c\x9f\x41\x9d"
               "\x9f";
    d.inLen  = strlen(d.input);
    d.outLen = MD5_DIGEST_SIZE;

    e.input  = "1234567890123456789012345678901234567890123456789012345678"
               "9012345678901234567890";
    e.output = "\x57\xed\xf4\xa2\x2b\xe3\xc9\x55\xac\x49\xda\x2e\x21\x07\xb6"
               "\x7a";
    e.inLen  = strlen(e.input);
    e.outLen = MD5_DIGEST_SIZE;

    test_md5[0] = a;
    test_md5[1] = b;
    test_md5[2] = c;
    test_md5[3] = d;
    test_md5[4] = e;

    wc_InitMd5(&md5);

    for (i = 0; i < times; ++i) {
        wc_Md5Update(&md5, (byte*)test_md5[i].input, (word32)test_md5[i].inLen);
        wc_Md5Final(&md5, hash);

        if (memcmp(hash, test_md5[i].output, MD5_DIGEST_SIZE) != 0)
            return -5 - i;
    }

    return 0;
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
    a.inLen  = strlen(a.input);
    a.outLen = MD4_DIGEST_SIZE;

    b.input  = "a";
    b.output = "\xbd\xe5\x2c\xb3\x1d\xe3\x3e\x46\x24\x5e\x05\xfb\xdb\xd6\xfb"
               "\x24";
    b.inLen  = strlen(b.input);
    b.outLen = MD4_DIGEST_SIZE;

    c.input  = "abc";
    c.output = "\xa4\x48\x01\x7a\xaf\x21\xd8\x52\x5f\xc1\x0a\xe8\x7a\xa6\x72"
               "\x9d";
    c.inLen  = strlen(c.input);
    c.outLen = MD4_DIGEST_SIZE;

    d.input  = "message digest";
    d.output = "\xd9\x13\x0a\x81\x64\x54\x9f\xe8\x18\x87\x48\x06\xe1\xc7\x01"
               "\x4b";
    d.inLen  = strlen(d.input);
    d.outLen = MD4_DIGEST_SIZE;

    e.input  = "abcdefghijklmnopqrstuvwxyz";
    e.output = "\xd7\x9e\x1c\x30\x8a\xa5\xbb\xcd\xee\xa8\xed\x63\xdf\x41\x2d"
               "\xa9";
    e.inLen  = strlen(e.input);
    e.outLen = MD4_DIGEST_SIZE;

    f.input  = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz012345"
               "6789";
    f.output = "\x04\x3f\x85\x82\xf2\x41\xdb\x35\x1c\xe6\x27\xe1\x53\xe7\xf0"
               "\xe4";
    f.inLen  = strlen(f.input);
    f.outLen = MD4_DIGEST_SIZE;

    g.input  = "1234567890123456789012345678901234567890123456789012345678"
               "9012345678901234567890";
    g.output = "\xe3\x3b\x4d\xdc\x9c\x38\xf2\x19\x9c\x3e\x7b\x16\x4f\xcc\x05"
               "\x36";
    g.inLen  = strlen(g.input);
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

        if (memcmp(hash, test_md4[i].output, MD4_DIGEST_SIZE) != 0)
            return -205 - i;
    }

    return 0;
}

#endif /* NO_MD4 */

#ifndef NO_SHA

int sha_test(void)
{
    Sha  sha;
    byte hash[SHA_DIGEST_SIZE];

    testVector a, b, c, d;
    testVector test_sha[4];
    int ret;
    int times = sizeof(test_sha) / sizeof(struct testVector), i;

    a.input  = "abc";
    a.output = "\xA9\x99\x3E\x36\x47\x06\x81\x6A\xBA\x3E\x25\x71\x78\x50\xC2"
               "\x6C\x9C\xD0\xD8\x9D";
    a.inLen  = strlen(a.input);
    a.outLen = SHA_DIGEST_SIZE;

    b.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    b.output = "\x84\x98\x3E\x44\x1C\x3B\xD2\x6E\xBA\xAE\x4A\xA1\xF9\x51\x29"
               "\xE5\xE5\x46\x70\xF1";
    b.inLen  = strlen(b.input);
    b.outLen = SHA_DIGEST_SIZE;

    c.input  = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
               "aaaaaa";
    c.output = "\x00\x98\xBA\x82\x4B\x5C\x16\x42\x7B\xD7\xA1\x12\x2A\x5A\x44"
               "\x2A\x25\xEC\x64\x4D";
    c.inLen  = strlen(c.input);
    c.outLen = SHA_DIGEST_SIZE;

    d.input  = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
               "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
               "aaaaaaaaaa";
    d.output = "\xAD\x5B\x3F\xDB\xCB\x52\x67\x78\xC2\x83\x9D\x2F\x15\x1E\xA7"
               "\x53\x99\x5E\x26\xA0";
    d.inLen  = strlen(d.input);
    d.outLen = SHA_DIGEST_SIZE;

    test_sha[0] = a;
    test_sha[1] = b;
    test_sha[2] = c;
    test_sha[3] = d;

    ret = wc_InitSha(&sha);
    if (ret != 0)
        return -4001;

    for (i = 0; i < times; ++i) {
        wc_ShaUpdate(&sha, (byte*)test_sha[i].input, (word32)test_sha[i].inLen);
        wc_ShaFinal(&sha, hash);

        if (memcmp(hash, test_sha[i].output, SHA_DIGEST_SIZE) != 0)
            return -10 - i;
    }

    return 0;
}

#endif /* NO_SHA */

#ifdef WOLFSSL_RIPEMD
int ripemd_test(void)
{
    RipeMd  ripemd;
    byte hash[RIPEMD_DIGEST_SIZE];

    testVector a, b, c, d;
    testVector test_ripemd[4];
    int times = sizeof(test_ripemd) / sizeof(struct testVector), i;

    a.input  = "abc";
    a.output = "\x8e\xb2\x08\xf7\xe0\x5d\x98\x7a\x9b\x04\x4a\x8e\x98\xc6"
               "\xb0\x87\xf1\x5a\x0b\xfc";
    a.inLen  = strlen(a.input);
    a.outLen = RIPEMD_DIGEST_SIZE;

    b.input  = "message digest";
    b.output = "\x5d\x06\x89\xef\x49\xd2\xfa\xe5\x72\xb8\x81\xb1\x23\xa8"
               "\x5f\xfa\x21\x59\x5f\x36";
    b.inLen  = strlen(b.input);
    b.outLen = RIPEMD_DIGEST_SIZE;

    c.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    c.output = "\x12\xa0\x53\x38\x4a\x9c\x0c\x88\xe4\x05\xa0\x6c\x27\xdc"
               "\xf4\x9a\xda\x62\xeb\x2b";
    c.inLen  = strlen(c.input);
    c.outLen = RIPEMD_DIGEST_SIZE;

    d.input  = "12345678901234567890123456789012345678901234567890123456"
               "789012345678901234567890";
    d.output = "\x9b\x75\x2e\x45\x57\x3d\x4b\x39\xf4\xdb\xd3\x32\x3c\xab"
               "\x82\xbf\x63\x32\x6b\xfb";
    d.inLen  = strlen(d.input);
    d.outLen = RIPEMD_DIGEST_SIZE;

    test_ripemd[0] = a;
    test_ripemd[1] = b;
    test_ripemd[2] = c;
    test_ripemd[3] = d;

    wc_InitRipeMd(&ripemd);

    for (i = 0; i < times; ++i) {
        wc_RipeMdUpdate(&ripemd, (byte*)test_ripemd[i].input,
                     (word32)test_ripemd[i].inLen);
        wc_RipeMdFinal(&ripemd, hash);

        if (memcmp(hash, test_ripemd[i].output, RIPEMD_DIGEST_SIZE) != 0)
            return -10 - i;
    }

    return 0;
}
#endif /* WOLFSSL_RIPEMD */


#ifdef HAVE_BLAKE2


#define BLAKE2_TESTS 3

static const byte blake2b_vec[BLAKE2_TESTS][BLAKE2B_OUTBYTES] =
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

    for (i = 0; i < BLAKE2_TESTS; i++) {
        ret = wc_InitBlake2b(&b2b, 64);
        if (ret != 0)
            return -4002;

        ret = wc_Blake2bUpdate(&b2b, input, i);
        if (ret != 0)
            return -4003;

        ret = wc_Blake2bFinal(&b2b, digest, 64);
        if (ret != 0)
            return -4004;

        if (memcmp(digest, blake2b_vec[i], 64) != 0) {
            return -300 - i;
        }
    }

    return 0;
}
#endif /* HAVE_BLAKE2 */


#ifndef NO_SHA256
int sha256_test(void)
{
    Sha256 sha;
    byte   hash[SHA256_DIGEST_SIZE];

    testVector a, b;
    testVector test_sha[2];
    int ret;
    int times = sizeof(test_sha) / sizeof(struct testVector), i;

    a.input  = "abc";
    a.output = "\xBA\x78\x16\xBF\x8F\x01\xCF\xEA\x41\x41\x40\xDE\x5D\xAE\x22"
               "\x23\xB0\x03\x61\xA3\x96\x17\x7A\x9C\xB4\x10\xFF\x61\xF2\x00"
               "\x15\xAD";
    a.inLen  = strlen(a.input);
    a.outLen = SHA256_DIGEST_SIZE;

    b.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    b.output = "\x24\x8D\x6A\x61\xD2\x06\x38\xB8\xE5\xC0\x26\x93\x0C\x3E\x60"
               "\x39\xA3\x3C\xE4\x59\x64\xFF\x21\x67\xF6\xEC\xED\xD4\x19\xDB"
               "\x06\xC1";
    b.inLen  = strlen(b.input);
    b.outLen = SHA256_DIGEST_SIZE;

    test_sha[0] = a;
    test_sha[1] = b;

    ret = wc_InitSha256(&sha);
    if (ret != 0)
        return -4005;

    for (i = 0; i < times; ++i) {
        ret = wc_Sha256Update(&sha, (byte*)test_sha[i].input,(word32)test_sha[i].inLen);
        if (ret != 0)
            return -4006;
        ret = wc_Sha256Final(&sha, hash);
        if (ret != 0)
            return -4007;

        if (memcmp(hash, test_sha[i].output, SHA256_DIGEST_SIZE) != 0)
            return -10 - i;
    }

    return 0;
}
#endif


#ifdef WOLFSSL_SHA512
int sha512_test(void)
{
    Sha512 sha;
    byte   hash[SHA512_DIGEST_SIZE];
    int    ret;

    testVector a, b;
    testVector test_sha[2];
    int times = sizeof(test_sha) / sizeof(struct testVector), i;

    a.input  = "abc";
    a.output = "\xdd\xaf\x35\xa1\x93\x61\x7a\xba\xcc\x41\x73\x49\xae\x20\x41"
               "\x31\x12\xe6\xfa\x4e\x89\xa9\x7e\xa2\x0a\x9e\xee\xe6\x4b\x55"
               "\xd3\x9a\x21\x92\x99\x2a\x27\x4f\xc1\xa8\x36\xba\x3c\x23\xa3"
               "\xfe\xeb\xbd\x45\x4d\x44\x23\x64\x3c\xe8\x0e\x2a\x9a\xc9\x4f"
               "\xa5\x4c\xa4\x9f";
    a.inLen  = strlen(a.input);
    a.outLen = SHA512_DIGEST_SIZE;

    b.input  = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhi"
               "jklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    b.output = "\x8e\x95\x9b\x75\xda\xe3\x13\xda\x8c\xf4\xf7\x28\x14\xfc\x14"
               "\x3f\x8f\x77\x79\xc6\xeb\x9f\x7f\xa1\x72\x99\xae\xad\xb6\x88"
               "\x90\x18\x50\x1d\x28\x9e\x49\x00\xf7\xe4\x33\x1b\x99\xde\xc4"
               "\xb5\x43\x3a\xc7\xd3\x29\xee\xb6\xdd\x26\x54\x5e\x96\xe5\x5b"
               "\x87\x4b\xe9\x09";
    b.inLen  = strlen(b.input);
    b.outLen = SHA512_DIGEST_SIZE;

    test_sha[0] = a;
    test_sha[1] = b;

    ret = wc_InitSha512(&sha);
    if (ret != 0)
        return -4009;

    for (i = 0; i < times; ++i) {
        ret = wc_Sha512Update(&sha, (byte*)test_sha[i].input,(word32)test_sha[i].inLen);
        if (ret != 0)
            return -4010;

        ret = wc_Sha512Final(&sha, hash);
        if (ret != 0)
            return -4011;

        if (memcmp(hash, test_sha[i].output, SHA512_DIGEST_SIZE) != 0)
            return -10 - i;
    }

    return 0;
}
#endif


#ifdef WOLFSSL_SHA384
int sha384_test(void)
{
    Sha384 sha;
    byte   hash[SHA384_DIGEST_SIZE];
    int    ret;

    testVector a, b;
    testVector test_sha[2];
    int times = sizeof(test_sha) / sizeof(struct testVector), i;

    a.input  = "abc";
    a.output = "\xcb\x00\x75\x3f\x45\xa3\x5e\x8b\xb5\xa0\x3d\x69\x9a\xc6\x50"
               "\x07\x27\x2c\x32\xab\x0e\xde\xd1\x63\x1a\x8b\x60\x5a\x43\xff"
               "\x5b\xed\x80\x86\x07\x2b\xa1\xe7\xcc\x23\x58\xba\xec\xa1\x34"
               "\xc8\x25\xa7";
    a.inLen  = strlen(a.input);
    a.outLen = SHA384_DIGEST_SIZE;

    b.input  = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhi"
               "jklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    b.output = "\x09\x33\x0c\x33\xf7\x11\x47\xe8\x3d\x19\x2f\xc7\x82\xcd\x1b"
               "\x47\x53\x11\x1b\x17\x3b\x3b\x05\xd2\x2f\xa0\x80\x86\xe3\xb0"
               "\xf7\x12\xfc\xc7\xc7\x1a\x55\x7e\x2d\xb9\x66\xc3\xe9\xfa\x91"
               "\x74\x60\x39";
    b.inLen  = strlen(b.input);
    b.outLen = SHA384_DIGEST_SIZE;

    test_sha[0] = a;
    test_sha[1] = b;

    ret = wc_InitSha384(&sha);
    if (ret != 0)
        return -4012;

    for (i = 0; i < times; ++i) {
        ret = wc_Sha384Update(&sha, (byte*)test_sha[i].input,(word32)test_sha[i].inLen);
        if (ret != 0)
            return -4013;

        ret = wc_Sha384Final(&sha, hash);
        if (ret != 0)
            return -4014;

        if (memcmp(hash, test_sha[i].output, SHA384_DIGEST_SIZE) != 0)
            return -10 - i;
    }

    return 0;
}
#endif /* WOLFSSL_SHA384 */


#if !defined(NO_HMAC) && !defined(NO_MD5)
int hmac_md5_test(void)
{
    Hmac hmac;
    byte hash[MD5_DIGEST_SIZE];

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
    a.inLen  = strlen(a.input);
    a.outLen = MD5_DIGEST_SIZE;

    b.input  = "what do ya want for nothing?";
    b.output = "\x75\x0c\x78\x3e\x6a\xb0\xb5\x03\xea\xa8\x6e\x31\x0a\x5d\xb7"
               "\x38";
    b.inLen  = strlen(b.input);
    b.outLen = MD5_DIGEST_SIZE;

    c.input  = "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD";
    c.output = "\x56\xbe\x34\x52\x1d\x14\x4c\x88\xdb\xb8\xc7\x33\xf0\xe8\xb3"
               "\xf6";
    c.inLen  = strlen(c.input);
    c.outLen = MD5_DIGEST_SIZE;

    test_hmac[0] = a;
    test_hmac[1] = b;
    test_hmac[2] = c;

    for (i = 0; i < times; ++i) {
#if defined(HAVE_FIPS) || defined(HAVE_CAVIUM)
        if (i == 1)
            continue; /* cavium can't handle short keys, fips not allowed */
#endif
#ifdef HAVE_CAVIUM
        if (wc_HmacInitCavium(&hmac, CAVIUM_DEV_ID) != 0)
            return -20009;
#endif
        ret = wc_HmacSetKey(&hmac, MD5, (byte*)keys[i], (word32)strlen(keys[i]));
        if (ret != 0)
            return -4015;
        ret = wc_HmacUpdate(&hmac, (byte*)test_hmac[i].input,
                   (word32)test_hmac[i].inLen);
        if (ret != 0)
            return -4016;
        ret = wc_HmacFinal(&hmac, hash);
        if (ret != 0)
            return -4017;

        if (memcmp(hash, test_hmac[i].output, MD5_DIGEST_SIZE) != 0)
            return -20 - i;
#ifdef HAVE_CAVIUM
        wc_HmacFreeCavium(&hmac);
#endif
    }

    return 0;
}
#endif /* NO_HMAC && NO_MD5 */

#if !defined(NO_HMAC) && !defined(NO_SHA)
int hmac_sha_test(void)
{
    Hmac hmac;
    byte hash[SHA_DIGEST_SIZE];

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
    a.inLen  = strlen(a.input);
    a.outLen = SHA_DIGEST_SIZE;

    b.input  = "what do ya want for nothing?";
    b.output = "\xef\xfc\xdf\x6a\xe5\xeb\x2f\xa2\xd2\x74\x16\xd5\xf1\x84\xdf"
               "\x9c\x25\x9a\x7c\x79";
    b.inLen  = strlen(b.input);
    b.outLen = SHA_DIGEST_SIZE;

    c.input  = "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD";
    c.output = "\x12\x5d\x73\x42\xb9\xac\x11\xcd\x91\xa3\x9a\xf4\x8a\xa1\x7b"
               "\x4f\x63\xf1\x75\xd3";
    c.inLen  = strlen(c.input);
    c.outLen = SHA_DIGEST_SIZE;

    test_hmac[0] = a;
    test_hmac[1] = b;
    test_hmac[2] = c;

    for (i = 0; i < times; ++i) {
#if defined(HAVE_FIPS) || defined(HAVE_CAVIUM)
        if (i == 1)
            continue; /* cavium can't handle short keys, fips not allowed */
#endif
#ifdef HAVE_CAVIUM
        if (wc_HmacInitCavium(&hmac, CAVIUM_DEV_ID) != 0)
            return -20010;
#endif
        ret = wc_HmacSetKey(&hmac, SHA, (byte*)keys[i], (word32)strlen(keys[i]));
        if (ret != 0)
            return -4018;
        ret = wc_HmacUpdate(&hmac, (byte*)test_hmac[i].input,
                   (word32)test_hmac[i].inLen);
        if (ret != 0)
            return -4019;
        ret = wc_HmacFinal(&hmac, hash);
        if (ret != 0)
            return -4020;

        if (memcmp(hash, test_hmac[i].output, SHA_DIGEST_SIZE) != 0)
            return -20 - i;
#ifdef HAVE_CAVIUM
        wc_HmacFreeCavium(&hmac);
#endif
    }

    return 0;
}
#endif


#if !defined(NO_HMAC) && !defined(NO_SHA256)
int hmac_sha256_test(void)
{
    Hmac hmac;
    byte hash[SHA256_DIGEST_SIZE];

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
    a.output = "\xb0\x34\x4c\x61\xd8\xdb\x38\x53\x5c\xa8\xaf\xce\xaf\x0b\xf1"
               "\x2b\x88\x1d\xc2\x00\xc9\x83\x3d\xa7\x26\xe9\x37\x6c\x2e\x32"
               "\xcf\xf7";
    a.inLen  = strlen(a.input);
    a.outLen = SHA256_DIGEST_SIZE;

    b.input  = "what do ya want for nothing?";
    b.output = "\x5b\xdc\xc1\x46\xbf\x60\x75\x4e\x6a\x04\x24\x26\x08\x95\x75"
               "\xc7\x5a\x00\x3f\x08\x9d\x27\x39\x83\x9d\xec\x58\xb9\x64\xec"
               "\x38\x43";
    b.inLen  = strlen(b.input);
    b.outLen = SHA256_DIGEST_SIZE;

    c.input  = "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD";
    c.output = "\x77\x3e\xa9\x1e\x36\x80\x0e\x46\x85\x4d\xb8\xeb\xd0\x91\x81"
               "\xa7\x29\x59\x09\x8b\x3e\xf8\xc1\x22\xd9\x63\x55\x14\xce\xd5"
               "\x65\xfe";
    c.inLen  = strlen(c.input);
    c.outLen = SHA256_DIGEST_SIZE;

    test_hmac[0] = a;
    test_hmac[1] = b;
    test_hmac[2] = c;

    for (i = 0; i < times; ++i) {
#if defined(HAVE_FIPS) || defined(HAVE_CAVIUM)
        if (i == 1)
            continue; /* cavium can't handle short keys, fips not allowed */
#endif
#ifdef HAVE_CAVIUM
        if (wc_HmacInitCavium(&hmac, CAVIUM_DEV_ID) != 0)
            return -20011;
#endif
        ret = wc_HmacSetKey(&hmac, SHA256, (byte*)keys[i],(word32)strlen(keys[i]));
        if (ret != 0)
            return -4021;
        ret = wc_HmacUpdate(&hmac, (byte*)test_hmac[i].input,
                   (word32)test_hmac[i].inLen);
        if (ret != 0)
            return -4022;
        ret = wc_HmacFinal(&hmac, hash);
        if (ret != 0)
            return -4023;

        if (memcmp(hash, test_hmac[i].output, SHA256_DIGEST_SIZE) != 0)
            return -20 - i;
#ifdef HAVE_CAVIUM
        wc_HmacFreeCavium(&hmac);
#endif
    }

    return 0;
}
#endif


#if !defined(NO_HMAC) && defined(HAVE_BLAKE2)
int hmac_blake2b_test(void)
{
    Hmac hmac;
    byte hash[BLAKE2B_256];

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
    a.output = "\x72\x93\x0d\xdd\xf5\xf7\xe1\x78\x38\x07\x44\x18\x0b\x3f\x51"
               "\x37\x25\xb5\x82\xc2\x08\x83\x2f\x1c\x99\xfd\x03\xa0\x16\x75"
               "\xac\xfd";
    a.inLen  = strlen(a.input);
    a.outLen = BLAKE2B_256;

    b.input  = "what do ya want for nothing?";
    b.output = "\x3d\x20\x50\x71\x05\xc0\x8c\x0c\x38\x44\x1e\xf7\xf9\xd1\x67"
               "\x21\xff\x64\xf5\x94\x00\xcf\xf9\x75\x41\xda\x88\x61\x9d\x7c"
               "\xda\x2b";
    b.inLen  = strlen(b.input);
    b.outLen = BLAKE2B_256;

    c.input  = "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD";
    c.output = "\xda\xfe\x2a\x24\xfc\xe7\xea\x36\x34\xbe\x41\x92\xc7\x11\xa7"
               "\x00\xae\x53\x9c\x11\x9c\x80\x74\x55\x22\x25\x4a\xb9\x55\xd3"
               "\x0f\x87";
    c.inLen  = strlen(c.input);
    c.outLen = BLAKE2B_256;

    test_hmac[0] = a;
    test_hmac[1] = b;
    test_hmac[2] = c;

    for (i = 0; i < times; ++i) {
#if defined(HAVE_FIPS) || defined(HAVE_CAVIUM)
        if (i == 1)
            continue; /* cavium can't handle short keys, fips not allowed */
#endif
#ifdef HAVE_CAVIUM
        if (wc_HmacInitCavium(&hmac, CAVIUM_DEV_ID) != 0)
            return -20011;
#endif
        ret = wc_HmacSetKey(&hmac, BLAKE2B_ID, (byte*)keys[i],
                         (word32)strlen(keys[i]));
        if (ret != 0)
            return -4024;
        ret = wc_HmacUpdate(&hmac, (byte*)test_hmac[i].input,
                   (word32)test_hmac[i].inLen);
        if (ret != 0)
            return -4025;
        ret = wc_HmacFinal(&hmac, hash);
        if (ret != 0)
            return -4026;

        if (memcmp(hash, test_hmac[i].output, BLAKE2B_256) != 0)
            return -20 - i;
#ifdef HAVE_CAVIUM
        wc_HmacFreeCavium(&hmac);
#endif
    }

    return 0;
}
#endif


#if !defined(NO_HMAC) && defined(WOLFSSL_SHA384)
int hmac_sha384_test(void)
{
    Hmac hmac;
    byte hash[SHA384_DIGEST_SIZE];

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
    a.output = "\xaf\xd0\x39\x44\xd8\x48\x95\x62\x6b\x08\x25\xf4\xab\x46\x90"
               "\x7f\x15\xf9\xda\xdb\xe4\x10\x1e\xc6\x82\xaa\x03\x4c\x7c\xeb"
               "\xc5\x9c\xfa\xea\x9e\xa9\x07\x6e\xde\x7f\x4a\xf1\x52\xe8\xb2"
               "\xfa\x9c\xb6";
    a.inLen  = strlen(a.input);
    a.outLen = SHA384_DIGEST_SIZE;

    b.input  = "what do ya want for nothing?";
    b.output = "\xaf\x45\xd2\xe3\x76\x48\x40\x31\x61\x7f\x78\xd2\xb5\x8a\x6b"
               "\x1b\x9c\x7e\xf4\x64\xf5\xa0\x1b\x47\xe4\x2e\xc3\x73\x63\x22"
               "\x44\x5e\x8e\x22\x40\xca\x5e\x69\xe2\xc7\x8b\x32\x39\xec\xfa"
               "\xb2\x16\x49";
    b.inLen  = strlen(b.input);
    b.outLen = SHA384_DIGEST_SIZE;

    c.input  = "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD";
    c.output = "\x88\x06\x26\x08\xd3\xe6\xad\x8a\x0a\xa2\xac\xe0\x14\xc8\xa8"
               "\x6f\x0a\xa6\x35\xd9\x47\xac\x9f\xeb\xe8\x3e\xf4\xe5\x59\x66"
               "\x14\x4b\x2a\x5a\xb3\x9d\xc1\x38\x14\xb9\x4e\x3a\xb6\xe1\x01"
               "\xa3\x4f\x27";
    c.inLen  = strlen(c.input);
    c.outLen = SHA384_DIGEST_SIZE;

    test_hmac[0] = a;
    test_hmac[1] = b;
    test_hmac[2] = c;

    for (i = 0; i < times; ++i) {
#if defined(HAVE_FIPS)
        if (i == 1)
            continue; /* fips not allowed */
#endif
        ret = wc_HmacSetKey(&hmac, SHA384, (byte*)keys[i],(word32)strlen(keys[i]));
        if (ret != 0)
            return -4027;
        ret = wc_HmacUpdate(&hmac, (byte*)test_hmac[i].input,
                   (word32)test_hmac[i].inLen);
        if (ret != 0)
            return -4028;
        ret = wc_HmacFinal(&hmac, hash);
        if (ret != 0)
            return -4029;

        if (memcmp(hash, test_hmac[i].output, SHA384_DIGEST_SIZE) != 0)
            return -20 - i;
    }

    return 0;
}
#endif


#if !defined(NO_HMAC) && defined(WOLFSSL_SHA512)
int hmac_sha512_test(void)
{
    Hmac hmac;
    byte hash[SHA512_DIGEST_SIZE];

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
    a.output = "\x87\xaa\x7c\xde\xa5\xef\x61\x9d\x4f\xf0\xb4\x24\x1a\x1d\x6c"
               "\xb0\x23\x79\xf4\xe2\xce\x4e\xc2\x78\x7a\xd0\xb3\x05\x45\xe1"
               "\x7c\xde\xda\xa8\x33\xb7\xd6\xb8\xa7\x02\x03\x8b\x27\x4e\xae"
               "\xa3\xf4\xe4\xbe\x9d\x91\x4e\xeb\x61\xf1\x70\x2e\x69\x6c\x20"
               "\x3a\x12\x68\x54";
    a.inLen  = strlen(a.input);
    a.outLen = SHA512_DIGEST_SIZE;

    b.input  = "what do ya want for nothing?";
    b.output = "\x16\x4b\x7a\x7b\xfc\xf8\x19\xe2\xe3\x95\xfb\xe7\x3b\x56\xe0"
               "\xa3\x87\xbd\x64\x22\x2e\x83\x1f\xd6\x10\x27\x0c\xd7\xea\x25"
               "\x05\x54\x97\x58\xbf\x75\xc0\x5a\x99\x4a\x6d\x03\x4f\x65\xf8"
               "\xf0\xe6\xfd\xca\xea\xb1\xa3\x4d\x4a\x6b\x4b\x63\x6e\x07\x0a"
               "\x38\xbc\xe7\x37";
    b.inLen  = strlen(b.input);
    b.outLen = SHA512_DIGEST_SIZE;

    c.input  = "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD";
    c.output = "\xfa\x73\xb0\x08\x9d\x56\xa2\x84\xef\xb0\xf0\x75\x6c\x89\x0b"
               "\xe9\xb1\xb5\xdb\xdd\x8e\xe8\x1a\x36\x55\xf8\x3e\x33\xb2\x27"
               "\x9d\x39\xbf\x3e\x84\x82\x79\xa7\x22\xc8\x06\xb4\x85\xa4\x7e"
               "\x67\xc8\x07\xb9\x46\xa3\x37\xbe\xe8\x94\x26\x74\x27\x88\x59"
               "\xe1\x32\x92\xfb";
    c.inLen  = strlen(c.input);
    c.outLen = SHA512_DIGEST_SIZE;

    test_hmac[0] = a;
    test_hmac[1] = b;
    test_hmac[2] = c;

    for (i = 0; i < times; ++i) {
#if defined(HAVE_FIPS)
        if (i == 1)
            continue; /* fips not allowed */
#endif
        ret = wc_HmacSetKey(&hmac, SHA512, (byte*)keys[i],(word32)strlen(keys[i]));
        if (ret != 0)
            return -4030;
        ret = wc_HmacUpdate(&hmac, (byte*)test_hmac[i].input,
                   (word32)test_hmac[i].inLen);
        if (ret != 0)
            return -4031;
        ret = wc_HmacFinal(&hmac, hash);
        if (ret != 0)
            return -4032;

        if (memcmp(hash, test_hmac[i].output, SHA512_DIGEST_SIZE) != 0)
            return -20 - i;
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
        int  keylen = 8;  /* strlen with key 0x00 not good */
        if (i == 3)
            keylen = 4;

#ifdef HAVE_CAVIUM
        if (wc_Arc4InitCavium(&enc, CAVIUM_DEV_ID) != 0)
            return -20001;
        if (wc_Arc4InitCavium(&dec, CAVIUM_DEV_ID) != 0)
            return -20002;
#endif

        wc_Arc4SetKey(&enc, (byte*)keys[i], keylen);
        wc_Arc4SetKey(&dec, (byte*)keys[i], keylen);

        wc_Arc4Process(&enc, cipher, (byte*)test_arc4[i].input,
                    (word32)test_arc4[i].outLen);
        wc_Arc4Process(&dec, plain,  cipher, (word32)test_arc4[i].outLen);

        if (memcmp(plain, test_arc4[i].input, test_arc4[i].outLen))
            return -20 - i;

        if (memcmp(cipher, test_arc4[i].output, test_arc4[i].outLen))
            return -20 - 5 - i;

#ifdef HAVE_CAVIUM
        wc_Arc4FreeCavium(&enc);
        wc_Arc4FreeCavium(&dec);
#endif
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
        memcpy(plain,  keys[i], 16);
        memcpy(cipher, ivs[i],  16);

        wc_Hc128_SetKey(&enc, plain, cipher);
        wc_Hc128_SetKey(&dec, plain, cipher);

        /* align input */
        memcpy(plain, test_hc128[i].input, test_hc128[i].outLen);
        wc_Hc128_Process(&enc, cipher, plain,  (word32)test_hc128[i].outLen);
        wc_Hc128_Process(&dec, plain,  cipher, (word32)test_hc128[i].outLen);

        if (memcmp(plain, test_hc128[i].input, test_hc128[i].outLen))
            return -120 - i;

        if (memcmp(cipher, test_hc128[i].output, test_hc128[i].outLen))
            return -120 - 5 - i;
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
        memcpy(plain,  keys[i], 16);
        if (ivs[i]) {
            memcpy(cipher, ivs[i],   8);
            iv = cipher;
        } else
            iv = NULL;
        wc_RabbitSetKey(&enc, plain, iv);
        wc_RabbitSetKey(&dec, plain, iv);

        /* align input */
        memcpy(plain, test_rabbit[i].input, test_rabbit[i].outLen);
        wc_RabbitProcess(&enc, cipher, plain,  (word32)test_rabbit[i].outLen);
        wc_RabbitProcess(&dec, plain,  cipher, (word32)test_rabbit[i].outLen);

        if (memcmp(plain, test_rabbit[i].input, test_rabbit[i].outLen))
            return -130 - i;

        if (memcmp(cipher, test_rabbit[i].output, test_rabbit[i].outLen))
            return -130 - 5 - i;
    }

    return 0;
}
#endif /* NO_RABBIT */


#ifdef HAVE_CHACHA
int chacha_test(void)
{
    ChaCha enc;
    ChaCha dec;
    byte   cipher[32];
    byte   plain[32];
    byte   input[] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
    word32 keySz;
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

    static const byte ivs1[] = {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00};
    static const byte ivs2[] = {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00};
    static const byte ivs3[] = {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x01};
    static const byte ivs4[] = {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00};


    const byte* ivs[] = {ivs1, ivs2, ivs3, ivs4};


    byte a[] = {0x76,0xb8,0xe0,0xad,0xa0,0xf1,0x3d,0x90};
    byte b[] = {0x45,0x40,0xf0,0x5a,0x9f,0x1f,0xb2,0x96};
    byte c[] = {0xde,0x9c,0xba,0x7b,0xf3,0xd6,0x9e,0xf5};
    byte d[] = {0x89,0x67,0x09,0x52,0x60,0x83,0x64,0xfd};

    byte* test_chacha[4];

    test_chacha[0] = a;
    test_chacha[1] = b;
    test_chacha[2] = c;
    test_chacha[3] = d;

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

        wc_Chacha_SetKey(&enc, keys[i], keySz);
        wc_Chacha_SetKey(&dec, keys[i], keySz);

        wc_Chacha_SetIV(&enc, cipher, 0);
        wc_Chacha_SetIV(&dec, cipher, 0);
        XMEMCPY(plain, input, 8);

        wc_Chacha_Process(&enc, cipher, plain,  (word32)8);
        wc_Chacha_Process(&dec, plain,  cipher, (word32)8);

        if (memcmp(test_chacha[i], cipher, 8))
            return -130 - 5 - i;

        if (memcmp(plain, input, 8))
            return -130 - i;
    }

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

    const byte msg[] =
    {
        0x43,0x72,0x79,0x70,0x74,0x6f,0x67,0x72,
        0x61,0x70,0x68,0x69,0x63,0x20,0x46,0x6f,
        0x72,0x75,0x6d,0x20,0x52,0x65,0x73,0x65,
        0x61,0x72,0x63,0x68,0x20,0x47,0x72,0x6f,
        0x75,0x70
    };

    const byte msg2[] =
    {
        0x48,0x65,0x6c,0x6c,0x6f,0x20,0x77,0x6f,0x72,
        0x6c,0x64,0x21
    };

    const byte msg3[] =
    {
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00
    };

    const byte correct[] =
    {
        0xa8,0x06,0x1d,0xc1,0x30,0x51,0x36,0xc6,
        0xc2,0x2b,0x8b,0xaf,0x0c,0x01,0x27,0xa9

    };

    const byte correct2[] =
    {
        0xa6,0xf7,0x45,0x00,0x8f,0x81,0xc9,0x16,
        0xa2,0x0d,0xcc,0x74,0xee,0xf2,0xb2,0xf0
    };

    const byte correct3[] =
    {
        0x49,0xec,0x78,0x09,0x0e,0x48,0x1e,0xc6,
        0xc2,0x6b,0x33,0xb9,0x1c,0xcc,0x03,0x07
    };

    const byte key[] = {
        0x85,0xd6,0xbe,0x78,0x57,0x55,0x6d,0x33,
        0x7f,0x44,0x52,0xfe,0x42,0xd5,0x06,0xa8,
        0x01,0x03,0x80,0x8a,0xfb,0x0d,0xb2,0xfd,
        0x4a,0xbf,0xf6,0xaf,0x41,0x49,0xf5,0x1b
    };

    const byte key2[] = {
        0x74,0x68,0x69,0x73,0x20,0x69,0x73,0x20,
        0x33,0x32,0x2d,0x62,0x79,0x74,0x65,0x20,
        0x6b,0x65,0x79,0x20,0x66,0x6f,0x72,0x20,
        0x50,0x6f,0x6c,0x79,0x31,0x33,0x30,0x35
    };

    const byte* msgs[]  = {msg, msg2, msg3};
    word32      szm[]   = {sizeof(msg),sizeof(msg2),sizeof(msg3)};
    const byte* keys[]  = {key, key2, key2};
    const byte* tests[] = {correct, correct2, correct3};

    for (i = 0; i < 3; i++) {
        ret = wc_Poly1305SetKey(&enc, keys[i], 32);
        if (ret != 0)
            return -1001;

        ret = wc_Poly1305Update(&enc, msgs[i], szm[i]);
        if (ret != 0)
            return -1005;

        ret = wc_Poly1305Final(&enc, tag);
        if (ret != 0)
            return -60;

        if (memcmp(tag, tests[i], sizeof(tag)))
            return -61;
    }

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

    byte generatedCiphertext[272];
    byte generatedPlaintext[272];
    byte generatedAuthTag[CHACHA20_POLY1305_AEAD_AUTHTAG_SIZE];
    int err;

    XMEMSET(generatedCiphertext, 0, sizeof(generatedCiphertext));
    XMEMSET(generatedAuthTag, 0, sizeof(generatedAuthTag));
    XMEMSET(generatedPlaintext, 0, sizeof(generatedPlaintext));

    /* Test #1 */

    err = wc_ChaCha20Poly1305_Encrypt(key1, iv1,
                                       aad1, sizeof(aad1),
                                       plaintext1, sizeof(plaintext1),
                                       generatedCiphertext, generatedAuthTag);
    if (err)
    {
        return err;
    }

    /* -- Check the ciphertext and authtag */

    if (XMEMCMP(generatedCiphertext, cipher1, sizeof(cipher1)))
    {
        return -1064;
    }

    if (XMEMCMP(generatedAuthTag, authTag1, sizeof(authTag1)))
    {
        return -1065;
    }

    /* -- Verify decryption works */

    err = wc_ChaCha20Poly1305_Decrypt(key1, iv1,
                                       aad1, sizeof(aad1),
                                       cipher1, sizeof(cipher1),
                                       authTag1, generatedPlaintext);
    if (err)
    {
        return err;
    }

    if (XMEMCMP(generatedPlaintext, plaintext1, sizeof( plaintext1)))
    {
        return -1066;
    }

    XMEMSET(generatedCiphertext, 0, sizeof(generatedCiphertext));
    XMEMSET(generatedAuthTag, 0, sizeof(generatedAuthTag));
    XMEMSET(generatedPlaintext, 0, sizeof(generatedPlaintext));

    /* Test #2 */

    err = wc_ChaCha20Poly1305_Encrypt(key2, iv2,
                                       aad2, sizeof(aad2),
                                       plaintext2, sizeof(plaintext2),
                                       generatedCiphertext, generatedAuthTag);
    if (err)
    {
        return err;
    }

    /* -- Check the ciphertext and authtag */

    if (XMEMCMP(generatedCiphertext, cipher2, sizeof(cipher2)))
    {
        return -1067;
    }

    if (XMEMCMP(generatedAuthTag, authTag2, sizeof(authTag2)))
    {
        return -1068;
    }

    /* -- Verify decryption works */

    err = wc_ChaCha20Poly1305_Decrypt(key2, iv2,
                                      aad2, sizeof(aad2),
                                      cipher2, sizeof(cipher2),
                                      authTag2, generatedPlaintext);
    if (err)
    {
        return err;
    }

    if (XMEMCMP(generatedPlaintext, plaintext2, sizeof(plaintext2)))
    {
        return -1069;
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
        return -31;

    wc_Des_CbcEncrypt(&enc, cipher, vector, sizeof(vector));
    ret = wc_Des_SetKey(&dec, key, iv, DES_DECRYPTION);
    if (ret != 0)
        return -32;
    wc_Des_CbcDecrypt(&dec, plain, cipher, sizeof(cipher));

    if (memcmp(plain, vector, sizeof(plain)))
        return -33;

    if (memcmp(cipher, verify, sizeof(cipher)))
        return -34;

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


#ifdef HAVE_CAVIUM
    if (wc_Des3_InitCavium(&enc, CAVIUM_DEV_ID) != 0)
        return -20005;
    if (wc_Des3_InitCavium(&dec, CAVIUM_DEV_ID) != 0)
        return -20006;
#endif
    ret = wc_Des3_SetKey(&enc, key3, iv3, DES_ENCRYPTION);
    if (ret != 0)
        return -31;
    ret = wc_Des3_SetKey(&dec, key3, iv3, DES_DECRYPTION);
    if (ret != 0)
        return -32;
    ret = wc_Des3_CbcEncrypt(&enc, cipher, vector, sizeof(vector));
    if (ret != 0)
        return -33;
    ret = wc_Des3_CbcDecrypt(&dec, plain, cipher, sizeof(cipher));
    if (ret != 0)
        return -34;

    if (memcmp(plain, vector, sizeof(plain)))
        return -35;

    if (memcmp(cipher, verify3, sizeof(cipher)))
        return -36;

#ifdef HAVE_CAVIUM
    wc_Des3_FreeCavium(&enc);
    wc_Des3_FreeCavium(&dec);
#endif
    return 0;
}
#endif /* NO_DES */


#ifndef NO_AES
int aes_test(void)
{
    Aes enc;
    Aes dec;

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
    int  ret;

#ifdef HAVE_CAVIUM
        if (wc_AesInitCavium(&enc, CAVIUM_DEV_ID) != 0)
            return -20003;
        if (wc_AesInitCavium(&dec, CAVIUM_DEV_ID) != 0)
            return -20004;
#endif
    ret = wc_AesSetKey(&enc, key, AES_BLOCK_SIZE, iv, AES_ENCRYPTION);
    if (ret != 0)
        return -1001;
    ret = wc_AesSetKey(&dec, key, AES_BLOCK_SIZE, iv, AES_DECRYPTION);
    if (ret != 0)
        return -1002;

    ret = wc_AesCbcEncrypt(&enc, cipher, msg,   AES_BLOCK_SIZE);
    if (ret != 0)
        return -1005;
    ret = wc_AesCbcDecrypt(&dec, plain, cipher, AES_BLOCK_SIZE);
    if (ret != 0)
        return -1006;

    if (memcmp(plain, msg, AES_BLOCK_SIZE))
        return -60;

    if (memcmp(cipher, verify, AES_BLOCK_SIZE))
        return -61;

#ifdef HAVE_CAVIUM
        wc_AesFreeCavium(&enc);
        wc_AesFreeCavium(&dec);
#endif
#ifdef WOLFSSL_AES_COUNTER
    {
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

        wc_AesSetKeyDirect(&enc, ctrKey, AES_BLOCK_SIZE, ctrIv, AES_ENCRYPTION);
        /* Ctr only uses encrypt, even on key setup */
        wc_AesSetKeyDirect(&dec, ctrKey, AES_BLOCK_SIZE, ctrIv, AES_ENCRYPTION);

        wc_AesCtrEncrypt(&enc, cipher, ctrPlain, AES_BLOCK_SIZE*4);
        wc_AesCtrEncrypt(&dec, plain, cipher, AES_BLOCK_SIZE*4);

        if (memcmp(plain, ctrPlain, AES_BLOCK_SIZE*4))
            return -66;

        if (memcmp(cipher, ctrCipher, AES_BLOCK_SIZE*4))
            return -67;

        /* let's try with just 9 bytes, non block size test */
        wc_AesSetKeyDirect(&enc, ctrKey, AES_BLOCK_SIZE, ctrIv, AES_ENCRYPTION);
        /* Ctr only uses encrypt, even on key setup */
        wc_AesSetKeyDirect(&dec, ctrKey, AES_BLOCK_SIZE, ctrIv, AES_ENCRYPTION);

        wc_AesCtrEncrypt(&enc, cipher, ctrPlain, 9);
        wc_AesCtrEncrypt(&dec, plain, cipher, 9);

        if (memcmp(plain, ctrPlain, 9))
            return -68;

        if (memcmp(cipher, ctrCipher, 9))
            return -69;

        /* and an additional 9 bytes to reuse tmp left buffer */
        wc_AesCtrEncrypt(&enc, cipher, ctrPlain, 9);
        wc_AesCtrEncrypt(&dec, plain, cipher, 9);

        if (memcmp(plain, ctrPlain, 9))
            return -70;

        if (memcmp(cipher, oddCipher, 9))
            return -71;
    }
#endif /* WOLFSSL_AES_COUNTER */

#if defined(WOLFSSL_AESNI) && defined(WOLFSSL_AES_DIRECT)
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
            return -1003;
        wc_AesEncryptDirect(&enc, cipher, niPlain);
        if (XMEMCMP(cipher, niCipher, AES_BLOCK_SIZE) != 0)
            return -20006;

        XMEMSET(plain, 0, AES_BLOCK_SIZE);
        ret = wc_AesSetKey(&dec, niKey, sizeof(niKey), plain, AES_DECRYPTION);
        if (ret != 0)
            return -1004;
        wc_AesDecryptDirect(&dec, plain, niCipher);
        if (XMEMCMP(plain, niPlain, AES_BLOCK_SIZE) != 0)
            return -20007;
    }
#endif /* WOLFSSL_AESNI && WOLFSSL_AES_DIRECT */

    return 0;
}

#ifdef HAVE_AESGCM
int aesgcm_test(void)
{
    Aes enc;

    /*
     * This is Test Case 16 from the document Galois/
     * Counter Mode of Operation (GCM) by McGrew and
     * Viega.
     */
    const byte k[] =
    {
        0xfe, 0xff, 0xe9, 0x92, 0x86, 0x65, 0x73, 0x1c,
        0x6d, 0x6a, 0x8f, 0x94, 0x67, 0x30, 0x83, 0x08,
        0xfe, 0xff, 0xe9, 0x92, 0x86, 0x65, 0x73, 0x1c,
        0x6d, 0x6a, 0x8f, 0x94, 0x67, 0x30, 0x83, 0x08
    };

    const byte iv[] =
    {
        0xca, 0xfe, 0xba, 0xbe, 0xfa, 0xce, 0xdb, 0xad,
        0xde, 0xca, 0xf8, 0x88
    };

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

    const byte a[] =
    {
        0xfe, 0xed, 0xfa, 0xce, 0xde, 0xad, 0xbe, 0xef,
        0xfe, 0xed, 0xfa, 0xce, 0xde, 0xad, 0xbe, 0xef,
        0xab, 0xad, 0xda, 0xd2
    };

    const byte c[] =
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

    const byte t[] =
    {
        0x76, 0xfc, 0x6e, 0xce, 0x0f, 0x4e, 0x17, 0x68,
        0xcd, 0xdf, 0x88, 0x53, 0xbb, 0x2d, 0x55, 0x1b
    };

    byte t2[sizeof(t)];
    byte p2[sizeof(c)];
    byte c2[sizeof(p)];

    int result;

    memset(t2, 0, sizeof(t2));
    memset(c2, 0, sizeof(c2));
    memset(p2, 0, sizeof(p2));

    wc_AesGcmSetKey(&enc, k, sizeof(k));
    /* AES-GCM encrypt and decrypt both use AES encrypt internally */
    wc_AesGcmEncrypt(&enc, c2, p, sizeof(c2), iv, sizeof(iv),
                                                 t2, sizeof(t2), a, sizeof(a));
    if (memcmp(c, c2, sizeof(c2)))
        return -68;
    if (memcmp(t, t2, sizeof(t2)))
        return -69;

    result = wc_AesGcmDecrypt(&enc, p2, c2, sizeof(p2), iv, sizeof(iv),
                                                 t2, sizeof(t2), a, sizeof(a));
    if (result != 0)
        return -70;
    if (memcmp(p, p2, sizeof(p2)))
        return -71;

    return 0;
}

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

    const byte k3[] =
    {
        0xb8, 0xe4, 0x9a, 0x5e, 0x37, 0xf9, 0x98, 0x2b,
        0xb9, 0x6d, 0xd0, 0xc9, 0xb6, 0xab, 0x26, 0xac
    };
    const byte iv3[] =
    {
        0xe4, 0x4a, 0x42, 0x18, 0x8c, 0xae, 0x94, 0x92,
        0x6a, 0x9c, 0x26, 0xb0
    };
    const byte a3[] =
    {
        0x9d, 0xb9, 0x61, 0x68, 0xa6, 0x76, 0x7a, 0x31,
        0xf8, 0x29, 0xe4, 0x72, 0x61, 0x68, 0x3f, 0x8a
    };
    const byte t3[] =
    {
        0x23, 0xe2, 0x9f, 0x66, 0xe4, 0xc6, 0x52, 0x48
    };

    byte tag[16];

    memset(tag, 0, sizeof(tag));
    wc_GmacSetKey(&gmac, k1, sizeof(k1));
    wc_GmacUpdate(&gmac, iv1, sizeof(iv1), a1, sizeof(a1), tag, sizeof(t1));
    if (memcmp(t1, tag, sizeof(t1)) != 0)
        return -126;

    memset(tag, 0, sizeof(tag));
    wc_GmacSetKey(&gmac, k2, sizeof(k2));
    wc_GmacUpdate(&gmac, iv2, sizeof(iv2), a2, sizeof(a2), tag, sizeof(t2));
    if (memcmp(t2, tag, sizeof(t2)) != 0)
        return -127;

    memset(tag, 0, sizeof(tag));
    wc_GmacSetKey(&gmac, k3, sizeof(k3));
    wc_GmacUpdate(&gmac, iv3, sizeof(iv3), a3, sizeof(a3), tag, sizeof(t3));
    if (memcmp(t3, tag, sizeof(t3)) != 0)
        return -128;

    return 0;
}
#endif /* HAVE_AESGCM */

#ifdef HAVE_AESCCM
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

    const byte a[] =
    {
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07
    };

    const byte c[] =
    {
        0x58, 0x8c, 0x97, 0x9a, 0x61, 0xc6, 0x63, 0xd2,
        0xf0, 0x66, 0xd0, 0xc2, 0xc0, 0xf9, 0x89, 0x80,
        0x6d, 0x5f, 0x6b, 0x61, 0xda, 0xc3, 0x84
    };

    const byte t[] =
    {
        0x17, 0xe8, 0xd1, 0x2c, 0xfd, 0xf9, 0x26, 0xe0
    };

    byte t2[sizeof(t)];
    byte p2[sizeof(p)];
    byte c2[sizeof(c)];

    int result;

    memset(t2, 0, sizeof(t2));
    memset(c2, 0, sizeof(c2));
    memset(p2, 0, sizeof(p2));

    wc_AesCcmSetKey(&enc, k, sizeof(k));
    /* AES-CCM encrypt and decrypt both use AES encrypt internally */
    wc_AesCcmEncrypt(&enc, c2, p, sizeof(c2), iv, sizeof(iv),
                                                 t2, sizeof(t2), a, sizeof(a));
    if (memcmp(c, c2, sizeof(c2)))
        return -107;
    if (memcmp(t, t2, sizeof(t2)))
        return -108;

    result = wc_AesCcmDecrypt(&enc, p2, c2, sizeof(p2), iv, sizeof(iv),
                                                 t2, sizeof(t2), a, sizeof(a));
    if (result != 0)
        return -109;
    if (memcmp(p, p2, sizeof(p2)))
        return -110;

    /* Test the authentication failure */
    t2[0]++; /* Corrupt the authentication tag. */
    result = wc_AesCcmDecrypt(&enc, p2, c, sizeof(p2), iv, sizeof(iv),
                                                 t2, sizeof(t2), a, sizeof(a));
    if (result == 0)
        return -111;

    /* Clear c2 to compare against p2. p2 should be set to zero in case of
     * authentication fail. */
    memset(c2, 0, sizeof(c2));
    if (memcmp(p2, c2, sizeof(p2)))
        return -112;

    return 0;
}
#endif /* HAVE_AESCCM */


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
    int i, testsSz;
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
                wc_CamelliaEncryptDirect(&cam, out, testVectors[i].plaintext);
                if (memcmp(out, testVectors[i].ciphertext, CAMELLIA_BLOCK_SIZE))
                    return testVectors[i].errorCode;
                break;
            case CAM_ECB_DEC:
                wc_CamelliaDecryptDirect(&cam, out, testVectors[i].ciphertext);
                if (memcmp(out, testVectors[i].plaintext, CAMELLIA_BLOCK_SIZE))
                    return testVectors[i].errorCode;
                break;
            case CAM_CBC_ENC:
                wc_CamelliaCbcEncrypt(&cam, out, testVectors[i].plaintext,
                                                           CAMELLIA_BLOCK_SIZE);
                if (memcmp(out, testVectors[i].ciphertext, CAMELLIA_BLOCK_SIZE))
                    return testVectors[i].errorCode;
                break;
            case CAM_CBC_DEC:
                wc_CamelliaCbcDecrypt(&cam, out, testVectors[i].ciphertext,
                                                           CAMELLIA_BLOCK_SIZE);
                if (memcmp(out, testVectors[i].plaintext, CAMELLIA_BLOCK_SIZE))
                    return testVectors[i].errorCode;
                break;
            default:
                break;
        }
    }

    /* Setting the IV and checking it was actually set. */
    wc_CamelliaSetIV(&cam, ivc);
    if (XMEMCMP(cam.reg, ivc, CAMELLIA_BLOCK_SIZE))
        return -1;

    /* Setting the IV to NULL should be same as all zeros IV */
    if (wc_CamelliaSetIV(&cam, NULL) != 0 ||
                                    XMEMCMP(cam.reg, ive, CAMELLIA_BLOCK_SIZE))
        return -1;

    /* First parameter should never be null */
    if (wc_CamelliaSetIV(NULL, NULL) == 0)
        return -1;

    /* First parameter should never be null, check it fails */
    if (wc_CamelliaSetKey(NULL, k1, sizeof(k1), NULL) == 0)
        return -1;

    /* Key should have a size of 16, 24, or 32 */
    if (wc_CamelliaSetKey(&cam, k1, 0, NULL) == 0)
        return -1;

    return 0;
}
#endif /* HAVE_CAMELLIA */


#if defined(HAVE_HASHDRBG) || defined(NO_RC4)

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

    byte output[SHA256_DIGEST_SIZE * 4];
    int ret;

    ret = wc_RNG_HealthTest(0, test1Entropy, sizeof(test1Entropy), NULL, 0,
                            output, sizeof(output));
    if (ret != 0)
        return -39;

    if (XMEMCMP(test1Output, output, sizeof(output)) != 0)
        return -40;

    ret = wc_RNG_HealthTest(1, test2EntropyA, sizeof(test2EntropyA),
                            test2EntropyB, sizeof(test2EntropyB),
                            output, sizeof(output));
    if (ret != 0)
        return -41;

    if (XMEMCMP(test2Output, output, sizeof(output)) != 0)
        return -42;

    return 0;
}

#else /* HAVE_HASHDRBG || NO_RC4 */

int random_test(void)
{
    RNG  rng;
    byte block[32];
    int ret;

#ifdef HAVE_CAVIUM
    ret = wc_InitRngCavium(&rng, CAVIUM_DEV_ID);
    if (ret != 0) return -2007;
#endif
    ret = wc_InitRng(&rng);
    if (ret != 0) return -39;

    ret = wc_RNG_GenerateBlock(&rng, block, sizeof(block));
    if (ret != 0) return -40;

    wc_FreeRng(&rng);

    return 0;
}

#endif /* HAVE_HASHDRBG || NO_RC4 */


#ifdef HAVE_NTRU

byte GetEntropy(ENTROPY_CMD cmd, byte* out);

byte GetEntropy(ENTROPY_CMD cmd, byte* out)
{
    static RNG rng;

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

#ifndef NO_RSA

#if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048)
    #ifdef FREESCALE_MQX
        static const char* clientKey  = "a:\\certs\\client-key.der";
        static const char* clientCert = "a:\\certs\\client-cert.der";
        #ifdef WOLFSSL_CERT_GEN
            static const char* caKeyFile  = "a:\\certs\\ca-key.der";
            static const char* caCertFile = "a:\\certs\\ca-cert.pem";
            #ifdef HAVE_ECC
                static const char* eccCaKeyFile  = "a:\\certs\\ecc-key.der";
                static const char* eccCaCertFile = "a:\\certs\\server-ecc.pem";
            #endif
        #endif
    #elif defined(WOLFSSL_MKD_SHELL)
        static char* clientKey = "certs/client-key.der";
        static char* clientCert = "certs/client-cert.der";
        void set_clientKey(char *key) {  clientKey = key ; }
        void set_clientCert(char *cert) {  clientCert = cert ; }
        #ifdef WOLFSSL_CERT_GEN
            static char* caKeyFile  = "certs/ca-key.der";
            static char* caCertFile = "certs/ca-cert.pem";
            void set_caKeyFile (char * key)  { caKeyFile   = key ; }
            void set_caCertFile(char * cert) { caCertFile = cert ; }
            #ifdef HAVE_ECC
                static const char* eccCaKeyFile  = "certs/ecc-key.der";
                static const char* eccCaCertFile = "certs/server-ecc.pem";
                void set_eccCaKeyFile (char * key)  { eccCaKeyFile  = key ; }
                void set_eccCaCertFile(char * cert) { eccCaCertFile = cert ; }
            #endif
        #endif
    #else
        static const char* clientKey  = "./certs/client-key.der";
        static const char* clientCert = "./certs/client-cert.der";
        #ifdef WOLFSSL_CERT_GEN
            static const char* caKeyFile  = "./certs/ca-key.der";
            static const char* caCertFile = "./certs/ca-cert.pem";
            #ifdef HAVE_ECC
                static const char* eccCaKeyFile  = "./certs/ecc-key.der";
                static const char* eccCaCertFile = "./certs/server-ecc.pem";
            #endif
        #endif
    #endif
#endif


int rsa_test(void)
{
    byte*   tmp;
    size_t bytes;
    RsaKey key;
    RNG    rng;
    word32 idx = 0;
    int    ret;
    byte   in[] = "Everyone gets Friday off.";
    word32 inLen = (word32)strlen((char*)in);
    byte   out[256];
    byte   plain[256];
#if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048)
    FILE*  file, * file2;
#endif
#ifdef WOLFSSL_TEST_CERT
    DecodedCert cert;
#endif

    tmp = (byte*)malloc(FOURK_BUF);
    if (tmp == NULL)
        return -40;

#ifdef USE_CERT_BUFFERS_1024
    XMEMCPY(tmp, client_key_der_1024, sizeof_client_key_der_1024);
    bytes = sizeof_client_key_der_1024;
#elif defined(USE_CERT_BUFFERS_2048)
    XMEMCPY(tmp, client_key_der_2048, sizeof_client_key_der_2048);
    bytes = sizeof_client_key_der_2048;
#else
    file = fopen(clientKey, "rb");

    if (!file) {
        err_sys("can't open ./certs/client-key.der, "
                "Please run from wolfSSL home dir", -40);
        free(tmp);
        return -40;
    }

    bytes = fread(tmp, 1, FOURK_BUF, file);
    fclose(file);
#endif /* USE_CERT_BUFFERS */

#ifdef HAVE_CAVIUM
    wc_RsaInitCavium(&key, CAVIUM_DEV_ID);
#endif
    ret = wc_InitRsaKey(&key, 0);
    if (ret != 0) {
        free(tmp);
        return -39;
    }
    ret = wc_RsaPrivateKeyDecode(tmp, &idx, &key, (word32)bytes);
    if (ret != 0) {
        free(tmp);
        return -41;
    }
    ret = wc_InitRng(&rng);
    if (ret != 0) {
        free(tmp);
        return -42;
    }
    ret = wc_RsaPublicEncrypt(in, inLen, out, sizeof(out), &key, &rng);
    if (ret < 0) {
        free(tmp);
        return -43;
    }
    ret = wc_RsaPrivateDecrypt(out, ret, plain, sizeof(plain), &key);
    if (ret < 0) {
        free(tmp);
        return -44;
    }
    if (memcmp(plain, in, inLen)) {
        free(tmp);
        return -45;
    }
    ret = wc_RsaSSL_Sign(in, inLen, out, sizeof(out), &key, &rng);
    if (ret < 0) {
        free(tmp);
        return -46;
    }
    memset(plain, 0, sizeof(plain));
    ret = wc_RsaSSL_Verify(out, ret, plain, sizeof(plain), &key);
    if (ret < 0) {
        free(tmp);
        return -47;
    }
    if (memcmp(plain, in, ret)) {
        free(tmp);
        return -48;
    }
#if defined(WOLFSSL_MDK_ARM)
    #define sizeof(s) strlen((char *)(s))
#endif

#ifdef USE_CERT_BUFFERS_1024
    XMEMCPY(tmp, client_cert_der_1024, sizeof_client_cert_der_1024);
    bytes = sizeof_client_cert_der_1024;
#elif defined(USE_CERT_BUFFERS_2048)
    XMEMCPY(tmp, client_cert_der_2048, sizeof_client_cert_der_2048);
    bytes = sizeof_client_cert_der_2048;
#else
    file2 = fopen(clientCert, "rb");
    if (!file2) {
        free(tmp);
        return -49;
    }

    bytes = fread(tmp, 1, FOURK_BUF, file2);
    fclose(file2);
#endif

#ifdef sizeof
		#undef sizeof
#endif

#ifdef WOLFSSL_TEST_CERT
    InitDecodedCert(&cert, tmp, (word32)bytes, 0);

    ret = ParseCert(&cert, CERT_TYPE, NO_VERIFY, 0);
    if (ret != 0) return -491;

    FreeDecodedCert(&cert);
#else
    (void)bytes;
#endif


#ifdef WOLFSSL_KEY_GEN
    {
        byte*  der;
        byte*  pem;
        int    derSz = 0;
        int    pemSz = 0;
        RsaKey derIn;
        RsaKey genKey;
        FILE*  keyFile;
        FILE*  pemFile;

        ret = wc_InitRsaKey(&genKey, 0);
        if (ret != 0)
            return -300;
        ret = wc_MakeRsaKey(&genKey, 1024, 65537, &rng);
        if (ret != 0)
            return -301;

        der = (byte*)malloc(FOURK_BUF);
        if (der == NULL) {
            wc_FreeRsaKey(&genKey);
            return -307;
        }
        pem = (byte*)malloc(FOURK_BUF);
        if (pem == NULL) {
            free(der);
            wc_FreeRsaKey(&genKey);
            return -308;
        }

        derSz = wc_RsaKeyToDer(&genKey, der, FOURK_BUF);
        if (derSz < 0) {
            free(der);
            free(pem);
            return -302;
        }

#ifdef FREESCALE_MQX
        keyFile = fopen("a:\\certs\\key.der", "wb");
#else
        keyFile = fopen("./key.der", "wb");
#endif
        if (!keyFile) {
            free(der);
            free(pem);
            wc_FreeRsaKey(&genKey);
            return -303;
        }
        ret = (int)fwrite(der, 1, derSz, keyFile);
        fclose(keyFile);
        if (ret != derSz) {
            free(der);
            free(pem);
            wc_FreeRsaKey(&genKey);
            return -313;
        }

        pemSz = wc_DerToPem(der, derSz, pem, FOURK_BUF, PRIVATEKEY_TYPE);
        if (pemSz < 0) {
            free(der);
            free(pem);
            wc_FreeRsaKey(&genKey);
            return -304;
        }

#ifdef FREESCALE_MQX
        pemFile = fopen("a:\\certs\\key.pem", "wb");
#else
        pemFile = fopen("./key.pem", "wb");
#endif
        if (!pemFile) {
            free(der);
            free(pem);
            wc_FreeRsaKey(&genKey);
            return -305;
        }
        ret = (int)fwrite(pem, 1, pemSz, pemFile);
        fclose(pemFile);
        if (ret != pemSz) {
            free(der);
            free(pem);
            wc_FreeRsaKey(&genKey);
            return -314;
        }

        ret = wc_InitRsaKey(&derIn, 0);
        if (ret != 0) {
            free(der);
            free(pem);
            wc_FreeRsaKey(&genKey);
            return -3060;
        }
        idx = 0;
        ret = wc_RsaPrivateKeyDecode(der, &idx, &derIn, derSz);
        if (ret != 0) {
            free(der);
            free(pem);
            wc_FreeRsaKey(&derIn);
            wc_FreeRsaKey(&genKey);
            return -306;
        }

        wc_FreeRsaKey(&derIn);
        wc_FreeRsaKey(&genKey);
        free(pem);
        free(der);
    }
#endif /* WOLFSSL_KEY_GEN */


#ifdef WOLFSSL_CERT_GEN
    /* self signed */
    {
        Cert        myCert;
        byte*       derCert;
        byte*       pem;
        FILE*       derFile;
        FILE*       pemFile;
        int         certSz;
        int         pemSz;
#ifdef WOLFSSL_TEST_CERT
        DecodedCert decode;
#endif

        derCert = (byte*)malloc(FOURK_BUF);
        if (derCert == NULL)
            return -309;
        pem = (byte*)malloc(FOURK_BUF);
        if (pem == NULL) {
            free(derCert);
            return -310;
        }

        wc_InitCert(&myCert);

        strncpy(myCert.subject.country, "US", CTC_NAME_SIZE);
        strncpy(myCert.subject.state, "OR", CTC_NAME_SIZE);
        strncpy(myCert.subject.locality, "Portland", CTC_NAME_SIZE);
        strncpy(myCert.subject.org, "yaSSL", CTC_NAME_SIZE);
        strncpy(myCert.subject.unit, "Development", CTC_NAME_SIZE);
        strncpy(myCert.subject.commonName, "www.yassl.com", CTC_NAME_SIZE);
        strncpy(myCert.subject.email, "info@yassl.com", CTC_NAME_SIZE);
        myCert.isCA    = 1;
        myCert.sigType = CTC_SHA256wRSA;

        certSz = wc_MakeSelfCert(&myCert, derCert, FOURK_BUF, &key, &rng);
        if (certSz < 0) {
            free(derCert);
            free(pem);
            return -401;
        }

#ifdef WOLFSSL_TEST_CERT
        InitDecodedCert(&decode, derCert, certSz, 0);
        ret = ParseCert(&decode, CERT_TYPE, NO_VERIFY, 0);
        if (ret != 0) {
            free(derCert);
            free(pem);
            return -402;
        }
        FreeDecodedCert(&decode);
#endif

#ifdef FREESCALE_MQX
        derFile = fopen("a:\\certs\\cert.der", "wb");
#else
        derFile = fopen("./cert.der", "wb");
#endif
        if (!derFile) {
            free(derCert);
            free(pem);
            return -403;
        }
        ret = (int)fwrite(derCert, 1, certSz, derFile);
        fclose(derFile);
        if (ret != certSz) {
            free(derCert);
            free(pem);
            return -414;
        }

        pemSz = wc_DerToPem(derCert, certSz, pem, FOURK_BUF, CERT_TYPE);
        if (pemSz < 0) {
            free(derCert);
            free(pem);
            return -404;
        }

#ifdef FREESCALE_MQX
        pemFile = fopen("a:\\certs\\cert.pem", "wb");
#else
        pemFile = fopen("./cert.pem", "wb");
#endif
        if (!pemFile) {
            free(derCert);
            free(pem);
            return -405;
        }
        ret = (int)fwrite(pem, 1, pemSz, pemFile);
        fclose(pemFile);
        if (ret != pemSz) {
            free(derCert);
            free(pem);
            return -406;
        }
        free(pem);
        free(derCert);
    }
    /* CA style */
    {
        RsaKey      caKey;
        Cert        myCert;
        byte*       derCert;
        byte*       pem;
        FILE*       derFile;
        FILE*       pemFile;
        int         certSz;
        int         pemSz;
        size_t      bytes3;
        word32      idx3 = 0;
        FILE*       file3 ;
#ifdef WOLFSSL_TEST_CERT
        DecodedCert decode;
#endif

        derCert = (byte*)malloc(FOURK_BUF);
        if (derCert == NULL)
            return -311;
        pem = (byte*)malloc(FOURK_BUF);
        if (pem == NULL) {
            free(derCert);
            return -312;
        }

        file3 = fopen(caKeyFile, "rb");

        if (!file3) {
            free(derCert);
            free(pem);
            return -412;
        }

        bytes3 = fread(tmp, 1, FOURK_BUF, file3);
        fclose(file3);

        ret = wc_InitRsaKey(&caKey, 0);
        if (ret != 0) {
            free(derCert);
            free(pem);
            return -411;
        }
        ret = wc_RsaPrivateKeyDecode(tmp, &idx3, &caKey, (word32)bytes3);
        if (ret != 0) {
            free(derCert);
            free(pem);
            wc_FreeRsaKey(&caKey);
            return -413;
        }

        wc_InitCert(&myCert);

        strncpy(myCert.subject.country, "US", CTC_NAME_SIZE);
        strncpy(myCert.subject.state, "OR", CTC_NAME_SIZE);
        strncpy(myCert.subject.locality, "Portland", CTC_NAME_SIZE);
        strncpy(myCert.subject.org, "yaSSL", CTC_NAME_SIZE);
        strncpy(myCert.subject.unit, "Development", CTC_NAME_SIZE);
        strncpy(myCert.subject.commonName, "www.yassl.com", CTC_NAME_SIZE);
        strncpy(myCert.subject.email, "info@yassl.com", CTC_NAME_SIZE);

        ret = wc_SetIssuer(&myCert, caCertFile);
        if (ret < 0) {
            free(derCert);
            free(pem);
            wc_FreeRsaKey(&caKey);
            return -405;
        }

        certSz = wc_MakeCert(&myCert, derCert, FOURK_BUF, &key, NULL, &rng);
        if (certSz < 0) {
            free(derCert);
            free(pem);
            wc_FreeRsaKey(&caKey);
            return -407;
        }

        certSz = wc_SignCert(myCert.bodySz, myCert.sigType, derCert, FOURK_BUF,
                          &caKey, NULL, &rng);
        if (certSz < 0) {
            free(derCert);
            free(pem);
            wc_FreeRsaKey(&caKey);
            return -408;
        }


#ifdef WOLFSSL_TEST_CERT
        InitDecodedCert(&decode, derCert, certSz, 0);
        ret = ParseCert(&decode, CERT_TYPE, NO_VERIFY, 0);
        if (ret != 0) {
            free(derCert);
            free(pem);
            wc_FreeRsaKey(&caKey);
            return -409;
        }
        FreeDecodedCert(&decode);
#endif

#ifdef FREESCALE_MQX
        derFile = fopen("a:\\certs\\othercert.der", "wb");
#else
        derFile = fopen("./othercert.der", "wb");
#endif
        if (!derFile) {
            free(derCert);
            free(pem);
            wc_FreeRsaKey(&caKey);
            return -410;
        }
        ret = (int)fwrite(derCert, 1, certSz, derFile);
        fclose(derFile);
        if (ret != certSz) {
            free(derCert);
            free(pem);
            wc_FreeRsaKey(&caKey);
            return -416;
        }

        pemSz = wc_DerToPem(derCert, certSz, pem, FOURK_BUF, CERT_TYPE);
        if (pemSz < 0) {
            free(derCert);
            free(pem);
            wc_FreeRsaKey(&caKey);
            return -411;
        }

#ifdef FREESCALE_MQX
        pemFile = fopen("a:\\certs\\othercert.pem", "wb");
#else
        pemFile = fopen("./othercert.pem", "wb");
#endif
        if (!pemFile) {
            free(derCert);
            free(pem);
            wc_FreeRsaKey(&caKey);
            return -412;
        }
        ret = (int)fwrite(pem, 1, pemSz, pemFile);
        if (ret != pemSz) {
            free(derCert);
            free(pem);
            wc_FreeRsaKey(&caKey);
            return -415;
        }
        fclose(pemFile);
        free(pem);
        free(derCert);
        wc_FreeRsaKey(&caKey);
    }
#ifdef HAVE_ECC
    /* ECC CA style */
    {
        ecc_key     caKey;
        Cert        myCert;
        byte*       derCert;
        byte*       pem;
        FILE*       derFile;
        FILE*       pemFile;
        int         certSz;
        int         pemSz;
        size_t      bytes3;
        word32      idx3 = 0;
        FILE*       file3;
#ifdef WOLFSSL_TEST_CERT
        DecodedCert decode;
#endif

        derCert = (byte*)malloc(FOURK_BUF);
        if (derCert == NULL)
            return -5311;
        pem = (byte*)malloc(FOURK_BUF);
        if (pem == NULL) {
            free(derCert);
            return -5312;
        }

        file3 = fopen(eccCaKeyFile, "rb");

        if (!file3) {
            free(derCert);
            free(pem);
            return -5412;
        }

        bytes3 = fread(tmp, 1, FOURK_BUF, file3);
        fclose(file3);

        wc_ecc_init(&caKey);
        ret = wc_EccPrivateKeyDecode(tmp, &idx3, &caKey, (word32)bytes3);
        if (ret != 0) {
            free(derCert);
            free(pem);
            return -5413;
        }

        wc_InitCert(&myCert);
        myCert.sigType = CTC_SHA256wECDSA;

        strncpy(myCert.subject.country, "US", CTC_NAME_SIZE);
        strncpy(myCert.subject.state, "OR", CTC_NAME_SIZE);
        strncpy(myCert.subject.locality, "Portland", CTC_NAME_SIZE);
        strncpy(myCert.subject.org, "wolfSSL", CTC_NAME_SIZE);
        strncpy(myCert.subject.unit, "Development", CTC_NAME_SIZE);
        strncpy(myCert.subject.commonName, "www.wolfssl.com", CTC_NAME_SIZE);
        strncpy(myCert.subject.email, "info@wolfssl.com", CTC_NAME_SIZE);

        ret = wc_SetIssuer(&myCert, eccCaCertFile);
        if (ret < 0) {
            free(pem);
            free(derCert);
            wc_ecc_free(&caKey);
            return -5405;
        }

        certSz = wc_MakeCert(&myCert, derCert, FOURK_BUF, NULL, &caKey, &rng);
        if (certSz < 0) {
            free(pem);
            free(derCert);
            wc_ecc_free(&caKey);
            return -5407;
        }

        certSz = wc_SignCert(myCert.bodySz, myCert.sigType, derCert, FOURK_BUF,
                          NULL, &caKey, &rng);
        if (certSz < 0) {
            free(pem);
            free(derCert);
            wc_ecc_free(&caKey);
            return -5408;
        }

#ifdef WOLFSSL_TEST_CERT
        InitDecodedCert(&decode, derCert, certSz, 0);
        ret = ParseCert(&decode, CERT_TYPE, NO_VERIFY, 0);
        if (ret != 0) {
            free(pem);
            free(derCert);
            wc_ecc_free(&caKey);
            return -5409;
        }
        FreeDecodedCert(&decode);
#endif

#ifdef FREESCALE_MQX
        derFile = fopen("a:\\certs\\certecc.der", "wb");
#else
        derFile = fopen("./certecc.der", "wb");
#endif
        if (!derFile) {
            free(pem);
            free(derCert);
            wc_ecc_free(&caKey);
            return -5410;
        }
        ret = (int)fwrite(derCert, 1, certSz, derFile);
        fclose(derFile);
        if (ret != certSz) {
            free(pem);
            free(derCert);
            wc_ecc_free(&caKey);
            return -5414;
        }

        pemSz = wc_DerToPem(derCert, certSz, pem, FOURK_BUF, CERT_TYPE);
        if (pemSz < 0) {
            free(pem);
            free(derCert);
            wc_ecc_free(&caKey);
            return -5411;
        }

#ifdef FREESCALE_MQX
        pemFile = fopen("a:\\certs\\certecc.pem", "wb");
#else
        pemFile = fopen("./certecc.pem", "wb");
#endif
        if (!pemFile) {
            free(pem);
            free(derCert);
            wc_ecc_free(&caKey);
            return -5412;
        }
        ret = (int)fwrite(pem, 1, pemSz, pemFile);
        if (ret != pemSz) {
            free(pem);
            free(derCert);
            wc_ecc_free(&caKey);
            return -5415;
        }
        fclose(pemFile);
        free(pem);
        free(derCert);
        wc_ecc_free(&caKey);
    }
#endif /* HAVE_ECC */
#ifdef HAVE_NTRU
    {
        RsaKey      caKey;
        Cert        myCert;
        byte*       derCert;
        byte*       pem;
        FILE*       derFile;
        FILE*       pemFile;
        FILE*       caFile;
        FILE*       ntruPrivFile;
        int         certSz;
        int         pemSz;
        word32      idx3;
#ifdef WOLFSSL_TEST_CERT
        DecodedCert decode;
#endif
        derCert = (byte*)malloc(FOURK_BUF);
        if (derCert == NULL)
            return -311;
        pem = (byte*)malloc(FOURK_BUF);
        if (pem == NULL) {
            free(derCert);
            return -312;
        }

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
            free(derCert);
            free(pem);
            return -448;
        }

        rc = ntru_crypto_ntru_encrypt_keygen(drbg, NTRU_EES401EP2,
                                             &public_key_len, NULL,
                                             &private_key_len, NULL);
        if (rc != NTRU_OK) {
            free(derCert);
            free(pem);
            return -449;
        }

        rc = ntru_crypto_ntru_encrypt_keygen(drbg, NTRU_EES401EP2,
                                             &public_key_len, public_key,
                                             &private_key_len, private_key);
        if (rc != NTRU_OK) {
            free(derCert);
            free(pem);
            return -450;
        }

        rc = ntru_crypto_drbg_uninstantiate(drbg);

        if (rc != NTRU_OK) {
            free(derCert);
            free(pem);
            return -451;
        }

        caFile = fopen(caKeyFile, "rb");

        if (!caFile) {
            free(derCert);
            free(pem);
            return -452;
        }

        bytes = fread(tmp, 1, FOURK_BUF, caFile);
        fclose(caFile);

        ret = wc_InitRsaKey(&caKey, 0);
        if (ret != 0) {
            free(derCert);
            free(pem);
            return -453;
        }
        ret = wc_RsaPrivateKeyDecode(tmp, &idx3, &caKey, (word32)bytes);
        if (ret != 0) {
            free(derCert);
            free(pem);
            return -454;
        }

        wc_InitCert(&myCert);

        strncpy(myCert.subject.country, "US", CTC_NAME_SIZE);
        strncpy(myCert.subject.state, "OR", CTC_NAME_SIZE);
        strncpy(myCert.subject.locality, "Portland", CTC_NAME_SIZE);
        strncpy(myCert.subject.org, "yaSSL", CTC_NAME_SIZE);
        strncpy(myCert.subject.unit, "Development", CTC_NAME_SIZE);
        strncpy(myCert.subject.commonName, "www.yassl.com", CTC_NAME_SIZE);
        strncpy(myCert.subject.email, "info@yassl.com", CTC_NAME_SIZE);

        ret = wc_SetIssuer(&myCert, caCertFile);
        if (ret < 0) {
            free(derCert);
            free(pem);
            wc_FreeRsaKey(&caKey);
            return -455;
        }

        certSz = wc_MakeNtruCert(&myCert, derCert, FOURK_BUF, public_key,
                              public_key_len, &rng);
        if (certSz < 0) {
            free(derCert);
            free(pem);
            wc_FreeRsaKey(&caKey);
            return -456;
        }

        certSz = wc_SignCert(myCert.bodySz, myCert.sigType, derCert, FOURK_BUF,
                          &caKey, NULL, &rng);
        wc_FreeRsaKey(&caKey);
        if (certSz < 0) {
            free(derCert);
            free(pem);
            return -457;
        }


#ifdef WOLFSSL_TEST_CERT
        InitDecodedCert(&decode, derCert, certSz, 0);
        ret = ParseCert(&decode, CERT_TYPE, NO_VERIFY, 0);
        if (ret != 0) {
            free(derCert);
            free(pem);
            return -458;
        }
        FreeDecodedCert(&decode);
#endif
        derFile = fopen("./ntru-cert.der", "wb");
        if (!derFile) {
            free(derCert);
            free(pem);
            return -459;
        }
        ret = (int)fwrite(derCert, 1, certSz, derFile);
        fclose(derFile);
        if (ret != certSz) {
            free(derCert);
            free(pem);
            return -473;
        }

        pemSz = wc_DerToPem(derCert, certSz, pem, FOURK_BUF, CERT_TYPE);
        if (pemSz < 0) {
            free(derCert);
            free(pem);
            return -460;
        }

        pemFile = fopen("./ntru-cert.pem", "wb");
        if (!pemFile) {
            free(derCert);
            free(pem);
            return -461;
        }
        ret = (int)fwrite(pem, 1, pemSz, pemFile);
        fclose(pemFile);
        if (ret != pemSz) {
            free(derCert);
            free(pem);
            return -474;
        }

        ntruPrivFile = fopen("./ntru-key.raw", "wb");
        if (!ntruPrivFile) {
            free(derCert);
            free(pem);
            return -462;
        }
        ret = (int)fwrite(private_key, 1, private_key_len, ntruPrivFile);
        fclose(ntruPrivFile);
        if (ret != private_key_len) {
            free(pem);
            free(derCert);
            return -475;
        }
        free(pem);
        free(derCert);
    }
#endif /* HAVE_NTRU */
#ifdef WOLFSSL_CERT_REQ
    {
        Cert        req;
        byte*       der;
        byte*       pem;
        int         derSz;
        int         pemSz;
        FILE*       reqFile;

        der = (byte*)malloc(FOURK_BUF);
        if (der == NULL)
            return -463;
        pem = (byte*)malloc(FOURK_BUF);
        if (pem == NULL) {
            free(der);
            return -464;
        }

        wc_InitCert(&req);

        req.version = 0;
        req.isCA    = 1;
        strncpy(req.challengePw, "yassl123", CTC_NAME_SIZE);
        strncpy(req.subject.country, "US", CTC_NAME_SIZE);
        strncpy(req.subject.state, "OR", CTC_NAME_SIZE);
        strncpy(req.subject.locality, "Portland", CTC_NAME_SIZE);
        strncpy(req.subject.org, "yaSSL", CTC_NAME_SIZE);
        strncpy(req.subject.unit, "Development", CTC_NAME_SIZE);
        strncpy(req.subject.commonName, "www.yassl.com", CTC_NAME_SIZE);
        strncpy(req.subject.email, "info@yassl.com", CTC_NAME_SIZE);
        req.sigType = CTC_SHA256wRSA;

        derSz = wc_MakeCertReq(&req, der, FOURK_BUF, &key, NULL);
        if (derSz < 0) {
            free(pem);
            free(der);
            return -465;
        }

        derSz = wc_SignCert(req.bodySz, req.sigType, der, FOURK_BUF,
                          &key, NULL, &rng);
        if (derSz < 0) {
            free(pem);
            free(der);
            return -466;
        }

        pemSz = wc_DerToPem(der, derSz, pem, FOURK_BUF, CERTREQ_TYPE);
        if (pemSz < 0) {
            free(pem);
            free(der);
            return -467;
        }

#ifdef FREESCALE_MQX
        reqFile = fopen("a:\\certs\\certreq.der", "wb");
#else
        reqFile = fopen("./certreq.der", "wb");
#endif
        if (!reqFile) {
            free(pem);
            free(der);
            return -468;
        }

        ret = (int)fwrite(der, 1, derSz, reqFile);
        fclose(reqFile);
        if (ret != derSz) {
            free(pem);
            free(der);
            return -471;
        }

#ifdef FREESCALE_MQX
        reqFile = fopen("a:\\certs\\certreq.pem", "wb");
#else
        reqFile = fopen("./certreq.pem", "wb");
#endif
        if (!reqFile) {
            free(pem);
            free(der);
            return -469;
        }
        ret = (int)fwrite(pem, 1, pemSz, reqFile);
        fclose(reqFile);
        if (ret != pemSz) {
            free(pem);
            free(der);
            return -470;
        }

        free(pem);
        free(der);
    }
#endif /* WOLFSSL_CERT_REQ */
#endif /* WOLFSSL_CERT_GEN */

    wc_FreeRsaKey(&key);
#ifdef HAVE_CAVIUM
    wc_RsaFreeCavium(&key);
#endif
    free(tmp);
    wc_FreeRng(&rng);

    return 0;
}

#endif


#ifndef NO_DH

#if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048)
    #ifdef FREESCALE_MQX
        static const char* dhKey = "a:\\certs\\dh2048.der";
    #elif defined(NO_ASN)
        /* don't use file, no DER parsing */
    #else
        static const char* dhKey = "./certs/dh2048.der";
    #endif
#endif

int dh_test(void)
{
    int    ret;
    word32 bytes;
    word32 idx = 0, privSz, pubSz, privSz2, pubSz2, agreeSz, agreeSz2;
    byte   tmp[1024];
    byte   priv[256];
    byte   pub[256];
    byte   priv2[256];
    byte   pub2[256];
    byte   agree[256];
    byte   agree2[256];
    DhKey  key;
    DhKey  key2;
    RNG    rng;

#ifdef USE_CERT_BUFFERS_1024
    XMEMCPY(tmp, dh_key_der_1024, sizeof_dh_key_der_1024);
    bytes = sizeof_dh_key_der_1024;
#elif defined(USE_CERT_BUFFERS_2048)
    XMEMCPY(tmp, dh_key_der_2048, sizeof_dh_key_der_2048);
    bytes = sizeof_dh_key_der_2048;
#elif defined(NO_ASN)
    /* don't use file, no DER parsing */
#else
    FILE*  file = fopen(dhKey, "rb");

    if (!file)
        return -50;

    bytes = (word32) fread(tmp, 1, sizeof(tmp), file);
    fclose(file);
#endif /* USE_CERT_BUFFERS */

    (void)idx;
    (void)tmp;
    (void)bytes;

    wc_InitDhKey(&key);
    wc_InitDhKey(&key2);
#ifdef NO_ASN
    ret = wc_DhSetKey(&key, dh_p, sizeof(dh_p), dh_g, sizeof(dh_g));
    if (ret != 0)
        return -51;

    ret = wc_DhSetKey(&key2, dh_p, sizeof(dh_p), dh_g, sizeof(dh_g));
    if (ret != 0)
        return -51;
#else
    ret = wc_DhKeyDecode(tmp, &idx, &key, bytes);
    if (ret != 0)
        return -51;

    idx = 0;
    ret = wc_DhKeyDecode(tmp, &idx, &key2, bytes);
    if (ret != 0)
        return -52;
#endif

    ret = wc_InitRng(&rng);
    if (ret != 0)
        return -53;

    ret =  wc_DhGenerateKeyPair(&key, &rng, priv, &privSz, pub, &pubSz);
    ret += wc_DhGenerateKeyPair(&key2, &rng, priv2, &privSz2, pub2, &pubSz2);
    if (ret != 0)
        return -54;

    ret =  wc_DhAgree(&key, agree, &agreeSz, priv, privSz, pub2, pubSz2);
    ret += wc_DhAgree(&key2, agree2, &agreeSz2, priv2, privSz2, pub, pubSz);
    if (ret != 0)
        return -55;

    if (memcmp(agree, agree2, agreeSz))
        return -56;

    wc_FreeDhKey(&key);
    wc_FreeDhKey(&key2);
    wc_FreeRng(&rng);

    return 0;
}

#endif /* NO_DH */


#ifndef NO_DSA

#if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048)
    #ifdef FREESCALE_MQX
        static const char* dsaKey = "a:\\certs\\dsa2048.der";
    #else
        static const char* dsaKey = "./certs/dsa2048.der";
    #endif
#endif

int dsa_test(void)
{
    int    ret, answer;
    word32 bytes;
    word32 idx = 0;
    byte   tmp[1024];
    DsaKey key;
    RNG    rng;
    Sha    sha;
    byte   hash[SHA_DIGEST_SIZE];
    byte   signature[40];


#ifdef USE_CERT_BUFFERS_1024
    XMEMCPY(tmp, dsa_key_der_1024, sizeof_dsa_key_der_1024);
    bytes = sizeof_dsa_key_der_1024;
#elif defined(USE_CERT_BUFFERS_2048)
    XMEMCPY(tmp, dsa_key_der_2048, sizeof_dsa_key_der_2048);
    bytes = sizeof_dsa_key_der_2048;
#else
    FILE*  file = fopen(dsaKey, "rb");

    if (!file)
        return -60;

    bytes = (word32) fread(tmp, 1, sizeof(tmp), file);
    fclose(file);
#endif /* USE_CERT_BUFFERS */

    ret = wc_InitSha(&sha);
    if (ret != 0)
        return -4002;
    wc_ShaUpdate(&sha, tmp, bytes);
    wc_ShaFinal(&sha, hash);

    wc_InitDsaKey(&key);
    ret = wc_DsaPrivateKeyDecode(tmp, &idx, &key, bytes);
    if (ret != 0) return -61;

    ret = wc_InitRng(&rng);
    if (ret != 0) return -62;

    ret = wc_DsaSign(hash, signature, &key, &rng);
    if (ret != 0) return -63;

    ret = wc_DsaVerify(hash, signature, &key, &answer);
    if (ret != 0) return -64;
    if (answer != 1) return -65;

    wc_FreeDsaKey(&key);
    wc_FreeRng(&rng);

    return 0;
}

#endif /* NO_DSA */


#ifdef OPENSSL_EXTRA

int openssl_test(void)
{
    EVP_MD_CTX md_ctx;
    testVector a, b, c, d, e, f;
    byte       hash[SHA256_DIGEST_SIZE*2];  /* max size */

    (void)a;
    (void)b;
    (void)c;
    (void)e;
    (void)f;

#ifndef NO_MD5

    a.input  = "1234567890123456789012345678901234567890123456789012345678"
               "9012345678901234567890";
    a.output = "\x57\xed\xf4\xa2\x2b\xe3\xc9\x55\xac\x49\xda\x2e\x21\x07\xb6"
               "\x7a";
    a.inLen  = strlen(a.input);
    a.outLen = MD5_DIGEST_SIZE;

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_md5());

    EVP_DigestUpdate(&md_ctx, a.input, (unsigned long)a.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (memcmp(hash, a.output, MD5_DIGEST_SIZE) != 0)
        return -71;

#endif /* NO_MD5 */

#ifndef NO_SHA

    b.input  = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
               "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
               "aaaaaaaaaa";
    b.output = "\xAD\x5B\x3F\xDB\xCB\x52\x67\x78\xC2\x83\x9D\x2F\x15\x1E\xA7"
               "\x53\x99\x5E\x26\xA0";
    b.inLen  = strlen(b.input);
    b.outLen = SHA_DIGEST_SIZE;

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_sha1());

    EVP_DigestUpdate(&md_ctx, b.input, (unsigned long)b.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (memcmp(hash, b.output, SHA_DIGEST_SIZE) != 0)
        return -72;

#endif /* NO_SHA */


    d.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    d.output = "\x24\x8D\x6A\x61\xD2\x06\x38\xB8\xE5\xC0\x26\x93\x0C\x3E\x60"
               "\x39\xA3\x3C\xE4\x59\x64\xFF\x21\x67\xF6\xEC\xED\xD4\x19\xDB"
               "\x06\xC1";
    d.inLen  = strlen(d.input);
    d.outLen = SHA256_DIGEST_SIZE;

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_sha256());

    EVP_DigestUpdate(&md_ctx, d.input, (unsigned long)d.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (memcmp(hash, d.output, SHA256_DIGEST_SIZE) != 0)
        return -78;

#ifdef WOLFSSL_SHA384

    e.input  = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhi"
               "jklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    e.output = "\x09\x33\x0c\x33\xf7\x11\x47\xe8\x3d\x19\x2f\xc7\x82\xcd\x1b"
               "\x47\x53\x11\x1b\x17\x3b\x3b\x05\xd2\x2f\xa0\x80\x86\xe3\xb0"
               "\xf7\x12\xfc\xc7\xc7\x1a\x55\x7e\x2d\xb9\x66\xc3\xe9\xfa\x91"
               "\x74\x60\x39";
    e.inLen  = strlen(e.input);
    e.outLen = SHA384_DIGEST_SIZE;

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_sha384());

    EVP_DigestUpdate(&md_ctx, e.input, (unsigned long)e.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (memcmp(hash, e.output, SHA384_DIGEST_SIZE) != 0)
        return -79;

#endif /* WOLFSSL_SHA384 */


#ifdef WOLFSSL_SHA512

    f.input  = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhi"
               "jklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    f.output = "\x8e\x95\x9b\x75\xda\xe3\x13\xda\x8c\xf4\xf7\x28\x14\xfc\x14"
               "\x3f\x8f\x77\x79\xc6\xeb\x9f\x7f\xa1\x72\x99\xae\xad\xb6\x88"
               "\x90\x18\x50\x1d\x28\x9e\x49\x00\xf7\xe4\x33\x1b\x99\xde\xc4"
               "\xb5\x43\x3a\xc7\xd3\x29\xee\xb6\xdd\x26\x54\x5e\x96\xe5\x5b"
               "\x87\x4b\xe9\x09";
    f.inLen  = strlen(f.input);
    f.outLen = SHA512_DIGEST_SIZE;

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_sha512());

    EVP_DigestUpdate(&md_ctx, f.input, (unsigned long)f.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (memcmp(hash, f.output, SHA512_DIGEST_SIZE) != 0)
        return -80;

#endif /* WOLFSSL_SHA512 */


#ifndef NO_MD5
    if (RAND_bytes(hash, sizeof(hash)) != 1)
        return -73;

    c.input  = "what do ya want for nothing?";
    c.output = "\x55\x78\xe8\x48\x4b\xcc\x93\x80\x93\xec\x53\xaf\x22\xd6\x14"
               "\x76";
    c.inLen  = strlen(c.input);
    c.outLen = MD5_DIGEST_SIZE;

    HMAC(EVP_md5(),
                 "JefeJefeJefeJefe", 16, (byte*)c.input, (int)c.inLen, hash, 0);

    if (memcmp(hash, c.output, MD5_DIGEST_SIZE) != 0)
        return -74;

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

    if (memcmp(plain, vector, sizeof(vector)) != 0)
        return -75;

    if (memcmp(cipher, verify, sizeof(verify)) != 0)
        return -76;

        /* test changing iv */
    DES_ncbc_encrypt(vector, cipher, 8, &sched, &iv, DES_ENCRYPT);
    DES_ncbc_encrypt(vector + 8, cipher + 8, 16, &sched, &iv, DES_ENCRYPT);

    if (memcmp(cipher, verify, sizeof(verify)) != 0)
        return -77;

    }  /* end des test */

#endif /* NO_DES3 */

#ifndef NO_AES

    {  /* evp_cipher test */
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
            return -81;

        if (EVP_Cipher(&ctx, cipher, (byte*)msg, 16) == 0)
            return -82;

        if (memcmp(cipher, verify, AES_BLOCK_SIZE))
            return -83;

        EVP_CIPHER_CTX_init(&ctx);
        if (EVP_CipherInit(&ctx, EVP_aes_128_cbc(), key, iv, 0) == 0)
            return -84;

        if (EVP_Cipher(&ctx, plain, cipher, 16) == 0)
            return -85;

        if (memcmp(plain, msg, AES_BLOCK_SIZE))
            return -86;


    }  /* end evp_cipher test */

#endif /* NO_AES */

    return 0;
}

#endif /* OPENSSL_EXTRA */


#ifndef NO_PWDBASED

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
                                                  iterations, kLen, SHA256, id);

    if (ret < 0)
        return -103;

    if ( (ret = memcmp(derived, verify, kLen)) != 0)
        return -104;

    iterations = 1000;
    ret = wc_PKCS12_PBKDF(derived, passwd2, sizeof(passwd2), salt2, 8,
                                                  iterations, kLen, SHA256, id);
    if (ret < 0)
        return -105;

    if ( (ret = memcmp(derived, verify2, 24)) != 0)
        return -106;

    return 0;
}


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

    int ret = wc_PBKDF2(derived, (byte*)passwd, (int)strlen(passwd), salt, 8,
                                                      iterations, kLen, SHA256);
    if (ret != 0)
        return ret;

    if (memcmp(derived, verify, sizeof(verify)) != 0)
        return -102;

    return 0;
}


#ifndef NO_SHA
int pbkdf1_test(void)
{
    char passwd[] = "password";
    const byte salt[] = { 0x78, 0x57, 0x8E, 0x5a, 0x5d, 0x63, 0xcb, 0x06 };
    int   iterations = 1000;
    int   kLen = 16;
    byte  derived[16];

    const byte verify[] = {
        0xDC, 0x19, 0x84, 0x7E, 0x05, 0xC6, 0x4D, 0x2F, 0xAF, 0x10, 0xEB, 0xFB,
        0x4A, 0x3D, 0x2A, 0x20
    };

    wc_PBKDF1(derived, (byte*)passwd, (int)strlen(passwd), salt, 8, iterations,
           kLen, SHA);

    if (memcmp(derived, verify, sizeof(verify)) != 0)
        return -101;

    return 0;
}
#endif


int pwdbased_test(void)
{
   int ret = 0;
#ifndef NO_SHA
   ret += pbkdf1_test();
#endif
   ret += pbkdf2_test();

   return ret + pkcs12_test();
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
    ret = wc_HKDF(SHA, ikm1, 22, NULL, 0, NULL, 0, okm1, L);
    if (ret != 0)
        return -2001;

    if (memcmp(okm1, res1, L) != 0)
        return -2002;

#ifndef HAVE_FIPS
    /* fips can't have key size under 14 bytes, salt is key too */
    ret = wc_HKDF(SHA, ikm1, 11, salt1, 13, info1, 10, okm1, L);
    if (ret != 0)
        return -2003;

    if (memcmp(okm1, res2, L) != 0)
        return -2004;
#endif /* HAVE_FIPS */
#endif /* NO_SHA */

#ifndef NO_SHA256
    ret = wc_HKDF(SHA256, ikm1, 22, NULL, 0, NULL, 0, okm1, L);
    if (ret != 0)
        return -2005;

    if (memcmp(okm1, res3, L) != 0)
        return -2006;

#ifndef HAVE_FIPS
    /* fips can't have key size under 14 bytes, salt is key too */
    ret = wc_HKDF(SHA256, ikm1, 22, salt1, 13, info1, 10, okm1, L);
    if (ret != 0)
        return -2007;

    if (memcmp(okm1, res4, L) != 0)
        return -2007;
#endif /* HAVE_FIPS */
#endif /* NO_SHA256 */

    return 0;
}

#endif /* HAVE_HKDF */


#ifdef HAVE_ECC

typedef struct rawEccVector {
    const char* msg;
    const char* Qx;
    const char* Qy;
    const char* d;
    const char* R;
    const char* S;
    const char* curveName;
    size_t msgLen;
} rawEccVector;

int ecc_test(void)
{
    RNG     rng;
    byte    sharedA[1024];
    byte    sharedB[1024];
    byte    sig[1024];
    byte    digest[20];
    byte    exportBuf[1024];
    word32  x, y;
    int     i, verify, ret;
    ecc_key userA, userB, pubKey;

    ret = wc_InitRng(&rng);
    if (ret != 0)
        return -1001;

    wc_ecc_init(&userA);
    wc_ecc_init(&userB);
    wc_ecc_init(&pubKey);

    ret = wc_ecc_make_key(&rng, 32, &userA);

    if (ret != 0)
        return -1014;

    ret = wc_ecc_check_key(&userA);
    if (ret != 0)
        return -1024;

    ret = wc_ecc_make_key(&rng, 32, &userB);

    if (ret != 0)
        return -1002;

    x = sizeof(sharedA);
    ret = wc_ecc_shared_secret(&userA, &userB, sharedA, &x);

    if (ret != 0)
        return -1015;

    y = sizeof(sharedB);
    ret = wc_ecc_shared_secret(&userB, &userA, sharedB, &y);

    if (ret != 0)
        return -1003;

    if (y != x)
        return -1004;

    if (memcmp(sharedA, sharedB, x))
        return -1005;

    x = sizeof(exportBuf);
    ret = wc_ecc_export_x963(&userA, exportBuf, &x);
    if (ret != 0)
        return -1006;

    ret = wc_ecc_import_x963(exportBuf, x, &pubKey);

    if (ret != 0)
        return -1007;

    y = sizeof(sharedB);
    ret = wc_ecc_shared_secret(&userB, &pubKey, sharedB, &y);

    if (ret != 0)
        return -1008;

    if (memcmp(sharedA, sharedB, y))
        return -1009;

#ifdef HAVE_COMP_KEY
    /* try compressed export / import too */
    x = sizeof(exportBuf);
    ret = wc_ecc_export_x963_ex(&userA, exportBuf, &x, 1);
    if (ret != 0)
        return -1010;

    wc_ecc_free(&pubKey);
    wc_ecc_init(&pubKey);
    ret = wc_ecc_import_x963(exportBuf, x, &pubKey);

    if (ret != 0)
        return -1011;
#endif

    y = sizeof(sharedB);
    ret = wc_ecc_shared_secret(&userB, &pubKey, sharedB, &y);

    if (ret != 0)
        return -1012;

    if (memcmp(sharedA, sharedB, y))
        return -1013;

    /* test DSA sign hash */
    for (i = 0; i < (int)sizeof(digest); i++)
        digest[i] = (byte)i;

    x = sizeof(sig);
    ret = wc_ecc_sign_hash(digest, sizeof(digest), sig, &x, &rng, &userA);

    if (ret != 0)
        return -1014;

    verify = 0;
    ret = wc_ecc_verify_hash(sig, x, digest, sizeof(digest), &verify, &userA);

    if (ret != 0)
        return -1015;

    if (verify != 1)
        return -1016;

    x = sizeof(exportBuf);
    ret = wc_ecc_export_private_only(&userA, exportBuf, &x);
    if (ret != 0)
        return -1017;

#if !defined(NO_SHA) && \
    ((defined(HAVE_ECC192) && defined(HAVE_ECC224)) || defined(HAVE_ALL_CURVES))
    {
        /* test raw ECC key import */
        Sha sha;
        byte hash[SHA_DIGEST_SIZE];
        rawEccVector a, b;
        rawEccVector test_ecc[2];
        int times = sizeof(test_ecc) / sizeof(rawEccVector);

        /* first [P-192,SHA-1] vector from FIPS 186-3 NIST vectors */
        a.msg = "\xeb\xf7\x48\xd7\x48\xeb\xbc\xa7\xd2\x9f\xb4\x73\x69\x8a"
                "\x6e\x6b\x4f\xb1\x0c\x86\x5d\x4a\xf0\x24\xcc\x39\xae\x3d"
                "\xf3\x46\x4b\xa4\xf1\xd6\xd4\x0f\x32\xbf\x96\x18\xa9\x1b"
                "\xb5\x98\x6f\xa1\xa2\xaf\x04\x8a\x0e\x14\xdc\x51\xe5\x26"
                "\x7e\xb0\x5e\x12\x7d\x68\x9d\x0a\xc6\xf1\xa7\xf1\x56\xce"
                "\x06\x63\x16\xb9\x71\xcc\x7a\x11\xd0\xfd\x7a\x20\x93\xe2"
                "\x7c\xf2\xd0\x87\x27\xa4\xe6\x74\x8c\xc3\x2f\xd5\x9c\x78"
                "\x10\xc5\xb9\x01\x9d\xf2\x1c\xdc\xc0\xbc\xa4\x32\xc0\xa3"
                "\xee\xd0\x78\x53\x87\x50\x88\x77\x11\x43\x59\xce\xe4\xa0"
                "\x71\xcf";
        a.msgLen = 128;
        a.Qx = "07008ea40b08dbe76432096e80a2494c94982d2d5bcf98e6";
        a.Qy = "76fab681d00b414ea636ba215de26d98c41bd7f2e4d65477";
        a.d  = "e14f37b3d1374ff8b03f41b9b3fdd2f0ebccf275d660d7f3";
        a.R  = "6994d962bdd0d793ffddf855ec5bf2f91a9698b46258a63e";
        a.S  = "02ba6465a234903744ab02bc8521405b73cf5fc00e1a9f41";
        a.curveName = "ECC-192";

        /* first [P-224,SHA-1] vector from FIPS 186-3 NIST vectors */
        b.msg = "\x36\xc8\xb2\x29\x86\x48\x7f\x67\x7c\x18\xd0\x97\x2a\x9e"
                "\x20\x47\xb3\xaf\xa5\x9e\xc1\x62\x76\x4e\xc3\x0b\x5b\x69"
                "\xe0\x63\x0f\x99\x0d\x4e\x05\xc2\x73\xb0\xe5\xa9\xd4\x28"
                "\x27\xb6\x95\xfc\x2d\x64\xd9\x13\x8b\x1c\xf4\xc1\x21\x55"
                "\x89\x4c\x42\x13\x21\xa7\xbb\x97\x0b\xdc\xe0\xfb\xf0\xd2"
                "\xae\x85\x61\xaa\xd8\x71\x7f\x2e\x46\xdf\xe3\xff\x8d\xea"
                "\xb4\xd7\x93\x23\x56\x03\x2c\x15\x13\x0d\x59\x9e\x26\xc1"
                "\x0f\x2f\xec\x96\x30\x31\xac\x69\x38\xa1\x8d\x66\x45\x38"
                "\xb9\x4d\xac\x55\x34\xef\x7b\x59\x94\x24\xd6\x9b\xe1\xf7"
                "\x1c\x20";
        b.msgLen = 128;
        b.Qx = "8a4dca35136c4b70e588e23554637ae251077d1365a6ba5db9585de7";
        b.Qy = "ad3dee06de0be8279d4af435d7245f14f3b4f82eb578e519ee0057b1";
        b.d  = "97c4b796e1639dd1035b708fc00dc7ba1682cec44a1002a1a820619f";
        b.R  = "147b33758321e722a0360a4719738af848449e2c1d08defebc1671a7";
        b.S  = "24fc7ed7f1352ca3872aa0916191289e2e04d454935d50fe6af3ad5b";
        b.curveName = "ECC-224";

        test_ecc[0] = a;
        test_ecc[1] = b;

        for (i = 0; i < times; i++) {

            wc_ecc_free(&userA);
            wc_ecc_init(&userA);

            memset(sig, 0, sizeof(sig));
            x = sizeof(sig);

            /* calculate SHA-1 hash of message */
            ret = wc_InitSha(&sha);
            if (ret != 0)
                return -1015 - i;

            wc_ShaUpdate(&sha, (byte*)test_ecc[i].msg, (word32)test_ecc[i].msgLen);
            wc_ShaFinal(&sha, hash);

            ret = wc_ecc_import_raw(&userA, test_ecc[i].Qx, test_ecc[i].Qy,
                                 test_ecc[i].d, test_ecc[i].curveName);
            if (ret != 0)
                return -1017 - i;

            ret = wc_ecc_rs_to_sig(test_ecc[i].R, test_ecc[i].S, sig, &x);
            if (ret != 0)
                return -1019 - i;

            ret = wc_ecc_verify_hash(sig, x, hash, sizeof(hash), &verify, &userA);
            if (ret != 0)
                return -1021 - i;

            if (verify != 1)
                return -1023 - i;
        }
    }
#endif /* defined(HAVE_ECC192) && defined(HAVE_ECC256) */


#ifdef WOLFSSL_KEY_GEN
    {
        int   derSz, pemSz;
        byte  der[FOURK_BUF];
        byte  pem[FOURK_BUF];
        FILE* keyFile;
        FILE* pemFile;

        derSz = wc_EccKeyToDer(&userB, der, FOURK_BUF);
        if (derSz < 0) {
            return -1024;
        }

        keyFile = fopen("./ecc-key.der", "wb");
        if (!keyFile) {
            return -1025;
        }
        ret = (int)fwrite(der, 1, derSz, keyFile);
        fclose(keyFile);
        if (ret != derSz) {
            return -1026;
        }

        pemSz = wc_DerToPem(der, derSz, pem, FOURK_BUF, ECC_PRIVATEKEY_TYPE);
        if (pemSz < 0) {
            return -1027;
        }

        pemFile = fopen("./ecc-key.pem", "wb");
        if (!pemFile) {
            return -1028;
        }
        ret = (int)fwrite(pem, 1, pemSz, pemFile);
        fclose(pemFile);
        if (ret != pemSz) {
            return -1029;
        }
    }
#endif /* WOLFSSL_KEY_GEN */

    wc_ecc_free(&pubKey);
    wc_ecc_free(&userB);
    wc_ecc_free(&userA);
    wc_FreeRng(&rng);

    return 0;
}

#ifdef HAVE_ECC_ENCRYPT

int ecc_encrypt_test(void)
{
    RNG     rng;
    int     ret;
    ecc_key userA, userB;
    byte    msg[48];
    byte    plain[48];
    byte    out[80];
    word32  outSz   = sizeof(out);
    word32  plainSz = sizeof(plain);
    int     i;

    ret = wc_InitRng(&rng);
    if (ret != 0)
        return -3001;

    wc_ecc_init(&userA);
    wc_ecc_init(&userB);

    ret  = wc_ecc_make_key(&rng, 32, &userA);
    ret += wc_ecc_make_key(&rng, 32, &userB);

    if (ret != 0)
        return -3002;

    for (i = 0; i < 48; i++)
        msg[i] = i;

    /* encrypt msg to B */
    ret = wc_ecc_encrypt(&userA, &userB, msg, sizeof(msg), out, &outSz, NULL);
    if (ret != 0)
        return -3003;

    /* decrypt msg from A */
    ret = wc_ecc_decrypt(&userB, &userA, out, outSz, plain, &plainSz, NULL);
    if (ret != 0)
        return -3004;

    if (memcmp(plain, msg, sizeof(msg)) != 0)
        return -3005;


    {  /* let's verify message exchange works, A is client, B is server */
        ecEncCtx* cliCtx = wc_ecc_ctx_new(REQ_RESP_CLIENT, &rng);
        ecEncCtx* srvCtx = wc_ecc_ctx_new(REQ_RESP_SERVER, &rng);

        byte cliSalt[EXCHANGE_SALT_SZ];
        byte srvSalt[EXCHANGE_SALT_SZ];
        const byte* tmpSalt;

        if (cliCtx == NULL || srvCtx == NULL)
            return -3006;

        /* get salt to send to peer */
        tmpSalt = wc_ecc_ctx_get_own_salt(cliCtx);
        if (tmpSalt == NULL)
            return -3007;
        memcpy(cliSalt, tmpSalt, EXCHANGE_SALT_SZ);

        tmpSalt = wc_ecc_ctx_get_own_salt(srvCtx);
        if (tmpSalt == NULL)
            return -3007;
        memcpy(srvSalt, tmpSalt, EXCHANGE_SALT_SZ);

        /* in actual use, we'd get the peer's salt over the transport */
        ret  = wc_ecc_ctx_set_peer_salt(cliCtx, srvSalt);
        ret += wc_ecc_ctx_set_peer_salt(srvCtx, cliSalt);

        ret += wc_ecc_ctx_set_info(cliCtx, (byte*)"wolfSSL MSGE", 11);
        ret += wc_ecc_ctx_set_info(srvCtx, (byte*)"wolfSSL MSGE", 11);

        if (ret != 0)
            return -3008;

        /* get encrypted msg (request) to send to B */
        outSz  = sizeof(out);
        ret = wc_ecc_encrypt(&userA, &userB, msg, sizeof(msg), out, &outSz,cliCtx);
        if (ret != 0)
            return -3009;

        /* B decrypts msg (request) from A */
        plainSz = sizeof(plain);
        ret = wc_ecc_decrypt(&userB, &userA, out, outSz, plain, &plainSz, srvCtx);
        if (ret != 0)
            return -3010;

        if (memcmp(plain, msg, sizeof(msg)) != 0)
            return -3011;

        {
            /* msg2 (response) from B to A */
            byte    msg2[48];
            byte    plain2[48];
            byte    out2[80];
            word32  outSz2   = sizeof(out2);
            word32  plainSz2 = sizeof(plain2);

            for (i = 0; i < 48; i++)
                msg2[i] = i+48;

            /* get encrypted msg (response) to send to B */
            ret = wc_ecc_encrypt(&userB, &userA, msg2, sizeof(msg2), out2,
                              &outSz2, srvCtx);
            if (ret != 0)
                return -3012;

            /* A decrypts msg (response) from B */
            ret = wc_ecc_decrypt(&userA, &userB, out2, outSz2, plain2, &plainSz2,
                             cliCtx);
            if (ret != 0)
                return -3013;

            if (memcmp(plain2, msg2, sizeof(msg2)) != 0)
                return -3014;
        }

        /* cleanup */
        wc_ecc_ctx_free(srvCtx);
        wc_ecc_ctx_free(cliCtx);
    }

    /* cleanup */
    wc_ecc_free(&userB);
    wc_ecc_free(&userA);
    wc_FreeRng(&rng);

    return 0;
}

#endif /* HAVE_ECC_ENCRYPT */
#endif /* HAVE_ECC */


#ifdef HAVE_CURVE25519

int curve25519_test(void)
{
    RNG     rng;
    byte    sharedA[32];
    byte    sharedB[32];
    byte    exportBuf[32];
    word32  x, y;
    curve25519_key userA, userB, pubKey;

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

    if (wc_InitRng(&rng) != 0)
        return -1001;

    wc_curve25519_init(&userA);
    wc_curve25519_init(&userB);
    wc_curve25519_init(&pubKey);

    /* make curve25519 keys */
    if (wc_curve25519_make_key(&rng, 32, &userA) != 0)
        return -1002;

    if (wc_curve25519_make_key(&rng, 32, &userB) != 0)
        return -1003;

    /* find shared secret key */
    if (wc_curve25519_shared_secret(&userA, &userB, sharedA, &x) != 0)
        return -1004;

    if (wc_curve25519_shared_secret(&userB, &userA, sharedB, &y) != 0)
        return -1005;

    /* compare shared secret keys to test they are the same */
    if (y != x)
        return -1006;

    if (XMEMCMP(sharedA, sharedB, x))
        return -1007;

    /* export a public key and import it for another user */
    if (wc_curve25519_export_public(&userA, exportBuf, &x) != 0)
        return -1008;

    if (wc_curve25519_import_public(exportBuf, x, &pubKey) != 0)
        return -1009;

    /* test shared key after importing a public key */
    XMEMSET(sharedB, 0, sizeof(sharedB));
    if (wc_curve25519_shared_secret(&userB, &pubKey, sharedB, &y) != 0)
        return -1010;

    if (XMEMCMP(sharedA, sharedB, y))
        return -1011;

    /* import RFC test vectors and compare shared key */
    if (wc_curve25519_import_private_raw(sa, sizeof(sa), pa, sizeof(pa), &userA)
            != 0)
        return -1012;

    if (wc_curve25519_import_private_raw(sb, sizeof(sb), pb, sizeof(pb), &userB)
            != 0)
        return -1013;

    /* test against known test vector */
    XMEMSET(sharedB, 0, sizeof(sharedB));
    if (wc_curve25519_shared_secret(&userA, &userB, sharedB, &y) != 0)
        return -1014;

    if (XMEMCMP(ss, sharedB, y))
        return -1015;

    /* test swaping roles of keys and generating same shared key */
    XMEMSET(sharedB, 0, sizeof(sharedB));
    if (wc_curve25519_shared_secret(&userB, &userA, sharedB, &y) != 0)
        return -1016;

    if (XMEMCMP(ss, sharedB, y))
        return -1017;

    /* clean up keys when done */
    wc_curve25519_free(&pubKey);
    wc_curve25519_free(&userB);
    wc_curve25519_free(&userA);

    wc_FreeRng(&rng);

    return 0;
}
#endif /* HAVE_CURVE25519 */


#ifdef HAVE_ED25519
int ed25519_test(void)
{
    RNG    rng;
    byte   out[ED25519_SIG_SIZE];
    byte   exportPKey[ED25519_KEY_SIZE];
    byte   exportSKey[ED25519_KEY_SIZE];
    word32 outlen;
    word32 exportPSz;
    word32 exportSSz;
    word32 keySz, sigSz;
    int    i, verify;
    ed25519_key key;
    ed25519_key key2;

    /* test vectors from
       https://tools.ietf.org/html/draft-josefsson-eddsa-ed25519-02
     */

    const byte sKey1[] = {
		0x9d,0x61,0xb1,0x9d,0xef,0xfd,0x5a,0x60,
		0xba,0x84,0x4a,0xf4,0x92,0xec,0x2c,0xc4,
		0x44,0x49,0xc5,0x69,0x7b,0x32,0x69,0x19,
		0x70,0x3b,0xac,0x03,0x1c,0xae,0x7f,0x60
    };

    const byte sKey2[] = {
		0x4c,0xcd,0x08,0x9b,0x28,0xff,0x96,0xda,
		0x9d,0xb6,0xc3,0x46,0xec,0x11,0x4e,0x0f,
		0x5b,0x8a,0x31,0x9f,0x35,0xab,0xa6,0x24,
		0xda,0x8c,0xf6,0xed,0x4f,0xb8,0xa6,0xfb
    };

    const byte sKey3[] = {
		0xc5,0xaa,0x8d,0xf4,0x3f,0x9f,0x83,0x7b,
		0xed,0xb7,0x44,0x2f,0x31,0xdc,0xb7,0xb1,
		0x66,0xd3,0x85,0x35,0x07,0x6f,0x09,0x4b,
		0x85,0xce,0x3a,0x2e,0x0b,0x44,0x58,0xf7
    };

    /* uncompressed test */
    const byte sKey4[] = {
		0x9d,0x61,0xb1,0x9d,0xef,0xfd,0x5a,0x60,
		0xba,0x84,0x4a,0xf4,0x92,0xec,0x2c,0xc4,
		0x44,0x49,0xc5,0x69,0x7b,0x32,0x69,0x19,
		0x70,0x3b,0xac,0x03,0x1c,0xae,0x7f,0x60
    };

    /* compressed prefix test */
    const byte sKey5[] = {
		0x9d,0x61,0xb1,0x9d,0xef,0xfd,0x5a,0x60,
		0xba,0x84,0x4a,0xf4,0x92,0xec,0x2c,0xc4,
		0x44,0x49,0xc5,0x69,0x7b,0x32,0x69,0x19,
		0x70,0x3b,0xac,0x03,0x1c,0xae,0x7f,0x60
    };

    const byte sKey6[] = {
		0xf5,0xe5,0x76,0x7c,0xf1,0x53,0x31,0x95,
		0x17,0x63,0x0f,0x22,0x68,0x76,0xb8,0x6c,
		0x81,0x60,0xcc,0x58,0x3b,0xc0,0x13,0x74,
		0x4c,0x6b,0xf2,0x55,0xf5,0xcc,0x0e,0xe5
    };

    const byte* sKeys[] = {sKey1, sKey2, sKey3, sKey4, sKey5, sKey6};

    const byte pKey1[] = {
		0xd7,0x5a,0x98,0x01,0x82,0xb1,0x0a,0xb7,
		0xd5,0x4b,0xfe,0xd3,0xc9,0x64,0x07,0x3a,
		0x0e,0xe1,0x72,0xf3,0xda,0xa6,0x23,0x25,
		0xaf,0x02,0x1a,0x68,0xf7,0x07,0x51,0x1a
    };

    const byte pKey2[] = {
		0x3d,0x40,0x17,0xc3,0xe8,0x43,0x89,0x5a,
		0x92,0xb7,0x0a,0xa7,0x4d,0x1b,0x7e,0xbc,
        0x9c,0x98,0x2c,0xcf,0x2e,0xc4,0x96,0x8c,
		0xc0,0xcd,0x55,0xf1,0x2a,0xf4,0x66,0x0c
    };

    const byte pKey3[] = {
		0xfc,0x51,0xcd,0x8e,0x62,0x18,0xa1,0xa3,
		0x8d,0xa4,0x7e,0xd0,0x02,0x30,0xf0,0x58,
		0x08,0x16,0xed,0x13,0xba,0x33,0x03,0xac,
		0x5d,0xeb,0x91,0x15,0x48,0x90,0x80,0x25
    };

    /* uncompressed test */
    const byte pKey4[] = {
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
    const byte pKey5[] = {
		0x40,0xd7,0x5a,0x98,0x01,0x82,0xb1,0x0a,0xb7,
		0xd5,0x4b,0xfe,0xd3,0xc9,0x64,0x07,0x3a,
		0x0e,0xe1,0x72,0xf3,0xda,0xa6,0x23,0x25,
		0xaf,0x02,0x1a,0x68,0xf7,0x07,0x51,0x1a
    };

    const byte pKey6[] = {
		0x27,0x81,0x17,0xfc,0x14,0x4c,0x72,0x34,
		0x0f,0x67,0xd0,0xf2,0x31,0x6e,0x83,0x86,
		0xce,0xff,0xbf,0x2b,0x24,0x28,0xc9,0xc5,
		0x1f,0xef,0x7c,0x59,0x7f,0x1d,0x42,0x6e
    };

    const byte* pKeys[] = {pKey1, pKey2, pKey3, pKey4, pKey5, pKey6};
    const byte  pKeySz[] = {sizeof(pKey1), sizeof(pKey2), sizeof(pKey3),
                            sizeof(pKey4), sizeof(pKey5), sizeof(pKey6)};

    const byte sig1[] = {
		0xe5,0x56,0x43,0x00,0xc3,0x60,0xac,0x72,
		0x90,0x86,0xe2,0xcc,0x80,0x6e,0x82,0x8a,
		0x84,0x87,0x7f,0x1e,0xb8,0xe5,0xd9,0x74,
		0xd8,0x73,0xe0,0x65,0x22,0x49,0x01,0x55,
		0x5f,0xb8,0x82,0x15,0x90,0xa3,0x3b,0xac,
		0xc6,0x1e,0x39,0x70,0x1c,0xf9,0xb4,0x6b,
		0xd2,0x5b,0xf5,0xf0,0x59,0x5b,0xbe,0x24,
		0x65,0x51,0x41,0x43,0x8e,0x7a,0x10,0x0b
    };

    const byte sig2[] = {
		0x92,0xa0,0x09,0xa9,0xf0,0xd4,0xca,0xb8,
		0x72,0x0e,0x82,0x0b,0x5f,0x64,0x25,0x40,
		0xa2,0xb2,0x7b,0x54,0x16,0x50,0x3f,0x8f,
		0xb3,0x76,0x22,0x23,0xeb,0xdb,0x69,0xda,
		0x08,0x5a,0xc1,0xe4,0x3e,0x15,0x99,0x6e,
		0x45,0x8f,0x36,0x13,0xd0,0xf1,0x1d,0x8c,
		0x38,0x7b,0x2e,0xae,0xb4,0x30,0x2a,0xee,
		0xb0,0x0d,0x29,0x16,0x12,0xbb,0x0c,0x00
    };

    const byte sig3[] = {
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
    const byte sig4[] = {
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
    const byte sig5[] = {
		0xe5,0x56,0x43,0x00,0xc3,0x60,0xac,0x72,
		0x90,0x86,0xe2,0xcc,0x80,0x6e,0x82,0x8a,
		0x84,0x87,0x7f,0x1e,0xb8,0xe5,0xd9,0x74,
		0xd8,0x73,0xe0,0x65,0x22,0x49,0x01,0x55,
		0x5f,0xb8,0x82,0x15,0x90,0xa3,0x3b,0xac,
		0xc6,0x1e,0x39,0x70,0x1c,0xf9,0xb4,0x6b,
		0xd2,0x5b,0xf5,0xf0,0x59,0x5b,0xbe,0x24,
		0x65,0x51,0x41,0x43,0x8e,0x7a,0x10,0x0b
    };

    const byte sig6[] = {
		0x0a,0xab,0x4c,0x90,0x05,0x01,0xb3,0xe2,
		0x4d,0x7c,0xdf,0x46,0x63,0x32,0x6a,0x3a,
		0x87,0xdf,0x5e,0x48,0x43,0xb2,0xcb,0xdb,
		0x67,0xcb,0xf6,0xe4,0x60,0xfe,0xc3,0x50,
		0xaa,0x53,0x71,0xb1,0x50,0x8f,0x9f,0x45,
		0x28,0xec,0xea,0x23,0xc4,0x36,0xd9,0x4b,
		0x5e,0x8f,0xcd,0x4f,0x68,0x1e,0x30,0xa6,
		0xac,0x00,0xa9,0x70,0x4a,0x18,0x8a,0x03
    };

    const byte* sigs[] = {sig1, sig2, sig3, sig4, sig5, sig6};

    const byte msg1[]  = {};
    const byte msg2[]  = {0x72};
    const byte msg3[]  = {0xAF,0x82};

    /* test of a 1024 byte long message */
    const byte msg4[]  = {
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

    const byte* msgs[] = {msg1, msg2, msg3, msg1, msg1, msg4};
    const word16 msgSz[] = {sizeof(msg1), sizeof(msg2), sizeof(msg3),
                            sizeof(msg1), sizeof(msg1), sizeof(msg4)};

    /* create ed25519 keys */
    wc_InitRng(&rng);
    wc_ed25519_init(&key);
    wc_ed25519_init(&key2);
    wc_ed25519_make_key(&rng, ED25519_KEY_SIZE, &key);
    wc_ed25519_make_key(&rng, ED25519_KEY_SIZE, &key2);

    /* helper functions for signature and key size */
    keySz = wc_ed25519_size(&key);
    sigSz = wc_ed25519_sig_size(&key);

    for (i = 0; i < 6; i++) {
        outlen = sizeof(out);
        XMEMSET(out, 0, sizeof(out));

        if (wc_ed25519_import_private_key(sKeys[i], ED25519_KEY_SIZE, pKeys[i],
                pKeySz[i], &key) != 0)
            return -1021 - i;

        if (wc_ed25519_sign_msg(msgs[i], msgSz[i], out, &outlen, &key)
                != 0)
            return -1027 - i;

        if (XMEMCMP(out, sigs[i], 64))
            return -1033 - i;

        /* test verify on good msg */
        if (wc_ed25519_verify_msg(out, outlen, msgs[i], msgSz[i], &verify,
                    &key) != 0 || verify != 1)
            return -1039 - i;

        /* test verify on bad msg */
        out[outlen-1] = out[outlen-1] + 1;
        if (wc_ed25519_verify_msg(out, outlen, msgs[i], msgSz[i], &verify,
                    &key) == 0 || verify == 1)
            return -1045 - i;

        /* test api for import/exporting keys */
        exportPSz = sizeof(exportPKey);
        exportSSz = sizeof(exportSKey);
        if (wc_ed25519_export_public(&key, exportPKey, &exportPSz) != 0)
            return -1051 - i;

        if (wc_ed25519_import_public(exportPKey, exportPSz, &key2) != 0)
            return -1057 - i;

        if (wc_ed25519_export_private_only(&key, exportSKey, &exportSSz) != 0)
            return -1063 - i;

        if (wc_ed25519_import_private_key(exportSKey, exportSSz,
                                          exportPKey, exportPSz, &key2) != 0)
            return -1069 - i;

        /* clear "out" buffer and test sign with imported keys */
        outlen = sizeof(out);
        XMEMSET(out, 0, sizeof(out));
        if (wc_ed25519_sign_msg(msgs[i], msgSz[i], out, &outlen, &key2) != 0)
            return -1075 - i;

        if (wc_ed25519_verify_msg(out, outlen, msgs[i], msgSz[i], &verify,
                                  &key2) != 0 || verify != 1)
            return -1081 - i;

        if (XMEMCMP(out, sigs[i], 64))
            return -1087 - i;
    }

    /* clean up keys when done */
    wc_ed25519_free(&key);
    wc_ed25519_free(&key2);

#if defined(HAVE_HASHDRBG) || defined(NO_RC4)
    wc_FreeRng(&rng);
#endif

    /* hush warrnings of unused keySz and sigSz */
    (void)keySz;
    (void)sigSz;

    return 0;
}
#endif /* HAVE_ED25519 */


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


int compress_test(void)
{
    int ret = 0;
    word32 dSz = sizeof(sample_text);
    word32 cSz = (dSz + (word32)(dSz * 0.001) + 12);
    byte *c = NULL;
    byte *d = NULL;

    c = calloc(cSz, sizeof(byte));
    d = calloc(dSz, sizeof(byte));

    if (c == NULL || d == NULL)
        ret = -300;

    if (ret == 0 && (ret = wc_Compress(c, cSz, sample_text, dSz, 0)) < 0)
        ret = -301;

    if (ret > 0) {
        cSz = (word32)ret;
        ret = 0;
    }

    if (ret == 0 && wc_DeCompress(d, dSz, c, cSz) != (int)dSz)
        ret = -302;

    if (ret == 0 && memcmp(d, sample_text, dSz))
        ret = -303;

    if (c) free(c);
    if (d) free(d);

    return ret;
}

#endif /* HAVE_LIBZ */

#ifdef HAVE_PKCS7

int pkcs7enveloped_test(void)
{
    int ret = 0;

    int cipher = DES3b;
    int envelopedSz, decodedSz;
    PKCS7 pkcs7;
    byte* cert;
    byte* privKey;
    byte  enveloped[2048];
    byte  decoded[2048];

    size_t certSz;
    size_t privKeySz;
    FILE*  certFile;
    FILE*  keyFile;
    FILE*  pkcs7File;
    const char* pkcs7OutFile = "pkcs7envelopedData.der";

    const byte data[] = { /* Hello World */
        0x48,0x65,0x6c,0x6c,0x6f,0x20,0x57,0x6f,
        0x72,0x6c,0x64
    };

    /* read client cert and key in DER format */
    cert = (byte*)malloc(FOURK_BUF);
    if (cert == NULL)
        return -201;

    privKey = (byte*)malloc(FOURK_BUF);
    if (privKey == NULL) {
        free(cert);
        return -202;
    }

    certFile = fopen(clientCert, "rb");
    if (!certFile) {
        free(cert);
        free(privKey);
        err_sys("can't open ./certs/client-cert.der, "
                "Please run from wolfSSL home dir", -42);
        return -42;
    }

    certSz = fread(cert, 1, FOURK_BUF, certFile);
    fclose(certFile);

    keyFile = fopen(clientKey, "rb");
    if (!keyFile) {
        free(cert);
        free(privKey);
        err_sys("can't open ./certs/client-key.der, "
                "Please run from wolfSSL home dir", -43);
        return -43;
    }

    privKeySz = fread(privKey, 1, FOURK_BUF, keyFile);
    fclose(keyFile);

    wc_PKCS7_InitWithCert(&pkcs7, cert, (word32)certSz);
    pkcs7.content     = (byte*)data;
    pkcs7.contentSz   = (word32)sizeof(data);
    pkcs7.contentOID  = DATA;
    pkcs7.encryptOID  = cipher;
    pkcs7.privateKey  = privKey;
    pkcs7.privateKeySz = (word32)privKeySz;

    /* encode envelopedData */
    envelopedSz = wc_PKCS7_EncodeEnvelopedData(&pkcs7, enveloped,
                                            sizeof(enveloped));
    if (envelopedSz <= 0) {
        free(cert);
        free(privKey);
        return -203;
    }

    /* decode envelopedData */
    decodedSz = wc_PKCS7_DecodeEnvelopedData(&pkcs7, enveloped, envelopedSz,
                                          decoded, sizeof(decoded));
    if (decodedSz <= 0) {
        free(cert);
        free(privKey);
        return -204;
    }

    /* test decode result */
    if (memcmp(decoded, data, sizeof(data)) != 0) {
        free(cert);
        free(privKey);
        return -205;
    }

    /* output pkcs7 envelopedData for external testing */
    pkcs7File = fopen(pkcs7OutFile, "wb");
    if (!pkcs7File) {
        free(cert);
        free(privKey);
        return -206;
    }

    ret = (int)fwrite(enveloped, envelopedSz, 1, pkcs7File);
    fclose(pkcs7File);

    free(cert);
    free(privKey);
    wc_PKCS7_Free(&pkcs7);

    if (ret > 0)
        return 0;

    return ret;
}

int pkcs7signed_test(void)
{
    int ret = 0;

    FILE* file;
    byte* certDer;
    byte* keyDer;
    byte* out;
    char data[] = "Hello World";
    word32 dataSz, outSz, certDerSz, keyDerSz;
    PKCS7 msg;
    RNG rng;

    byte transIdOid[] =
               { 0x06, 0x0a, 0x60, 0x86, 0x48, 0x01, 0x86, 0xF8, 0x45, 0x01,
                 0x09, 0x07 };
    byte messageTypeOid[] =
               { 0x06, 0x0a, 0x60, 0x86, 0x48, 0x01, 0x86, 0xF8, 0x45, 0x01,
                 0x09, 0x02 };
    byte senderNonceOid[] =
               { 0x06, 0x0a, 0x60, 0x86, 0x48, 0x01, 0x86, 0xF8, 0x45, 0x01,
                 0x09, 0x05 };
    byte transId[(SHA_DIGEST_SIZE + 1) * 2 + 1];
    byte messageType[] = { 0x13, 2, '1', '9' };
    byte senderNonce[PKCS7_NONCE_SZ + 2];

    PKCS7Attrib attribs[] =
    {
        { transIdOid, sizeof(transIdOid),
                     transId, sizeof(transId) - 1 }, /* take off the null */
        { messageTypeOid, sizeof(messageTypeOid),
                     messageType, sizeof(messageType) },
        { senderNonceOid, sizeof(senderNonceOid),
                     senderNonce, sizeof(senderNonce) }
    };

    dataSz = (word32) strlen(data);
    outSz = FOURK_BUF;

    certDer = (byte*)malloc(FOURK_BUF);
    if (certDer == NULL)
        return -207;
    keyDer = (byte*)malloc(FOURK_BUF);
    if (keyDer == NULL) {
        free(certDer);
        return -208;
    }
    out = (byte*)malloc(FOURK_BUF);
    if (out == NULL) {
        free(certDer);
        free(keyDer);
        return -209;
    }

    /* read in DER cert of recipient, into cert of size certSz */
    file = fopen(clientCert, "rb");
    if (!file) {
        free(certDer);
        free(keyDer);
        free(out);
        err_sys("can't open ./certs/client-cert.der, "
                "Please run from wolfSSL home dir", -44);
        return -44;
    }
    certDerSz = (word32)fread(certDer, 1, FOURK_BUF, file);
    fclose(file);

    file = fopen(clientKey, "rb");
    if (!file) {
        free(certDer);
        free(keyDer);
        free(out);
        err_sys("can't open ./certs/client-key.der, "
                "Please run from wolfSSL home dir", -45);
        return -45;
    }
    keyDerSz = (word32)fread(keyDer, 1, FOURK_BUF, file);
    fclose(file);

    ret = wc_InitRng(&rng);
    if (ret != 0) {
        free(certDer);
        free(keyDer);
        free(out);
        return -210;
    }

    senderNonce[0] = 0x04;
    senderNonce[1] = PKCS7_NONCE_SZ;

    ret = wc_RNG_GenerateBlock(&rng, &senderNonce[2], PKCS7_NONCE_SZ);
    if (ret != 0) {
        free(certDer);
        free(keyDer);
        free(out);
        return -211;
    }

    wc_PKCS7_InitWithCert(&msg, certDer, certDerSz);
    msg.privateKey = keyDer;
    msg.privateKeySz = keyDerSz;
    msg.content = (byte*)data;
    msg.contentSz = dataSz;
    msg.hashOID = SHAh;
    msg.encryptOID = RSAk;
    msg.signedAttribs = attribs;
    msg.signedAttribsSz = sizeof(attribs)/sizeof(PKCS7Attrib);
    msg.rng = &rng;
    {
        Sha sha;
        byte digest[SHA_DIGEST_SIZE];
        int i,j;

        transId[0] = 0x13;
        transId[1] = SHA_DIGEST_SIZE * 2;

        ret = wc_InitSha(&sha);
        if (ret != 0) {
            free(certDer);
            free(keyDer);
            free(out);
            return -4003;
        }
        wc_ShaUpdate(&sha, msg.publicKey, msg.publicKeySz);
        wc_ShaFinal(&sha, digest);

        for (i = 0, j = 2; i < SHA_DIGEST_SIZE; i++, j += 2) {
            snprintf((char*)&transId[j], 3, "%02x", digest[i]);
        }
    }
    ret = wc_PKCS7_EncodeSignedData(&msg, out, outSz);
    if (ret < 0) {
        free(certDer);
        free(keyDer);
        free(out);
        wc_PKCS7_Free(&msg);
        return -212;
    }
    else
        outSz = ret;

    /* write PKCS#7 to output file for more testing */
    file = fopen("./pkcs7signedData.der", "wb");
    if (!file) {
        free(certDer);
        free(keyDer);
        free(out);
        wc_PKCS7_Free(&msg);
        return -213;
    }
    ret = (int)fwrite(out, 1, outSz, file);
    fclose(file);
    if (ret != (int)outSz) {
        free(certDer);
        free(keyDer);
        free(out);
        wc_PKCS7_Free(&msg);
        return -218;
    }

    wc_PKCS7_Free(&msg);
    wc_PKCS7_InitWithCert(&msg, NULL, 0);

    ret = wc_PKCS7_VerifySignedData(&msg, out, outSz);
    if (ret < 0) {
        free(certDer);
        free(keyDer);
        free(out);
        wc_PKCS7_Free(&msg);
        return -214;
    }

    if (msg.singleCert == NULL || msg.singleCertSz == 0) {
        free(certDer);
        free(keyDer);
        free(out);
        wc_PKCS7_Free(&msg);
        return -215;
    }

    file = fopen("./pkcs7cert.der", "wb");
    if (!file) {
        free(certDer);
        free(keyDer);
        free(out);
        wc_PKCS7_Free(&msg);
        return -216;
    }
    ret = (int)fwrite(msg.singleCert, 1, msg.singleCertSz, file);
    fclose(file);

    free(certDer);
    free(keyDer);
    free(out);
    wc_PKCS7_Free(&msg);

    wc_FreeRng(&rng);

    if (ret > 0)
        return 0;

    return ret;
}

#endif /* HAVE_PKCS7 */

#endif /* NO_CRYPT_TEST */
