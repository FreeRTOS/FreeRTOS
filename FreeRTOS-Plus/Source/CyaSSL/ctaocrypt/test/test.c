/* test.c
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

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <string.h>
#include <stdio.h>
#include <stdlib.h>

#ifdef CYASSL_TEST_CERT
    #include <cyassl/ctaocrypt/asn.h>
#else
    #include <cyassl/ctaocrypt/asn_public.h>
#endif
#include <cyassl/ctaocrypt/md2.h>
#include <cyassl/ctaocrypt/md5.h>
#include <cyassl/ctaocrypt/md4.h>
#include <cyassl/ctaocrypt/sha.h>
#include <cyassl/ctaocrypt/sha256.h>
#include <cyassl/ctaocrypt/sha512.h>
#include <cyassl/ctaocrypt/arc4.h>
#include <cyassl/ctaocrypt/random.h>
#include <cyassl/ctaocrypt/coding.h>
#include <cyassl/ctaocrypt/rsa.h>
#include <cyassl/ctaocrypt/des3.h>
#include <cyassl/ctaocrypt/aes.h>
#include <cyassl/ctaocrypt/hmac.h>
#include <cyassl/ctaocrypt/dh.h>
#include <cyassl/ctaocrypt/dsa.h>
#include <cyassl/ctaocrypt/hc128.h>
#include <cyassl/ctaocrypt/rabbit.h>
#include <cyassl/ctaocrypt/pwdbased.h>
#include <cyassl/ctaocrypt/ripemd.h>
#ifdef HAVE_ECC
    #include <cyassl/ctaocrypt/ecc.h>
#endif    

#ifdef _MSC_VER
    /* 4996 warning to use MS extensions e.g., strcpy_s instead of strncpy */
    #pragma warning(disable: 4996)
#endif

#ifdef OPENSSL_EXTRA
    #include <cyassl/openssl/evp.h>
    #include <cyassl/openssl/rand.h>
    #include <cyassl/openssl/hmac.h>
    #include <cyassl/openssl/des.h>
#endif

#ifdef HAVE_NTRU
    #include "crypto_ntru.h"
#endif


#ifdef THREADX
    /* since just testing, use THREADX log printf instead */
    int dc_log_printf(char*, ...);
        #undef printf
        #define printf dc_log_printf
#endif


typedef struct testVector {
    char*  input;
    char*  output; 
    size_t inLen;
    size_t outLen;
} testVector;

int  md2_test();
int  md5_test();
int  md4_test();
int  sha_test();
int  sha256_test();
int  sha512_test();
int  sha384_test();
int  hmac_test();
int  arc4_test();
int  hc128_test();
int  rabbit_test();
int  des_test();
int  des3_test();
int  aes_test();
int  aesgcm_test();
int  rsa_test();
int  dh_test();
int  dsa_test();
int  random_test();
int  pwdbased_test();
int  ripemd_test();
int  openssl_test();   /* test mini api */
#ifdef HAVE_ECC
    int  ecc_test();
#endif

int PemToDer(const char* inName, const char* outName);


void err_sys(const char* msg, int es)
{
    printf("%s error = %d\n", msg, es);
#ifndef THREADX
    exit(es);
#endif
}

/* func_args from test.h, so don't have to pull in other junk */
typedef struct func_args {
    int    argc;
    char** argv;
    int    return_code;
} func_args;


void ctaocrypt_test(void* args)
{
    int ret = 0;

    ((func_args*)args)->return_code = -1; /* error state */

    if (CheckCtcSettings() != 1)
        err_sys("Build vs runtime math mismatch\n", -1234);

#ifdef USE_FAST_MATH
    if (CheckFastMathSettings() != 1)
        err_sys("Build vs runtime fastmath FP_MAX_BITS mismatch\n", -1235);
#endif
    
    if ( (ret = md5_test()) ) 
        err_sys("MD5      test failed!\n", ret);
    else
        printf( "MD5      test passed!\n");

#ifdef CYASSL_MD2
    if ( (ret = md2_test()) ) 
        err_sys("MD2      test failed!\n", ret);
    else
        printf( "MD2      test passed!\n");
#endif

#ifndef NO_MD4
    if ( (ret = md4_test()) ) 
        err_sys("MD4      test failed!\n", ret);
    else
        printf( "MD4      test passed!\n");
#endif

    if ( (ret = sha_test()) ) 
        err_sys("SHA      test failed!\n", ret);
    else
        printf( "SHA      test passed!\n");

#ifndef NO_SHA256
    if ( (ret = sha256_test()) ) 
        err_sys("SHA-256  test failed!\n", ret);
    else
        printf( "SHA-256  test passed!\n");
#endif

#ifdef CYASSL_SHA384
    if ( (ret = sha384_test()) ) 
        err_sys("SHA-384  test failed!\n", ret);
    else
        printf( "SHA-384  test passed!\n");
#endif

#ifdef CYASSL_SHA512
    if ( (ret = sha512_test()) ) 
        err_sys("SHA-512  test failed!\n", ret);
    else
        printf( "SHA-512  test passed!\n");
#endif

#ifdef CYASSL_RIPEMD
    if ( (ret = ripemd_test()) ) 
        err_sys("RIPEMD   test failed!\n", ret);
    else
        printf( "RIPEMD   test passed!\n");
#endif

#ifndef NO_HMAC
    if ( (ret = hmac_test()) ) 
        err_sys("HMAC     test failed!\n", ret);
    else
        printf( "HMAC     test passed!\n");
#endif

    if ( (ret = arc4_test()) )
        err_sys("ARC4     test failed!\n", ret);
    else
        printf( "ARC4     test passed!\n");

#ifndef NO_HC128
    if ( (ret = hc128_test()) )
        err_sys("HC-128   test failed!\n", ret);
    else
        printf( "HC-128   test passed!\n");
#endif

#ifndef NO_RABBIT
    if ( (ret = rabbit_test()) )
        err_sys("Rabbit   test failed!\n", ret);
    else
        printf( "Rabbit   test passed!\n");
#endif

#ifndef NO_DES3
    if ( (ret = des_test()) )
        err_sys("DES      test failed!\n", ret);
    else
        printf( "DES      test passed!\n");
#endif

#ifndef NO_DES3
    if ( (ret = des3_test()) )
        err_sys("DES3     test failed!\n", ret);
    else
        printf( "DES3     test passed!\n");
#endif

#ifndef NO_AES
    if ( (ret = aes_test()) )
        err_sys("AES      test failed!\n", ret);
    else
        printf( "AES      test passed!\n");

#ifdef HAVE_AESGCM
    if ( (ret = aesgcm_test()) )
        err_sys("AES-GCM  test failed!\n", ret);
    else
        printf( "AES-GCM  test passed!\n");
#endif
#endif

    if ( (ret = random_test()) )
        err_sys("RANDOM   test failed!\n", ret);
    else
        printf( "RANDOM   test passed!\n");

    if ( (ret = rsa_test()) ) 
        err_sys("RSA      test failed!\n", ret);
    else
        printf( "RSA      test passed!\n");

#ifndef NO_DH
    if ( (ret = dh_test()) ) 
        err_sys("DH       test failed!\n", ret);
    else
        printf( "DH       test passed!\n");
#endif

#ifndef NO_DSA
    if ( (ret = dsa_test()) ) 
        err_sys("DSA      test failed!\n", ret);
    else
        printf( "DSA      test passed!\n");
#endif
    
#ifndef NO_PWDBASED
    if ( (ret = pwdbased_test()) ) 
        err_sys("PWDBASED test failed!\n", ret);
    else
        printf( "PWDBASED test passed!\n");
#endif
    
#ifdef OPENSSL_EXTRA
    if ( (ret = openssl_test()) ) 
        err_sys("OPENSSL  test failed!\n", ret);
    else
        printf( "OPENSSL  test passed!\n");
#endif

#ifdef HAVE_ECC
    if ( (ret = ecc_test()) ) 
        err_sys("ECC      test failed!\n", ret);
    else
        printf( "ECC      test passed!\n");
#endif

    ((func_args*)args)->return_code = ret;
}


/* so overall tests can pull in test function */
#ifndef NO_MAIN_DRIVER

    int main(int argc, char** argv)
    {
        func_args args;

        args.argc = argc;
        args.argv = argv;

        ctaocrypt_test(&args);
        return args.return_code;
    }

#endif /* NO_MAIN_DRIVER */


#ifdef CYASSL_MD2
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
    a.outLen = strlen(a.output);

    b.input  = "a";
    b.output = "\x32\xec\x01\xec\x4a\x6d\xac\x72\xc0\xab\x96\xfb\x34\xc0"
               "\xb5\xd1";
    b.inLen  = strlen(b.input);
    b.outLen = strlen(b.output);

    c.input  = "abc";
    c.output = "\xda\x85\x3b\x0d\x3f\x88\xd9\x9b\x30\x28\x3a\x69\xe6\xde"
               "\xd6\xbb";
    c.inLen  = strlen(c.input);
    c.outLen = strlen(c.output);

    d.input  = "message digest";
    d.output = "\xab\x4f\x49\x6b\xfb\x2a\x53\x0b\x21\x9f\xf3\x30\x31\xfe"
               "\x06\xb0";
    d.inLen  = strlen(d.input);
    d.outLen = strlen(d.output);

    e.input  = "abcdefghijklmnopqrstuvwxyz";
    e.output = "\x4e\x8d\xdf\xf3\x65\x02\x92\xab\x5a\x41\x08\xc3\xaa\x47"
               "\x94\x0b";
    e.inLen  = strlen(e.input);
    e.outLen = strlen(e.output);

    f.input  = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz012345"
               "6789";
    f.output = "\xda\x33\xde\xf2\xa4\x2d\xf1\x39\x75\x35\x28\x46\xc3\x03"
               "\x38\xcd";
    f.inLen  = strlen(f.input);
    f.outLen = strlen(f.output);

    g.input  = "1234567890123456789012345678901234567890123456789012345678"
               "9012345678901234567890";
    g.output = "\xd5\x97\x6f\x79\xd8\x3d\x3a\x0d\xc9\x80\x6c\x3c\x66\xf3"
               "\xef\xd8";
    g.inLen  = strlen(g.input);
    g.outLen = strlen(g.output);

    test_md2[0] = a;
    test_md2[1] = b;
    test_md2[2] = c;
    test_md2[3] = d;
    test_md2[4] = e;
    test_md2[5] = f;
    test_md2[6] = g;

    InitMd2(&md2);

    for (i = 0; i < times; ++i) {
        Md2Update(&md2, (byte*)test_md2[i].input, (word32)test_md2[i].inLen);
        Md2Final(&md2, hash);

        if (memcmp(hash, test_md2[i].output, MD2_DIGEST_SIZE) != 0)
            return -155 - i;
    }

    return 0;
}
#endif 


int md5_test()
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
    a.outLen = strlen(a.output);

    b.input  = "message digest";
    b.output = "\xf9\x6b\x69\x7d\x7c\xb7\x93\x8d\x52\x5a\x2f\x31\xaa\xf1\x61"
               "\xd0";
    b.inLen  = strlen(b.input);
    b.outLen = strlen(b.output);

    c.input  = "abcdefghijklmnopqrstuvwxyz";
    c.output = "\xc3\xfc\xd3\xd7\x61\x92\xe4\x00\x7d\xfb\x49\x6c\xca\x67\xe1"
               "\x3b";
    c.inLen  = strlen(c.input);
    c.outLen = strlen(c.output);

    d.input  = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz012345"
               "6789";
    d.output = "\xd1\x74\xab\x98\xd2\x77\xd9\xf5\xa5\x61\x1c\x2c\x9f\x41\x9d"
               "\x9f";
    d.inLen  = strlen(d.input);
    d.outLen = strlen(d.output);

    e.input  = "1234567890123456789012345678901234567890123456789012345678"
               "9012345678901234567890";
    e.output = "\x57\xed\xf4\xa2\x2b\xe3\xc9\x55\xac\x49\xda\x2e\x21\x07\xb6"
               "\x7a";
    e.inLen  = strlen(e.input);
    e.outLen = strlen(e.output);

    test_md5[0] = a;
    test_md5[1] = b;
    test_md5[2] = c;
    test_md5[3] = d;
    test_md5[4] = e;

    InitMd5(&md5);

    for (i = 0; i < times; ++i) {
        Md5Update(&md5, (byte*)test_md5[i].input, (word32)test_md5[i].inLen);
        Md5Final(&md5, hash);

        if (memcmp(hash, test_md5[i].output, MD5_DIGEST_SIZE) != 0)
            return -5 - i;
    }

    return 0;
}


#ifndef NO_MD4

int md4_test()
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
    a.outLen = strlen(a.output);

    b.input  = "a";
    b.output = "\xbd\xe5\x2c\xb3\x1d\xe3\x3e\x46\x24\x5e\x05\xfb\xdb\xd6\xfb" 
               "\x24";
    b.inLen  = strlen(b.input);
    b.outLen = strlen(b.output);

    c.input  = "abc";
    c.output = "\xa4\x48\x01\x7a\xaf\x21\xd8\x52\x5f\xc1\x0a\xe8\x7a\xa6\x72" 
               "\x9d";
    c.inLen  = strlen(c.input);
    c.outLen = strlen(c.output);

    d.input  = "message digest";
    d.output = "\xd9\x13\x0a\x81\x64\x54\x9f\xe8\x18\x87\x48\x06\xe1\xc7\x01" 
               "\x4b";
    d.inLen  = strlen(d.input);
    d.outLen = strlen(d.output);

    e.input  = "abcdefghijklmnopqrstuvwxyz";
    e.output = "\xd7\x9e\x1c\x30\x8a\xa5\xbb\xcd\xee\xa8\xed\x63\xdf\x41\x2d" 
               "\xa9";
    e.inLen  = strlen(e.input);
    e.outLen = strlen(e.output);

    f.input  = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz012345"
               "6789";
    f.output = "\x04\x3f\x85\x82\xf2\x41\xdb\x35\x1c\xe6\x27\xe1\x53\xe7\xf0" 
               "\xe4";
    f.inLen  = strlen(f.input);
    f.outLen = strlen(f.output);

    g.input  = "1234567890123456789012345678901234567890123456789012345678"
               "9012345678901234567890";
    g.output = "\xe3\x3b\x4d\xdc\x9c\x38\xf2\x19\x9c\x3e\x7b\x16\x4f\xcc\x05" 
               "\x36";
    g.inLen  = strlen(g.input);
    g.outLen = strlen(g.output);

    test_md4[0] = a;
    test_md4[1] = b;
    test_md4[2] = c;
    test_md4[3] = d;
    test_md4[4] = e;
    test_md4[5] = f;
    test_md4[6] = g;

    InitMd4(&md4);

    for (i = 0; i < times; ++i) {
        Md4Update(&md4, (byte*)test_md4[i].input, (word32)test_md4[i].inLen);
        Md4Final(&md4, hash);

        if (memcmp(hash, test_md4[i].output, MD4_DIGEST_SIZE) != 0)
            return -205 - i;
    }

    return 0;
}

#endif /* NO_MD4 */

int sha_test()
{
    Sha  sha;
    byte hash[SHA_DIGEST_SIZE];

    testVector a, b, c, d;
    testVector test_sha[4];
    int times = sizeof(test_sha) / sizeof(struct testVector), i;

    a.input  = "abc";
    a.output = "\xA9\x99\x3E\x36\x47\x06\x81\x6A\xBA\x3E\x25\x71\x78\x50\xC2"
               "\x6C\x9C\xD0\xD8\x9D";
    a.inLen  = strlen(a.input);
    a.outLen = strlen(a.output);

    b.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    b.output = "\x84\x98\x3E\x44\x1C\x3B\xD2\x6E\xBA\xAE\x4A\xA1\xF9\x51\x29"
               "\xE5\xE5\x46\x70\xF1";
    b.inLen  = strlen(b.input);
    b.outLen = strlen(b.output);

    c.input  = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
               "aaaaaa";
    c.output = "\x00\x98\xBA\x82\x4B\x5C\x16\x42\x7B\xD7\xA1\x12\x2A\x5A\x44"
               "\x2A\x25\xEC\x64\x4D";
    c.inLen  = strlen(c.input);
    c.outLen = strlen(c.output);

    d.input  = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
               "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
               "aaaaaaaaaa";
    d.output = "\xAD\x5B\x3F\xDB\xCB\x52\x67\x78\xC2\x83\x9D\x2F\x15\x1E\xA7"
               "\x53\x99\x5E\x26\xA0";
    d.inLen  = strlen(d.input);
    d.outLen = strlen(d.output);

    test_sha[0] = a;
    test_sha[1] = b;
    test_sha[2] = c;
    test_sha[3] = d;

    InitSha(&sha);

    for (i = 0; i < times; ++i) {
        ShaUpdate(&sha, (byte*)test_sha[i].input, (word32)test_sha[i].inLen);
        ShaFinal(&sha, hash);

        if (memcmp(hash, test_sha[i].output, SHA_DIGEST_SIZE) != 0)
            return -10 - i;
    }

    return 0;
}


#ifdef CYASSL_RIPEMD
int ripemd_test()
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
    a.outLen = strlen(a.output);

    b.input  = "message digest";
    b.output = "\x5d\x06\x89\xef\x49\xd2\xfa\xe5\x72\xb8\x81\xb1\x23\xa8"
               "\x5f\xfa\x21\x59\x5f\x36";
    b.inLen  = strlen(b.input);
    b.outLen = strlen(b.output);

    c.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"; 
    c.output = "\x12\xa0\x53\x38\x4a\x9c\x0c\x88\xe4\x05\xa0\x6c\x27\xdc"
               "\xf4\x9a\xda\x62\xeb\x2b";
    c.inLen  = strlen(c.input);
    c.outLen = strlen(c.output);

    d.input  = "12345678901234567890123456789012345678901234567890123456"
               "789012345678901234567890";
    d.output = "\x9b\x75\x2e\x45\x57\x3d\x4b\x39\xf4\xdb\xd3\x32\x3c\xab"
               "\x82\xbf\x63\x32\x6b\xfb"; 
    d.inLen  = strlen(d.input);
    d.outLen = strlen(d.output);

    test_ripemd[0] = a;
    test_ripemd[1] = b;
    test_ripemd[2] = c;
    test_ripemd[3] = d;

    InitRipeMd(&ripemd);

    for (i = 0; i < times; ++i) {
        RipeMdUpdate(&ripemd, (byte*)test_ripemd[i].input,
                     (word32)test_ripemd[i].inLen);
        RipeMdFinal(&ripemd, hash);

        if (memcmp(hash, test_ripemd[i].output, RIPEMD_DIGEST_SIZE) != 0)
            return -10 - i;
    }

    return 0;
}
#endif /* CYASSL_RIPEMD */


#ifndef NO_SHA256
int sha256_test()
{
    Sha256 sha;
    byte   hash[SHA256_DIGEST_SIZE];

    testVector a, b;
    testVector test_sha[2];
    int times = sizeof(test_sha) / sizeof(struct testVector), i;

    a.input  = "abc";
    a.output = "\xBA\x78\x16\xBF\x8F\x01\xCF\xEA\x41\x41\x40\xDE\x5D\xAE\x22"
               "\x23\xB0\x03\x61\xA3\x96\x17\x7A\x9C\xB4\x10\xFF\x61\xF2\x00"
               "\x15\xAD";
    a.inLen  = strlen(a.input);
    a.outLen = strlen(a.output);

    b.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    b.output = "\x24\x8D\x6A\x61\xD2\x06\x38\xB8\xE5\xC0\x26\x93\x0C\x3E\x60"
               "\x39\xA3\x3C\xE4\x59\x64\xFF\x21\x67\xF6\xEC\xED\xD4\x19\xDB"
               "\x06\xC1";
    b.inLen  = strlen(b.input);
    b.outLen = strlen(b.output);

    test_sha[0] = a;
    test_sha[1] = b;

    InitSha256(&sha);

    for (i = 0; i < times; ++i) {
        Sha256Update(&sha, (byte*)test_sha[i].input,(word32)test_sha[i].inLen);
        Sha256Final(&sha, hash);

        if (memcmp(hash, test_sha[i].output, SHA256_DIGEST_SIZE) != 0)
            return -10 - i;
    }

    return 0;
}
#endif


#ifdef CYASSL_SHA512
int sha512_test()
{
    Sha512 sha;
    byte   hash[SHA512_DIGEST_SIZE];

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
    a.outLen = strlen(a.output);

    b.input  = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhi"
               "jklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    b.output = "\x8e\x95\x9b\x75\xda\xe3\x13\xda\x8c\xf4\xf7\x28\x14\xfc\x14"
               "\x3f\x8f\x77\x79\xc6\xeb\x9f\x7f\xa1\x72\x99\xae\xad\xb6\x88"
               "\x90\x18\x50\x1d\x28\x9e\x49\x00\xf7\xe4\x33\x1b\x99\xde\xc4"
               "\xb5\x43\x3a\xc7\xd3\x29\xee\xb6\xdd\x26\x54\x5e\x96\xe5\x5b"
               "\x87\x4b\xe9\x09"; 
    b.inLen  = strlen(b.input);
    b.outLen = strlen(b.output);

    test_sha[0] = a;
    test_sha[1] = b;

    InitSha512(&sha);

    for (i = 0; i < times; ++i) {
        Sha512Update(&sha, (byte*)test_sha[i].input,(word32)test_sha[i].inLen);
        Sha512Final(&sha, hash);

        if (memcmp(hash, test_sha[i].output, SHA512_DIGEST_SIZE) != 0)
            return -10 - i;
    }

    return 0;
}
#endif


#ifdef CYASSL_SHA384
int sha384_test()
{
    Sha384 sha;
    byte   hash[SHA384_DIGEST_SIZE];

    testVector a, b;
    testVector test_sha[2];
    int times = sizeof(test_sha) / sizeof(struct testVector), i;

    a.input  = "abc";
    a.output = "\xcb\x00\x75\x3f\x45\xa3\x5e\x8b\xb5\xa0\x3d\x69\x9a\xc6\x50"
               "\x07\x27\x2c\x32\xab\x0e\xde\xd1\x63\x1a\x8b\x60\x5a\x43\xff"
               "\x5b\xed\x80\x86\x07\x2b\xa1\xe7\xcc\x23\x58\xba\xec\xa1\x34"
               "\xc8\x25\xa7";
    a.inLen  = strlen(a.input);
    a.outLen = strlen(a.output);

    b.input  = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhi"
               "jklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    b.output = "\x09\x33\x0c\x33\xf7\x11\x47\xe8\x3d\x19\x2f\xc7\x82\xcd\x1b"
               "\x47\x53\x11\x1b\x17\x3b\x3b\x05\xd2\x2f\xa0\x80\x86\xe3\xb0"
               "\xf7\x12\xfc\xc7\xc7\x1a\x55\x7e\x2d\xb9\x66\xc3\xe9\xfa\x91"
               "\x74\x60\x39";
    b.inLen  = strlen(b.input);
    b.outLen = strlen(b.output);

    test_sha[0] = a;
    test_sha[1] = b;

    InitSha384(&sha);

    for (i = 0; i < times; ++i) {
        Sha384Update(&sha, (byte*)test_sha[i].input,(word32)test_sha[i].inLen);
        Sha384Final(&sha, hash);

        if (memcmp(hash, test_sha[i].output, SHA384_DIGEST_SIZE) != 0)
            return -10 - i;
    }

    return 0;
}
#endif /* CYASSL_SHA384 */


#ifndef NO_HMAC
int hmac_test()
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

    int times = sizeof(test_hmac) / sizeof(testVector), i;

    a.input  = "Hi There";
    a.output = "\x92\x94\x72\x7a\x36\x38\xbb\x1c\x13\xf4\x8e\xf8\x15\x8b\xfc"
               "\x9d";
    a.inLen  = strlen(a.input);
    a.outLen = strlen(a.output);

    b.input  = "what do ya want for nothing?";
    b.output = "\x75\x0c\x78\x3e\x6a\xb0\xb5\x03\xea\xa8\x6e\x31\x0a\x5d\xb7"
               "\x38";
    b.inLen  = strlen(b.input);
    b.outLen = strlen(b.output);

    c.input  = "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD\xDD"
               "\xDD\xDD\xDD\xDD\xDD\xDD";
    c.output = "\x56\xbe\x34\x52\x1d\x14\x4c\x88\xdb\xb8\xc7\x33\xf0\xe8\xb3"
               "\xf6";
    c.inLen  = strlen(c.input);
    c.outLen = strlen(c.output);

    test_hmac[0] = a;
    test_hmac[1] = b;
    test_hmac[2] = c;

    for (i = 0; i < times; ++i) {
        HmacSetKey(&hmac, MD5, (byte*)keys[i], (word32)strlen(keys[i]));
        HmacUpdate(&hmac, (byte*)test_hmac[i].input,
                   (word32)test_hmac[i].inLen);
        HmacFinal(&hmac, hash);

        if (memcmp(hash, test_hmac[i].output, MD5_DIGEST_SIZE) != 0)
            return -20 - i;
    }

    return 0;
}
#endif


int arc4_test()
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
    a.inLen  = strlen(a.input);
    a.outLen = strlen(a.output);

    b.input  = "\x00\x00\x00\x00\x00\x00\x00\x00";
    b.output = "\x74\x94\xc2\xe7\x10\x4b\x08\x79";
    b.inLen  = strlen(b.input);
    b.outLen = strlen(b.output);

    c.input  = "\x00\x00\x00\x00\x00\x00\x00\x00";
    c.output = "\xde\x18\x89\x41\xa3\x37\x5d\x3a";
    c.inLen  = strlen(c.input);
    c.outLen = strlen(c.output);

    d.input  = "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00";
    d.output = "\xd6\xa1\x41\xa7\xec\x3c\x38\xdf\xbd\x61";
    d.inLen  = strlen(d.input);
    d.outLen = strlen(d.output);

    test_arc4[0] = a;
    test_arc4[1] = b;
    test_arc4[2] = c;
    test_arc4[3] = d;

    for (i = 0; i < times; ++i) {
        Arc4 enc;
        Arc4 dec;

        Arc4SetKey(&enc, (byte*)keys[i], (word32)strlen(keys[i]));
        Arc4SetKey(&dec, (byte*)keys[i], (word32)strlen(keys[i]));

        Arc4Process(&enc, cipher, (byte*)test_arc4[i].input,
                    (word32)test_arc4[i].outLen);
        Arc4Process(&dec, plain,  cipher, (word32)test_arc4[i].outLen);

        if (memcmp(plain, test_arc4[i].input, test_arc4[i].outLen))
            return -20 - i;

        if (memcmp(cipher, test_arc4[i].output, test_arc4[i].outLen))
            return -20 - 5 - i;
    }

    return 0;
}


int hc128_test()
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
    a.inLen  = strlen(a.input);
    a.outLen = strlen(a.output);

    b.input  = "\x00\x00\x00\x00\x00\x00\x00\x00";
    b.output = "\x33\x7F\x86\x11\xC6\xED\x61\x5F";
    b.inLen  = strlen(b.input);
    b.outLen = strlen(b.output);

    c.input  = "\x00\x00\x00\x00\x00\x00\x00\x00";
    c.output = "\x2E\x1E\xD1\x2A\x85\x51\xC0\x5A";
    c.inLen  = strlen(c.input);
    c.outLen = strlen(c.output);

    d.input  = "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00";
    d.output = "\x1C\xD8\xAE\xDD\xFE\x52\xE2\x17\xE8\x35\xD0\xB7\xE8\x4E\x29";
    d.inLen  = strlen(d.input);
    d.outLen = strlen(d.output);

    test_hc128[0] = a;
    test_hc128[1] = b;
    test_hc128[2] = c;
    test_hc128[3] = d;

    for (i = 0; i < times; ++i) {
        HC128 enc;
        HC128 dec;

        Hc128_SetKey(&enc, (byte*)keys[i], (byte*)ivs[i]);
        Hc128_SetKey(&dec, (byte*)keys[i], (byte*)ivs[i]);

        Hc128_Process(&enc, cipher, (byte*)test_hc128[i].input,
                    (word32)test_hc128[i].outLen);
        Hc128_Process(&dec, plain,  cipher, (word32)test_hc128[i].outLen);

        if (memcmp(plain, test_hc128[i].input, test_hc128[i].outLen))
            return -120 - i;

        if (memcmp(cipher, test_hc128[i].output, test_hc128[i].outLen))
            return -120 - 5 - i;
    }

#endif /* HAVE_HC128 */
    return 0;
}


#ifndef NO_RABBIT
int rabbit_test()
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
    a.inLen  = strlen(a.input);
    a.outLen = strlen(a.output);

    b.input  = "\x00\x00\x00\x00\x00\x00\x00\x00";
    b.output = "\x6D\x7D\x01\x22\x92\xCC\xDC\xE0";
    b.inLen  = strlen(b.input);
    b.outLen = strlen(b.output);

    c.input  = "\x00\x00\x00\x00\x00\x00\x00\x00";
    c.output = "\x9C\x51\xE2\x87\x84\xC3\x7F\xE9";
    c.inLen  = strlen(c.input);
    c.outLen = strlen(c.output);

    test_rabbit[0] = a;
    test_rabbit[1] = b;
    test_rabbit[2] = c;

    for (i = 0; i < times; ++i) {
        Rabbit enc;
        Rabbit dec;

        RabbitSetKey(&enc, (byte*)keys[i], (byte*)ivs[i]);
        RabbitSetKey(&dec, (byte*)keys[i], (byte*)ivs[i]);

        RabbitProcess(&enc, cipher, (byte*)test_rabbit[i].input,
                    (word32)test_rabbit[i].outLen);
        RabbitProcess(&dec, plain,  cipher, (word32)test_rabbit[i].outLen);

        if (memcmp(plain, test_rabbit[i].input, test_rabbit[i].outLen))
            return -130 - i;

        if (memcmp(cipher, test_rabbit[i].output, test_rabbit[i].outLen))
            return -130 - 5 - i;
    }

    return 0;
}
#endif /* NO_RABBIT */


#ifndef NO_DES3
int des_test()
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


    Des_SetKey(&enc, key, iv, DES_ENCRYPTION);
    Des_CbcEncrypt(&enc, cipher, vector, sizeof(vector));
    Des_SetKey(&dec, key, iv, DES_DECRYPTION);
    Des_CbcDecrypt(&dec, plain, cipher, sizeof(cipher));

    if (memcmp(plain, vector, sizeof(plain)))
        return -31;

    if (memcmp(cipher, verify, sizeof(cipher)))
        return -32;

    return 0;
}
#endif /* NO_DES3 */


#ifndef NO_DES3
int des3_test()
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


    Des3_SetKey(&enc, key3, iv3, DES_ENCRYPTION);
    Des3_CbcEncrypt(&enc, cipher, vector, sizeof(vector));
    Des3_SetKey(&dec, key3, iv3, DES_DECRYPTION);
    Des3_CbcDecrypt(&dec, plain, cipher, sizeof(cipher));

    if (memcmp(plain, vector, sizeof(plain)))
        return -33;

    if (memcmp(cipher, verify3, sizeof(cipher)))
        return -34;

    return 0;
}
#endif /* NO_DES */


#ifndef NO_AES
int aes_test()
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

    AesSetKey(&enc, key, AES_BLOCK_SIZE, iv, AES_ENCRYPTION);
    AesSetKey(&dec, key, AES_BLOCK_SIZE, iv, AES_DECRYPTION);

    AesCbcEncrypt(&enc, cipher, msg,   AES_BLOCK_SIZE);
    AesCbcDecrypt(&dec, plain, cipher, AES_BLOCK_SIZE);

    if (memcmp(plain, msg, AES_BLOCK_SIZE))
        return -60;

    if (memcmp(cipher, verify, AES_BLOCK_SIZE))
        return -61;

#ifdef CYASSL_AES_COUNTER
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

        AesSetKey(&enc, ctrKey, AES_BLOCK_SIZE, ctrIv, AES_ENCRYPTION);
        /* Ctr only uses encrypt, even on key setup */
        AesSetKey(&dec, ctrKey, AES_BLOCK_SIZE, ctrIv, AES_ENCRYPTION);

        AesCtrEncrypt(&enc, cipher, ctrPlain, AES_BLOCK_SIZE*4);
        AesCtrEncrypt(&dec, plain, cipher, AES_BLOCK_SIZE*4);

        if (memcmp(plain, ctrPlain, AES_BLOCK_SIZE*4))
            return -66;

        if (memcmp(cipher, ctrCipher, AES_BLOCK_SIZE*4))
            return -67;
    }
#endif /* CYASSL_AES_COUNTER */

    return 0;
}

#ifdef HAVE_AESGCM
int aesgcm_test()
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
        0xde, 0xca, 0xf8, 0x88, 0x00, 0x00, 0x00, 0x00
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

    byte t2[16];
    byte p2[60];
    byte c2[60];

    int result;

    memset(t2, 0, 16);
    memset(c2, 0, 60);
    memset(p2, 0, 60);

    AesGcmSetKey(&enc, k, sizeof(k), iv);
    AesGcmSetExpIV(&enc, iv + /*AES_GCM_IMP_IV_SZ*/ 4);
    /* AES-GCM encrypt and decrypt both use AES encrypt internally */
    AesGcmEncrypt(&enc, c2, p, sizeof(c2), t2, sizeof(t2), a, sizeof(a));
    if (memcmp(c, c2, sizeof(c2)))
        return -68;
    if (memcmp(t, t2, sizeof(t2)))
        return -69;

    result = AesGcmDecrypt(&enc,
                        p2, c2, sizeof(p2), t2, sizeof(t2), a, sizeof(a));
    if (result != 0)
        return -70;
    if (memcmp(p, p2, sizeof(p2)))
        return -71;

    return 0;
}
#endif /* HAVE_AESGCM */


#endif /* NO_AES */


int random_test()
{
    RNG  rng;
    byte block[32];
    int ret = InitRng(&rng);
    if (ret != 0) return -39;

    RNG_GenerateBlock(&rng, block, sizeof(block));

    return 0;
}


static const char* clientKey  = "./certs/client-key.der";
static const char* clientCert = "./certs/client-cert.der";
#ifdef CYASSL_CERT_GEN
    static const char* caKeyFile  = "./certs/ca-key.der";
    static const char* caCertFile = "./certs/ca-cert.pem";
#endif


#ifdef HAVE_NTRU

static byte GetEntropy(ENTROPY_CMD cmd, byte* out)
{
    static RNG rng;

    if (cmd == INIT) {
        int ret = InitRng(&rng);
        if (ret == 0)
            return 1;
        else
            return 0;
    }

    if (out == NULL)
        return 0;

    if (cmd == GET_BYTE_OF_ENTROPY) {
        RNG_GenerateBlock(&rng, out, 1);
        return 1;
    }

    if (cmd == GET_NUM_BYTES_PER_BYTE_OF_ENTROPY) {
        *out = 1;
        return 1;
    }

    return 0;
}

#endif /* HAVE_NTRU */

int rsa_test()
{
    byte   tmp[2048], tmp2[2048];
    size_t bytes, bytes2;
    RsaKey key;
    RNG    rng;
    word32 idx = 0;
    int    ret;
    byte   in[] = "Everyone gets Friday off.";
    word32 inLen = (word32)strlen((char*)in);
    byte   out[256];
    byte   plain[256];
#ifdef CYASSL_TEST_CERT
    DecodedCert cert;
#endif

    FILE*  file = fopen(clientKey, "rb"), * file2;

    if (!file)
        err_sys("can't open ./certs/client-key.der, "
                "Please run from CyaSSL home dir", -40);

    bytes = fread(tmp, 1, sizeof(tmp), file);
  
    InitRsaKey(&key, 0);  
    ret = RsaPrivateKeyDecode(tmp, &idx, &key, (word32)bytes);
    if (ret != 0) return -41;

    ret = InitRng(&rng);
    if (ret != 0) return -42;

    ret = RsaPublicEncrypt(in, inLen, out, sizeof(out), &key, &rng);
    if (ret < 0) return -43;

    ret = RsaPrivateDecrypt(out, ret, plain, sizeof(plain), &key);
    if (ret < 0) return -44;

    if (memcmp(plain, in, inLen)) return -45;

    ret = RsaSSL_Sign(in, inLen, out, sizeof(out), &key, &rng);
    if (ret < 0) return -46;

    memset(plain, 0, sizeof(plain));
    ret = RsaSSL_Verify(out, ret, plain, sizeof(plain), &key);
    if (ret < 0) return -47;

    if (memcmp(plain, in, ret)) return -48;

    file2 = fopen(clientCert, "rb");
    if (!file2)
        return -49;

    bytes2 = fread(tmp2, 1, sizeof(tmp2), file2);

#ifdef CYASSL_TEST_CERT
    InitDecodedCert(&cert, (byte*)&tmp2, (word32)bytes2, 0);

    ret = ParseCert(&cert, CERT_TYPE, NO_VERIFY, 0);
    if (ret != 0) return -491;

    FreeDecodedCert(&cert);
#endif

    fclose(file2);
    fclose(file);

#ifdef CYASSL_KEY_GEN
    {
        byte   der[4096];
        byte   pem[4096];
        word32 derSz = 0;
        word32 pemSz = 0;
        RsaKey derIn;
        RsaKey genKey;
        FILE* keyFile;
        FILE* pemFile;

        InitRsaKey(&genKey, 0);
        ret = MakeRsaKey(&genKey, 1024, 65537, &rng);
        if (ret != 0)
            return -301;

        derSz = RsaKeyToDer(&genKey, der, sizeof(der));
        if (derSz < 0)
            return -302;

        keyFile = fopen("./key.der", "wb");
        if (!keyFile)
            return -303;
        ret = fwrite(der, derSz, 1, keyFile);
        fclose(keyFile);

        pemSz = DerToPem(der, derSz, pem, sizeof(pem), PRIVATEKEY_TYPE);
        if (pemSz < 0)
            return -304;

        pemFile = fopen("./key.pem", "wb");
        if (!pemFile) 
            return -305;
        ret = fwrite(pem, pemSz, 1, pemFile);
        fclose(pemFile);

        InitRsaKey(&derIn, 0);
        idx = 0;
        ret = RsaPrivateKeyDecode(der, &idx, &derIn, derSz);
        if (ret != 0)
            return -306;

        FreeRsaKey(&derIn);
        FreeRsaKey(&genKey);
    }
#endif /* CYASSL_KEY_GEN */


#ifdef CYASSL_CERT_GEN
    /* self signed */
    {
        Cert        myCert;
        byte        derCert[4096];
        byte        pem[4096];
        FILE*       derFile;
        FILE*       pemFile;
        int         certSz;
        int         pemSz;
#ifdef CYASSL_TEST_CERT
        DecodedCert decode;
#endif

        InitCert(&myCert);

        strncpy(myCert.subject.country, "US", CTC_NAME_SIZE);
        strncpy(myCert.subject.state, "OR", CTC_NAME_SIZE);
        strncpy(myCert.subject.locality, "Portland", CTC_NAME_SIZE);
        strncpy(myCert.subject.org, "yaSSL", CTC_NAME_SIZE);
        strncpy(myCert.subject.unit, "Development", CTC_NAME_SIZE);
        strncpy(myCert.subject.commonName, "www.yassl.com", CTC_NAME_SIZE);
        strncpy(myCert.subject.email, "info@yassl.com", CTC_NAME_SIZE);
        myCert.isCA    = 1;
        myCert.sigType = CTC_SHA256wRSA;

        certSz = MakeSelfCert(&myCert, derCert, sizeof(derCert), &key, &rng); 
        if (certSz < 0)
            return -401;

#ifdef CYASSL_TEST_CERT
        InitDecodedCert(&decode, derCert, certSz, 0);
        ret = ParseCert(&decode, CERT_TYPE, NO_VERIFY, 0);
        if (ret != 0)
            return -402;
        FreeDecodedCert(&decode);
#endif
        derFile = fopen("./cert.der", "wb");
        if (!derFile)
            return -403;
        ret = fwrite(derCert, certSz, 1, derFile);
        fclose(derFile);

        pemSz = DerToPem(derCert, certSz, pem, sizeof(pem), CERT_TYPE);
        if (pemSz < 0)
            return -404;

        pemFile = fopen("./cert.pem", "wb");
        if (!pemFile)
            return -405;
        ret = fwrite(pem, pemSz, 1, pemFile);
        fclose(pemFile);


    }
    /* CA style */
    {
        RsaKey      caKey;
        Cert        myCert;
        byte        derCert[4096];
        byte        pem[4096];
        FILE*       derFile;
        FILE*       pemFile;
        int         certSz;
        int         pemSz;
        byte        tmp[2048];
        size_t      bytes;
        word32      idx = 0;
#ifdef CYASSL_TEST_CERT
        DecodedCert decode;
#endif

        FILE*  file = fopen(caKeyFile, "rb");

        if (!file)
            return -412;

        bytes = fread(tmp, 1, sizeof(tmp), file);
  
        InitRsaKey(&caKey, 0);  
        ret = RsaPrivateKeyDecode(tmp, &idx, &caKey, (word32)bytes);
        if (ret != 0) return -413;

        InitCert(&myCert);

        strncpy(myCert.subject.country, "US", CTC_NAME_SIZE);
        strncpy(myCert.subject.state, "OR", CTC_NAME_SIZE);
        strncpy(myCert.subject.locality, "Portland", CTC_NAME_SIZE);
        strncpy(myCert.subject.org, "yaSSL", CTC_NAME_SIZE);
        strncpy(myCert.subject.unit, "Development", CTC_NAME_SIZE);
        strncpy(myCert.subject.commonName, "www.yassl.com", CTC_NAME_SIZE);
        strncpy(myCert.subject.email, "info@yassl.com", CTC_NAME_SIZE);

        ret = SetIssuer(&myCert, caCertFile);
        if (ret < 0)
            return -405;

        certSz = MakeCert(&myCert, derCert, sizeof(derCert), &key, &rng); 
        if (certSz < 0)
            return -407;

        certSz = SignCert(&myCert, derCert, sizeof(derCert), &caKey, &rng);
        if (certSz < 0)
            return -408;


#ifdef CYASSL_TEST_CERT
        InitDecodedCert(&decode, derCert, certSz, 0);
        ret = ParseCert(&decode, CERT_TYPE, NO_VERIFY, 0);
        if (ret != 0)
            return -409;
        FreeDecodedCert(&decode);
#endif

        derFile = fopen("./othercert.der", "wb");
        if (!derFile)
            return -410;
        ret = fwrite(derCert, certSz, 1, derFile);
        fclose(derFile);

        pemSz = DerToPem(derCert, certSz, pem, sizeof(pem), CERT_TYPE);
        if (pemSz < 0)
            return -411;

        pemFile = fopen("./othercert.pem", "wb");
        if (!pemFile)
            return -412;
        ret = fwrite(pem, pemSz, 1, pemFile);
        fclose(pemFile);
    }
#ifdef HAVE_NTRU
    {
        RsaKey      caKey;
        Cert        myCert;
        byte        derCert[4096];
        byte        pem[4096];
        FILE*       derFile;
        FILE*       pemFile;
        FILE*       caFile;
        FILE*       ntruPrivFile;
        int         certSz;
        int         pemSz;
        byte        tmp[2048];
        size_t      bytes;
        word32      idx = 0;
#ifdef CYASSL_TEST_CERT
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
        word32 rc = crypto_drbg_instantiate(112, pers_str, sizeof(pers_str),
                                            GetEntropy, &drbg);
        if (rc != DRBG_OK)
            return -450;

        rc = crypto_ntru_encrypt_keygen(drbg, NTRU_EES401EP2, &public_key_len,
                                        NULL, &private_key_len, NULL);
        if (rc != NTRU_OK)
            return -451;

        rc = crypto_ntru_encrypt_keygen(drbg, NTRU_EES401EP2, &public_key_len,
                                     public_key, &private_key_len, private_key);
        crypto_drbg_uninstantiate(drbg);

        if (rc != NTRU_OK)
            return -452;

        caFile = fopen(caKeyFile, "rb");

        if (!caFile)
            return -453;

        bytes = fread(tmp, 1, sizeof(tmp), caFile);
        fclose(caFile);
  
        InitRsaKey(&caKey, 0);  
        ret = RsaPrivateKeyDecode(tmp, &idx, &caKey, (word32)bytes);
        if (ret != 0) return -454;

        InitCert(&myCert);

        strncpy(myCert.subject.country, "US", CTC_NAME_SIZE);
        strncpy(myCert.subject.state, "OR", CTC_NAME_SIZE);
        strncpy(myCert.subject.locality, "Portland", CTC_NAME_SIZE);
        strncpy(myCert.subject.org, "yaSSL", CTC_NAME_SIZE);
        strncpy(myCert.subject.unit, "Development", CTC_NAME_SIZE);
        strncpy(myCert.subject.commonName, "www.yassl.com", CTC_NAME_SIZE);
        strncpy(myCert.subject.email, "info@yassl.com", CTC_NAME_SIZE);

        ret = SetIssuer(&myCert, caCertFile);
        if (ret < 0)
            return -455;

        certSz = MakeNtruCert(&myCert, derCert, sizeof(derCert), public_key,
                              public_key_len, &rng); 
        if (certSz < 0)
            return -456;

        certSz = SignCert(&myCert, derCert, sizeof(derCert), &caKey, &rng);
        if (certSz < 0)
            return -457;


#ifdef CYASSL_TEST_CERT
        InitDecodedCert(&decode, derCert, certSz, 0);
        ret = ParseCert(&decode, CERT_TYPE, NO_VERIFY, 0);
        if (ret != 0)
            return -458;
        FreeDecodedCert(&decode);
#endif
        derFile = fopen("./ntru-cert.der", "wb");
        if (!derFile)
            return -459;
        ret = fwrite(derCert, certSz, 1, derFile);
        fclose(derFile);

        pemSz = DerToPem(derCert, certSz, pem, sizeof(pem), CERT_TYPE);
        if (pemSz < 0)
            return -460;

        pemFile = fopen("./ntru-cert.pem", "wb");
        if (!pemFile)
            return -461;
        ret = fwrite(pem, pemSz, 1, pemFile);
        fclose(pemFile);

        ntruPrivFile = fopen("./ntru-key.raw", "wb");
        if (!ntruPrivFile)
            return -462;
        ret = fwrite(private_key, private_key_len, 1, ntruPrivFile);
        fclose(ntruPrivFile);
    }
#endif /* HAVE_NTRU */
#endif /* CYASSL_CERT_GEN */

    FreeRsaKey(&key);

    return 0;
}


static const char* dhKey = "./certs/dh2048.der";

#ifndef NO_DH

int dh_test()
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
    FILE*  file = fopen(dhKey, "rb");

    if (!file)
        return -50;

    bytes = (word32) fread(tmp, 1, sizeof(tmp), file);

    InitDhKey(&key);  
    InitDhKey(&key2);  
    ret = DhKeyDecode(tmp, &idx, &key, bytes);
    if (ret != 0)
        return -51;

    idx = 0;
    ret = DhKeyDecode(tmp, &idx, &key2, bytes);
    if (ret != 0)
        return -52;

    ret = InitRng(&rng);
    if (ret != 0)
        return -53;
    
    ret = DhGenerateKeyPair(&key, &rng, priv, &privSz, pub, &pubSz);
    ret = DhGenerateKeyPair(&key2, &rng, priv2, &privSz2, pub2, &pubSz2);
    if (ret != 0)
        return -54;

    ret = DhAgree(&key, agree, &agreeSz, priv, privSz, pub2, pubSz2);
    ret = DhAgree(&key2, agree2, &agreeSz2, priv2, privSz2, pub, pubSz);
    if (ret != 0)
        return -55;

    if (memcmp(agree, agree2, agreeSz))
        return -56;

    FreeDhKey(&key);
    FreeDhKey(&key2);
    fclose(file);

    return 0;
}

#endif /* NO_DH */


static const char* dsaKey = "./certs/dsa2048.der";

#ifndef NO_DSA

int dsa_test()
{
    int    ret, answer;
    word32 bytes;
    word32 idx = 0;
    byte   tmp[1024];
    DsaKey key;
    RNG    rng;
    FILE*  file = fopen(dsaKey, "rb");
    Sha    sha;
    byte   hash[SHA_DIGEST_SIZE];
    byte   signature[40];

    if (!file)
        return -60;

    bytes = (word32) fread(tmp, 1, sizeof(tmp), file);
  
    InitSha(&sha);
    ShaUpdate(&sha, tmp, bytes);
    ShaFinal(&sha, hash);

    InitDsaKey(&key);
    ret = DsaPrivateKeyDecode(tmp, &idx, &key, bytes);
    if (ret != 0) return -61;

    ret = InitRng(&rng);
    if (ret != 0) return -62;

    ret = DsaSign(hash, signature, &key, &rng);
    if (ret != 0) return -63;

    ret = DsaVerify(hash, signature, &key, &answer);
    if (ret != 0) return -64;
    if (answer != 1) return -65;
    
    FreeDsaKey(&key);
    fclose(file);
    
    return 0;
}

#endif /* NO_DSA */


#ifdef OPENSSL_EXTRA

int openssl_test()
{
    EVP_MD_CTX md_ctx;
    testVector a, b, c, d, e, f;
    byte       hash[SHA_DIGEST_SIZE*4];  /* max size */

    (void)e;
    (void)f;

    a.input  = "1234567890123456789012345678901234567890123456789012345678"
               "9012345678901234567890";
    a.output = "\x57\xed\xf4\xa2\x2b\xe3\xc9\x55\xac\x49\xda\x2e\x21\x07\xb6"
               "\x7a";
    a.inLen  = strlen(a.input);
    a.outLen = strlen(a.output);

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_md5());

    EVP_DigestUpdate(&md_ctx, a.input, a.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (memcmp(hash, a.output, MD5_DIGEST_SIZE) != 0)
        return -71;

    b.input  = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
               "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
               "aaaaaaaaaa";
    b.output = "\xAD\x5B\x3F\xDB\xCB\x52\x67\x78\xC2\x83\x9D\x2F\x15\x1E\xA7"
               "\x53\x99\x5E\x26\xA0";
    b.inLen  = strlen(b.input);
    b.outLen = strlen(b.output);

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_sha1());

    EVP_DigestUpdate(&md_ctx, b.input, b.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (memcmp(hash, b.output, SHA_DIGEST_SIZE) != 0)
        return -72;


    d.input  = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    d.output = "\x24\x8D\x6A\x61\xD2\x06\x38\xB8\xE5\xC0\x26\x93\x0C\x3E\x60"
               "\x39\xA3\x3C\xE4\x59\x64\xFF\x21\x67\xF6\xEC\xED\xD4\x19\xDB"
               "\x06\xC1";
    d.inLen  = strlen(d.input);
    d.outLen = strlen(d.output);

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_sha256());

    EVP_DigestUpdate(&md_ctx, d.input, d.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (memcmp(hash, d.output, SHA256_DIGEST_SIZE) != 0)
        return -78;

#ifdef CYASSL_SHA384

    e.input  = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhi"
               "jklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    e.output = "\x09\x33\x0c\x33\xf7\x11\x47\xe8\x3d\x19\x2f\xc7\x82\xcd\x1b"
               "\x47\x53\x11\x1b\x17\x3b\x3b\x05\xd2\x2f\xa0\x80\x86\xe3\xb0"
               "\xf7\x12\xfc\xc7\xc7\x1a\x55\x7e\x2d\xb9\x66\xc3\xe9\xfa\x91"
               "\x74\x60\x39";    
    e.inLen  = strlen(e.input);
    e.outLen = strlen(e.output);

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_sha384());

    EVP_DigestUpdate(&md_ctx, e.input, e.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (memcmp(hash, e.output, SHA384_DIGEST_SIZE) != 0)
        return -79;

#endif /* CYASSL_SHA384 */


#ifdef CYASSL_SHA512

    f.input  = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhi"
               "jklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    f.output = "\x8e\x95\x9b\x75\xda\xe3\x13\xda\x8c\xf4\xf7\x28\x14\xfc\x14"
               "\x3f\x8f\x77\x79\xc6\xeb\x9f\x7f\xa1\x72\x99\xae\xad\xb6\x88"
               "\x90\x18\x50\x1d\x28\x9e\x49\x00\xf7\xe4\x33\x1b\x99\xde\xc4"
               "\xb5\x43\x3a\xc7\xd3\x29\xee\xb6\xdd\x26\x54\x5e\x96\xe5\x5b"
               "\x87\x4b\xe9\x09"; 
    f.inLen  = strlen(f.input);
    f.outLen = strlen(f.output);

    EVP_MD_CTX_init(&md_ctx);
    EVP_DigestInit(&md_ctx, EVP_sha512());

    EVP_DigestUpdate(&md_ctx, f.input, f.inLen);
    EVP_DigestFinal(&md_ctx, hash, 0);

    if (memcmp(hash, f.output, SHA512_DIGEST_SIZE) != 0)
        return -80;

#endif /* CYASSL_SHA512 */


    if (RAND_bytes(hash, sizeof(hash)) != 1)
        return -73;
            
    c.input  = "what do ya want for nothing?";
    c.output = "\x75\x0c\x78\x3e\x6a\xb0\xb5\x03\xea\xa8\x6e\x31\x0a\x5d\xb7"
               "\x38";
    c.inLen  = strlen(c.input);
    c.outLen = strlen(c.output);

    HMAC(EVP_md5(), "Jefe", 4, (byte*)c.input, (int)c.inLen, hash, 0);

    if (memcmp(hash, c.output, MD5_DIGEST_SIZE) != 0)
        return -74;

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

    return 0;
}

#endif /* OPENSSL_EXTRA */


#ifndef NO_PWDBASED

int pkcs12_test()
{
    const byte passwd[] = { 0x00, 0x73, 0x00, 0x6d, 0x00, 0x65, 0x00, 0x67,
                            0x00, 0x00 }; 
    const byte salt[] =   { 0x0a, 0x58, 0xCF, 0x64, 0x53, 0x0d, 0x82, 0x3f };

    const byte passwd2[] = { 0x00, 0x71, 0x00, 0x75, 0x00, 0x65, 0x00, 0x65,
                             0x00, 0x67, 0x00, 0x00 }; 
    const byte salt2[] =   { 0x16, 0x82, 0xC0, 0xfC, 0x5b, 0x3f, 0x7e, 0xc5 };
    byte  derived[64];

    const byte verify[] = {
        0x8A, 0xAA, 0xE6, 0x29, 0x7B, 0x6C, 0xB0, 0x46,
        0x42, 0xAB, 0x5B, 0x07, 0x78, 0x51, 0x28, 0x4E,
        0xB7, 0x12, 0x8F, 0x1A, 0x2A, 0x7F, 0xBC, 0xA3
    };

    const byte verify2[] = {
        0x48, 0x3D, 0xD6, 0xE9, 0x19, 0xD7, 0xDE, 0x2E,
        0x8E, 0x64, 0x8B, 0xA8, 0xF8, 0x62, 0xF3, 0xFB,
        0xFB, 0xDC, 0x2B, 0xCB, 0x2C, 0x02, 0x95, 0x7F
    };

    int id         =  1;
    int kLen       = 24;
    int iterations =  1;
    int ret = PKCS12_PBKDF(derived, passwd, sizeof(passwd), salt, 8, iterations,
                           kLen, SHA, id);

    if ( (ret = memcmp(derived, verify, kLen)) != 0)
        return -103;

    iterations = 1000;
    ret = PKCS12_PBKDF(derived, passwd2, sizeof(passwd2), salt2, 8, iterations, 
                       kLen, SHA, id);
    if ( (ret = memcmp(derived, verify2, 24)) != 0)
        return -104;

    return 0;
}


int pbkdf2_test()
{
    char passwd[] = "password";
    const byte salt[] = { 0x78, 0x57, 0x8E, 0x5a, 0x5d, 0x63, 0xcb, 0x06 };
    int   iterations = 2048;
    int   kLen = 24;
    byte  derived[64];

    const byte verify[] = {
        0xBF, 0xDE, 0x6B, 0xE9, 0x4D, 0xF7, 0xE1, 0x1D, 0xD4, 0x09, 0xBC, 0xE2,
        0x0A, 0x02, 0x55, 0xEC, 0x32, 0x7C, 0xB9, 0x36, 0xFF, 0xE9, 0x36, 0x43

    };

    PBKDF2(derived, (byte*)passwd, strlen(passwd), salt, 8, iterations, kLen,
           SHA);

    if (memcmp(derived, verify, sizeof(verify)) != 0)
        return -102;

    return 0;
}


int pbkdf1_test()
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

    PBKDF1(derived, (byte*)passwd, strlen(passwd), salt, 8, iterations, kLen,
           SHA);

    if (memcmp(derived, verify, sizeof(verify)) != 0)
        return -101;

    return 0;
}


int pwdbased_test()
{
   int ret =  pbkdf1_test();
   ret += pbkdf2_test();

   return ret + pkcs12_test();
}

#endif /* NO_PWDBASED */


#ifdef HAVE_ECC

int ecc_test()
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

    ret = InitRng(&rng);
    if (ret != 0)
        return -1001;

    ecc_init(&userA);
    ecc_init(&userB);
    ecc_init(&pubKey);

    ret = ecc_make_key(&rng, 32, &userA);
    ret = ecc_make_key(&rng, 32, &userB);

    if (ret != 0)
        return -1002;

    x = sizeof(sharedA);
    ret = ecc_shared_secret(&userA, &userB, sharedA, &x);
   
    y = sizeof(sharedB);
    ret = ecc_shared_secret(&userB, &userA, sharedB, &y);
    
    if (ret != 0)
        return -1003;

    if (y != x)
        return -1004;

    if (memcmp(sharedA, sharedB, x))
        return -1005;

    x = sizeof(exportBuf);
    ret = ecc_export_x963(&userA, exportBuf, &x);
    if (ret != 0)
        return -1006;

    ret = ecc_import_x963(exportBuf, x, &pubKey);

    if (ret != 0) 
        return -1007;

    y = sizeof(sharedB);
    ret = ecc_shared_secret(&userB, &pubKey, sharedB, &y);
   
    if (ret != 0)
        return -1008;

    if (memcmp(sharedA, sharedB, y))
        return -1010;

    /* test DSA sign hash */
    for (i = 0; i < sizeof(digest); i++)
        digest[i] = i;

    x = sizeof(sig);
    ret = ecc_sign_hash(digest, sizeof(digest), sig, &x, &rng, &userA);
    
    verify = 0;
    ret = ecc_verify_hash(sig, x, digest, sizeof(digest), &verify, &userA);

    if (ret != 0)
        return -1011;

    if (verify != 1)
        return -1012;

    ecc_free(&pubKey);
    ecc_free(&userB);
    ecc_free(&userA);

    return 0;
}

#endif /* HAVE_ECC */
