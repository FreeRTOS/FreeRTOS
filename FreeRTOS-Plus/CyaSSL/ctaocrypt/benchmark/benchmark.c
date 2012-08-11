/* benchmark.c
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

/* CTaoCrypt benchmark */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <string.h>
#include <stdio.h>

#include <cyassl/ctaocrypt/des3.h>
#include <cyassl/ctaocrypt/arc4.h>
#include <cyassl/ctaocrypt/hc128.h>
#include <cyassl/ctaocrypt/rabbit.h>
#include <cyassl/ctaocrypt/aes.h>
#include <cyassl/ctaocrypt/md5.h>
#include <cyassl/ctaocrypt/sha.h>
#include <cyassl/ctaocrypt/sha256.h>
#include <cyassl/ctaocrypt/sha512.h>
#include <cyassl/ctaocrypt/rsa.h>
#include <cyassl/ctaocrypt/asn.h>
#include <cyassl/ctaocrypt/ripemd.h>
#include <cyassl/ctaocrypt/ecc.h>

#include <cyassl/ctaocrypt/dh.h>

#ifdef _MSC_VER
    /* 4996 warning to use MS extensions e.g., strcpy_s instead of strncpy */
    #pragma warning(disable: 4996)
#endif

void bench_des();
void bench_arc4();
void bench_hc128();
void bench_rabbit();
void bench_aes(int);

void bench_md5();
void bench_sha();
void bench_sha256();
void bench_sha512();
void bench_ripemd();

void bench_rsa();
void bench_rsaKeyGen();
void bench_dh();
#ifdef HAVE_ECC
void bench_eccKeyGen();
void bench_eccKeyAgree();
#endif

double current_time();



int main(int argc, char** argv)
{
#ifndef NO_AES
    bench_aes(0);
    bench_aes(1);
#endif
    bench_arc4();
#ifdef HAVE_HC128
    bench_hc128();
#endif
#ifndef NO_RABBIT
    bench_rabbit();
#endif
#ifndef NO_DES3
    bench_des();
#endif
    
    printf("\n");

    bench_md5();
    bench_sha();
#ifndef NO_SHA256
    bench_sha256();
#endif
#ifdef CYASSL_SHA512
    bench_sha512();
#endif
#ifdef CYASSL_RIPEMD
    bench_ripemd();
#endif

    printf("\n");
    
    bench_rsa();

#ifndef NO_DH
    bench_dh();
#endif

#ifdef CYASSL_KEY_GEN
    bench_rsaKeyGen();
#endif

#ifdef HAVE_ECC 
    bench_eccKeyGen();
    bench_eccKeyAgree();
#endif

    return 0;
}

const int megs  = 5;     /* how many megs to test (en/de)cryption */
const int times = 100;   /* public key iterations */

const byte key[] = 
{
    0x01,0x23,0x45,0x67,0x89,0xab,0xcd,0xef,
    0xfe,0xde,0xba,0x98,0x76,0x54,0x32,0x10,
    0x89,0xab,0xcd,0xef,0x01,0x23,0x45,0x67
};

const byte iv[] = 
{
    0x12,0x34,0x56,0x78,0x90,0xab,0xcd,0xef,
    0x01,0x01,0x01,0x01,0x01,0x01,0x01,0x01,
    0x11,0x21,0x31,0x41,0x51,0x61,0x71,0x81
    
};


byte plain [1024*1024];
byte cipher[1024*1024];


#ifndef NO_AES
void bench_aes(int show)
{
    Aes    enc;
    double start, total, persec;
    int    i;

    AesSetKey(&enc, key, 16, iv, AES_ENCRYPTION);
    start = current_time();

    for(i = 0; i < megs; i++)
        AesCbcEncrypt(&enc, plain, cipher, sizeof(plain));

    total = current_time() - start;

    persec = 1 / total * megs;

    if (show)
        printf("AES      %d megs took %5.3f seconds, %6.2f MB/s\n", megs, total,
                                                                    persec);
}
#endif


#ifndef NO_DES3
void bench_des()
{
    Des3   enc;
    double start, total, persec;
    int    i;

    Des3_SetKey(&enc, key, iv, DES_ENCRYPTION);
    start = current_time();

    for(i = 0; i < megs; i++)
        Des3_CbcEncrypt(&enc, plain, cipher, sizeof(plain));

    total = current_time() - start;

    persec = 1 / total * megs;

    printf("3DES     %d megs took %5.3f seconds, %6.2f MB/s\n", megs, total,
                                                             persec);
}
#endif


void bench_arc4()
{
    Arc4   enc;
    double start, total, persec;
    int    i;
    
    Arc4SetKey(&enc, key, 16);
    start = current_time();

    for(i = 0; i < megs; i++)
        Arc4Process(&enc, cipher, plain, sizeof(plain));

    total = current_time() - start;
    persec = 1 / total * megs;

    printf("ARC4     %d megs took %5.3f seconds, %6.2f MB/s\n", megs, total,
                                                             persec);
}


#ifdef HAVE_HC128
void bench_hc128()
{
    HC128  enc;
    double start, total, persec;
    int    i;
    
    Hc128_SetKey(&enc, key, iv);
    start = current_time();

    for(i = 0; i < megs; i++)
        Hc128_Process(&enc, cipher, plain, sizeof(plain));

    total = current_time() - start;
    persec = 1 / total * megs;

    printf("HC128    %d megs took %5.3f seconds, %6.2f MB/s\n", megs, total,
                                                             persec);
}
#endif /* HAVE_HC128 */


#ifndef NO_RABBIT
void bench_rabbit()
{
    Rabbit  enc;
    double start, total, persec;
    int    i;
    
    RabbitSetKey(&enc, key, iv);
    start = current_time();

    for(i = 0; i < megs; i++)
        RabbitProcess(&enc, cipher, plain, sizeof(plain));

    total = current_time() - start;
    persec = 1 / total * megs;

    printf("RABBIT   %d megs took %5.3f seconds, %6.2f MB/s\n", megs, total,
                                                             persec);
}
#endif /* NO_RABBIT */


void bench_md5()
{
    Md5    hash;
    byte   digest[MD5_DIGEST_SIZE];
    double start, total, persec;
    int    i;

    InitMd5(&hash);
    start = current_time();

    for(i = 0; i < megs; i++)
        Md5Update(&hash, plain, sizeof(plain));
   
    Md5Final(&hash, digest);

    total = current_time() - start;
    persec = 1 / total * megs;

    printf("MD5      %d megs took %5.3f seconds, %6.2f MB/s\n", megs, total,
                                                             persec);
}


void bench_sha()
{
    Sha    hash;
    byte   digest[SHA_DIGEST_SIZE];
    double start, total, persec;
    int    i;
        
    InitSha(&hash);
    start = current_time();
    
    for(i = 0; i < megs; i++)
        ShaUpdate(&hash, plain, sizeof(plain));
   
    ShaFinal(&hash, digest);

    total = current_time() - start;
    persec = 1 / total * megs;

    printf("SHA      %d megs took %5.3f seconds, %6.2f MB/s\n", megs, total,
                                                             persec);
}


#ifndef NO_SHA256
void bench_sha256()
{
    Sha256 hash;
    byte   digest[SHA256_DIGEST_SIZE];
    double start, total, persec;
    int    i;
        
    InitSha256(&hash);
    start = current_time();
    
    for(i = 0; i < megs; i++)
        Sha256Update(&hash, plain, sizeof(plain));
   
    Sha256Final(&hash, digest);

    total = current_time() - start;
    persec = 1 / total * megs;

    printf("SHA-256  %d megs took %5.3f seconds, %6.2f MB/s\n", megs, total,
                                                             persec);
}
#endif

#ifdef CYASSL_SHA512
void bench_sha512()
{
    Sha512 hash;
    byte   digest[SHA512_DIGEST_SIZE];
    double start, total, persec;
    int    i;
        
    InitSha512(&hash);
    start = current_time();
    
    for(i = 0; i < megs; i++)
        Sha512Update(&hash, plain, sizeof(plain));
   
    Sha512Final(&hash, digest);

    total = current_time() - start;
    persec = 1 / total * megs;

    printf("SHA-512  %d megs took %5.3f seconds, %6.2f MB/s\n", megs, total,
                                                             persec);
}
#endif

#ifdef CYASSL_RIPEMD
void bench_ripemd()
{
    RipeMd hash;
    byte   digest[RIPEMD_DIGEST_SIZE];
    double start, total, persec;
    int    i;
        
    InitRipeMd(&hash);
    start = current_time();
    
    for(i = 0; i < megs; i++)
        RipeMdUpdate(&hash, plain, sizeof(plain));
   
    RipeMdFinal(&hash, digest);

    total = current_time() - start;
    persec = 1 / total * megs;

    printf("RIPEMD   %d megs took %5.3f seconds, %6.2f MB/s\n", megs, total,
                                                             persec);
}
#endif


RNG rng;

void bench_rsa()
{
    int    i;
    byte   tmp[4096];
    size_t bytes;
    word32 idx = 0;

    byte      message[] = "Everyone gets Friday off.";
    byte      cipher[512];  /* for up to 4096 bit */
    byte*     output;
    const int len = (int)strlen((char*)message);
    double    start, total, each, milliEach;
    
    RsaKey key;
    FILE*  file = fopen("./certs/rsa2048.der", "rb");

    if (!file) {
        printf("can't find ./certs/rsa2048.der, "
               "Please run from CyaSSL home dir\n");
        return;
    }

    InitRng(&rng);
    bytes = fread(tmp, 1, sizeof(tmp), file);
    InitRsaKey(&key, 0);
    bytes = RsaPrivateKeyDecode(tmp, &idx, &key, (word32)bytes);
    
    start = current_time();

    for (i = 0; i < times; i++)
        bytes = RsaPublicEncrypt(message,len,cipher,sizeof(cipher), &key, &rng);

    total = current_time() - start;
    each  = total / times;   /* per second   */
    milliEach = each * 1000; /* milliseconds */

    printf("RSA 2048 encryption took %6.2f milliseconds, avg over %d" 
           " iterations\n", milliEach, times);

    start = current_time();

    for (i = 0; i < times; i++)
        RsaPrivateDecryptInline(cipher, (word32)bytes, &output, &key);

    total = current_time() - start;
    each  = total / times;   /* per second   */
    milliEach = each * 1000; /* milliseconds */

    printf("RSA 2048 decryption took %6.2f milliseconds, avg over %d" 
           " iterations\n", milliEach, times);

    fclose(file);
    FreeRsaKey(&key);
}


#ifndef NO_DH
void bench_dh()
{
    int    i;
    byte   tmp[1024];
    size_t bytes;
    word32 idx = 0, pubSz, privSz, pubSz2, privSz2, agreeSz;

    byte   pub[256];    /* for 2048 bit */
    byte   priv[256];   /* for 2048 bit */
    byte   pub2[256];   /* for 2048 bit */
    byte   priv2[256];  /* for 2048 bit */
    byte   agree[256];  /* for 2048 bit */
    
    double start, total, each, milliEach;
    DhKey  key;
    FILE*  file = fopen("./certs/dh2048.der", "rb");

    if (!file) {
        printf("can't find ./certs/dh2048.der, "
               "Please run from CyaSSL home dir\n");
        return;
    }

    bytes = fread(tmp, 1, sizeof(tmp), file);
    InitDhKey(&key);
    bytes = DhKeyDecode(tmp, &idx, &key, (word32)bytes);

    start = current_time();

    for (i = 0; i < times; i++)
        DhGenerateKeyPair(&key, &rng, priv, &privSz, pub, &pubSz);

    total = current_time() - start;
    each  = total / times;   /* per second   */
    milliEach = each * 1000; /* milliseconds */

    printf("DH  2048 key generation  %6.2f milliseconds, avg over %d" 
           " iterations\n", milliEach, times);

    DhGenerateKeyPair(&key, &rng, priv2, &privSz2, pub2, &pubSz2);
    start = current_time();

    for (i = 0; i < times; i++)
        DhAgree(&key, agree, &agreeSz, priv, privSz, pub2, pubSz2);

    total = current_time() - start;
    each  = total / times;   /* per second   */
    milliEach = each * 1000; /* milliseconds */

    printf("DH  2048 key agreement   %6.2f milliseconds, avg over %d" 
           " iterations\n", milliEach, times);

    fclose(file);
    FreeDhKey(&key);
}
#endif

#ifdef CYASSL_KEY_GEN
void bench_rsaKeyGen()
{
    RsaKey genKey;
    double start, total, each, milliEach;
    int    i;
    const int genTimes = 5;
  
    /* 1024 bit */ 
    start = current_time();

    for(i = 0; i < genTimes; i++) {
        InitRsaKey(&genKey, 0); 
        MakeRsaKey(&genKey, 1024, 65537, &rng);
        FreeRsaKey(&genKey);
    }

    total = current_time() - start;
    each  = total / genTimes;  /* per second  */
    milliEach = each * 1000;   /* millisconds */
    printf("\n");
    printf("RSA 1024 key generation  %6.2f milliseconds, avg over %d" 
           " iterations\n", milliEach, genTimes);

    /* 2048 bit */
    start = current_time();

    for(i = 0; i < genTimes; i++) {
        InitRsaKey(&genKey, 0); 
        MakeRsaKey(&genKey, 2048, 65537, &rng);
        FreeRsaKey(&genKey);
    }

    total = current_time() - start;
    each  = total / genTimes;  /* per second  */
    milliEach = each * 1000;   /* millisconds */
    printf("RSA 2048 key generation  %6.2f milliseconds, avg over %d" 
           " iterations\n", milliEach, genTimes);
}
#endif /* CYASSL_KEY_GEN */

#ifdef HAVE_ECC 
void bench_eccKeyGen()
{
    ecc_key genKey;
    double start, total, each, milliEach;
    int    i;
    const int genTimes = 5;
  
    /* 256 bit */ 
    start = current_time();

    for(i = 0; i < genTimes; i++) {
        int ret = ecc_make_key(&rng, 32, &genKey);
        ecc_free(&genKey);
    }

    total = current_time() - start;
    each  = total / genTimes;  /* per second  */
    milliEach = each * 1000;   /* millisconds */
    printf("\n");
    printf("ECC  256 key generation  %6.2f milliseconds, avg over %d" 
           " iterations\n", milliEach, genTimes);
}


void bench_eccKeyAgree()
{
    ecc_key genKey, genKey2;
    double start, total, each, milliEach;
    int    i;
    const int agreeTimes = 5;
    byte   shared[1024];
    byte   sig[1024];
    byte   digest[32];
    word32 x;
  
    ecc_make_key(&rng, 32, &genKey);
    ecc_make_key(&rng, 32, &genKey2);

    /* 256 bit */ 
    start = current_time();

    for(i = 0; i < agreeTimes; i++) {
        x = sizeof(shared);
        ecc_shared_secret(&genKey, &genKey2, shared, &x);
    }

    total = current_time() - start;
    each  = total / agreeTimes;  /* per second  */
    milliEach = each * 1000;   /* millisconds */
    printf("EC-DHE   key agreement   %6.2f milliseconds, avg over %d" 
           " iterations\n", milliEach, agreeTimes);

    /* make dummy digest */
    for (i = 0; i < sizeof(digest); i++)
        digest[i] = i;


    start = current_time();

    for(i = 0; i < agreeTimes; i++) {
        x = sizeof(sig);
        ecc_sign_hash(digest, sizeof(digest), sig, &x, &rng, &genKey);
    }

    total = current_time() - start;
    each  = total / agreeTimes;  /* per second  */
    milliEach = each * 1000;   /* millisconds */
    printf("EC-DSA   sign time       %6.2f milliseconds, avg over %d" 
           " iterations\n", milliEach, agreeTimes);

    ecc_free(&genKey2);
    ecc_free(&genKey);
}
#endif /* HAVE_ECC */


#ifdef _WIN32

    #define WIN32_LEAN_AND_MEAN
    #include <windows.h>

    double current_time()
    {
        static int init = 0;
        static LARGE_INTEGER freq;
    
        LARGE_INTEGER count;

        if (!init) {
            QueryPerformanceFrequency(&freq);
            init = 1;
        }

        QueryPerformanceCounter(&count);

        return (double)count.QuadPart / freq.QuadPart;
    }

#else

    #include <sys/time.h>

    double current_time()
    {
        struct timeval tv;
        gettimeofday(&tv, 0);

        return (double)tv.tv_sec + (double)tv.tv_usec / 1000000;
    }

#endif /* _WIN32 */

