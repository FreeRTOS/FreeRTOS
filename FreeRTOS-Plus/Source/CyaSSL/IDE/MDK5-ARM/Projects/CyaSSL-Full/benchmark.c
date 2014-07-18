/* benchmark.c
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

/* CTaoCrypt benchmark */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <cyassl/ctaocrypt/settings.h>

#include <string.h>
#include <stdio.h>

#include <cyassl/ctaocrypt/des3.h>
#include <cyassl/ctaocrypt/arc4.h>
#include <cyassl/ctaocrypt/hc128.h>
#include <cyassl/ctaocrypt/rabbit.h>
#include <cyassl/ctaocrypt/aes.h>
#include <cyassl/ctaocrypt/camellia.h>
#include <cyassl/ctaocrypt/md5.h>
#include <cyassl/ctaocrypt/sha.h>
#include <cyassl/ctaocrypt/sha256.h>
#include <cyassl/ctaocrypt/sha512.h>
#include <cyassl/ctaocrypt/rsa.h>
#include <cyassl/ctaocrypt/asn.h>
#include <cyassl/ctaocrypt/ripemd.h>
#include <cyassl/ctaocrypt/ecc.h>

#include <cyassl/ctaocrypt/dh.h>
#ifdef HAVE_CAVIUM
    #include "cavium_sysdep.h"
    #include "cavium_common.h"
    #include "cavium_ioctl.h"
#endif

#if defined(CYASSL_MDK_ARM)
    extern FILE * CyaSSL_fopen(const char *fname, const char *mode) ;
    #define fopen CyaSSL_fopen
#endif

#if defined(USE_CERT_BUFFERS_1024) || defined(USE_CERT_BUFFERS_2048)
    /* include test cert and key buffers for use with NO_FILESYSTEM */
    #if defined(CYASSL_MDK_ARM)
        #include "cert_data.h" /* use certs_test.c for initial data, 
                                      so other commands can share the data. */
    #else
        #include <cyassl/certs_test.h>
    #endif
#endif


#ifdef HAVE_BLAKE2
    #include <cyassl/ctaocrypt/blake2.h>
    void bench_blake2(void);
#endif

#ifdef _MSC_VER
    /* 4996 warning to use MS extensions e.g., strcpy_s instead of strncpy */
    #pragma warning(disable: 4996)
#endif

void bench_des(void);
void bench_arc4(void);
void bench_hc128(void);
void bench_rabbit(void);
void bench_aes(int);
void bench_aesgcm(void);
void bench_aesccm(void);
void bench_aesctr(void);
void bench_camellia(void);

void bench_md5(void);
void bench_sha(void);
void bench_sha256(void);
void bench_sha512(void);
void bench_ripemd(void);

void bench_rsa(void);
void bench_rsaKeyGen(void);
void bench_dh(void);
#ifdef HAVE_ECC
void bench_eccKeyGen(void);
void bench_eccKeyAgree(void);
#endif

double current_time(int);


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

#endif


/* so embedded projects can pull in tests on their own */
#if !defined(NO_MAIN_DRIVER)

int main(int argc, char** argv)

{
  (void)argc;
  (void)argv;
#else
int benchmark_test(void *args) 
{
#endif

	#ifdef HAVE_CAVIUM
    int ret = OpenNitroxDevice(CAVIUM_DIRECT, CAVIUM_DEV_ID);
    if (ret != 0) {
        printf("Cavium OpenNitroxDevice failed\n");
        exit(-1);
    }
#endif /* HAVE_CAVIUM */
#ifndef NO_AES
    bench_aes(0);
    bench_aes(1);
#endif
#ifdef HAVE_AESGCM
    bench_aesgcm();
#endif

#ifdef CYASSL_AES_COUNTER
    bench_aesctr();
#endif

#ifdef HAVE_AESCCM
    bench_aesccm();
#endif
#ifdef HAVE_CAMELLIA
    bench_camellia();
#endif
#ifndef NO_RC4
    bench_arc4();
#endif
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

#ifndef NO_MD5
    bench_md5();
#endif
#ifndef NO_SHA
    bench_sha();
#endif
#ifndef NO_SHA256
    bench_sha256();
#endif
#ifdef CYASSL_SHA512
    bench_sha512();
#endif
#ifdef CYASSL_RIPEMD
    bench_ripemd();
#endif
#ifdef HAVE_BLAKE2
    bench_blake2();
#endif

    printf("\n");

#ifndef NO_RSA
    bench_rsa();
#endif

#ifndef NO_DH
    bench_dh();
#endif

#if defined(CYASSL_KEY_GEN) && !defined(NO_RSA)
    bench_rsaKeyGen();
#endif

#ifdef HAVE_ECC 
    bench_eccKeyGen();
    bench_eccKeyAgree();
#endif

    return 0;
}


#ifdef BENCH_EMBEDDED
enum BenchmarkBounds {
    numBlocks  = 25, /* how many kB to test (en/de)cryption */
    ntimes     = 1,
    genTimes   = 5,  /* public key iterations */
    agreeTimes = 5
};
static const char blockType[] = "kB";   /* used in printf output */
#else
enum BenchmarkBounds {
    numBlocks  = 5,  /* how many megs to test (en/de)cryption */
    ntimes     = 100,
    genTimes   = 100,
    agreeTimes = 100
};
static const char blockType[] = "megs"; /* used in printf output */
#endif

static const byte key[] = 
{
    0x01,0x23,0x45,0x67,0x89,0xab,0xcd,0xef,
    0xfe,0xde,0xba,0x98,0x76,0x54,0x32,0x10,
    0x89,0xab,0xcd,0xef,0x01,0x23,0x45,0x67
};

static const byte iv[] = 
{
    0x12,0x34,0x56,0x78,0x90,0xab,0xcd,0xef,
    0x01,0x01,0x01,0x01,0x01,0x01,0x01,0x01,
    0x11,0x21,0x31,0x41,0x51,0x61,0x71,0x81
    
};


/* use kB instead of mB for embedded benchmarking */
#ifdef BENCH_EMBEDDED
static byte plain [1024];
static byte cipher[1024];
#else
static byte plain [1024*1024];
static byte cipher[1024*1024];
#endif


#ifndef NO_AES
void bench_aes(int show)
{
    Aes    enc;
    double start, total, persec;
    int    i;
    int    ret;

#ifdef HAVE_CAVIUM
    if (AesInitCavium(&enc, CAVIUM_DEV_ID) != 0) {
        printf("aes init cavium failed\n");
        return;
    }
#endif

    ret = AesSetKey(&enc, key, 16, iv, AES_ENCRYPTION);
    if (ret != 0) {
        printf("AesSetKey failed, ret = %d\n", ret);
        return;
    }
    start = current_time(1);

    for(i = 0; i < numBlocks; i++)
        AesCbcEncrypt(&enc, plain, cipher, sizeof(plain));

    total = current_time(0) - start;

    persec = 1 / total * numBlocks;
#ifdef BENCH_EMBEDDED
    /* since using kB, convert to MB/s */
    persec = persec / 1024;
#endif

    if (show)
        printf("AES      %d %s took %5.3f seconds, %7.3f MB/s\n", numBlocks,
                                                  blockType, total, persec);
#ifdef HAVE_CAVIUM
    AesFreeCavium(&enc);
#endif
}
#endif


#if defined(HAVE_AESGCM) || defined(HAVE_AESCCM)
    static byte additional[13];
    static byte tag[16];
#endif


#ifdef HAVE_AESGCM
void bench_aesgcm(void)
{
    Aes    enc;
    double start, total, persec;
    int    i;

    AesGcmSetKey(&enc, key, 16);
    start = current_time(1);

    for(i = 0; i < numBlocks; i++)
        AesGcmEncrypt(&enc, cipher, plain, sizeof(plain), iv, 12,
                        tag, 16, additional, 13);

    total = current_time(0) - start;

    persec = 1 / total * numBlocks;
#ifdef BENCH_EMBEDDED
    /* since using kB, convert to MB/s */
    persec = persec / 1024;
#endif

    printf("AES-GCM  %d %s took %5.3f seconds, %7.3f MB/s\n", numBlocks,
                                              blockType, total, persec);
}
#endif

#ifdef CYASSL_AES_COUNTER
void bench_aesctr(void)
{
    Aes    enc;
    double start, total, persec;
    int    i;

    AesSetKeyDirect(&enc, key, AES_BLOCK_SIZE, iv, AES_ENCRYPTION);
    start = current_time(1);

    for(i = 0; i < numBlocks; i++)
        AesCtrEncrypt(&enc, plain, cipher, sizeof(plain));

    total = current_time(0) - start;

    persec = 1 / total * numBlocks;
#ifdef BENCH_EMBEDDED
    /* since using kB, convert to MB/s */
    persec = persec / 1024;
#endif

    printf("AES-CTR  %d %s took %5.3f seconds, %7.3f MB/s\n", numBlocks,
                                              blockType, total, persec);
}
#endif



#ifdef HAVE_AESCCM
void bench_aesccm(void)
{
    Aes    enc;
    double start, total, persec;
    int    i;

    AesCcmSetKey(&enc, key, 16);
    start = current_time(1);

    for(i = 0; i < numBlocks; i++)
        AesCcmEncrypt(&enc, cipher, plain, sizeof(plain), iv, 12,
                        tag, 16, additional, 13);

    total = current_time(0) - start;

    persec = 1 / total * numBlocks;
#ifdef BENCH_EMBEDDED
    /* since using kB, convert to MB/s */
    persec = persec / 1024;
#endif

    printf("AES-CCM  %d %s took %5.3f seconds, %7.3f MB/s\n", numBlocks,
                                              blockType, total, persec);
}
#endif


#ifdef HAVE_CAMELLIA
void bench_camellia(void)
{
    Camellia cam;
    double start, total, persec;
    int    i, ret;

    ret = CamelliaSetKey(&cam, key, 16, iv);
    if (ret != 0) {
        printf("CamelliaSetKey failed, ret = %d\n", ret);
        return;
    }
    start = current_time(1);

    for(i = 0; i < numBlocks; i++)
        CamelliaCbcEncrypt(&cam, plain, cipher, sizeof(plain));

    total = current_time(0) - start;

    persec = 1 / total * numBlocks;
#ifdef BENCH_EMBEDDED
    /* since using kB, convert to MB/s */
    persec = persec / 1024;
#endif

    printf("Camellia %d %s took %5.3f seconds, %7.3f MB/s\n", numBlocks,
                                              blockType, total, persec);
}
#endif


#ifndef NO_DES3
void bench_des(void)
{
    Des3   enc;
    double start, total, persec;
    int    i, ret;

#ifdef HAVE_CAVIUM
    if (Des3_InitCavium(&enc, CAVIUM_DEV_ID) != 0)
        printf("des3 init cavium failed\n");
#endif
    ret = Des3_SetKey(&enc, key, iv, DES_ENCRYPTION);
    if (ret != 0) {
        printf("Des3_SetKey failed, ret = %d\n", ret);
        return;
    }
    start = current_time(1);

    for(i = 0; i < numBlocks; i++)
        Des3_CbcEncrypt(&enc, plain, cipher, sizeof(plain));

    total = current_time(0) - start;

    persec = 1 / total * numBlocks;
#ifdef BENCH_EMBEDDED
    /* since using kB, convert to MB/s */
    persec = persec / 1024;
#endif

    printf("3DES     %d %s took %5.3f seconds, %7.3f MB/s\n", numBlocks,
                                              blockType, total, persec);
#ifdef HAVE_CAVIUM
    Des3_FreeCavium(&enc);
#endif
}
#endif


#ifndef NO_RC4
void bench_arc4(void)
{
    Arc4   enc;
    double start, total, persec;
    int    i;
    
#ifdef HAVE_CAVIUM
    if (Arc4InitCavium(&enc, CAVIUM_DEV_ID) != 0)
        printf("arc4 init cavium failed\n");
#endif

    Arc4SetKey(&enc, key, 16);
    start = current_time(1);

    for(i = 0; i < numBlocks; i++)
        Arc4Process(&enc, cipher, plain, sizeof(plain));

    total = current_time(0) - start;
    persec = 1 / total * numBlocks;
#ifdef BENCH_EMBEDDED
    /* since using kB, convert to MB/s */
    persec = persec / 1024;
#endif

    printf("ARC4     %d %s took %5.3f seconds, %7.3f MB/s\n", numBlocks,
                                              blockType, total, persec);
#ifdef HAVE_CAVIUM
    Arc4FreeCavium(&enc);
#endif
}
#endif


#ifdef HAVE_HC128
void bench_hc128(void)
{
    HC128  enc;
    double start, total, persec;
    int    i;
    
    Hc128_SetKey(&enc, key, iv);
    start = current_time(1);

    for(i = 0; i < numBlocks; i++)
        Hc128_Process(&enc, cipher, plain, sizeof(plain));

    total = current_time(0) - start;
    persec = 1 / total * numBlocks;
#ifdef BENCH_EMBEDDED
    /* since using kB, convert to MB/s */
    persec = persec / 1024;
#endif

    printf("HC128    %d %s took %5.3f seconds, %7.3f MB/s\n", numBlocks,
                                              blockType, total, persec);
}
#endif /* HAVE_HC128 */


#ifndef NO_RABBIT
void bench_rabbit(void)
{
    Rabbit  enc;
    double start, total, persec;
    int    i;
    
    RabbitSetKey(&enc, key, iv);
    start = current_time(1);

    for(i = 0; i < numBlocks; i++)
        RabbitProcess(&enc, cipher, plain, sizeof(plain));

    total = current_time(0) - start;
    persec = 1 / total * numBlocks;
#ifdef BENCH_EMBEDDED
    /* since using kB, convert to MB/s */
    persec = persec / 1024;
#endif

    printf("RABBIT   %d %s took %5.3f seconds, %7.3f MB/s\n", numBlocks,
                                              blockType, total, persec);
}
#endif /* NO_RABBIT */


#ifndef NO_MD5
void bench_md5(void)
{
    Md5    hash;
    byte   digest[MD5_DIGEST_SIZE];
    double start, total, persec;
    int    i;

    InitMd5(&hash);
    start = current_time(1);

    for(i = 0; i < numBlocks; i++)
        Md5Update(&hash, plain, sizeof(plain));
   
    Md5Final(&hash, digest);

    total = current_time(0) - start;
    persec = 1 / total * numBlocks;
#ifdef BENCH_EMBEDDED
    /* since using kB, convert to MB/s */
    persec = persec / 1024;
#endif

    printf("MD5      %d %s took %5.3f seconds, %7.3f MB/s\n", numBlocks,
                                              blockType, total, persec);
}
#endif /* NO_MD5 */


#ifndef NO_SHA
void bench_sha(void)
{
    Sha    hash;
    byte   digest[SHA_DIGEST_SIZE];
    double start, total, persec;
    int    i, ret;
        
    ret = InitSha(&hash);
    if (ret != 0) {
        printf("InitSha failed, ret = %d\n", ret);
        return;
    }
    start = current_time(1);
    
    for(i = 0; i < numBlocks; i++)
        ShaUpdate(&hash, plain, sizeof(plain));
   
    ShaFinal(&hash, digest);

    total = current_time(0) - start;
    persec = 1 / total * numBlocks;
#ifdef BENCH_EMBEDDED
    /* since using kB, convert to MB/s */
    persec = persec / 1024;
#endif

    printf("SHA      %d %s took %5.3f seconds, %7.3f MB/s\n", numBlocks,
                                              blockType, total, persec);
}
#endif /* NO_SHA */


#ifndef NO_SHA256
void bench_sha256(void)
{
    Sha256 hash;
    byte   digest[SHA256_DIGEST_SIZE];
    double start, total, persec;
    int    i, ret;
        
    ret = InitSha256(&hash);
    if (ret != 0) {
        printf("InitSha256 failed, ret = %d\n", ret);
        return;
    }
    start = current_time(1);
    
    for(i = 0; i < numBlocks; i++) {
        ret = Sha256Update(&hash, plain, sizeof(plain));
        if (ret != 0) {
            printf("Sha256Update failed, ret = %d\n", ret);
            return;
        }
    }
   
    ret = Sha256Final(&hash, digest);
    if (ret != 0) {
        printf("Sha256Final failed, ret = %d\n", ret);
        return;
    }

    total = current_time(0) - start;
    persec = 1 / total * numBlocks;
#ifdef BENCH_EMBEDDED
    /* since using kB, convert to MB/s */
    persec = persec / 1024;
#endif

    printf("SHA-256  %d %s took %5.3f seconds, %7.3f MB/s\n", numBlocks,
                                              blockType, total, persec);
}
#endif

#ifdef CYASSL_SHA512
void bench_sha512(void)
{
    Sha512 hash;
    byte   digest[SHA512_DIGEST_SIZE];
    double start, total, persec;
    int    i, ret;
        
    ret = InitSha512(&hash);
    if (ret != 0) {
        printf("InitSha512 failed, ret = %d\n", ret);
        return;
    }
    start = current_time(1);
    
    for(i = 0; i < numBlocks; i++) {
        ret = Sha512Update(&hash, plain, sizeof(plain));
        if (ret != 0) {
            printf("Sha512Update failed, ret = %d\n", ret);
            return;
        }
    }

    ret = Sha512Final(&hash, digest);
    if (ret != 0) {
        printf("Sha512Final failed, ret = %d\n", ret);
        return;
    }

    total = current_time(0) - start;
    persec = 1 / total * numBlocks;
#ifdef BENCH_EMBEDDED
    /* since using kB, convert to MB/s */
    persec = persec / 1024;
#endif

    printf("SHA-512  %d %s took %5.3f seconds, %7.3f MB/s\n", numBlocks,
                                              blockType, total, persec);
}
#endif

#ifdef CYASSL_RIPEMD
void bench_ripemd(void)
{
    RipeMd hash;
    byte   digest[RIPEMD_DIGEST_SIZE];
    double start, total, persec;
    int    i;
        
    InitRipeMd(&hash);
    start = current_time(1);
    
    for(i = 0; i < numBlocks; i++)
        RipeMdUpdate(&hash, plain, sizeof(plain));
   
    RipeMdFinal(&hash, digest);

    total = current_time(0) - start;
    persec = 1 / total * numBlocks;
#ifdef BENCH_EMBEDDED
    /* since using kB, convert to MB/s */
    persec = persec / 1024;
#endif

    printf("RIPEMD   %d %s took %5.3f seconds, %7.3f MB/s\n", numBlocks,
                                              blockType, total, persec);
}
#endif


#ifdef HAVE_BLAKE2
void bench_blake2(void)
{
    Blake2b b2b;
    byte    digest[64];
    double  start, total, persec;
    int     i, ret;
       
    ret = InitBlake2b(&b2b, 64);
    if (ret != 0) {
        printf("InitBlake2b failed, ret = %d\n", ret);
        return;
    }
    start = current_time(1);
    
    for(i = 0; i < numBlocks; i++) {
        ret = Blake2bUpdate(&b2b, plain, sizeof(plain));
        if (ret != 0) {
            printf("Blake2bUpdate failed, ret = %d\n", ret);
            return;
        }
    }
   
    ret = Blake2bFinal(&b2b, digest, 64);
    if (ret != 0) {
        printf("Blake2bFinal failed, ret = %d\n", ret);
        return;
    }

    total = current_time(0) - start;
    persec = 1 / total * numBlocks;
#ifdef BENCH_EMBEDDED
    /* since using kB, convert to MB/s */
    persec = persec / 1024;
#endif

    printf("BLAKE2b  %d %s took %5.3f seconds, %7.3f MB/s\n", numBlocks,
                                              blockType, total, persec);
}
#endif


#if !defined(NO_RSA) || !defined(NO_DH) \
                                || defined(CYASSL_KEYGEN) || defined(HAVE_ECC)
static RNG rng;
#endif

#ifndef NO_RSA


#if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048) && \
                                                    defined(CYASSL_MDK_SHELL)
static char *certRSAname = "certs/rsa2048.der" ;
static void set_Bench_RSA_File(char * cert) { certRSAname = cert ; }   
                                                 /* set by shell command */
#elif defined(CYASSL_MDK_SHELL)
    /* nothing */
#else
static const char *certRSAname = "certs/rsa2048.der" ;
#endif

void bench_rsa(void)
{
    int    i;
    int    ret;
    byte   tmp[3072];
    size_t bytes;
    word32 idx = 0;

    byte      message[] = "Everyone gets Friday off.";
    byte      enc[512];  /* for up to 4096 bit */
    const int len = (int)strlen((char*)message);
    double    start, total, each, milliEach;
    
    RsaKey rsaKey;
    int    rsaKeySz = 2048; /* used in printf */

#ifdef USE_CERT_BUFFERS_1024
    XMEMCPY(tmp, rsa_key_der_1024, sizeof_rsa_key_der_1024);
    bytes = sizeof_rsa_key_der_1024;
    rsaKeySz = 1024;
#elif defined(USE_CERT_BUFFERS_2048)
    XMEMCPY(tmp, rsa_key_der_2048, sizeof_rsa_key_der_2048);
    bytes = sizeof_rsa_key_der_2048;
#else
    FILE*  file = fopen(certRSAname, "rb");

    if (!file) {
        printf("can't find %s, Please run from CyaSSL home dir\n", certRSAname);
        return;
    }
    
    bytes = fread(tmp, 1, sizeof(tmp), file);
    fclose(file);
#endif /* USE_CERT_BUFFERS */

		
#ifdef HAVE_CAVIUM
    if (RsaInitCavium(&rsaKey, CAVIUM_DEV_ID) != 0)
        printf("RSA init cavium failed\n");
#endif
    ret = InitRng(&rng);
    if (ret < 0) {
        printf("InitRNG failed\n");
        return;
    }
    ret = InitRsaKey(&rsaKey, 0);
    if (ret < 0) {
        printf("InitRsaKey failed\n");
        return;
    }
    ret = RsaPrivateKeyDecode(tmp, &idx, &rsaKey, (word32)bytes);
    
    start = current_time(1);

    for (i = 0; i < ntimes; i++)
        ret = RsaPublicEncrypt(message,len,enc,sizeof(enc), &rsaKey, &rng);

    total = current_time(0) - start;
    each  = total / ntimes;   /* per second   */
    milliEach = each * 1000; /* milliseconds */

    printf("RSA %d encryption took %6.3f milliseconds, avg over %d"
           " iterations\n", rsaKeySz, milliEach, ntimes);

    if (ret < 0) {
        printf("Rsa Public Encrypt failed\n");
        return;
    }

    start = current_time(1);

    for (i = 0; i < ntimes; i++) {
         byte  out[512];  /* for up to 4096 bit */
         RsaPrivateDecrypt(enc, (word32)ret, out, sizeof(out), &rsaKey);
    }

    total = current_time(0) - start;
    each  = total / ntimes;   /* per second   */
    milliEach = each * 1000; /* milliseconds */

    printf("RSA %d decryption took %6.3f milliseconds, avg over %d"
           " iterations\n", rsaKeySz, milliEach, ntimes);

    FreeRsaKey(&rsaKey);
#ifdef HAVE_CAVIUM
    RsaFreeCavium(&rsaKey);
#endif
}
#endif


#ifndef NO_DH


#if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048) && \
                                                    defined(CYASSL_MDK_SHELL)
static char *certDHname = "certs/dh2048.der" ;
void set_Bench_DH_File(char * cert) { certDHname = cert ; }    
                                            /* set by shell command */
#elif defined(CYASSL_MDK_SHELL)
    /* nothing */
#else
static const char *certDHname = "certs/dh2048.der" ;
#endif

void bench_dh(void)
{
    int    i, ret;
    byte   tmp[1024];
    size_t bytes;
    word32 idx = 0, pubSz, privSz = 0, pubSz2, privSz2, agreeSz;

    byte   pub[256];    /* for 2048 bit */
    byte   priv[256];   /* for 2048 bit */
    byte   pub2[256];   /* for 2048 bit */
    byte   priv2[256];  /* for 2048 bit */
    byte   agree[256];  /* for 2048 bit */
    
    double start, total, each, milliEach;
    DhKey  dhKey;
    int    dhKeySz = 2048; /* used in printf */

	
#ifdef USE_CERT_BUFFERS_1024
    XMEMCPY(tmp, dh_key_der_1024, sizeof_dh_key_der_1024);
    bytes = sizeof_dh_key_der_1024;
    dhKeySz = 1024;
#elif defined(USE_CERT_BUFFERS_2048)
    XMEMCPY(tmp, dh_key_der_2048, sizeof_dh_key_der_2048);
    bytes = sizeof_dh_key_der_2048;
#else
    FILE*  file = fopen(certDHname, "rb");

    if (!file) {
        printf("can't find %s,  Please run from CyaSSL home dir\n", certDHname);
        return;
    }

    ret = InitRng(&rng);
    if (ret < 0) {
        printf("InitRNG failed\n");
        return;
    }
    bytes = fread(tmp, 1, sizeof(tmp), file);
#endif /* USE_CERT_BUFFERS */

		
    InitDhKey(&dhKey);
    bytes = DhKeyDecode(tmp, &idx, &dhKey, (word32)bytes);
    if (bytes != 0) {
        printf("dhekydecode failed, can't benchmark\n");
        #if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048)
            fclose(file);
        #endif
        return;
    }

    start = current_time(1);

    for (i = 0; i < ntimes; i++)
        DhGenerateKeyPair(&dhKey, &rng, priv, &privSz, pub, &pubSz);

    total = current_time(0) - start;
    each  = total / ntimes;   /* per second   */
    milliEach = each * 1000; /* milliseconds */

    printf("DH  %d key generation  %6.3f milliseconds, avg over %d"
           " iterations\n", dhKeySz, milliEach, ntimes);

    DhGenerateKeyPair(&dhKey, &rng, priv2, &privSz2, pub2, &pubSz2);
    start = current_time(1);

    for (i = 0; i < ntimes; i++)
        DhAgree(&dhKey, agree, &agreeSz, priv, privSz, pub2, pubSz2);

    total = current_time(0) - start;
    each  = total / ntimes;   /* per second   */
    milliEach = each * 1000; /* milliseconds */

    printf("DH  %d key agreement   %6.3f milliseconds, avg over %d"
           " iterations\n", dhKeySz, milliEach, ntimes);

#if !defined(USE_CERT_BUFFERS_1024) && !defined(USE_CERT_BUFFERS_2048)
    fclose(file);
#endif
    FreeDhKey(&dhKey);
}
#endif

#if defined(CYASSL_KEY_GEN) && !defined(NO_RSA)
void bench_rsaKeyGen(void)
{
    RsaKey genKey;
    double start, total, each, milliEach;
    int    i;
  
    /* 1024 bit */ 
    start = current_time(1);

    for(i = 0; i < genTimes; i++) {
        InitRsaKey(&genKey, 0); 
        MakeRsaKey(&genKey, 1024, 65537, &rng);
        FreeRsaKey(&genKey);
    }

    total = current_time(0) - start;
    each  = total / genTimes;  /* per second  */
    milliEach = each * 1000;   /* millisconds */
    printf("\n");
    printf("RSA 1024 key generation  %6.3f milliseconds, avg over %d"
           " iterations\n", milliEach, genTimes);

    /* 2048 bit */
    start = current_time(1);

    for(i = 0; i < genTimes; i++) {
        InitRsaKey(&genKey, 0); 
        MakeRsaKey(&genKey, 2048, 65537, &rng);
        FreeRsaKey(&genKey);
    }

    total = current_time(0) - start;
    each  = total / genTimes;  /* per second  */
    milliEach = each * 1000;   /* millisconds */
    printf("RSA 2048 key generation  %6.3f milliseconds, avg over %d"
           " iterations\n", milliEach, genTimes);
}
#endif /* CYASSL_KEY_GEN */

#ifdef HAVE_ECC 
void bench_eccKeyGen(void)
{
    ecc_key genKey;
    double start, total, each, milliEach;
    int    i, ret;
  
    ret = InitRng(&rng);
    if (ret < 0) {
        printf("InitRNG failed\n");
        return;
    }
    /* 256 bit */ 
    start = current_time(1);

    for(i = 0; i < genTimes; i++) {
        ecc_make_key(&rng, 32, &genKey);
        ecc_free(&genKey);
    }

    total = current_time(0) - start;
    each  = total / genTimes;  /* per second  */
    milliEach = each * 1000;   /* millisconds */
    printf("\n");
    printf("ECC  256 key generation  %6.3f milliseconds, avg over %d"
           " iterations\n", milliEach, genTimes);
}


void bench_eccKeyAgree(void)
{
    ecc_key genKey, genKey2;
    double start, total, each, milliEach;
    int    i, ret;
    byte   shared[1024];
    byte   sig[1024];
    byte   digest[32];
    word32 x = 0;
 
    ecc_init(&genKey);
    ecc_init(&genKey2);

    ret = InitRng(&rng);
    if (ret < 0) {
        printf("InitRNG failed\n");
        return;
    }

    ret = ecc_make_key(&rng, 32, &genKey);
    if (ret != 0) {
        printf("ecc_make_key failed\n");
        return;
    }
    ret = ecc_make_key(&rng, 32, &genKey2);
    if (ret != 0) {
        printf("ecc_make_key failed\n");
        return;
    }

    /* 256 bit */ 
    start = current_time(1);

    for(i = 0; i < agreeTimes; i++) {
        x = sizeof(shared);
        ret = ecc_shared_secret(&genKey, &genKey2, shared, &x);
        if (ret != 0) {
            printf("ecc_shared_secret failed\n");
            return; 
        }
    }

    total = current_time(0) - start;
    each  = total / agreeTimes;  /* per second  */
    milliEach = each * 1000;   /* millisconds */
    printf("EC-DHE   key agreement   %6.3f milliseconds, avg over %d"
           " iterations\n", milliEach, agreeTimes);

    /* make dummy digest */
    for (i = 0; i < (int)sizeof(digest); i++)
        digest[i] = (byte)i;


    start = current_time(1);

    for(i = 0; i < agreeTimes; i++) {
        x = sizeof(sig);
        ret = ecc_sign_hash(digest, sizeof(digest), sig, &x, &rng, &genKey);
        if (ret != 0) {
            printf("ecc_sign_hash failed\n");
            return; 
        }
    }

    total = current_time(0) - start;
    each  = total / agreeTimes;  /* per second  */
    milliEach = each * 1000;   /* millisconds */
    printf("EC-DSA   sign   time     %6.3f milliseconds, avg over %d"
           " iterations\n", milliEach, agreeTimes);

    start = current_time(1);

    for(i = 0; i < agreeTimes; i++) {
        int verify = 0;
        ret = ecc_verify_hash(sig, x, digest, sizeof(digest), &verify, &genKey);
        if (ret != 0) {
            printf("ecc_verify_hash failed\n");
            return; 
        }
    }

    total = current_time(0) - start;
    each  = total / agreeTimes;  /* per second  */
    milliEach = each * 1000;     /* millisconds */
    printf("EC-DSA   verify time     %6.3f milliseconds, avg over %d"
           " iterations\n", milliEach, agreeTimes);

    ecc_free(&genKey2);
    ecc_free(&genKey);
}
#endif /* HAVE_ECC */


#ifdef _WIN32

    #define WIN32_LEAN_AND_MEAN
    #include <windows.h>

    double current_time(int reset)
    {
        static int init = 0;
        static LARGE_INTEGER freq;
    
        LARGE_INTEGER count;

        (void)reset;

        if (!init) {
            QueryPerformanceFrequency(&freq);
            init = 1;
        }

        QueryPerformanceCounter(&count);

        return (double)count.QuadPart / freq.QuadPart;
    }

#elif defined MICROCHIP_PIC32
    #if defined(CYASSL_MICROCHIP_PIC32MZ)
        #define CLOCK 8000000.0
    #else
        #include <peripheral/timer.h>
        #define CLOCK 4000000.0
    #endif

    double current_time(int reset)
    {
        unsigned int ns;

        if (reset) {
            WriteCoreTimer(0);
        }

        /* get timer in ns */
        ns = ReadCoreTimer();

        /* return seconds as a double */
        return ( ns / CLOCK * 2.0);
    }

#elif defined CYASSL_MDK_ARM

    extern double current_time(int reset) ;

#elif defined FREERTOS

    double current_time(int reset)
    {
        (void) reset;

        portTickType tickCount;

        /* tick count == ms, if configTICK_RATE_HZ is set to 1000 */
        tickCount = xTaskGetTickCount();
        return (double)tickCount / 1000;
    }

#else

    #include <sys/time.h>

    double current_time(int reset)
    {
        struct timeval tv;

        (void)reset;

        gettimeofday(&tv, 0);

        return (double)tv.tv_sec + (double)tv.tv_usec / 1000000;
    }

#endif /* _WIN32 */
