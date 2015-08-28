/* benchmark_main.c
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

#if defined(CYASSL_MICROCHIP_PIC32MZ)
    #define MICROCHIP_PIC32
    #include <xc.h>

    #include "MZ-configBits.h"

    #include "PIC32MZ-serial.h"
    #define SYSTEMConfigPerformance /* void out SYSTEMConfigPerformance(); */
#else
    #define PIC32_STARTER_KIT
    #include <p32xxxx.h>
    #include <plib.h>
    #include <sys/appio.h>
    #define init_serial() /* void out init_serial() ; */
#endif

void bench_des(void);
void bench_arc4(void);
void bench_hc128(void);
void bench_rabbit(void);
void bench_aes(int);
void bench_aesgcm(void);

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

/*
 * Main driver for CTaoCrypt benchmarks.
 */
int main(int argc, char** argv) {
    volatile int i ;
    int j ;

    PRECONbits.PFMWS = 2;
    PRECONbits.PREFEN = 0b11;

    init_serial() ;  /* initialize PIC32MZ serial I/O */
    SYSTEMConfigPerformance(80000000);
    DBINIT();

    for(j=0; j<100; j++) {
        for(i=0; i<10000000; i++);
        printf("time=%f\n", current_time(0)) ;
    }  
    printf("wolfCrypt Benchmark:\n");

#ifndef NO_AES
    bench_aes(0);
    bench_aes(1);
#endif
#ifdef HAVE_AESGCM
    bench_aesgcm();
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
    printf("End of wolfCrypt Benchmark:\n");
    return 0;
}

