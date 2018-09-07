/* pic32mz-crypt.h
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

#ifndef PIC32MZ_CRYPT_H
#define PIC32MZ_CRYPT_H

#ifdef  WOLFSSL_MICROCHIP_PIC32MZ

#define MICROCHIP_PIC32
#include <xc.h>
#include <sys/endian.h>
#include <sys/kmem.h>

typedef struct saCtrl {
    unsigned int CRYPTOALGO : 4;
    unsigned int MULTITASK : 3;
    unsigned int KEYSIZE : 2;
    unsigned int ENCTYPE : 1;
    unsigned int ALGO : 7;
    unsigned int : 3;
    unsigned int FLAGS : 1;
    unsigned int FB : 1;
    unsigned int LOADIV : 1;
    unsigned int LNC : 1;
    unsigned int IRFLAG : 1;
    unsigned int ICVONLY : 1;
    unsigned int OR_EN : 1;
    unsigned int NO_RX : 1;
    unsigned int : 1;
    unsigned int VERIFY : 1;
    unsigned int : 2;
} saCtrl;

typedef struct securityAssociation {
    saCtrl SA_CTRL;
    unsigned int SA_AUTHKEY[8];
    unsigned int SA_ENCKEY[8];
    unsigned int SA_AUTHIV[8];
    unsigned int SA_ENCIV[4];
} securityAssociation;

typedef struct bdCtrl {
    unsigned int BUFLEN : 16;
    unsigned int CBD_INT_EN : 1;
    unsigned int PKT_INT_EN : 1;
    unsigned int LIFM : 1;
    unsigned int LAST_BD: 1;
    unsigned int : 2;
    unsigned int SA_FETCH_EN : 1;
    unsigned int : 8;
    unsigned int DESC_EN : 1;
} bdCtrl;

typedef struct bufferDescriptor {
    bdCtrl BD_CTRL;
    unsigned int SA_ADDR;
    unsigned int SRCADDR;
    unsigned int DSTADDR;
    unsigned int NXTPTR;
    unsigned int UPDPTR;
    unsigned int MSGLEN;
    unsigned int ENCOFF;
} bufferDescriptor;


#define PIC32_ENCRYPTION      0b1
#define PIC32_DECRYPTION      0b0

#define PIC32_ALGO_HMAC1     0b01000000
#define PIC32_ALGO_SHA256    0b00100000
#define PIC32_ALGO_SHA1      0b00010000
#define PIC32_ALGO_MD5       0b00001000
#define PIC32_ALGO_AES       0b00000100
#define PIC32_ALGO_TDES      0b00000010
#define PIC32_ALGO_DES       0b00000001

#define PIC32_CRYPTOALGO_AES_GCM 0b1110
#define PIC32_CRYPTOALGO_RCTR    0b1101
#define PIC32_CRYPTOALGO_RCBC    0b1001
#define PIC32_CRYPTOALGO_REBC    0b1000
#define PIC32_CRYPTOALGO_TCBC    0b0101
#define PIC32_CRYPTOALGO_CBC     0b0001

#define PIC32_AES_KEYSIZE_256     0b10
#define PIC32_AES_KEYSIZE_192     0b01
#define PIC32_AES_KEYSIZE_128     0b00

#define PIC32_AES_BLOCK_SIZE 16
#define MD5_HASH_SIZE 16
#define SHA1_HASH_SIZE 20
#define SHA256_HASH_SIZE 32
#define PIC32_HASH_SIZE 32

#define PIC32MZ_MAX_BD   2
typedef struct {      /* Crypt Engine descripter */
    int bdCount ;
    int err   ;
    volatile bufferDescriptor 
        bd[PIC32MZ_MAX_BD] __attribute__((aligned (8), coherent));
    securityAssociation 
        sa                 __attribute__((aligned (8), coherent));
} pic32mz_desc ;

#define PIC32MZ_IF_RAM(addr) (KVA_TO_PA(addr) < 0x80000)

#define WAIT_ENGINE \
    { volatile int v ; while (CESTATbits.ACTIVE) ; for(v=0; v<100; v++) ; }

#ifdef DEBUG_CYASSL
static void print_mem(const unsigned char *p, int size) {
    for(; size>0; size--, p++) {
        if(size%4 == 0)printf(" ") ;
            printf("%02x", (int)*p) ;
    }
    puts("") ;
}
#endif

#endif
#endif /* PIC32MZ_CRYPT_H */
