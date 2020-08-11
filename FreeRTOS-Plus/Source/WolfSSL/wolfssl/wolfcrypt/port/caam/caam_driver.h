/* caam_driver.h
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */

#ifndef CAAM_DRIVER_H
#define CAAM_DRIVER_H

#define CAAM_BASE 0xf2100000

#define CAAM_PAGE 0xf0100000
#define CAAM_PAGE_MAX 6

/******************************************************************************
  Basic Descriptors
  ****************************************************************************/

/* descriptor commands */
#define CAAM_KEY      0x00000000
#define CAAM_LOAD     0x10000000
#define CAAM_LOAD_CTX 0x10200000
#define CAAM_IMM      0x00800000
#define CAAM_FIFO_L   0x20000000
#define CAAM_FIFO_S   0x60000000
#define CAAM_FIFO_S_SKEY 0x60260000
#define CAAM_STORE       0x50000000
#define CAAM_STORE_CTX   0x50200000
#define CAAM_MOVE        0x78000000
#define CAAM_OP          0x80000000
#define CAAM_SIG         0x90000000
#define CAAM_JUMP        0xA0000000
#define CAAM_SEQI        0xF0000000/* SEQ in  */
#define CAAM_SEQO        0xF8000000/* SEQ out */
#define CAAM_HEAD        0xB0800000
#define CAAM_NWB         0x00200000

#define CAAM_BLOB_ENCAP 0x07000000
#define CAAM_BLOB_DECAP 0x06000000
#define CAAM_OPID_BLOB  0x000D0000

/* algorithms modes and types */
#define CAAM_CLASS1 0x02000000/* i.e. AES */
#define CAAM_CLASS2 0x04000000/* i.e. hash algos */

#define CAAM_ENC    0x00000001
#define CAAM_DEC    0x00000000
#define CAAM_ALG_INIT   0x00000004
#define CAAM_ALG_INITF  0x0000000C
#define CAAM_ALG_UPDATE 0x00000000
#define CAAM_ALG_FINAL  0x00000008

    /* AES 10h */
#define CAAM_AESCTR 0x00100000
#define CAAM_AESCBC 0x00100100
#define CAAM_AESECB 0x00100200
#define CAAM_AESCFB 0x00100300
#define CAAM_AESOFB 0x00100400
#define CAAM_CMAC   0x00100600
#define CAAM_AESCCM 0x00100800

    /* HASH 40h */
#define CAAM_MD5    0x00400000
#define CAAM_SHA    0x00410000
#define CAAM_SHA224 0x00420000
#define CAAM_SHA256 0x00430000
#define CAAM_SHA384 0x00440000
#define CAAM_SHA512 0x00450000

    /* HMAC 40h + 10 AAI */
#define CAAM_HMAC_MD5    0x00400010
#define CAAM_HMAC_SHA    0x00410010
#define CAAM_HMAC_SHA224 0x00420010
#define CAAM_HMAC_SHA256 0x00430010
#define CAAM_HMAC_SHA384 0x00440010
#define CAAM_HMAC_SHA512 0x00450010

#define CAAM_MD5_CTXSZ (16 + 8)
#define CAAM_SHA_CTXSZ (20 + 8)
#define CAAM_SHA224_CTXSZ (32 + 8)
#define CAAM_SHA256_CTXSZ (32 + 8)
#define CAAM_SHA384_CTXSZ (64 + 8)
#define CAAM_SHA512_CTXSZ (64 + 8)

    /* RNG 50h */
#define CAAM_RNG 0x00500000

    /* Used to get raw entropy from TRNG */
#define CAAM_ENTROPY 0x00500001

#define FIFOL_TYPE_MSG 0x00100000
#define FIFOL_TYPE_AAD 0x00300000
#define FIFOL_TYPE_FC1 0x00010000
#define FIFOL_TYPE_LC1 0x00020000
#define FIFOL_TYPE_LC2 0x00040000

#define FIFOS_TYPE_MSG 0x00300000

/* continue bit set if more output is expected */
#define CAAM_FIFOS_CONT 0x00800000

#define CAAM_PAGE_SZ 4096

/* RNG Registers */
#define CAAM_RTMCTL      CAAM_BASE + 0X0600
#define CAAM_RTSDCTL     CAAM_BASE + 0X0610
#define CAAM_RTFRQMIN    CAAM_BASE + 0X0618
#define CAAM_RTFRQMAX    CAAM_BASE + 0X061C
#define CAAM_RDSTA       CAAM_BASE + 0X06C0
#define CAAM_RTSTATUS    CAAM_BASE + 0x063C

/* each of the following 11 RTENT registers are an offset of 4 from RTENT0 */
#define CAAM_RTENT0      CAAM_BASE + 0x0640
#define CAAM_RTENT11     CAAM_BASE + 0x066C /* Max RTENT register */

/* RNG Masks/Values */
#ifndef CAAM_ENT_DLY
    #define CAAM_ENT_DLY   1200 /* @TODO lower value may gain performance */
#endif
#define CAAM_PRGM      0x00010000 /* Set RTMCTL to program state */
#define CAAM_TRNG      0x00000020 /* Set TRNG access */
#define CAAM_CTLERR    0x00001000
#define CAAM_ENTVAL    0x00000400 /* checking RTMCTL for entropy ready */

/* Input Job Ring Registers */
#define CAAM_IRBAR0      CAAM_BASE + 0x1004
#define CAAM_IRSR0       CAAM_BASE + 0x100C
#define CAAM_IRJAR0      CAAM_BASE + 0x101C

/* Output Job Ring Registers */
#define CAAM_ORBAR0      CAAM_BASE + 0x1024
#define CAAM_ORSR0       CAAM_BASE + 0x102C
#define CAAM_ORJAR0      CAAM_BASE + 0x103C


/* Status Registers */
#define CAAM_STATUS      CAAM_BASE + 0x0FD4
#define CAAM_VERSION_MS  CAAM_BASE + 0x0FE8
#define CAAM_VERSION_LS  CAAM_BASE + 0x0FEC
#define CAMM_SUPPORT_MS  CAAM_BASE + 0x0FF0
#define CAMM_SUPPORT_LS  CAAM_BASE + 0x0FF4


#define CAAM_C1DSR_LS    CAAM_BASE + 0x8014
#define CAAM_C1MR        CAAM_BASE + 0x8004


/* output FIFO  is 16 entries deep and each entry has a two 4 byte registers */
#define CAAM_FIFOO_MS    CAAM_BASE + 0x87F0
#define CAAM_FIFOO_LS    CAAM_BASE + 0x87F4

/* input FIFO is 16 entries deep with each entry having two 4 byte registers
   All data written to it from IP bus should be in big endian format */
#define CAAM_FIFOI_LS    CAAM_BASE + 0x87E0

/* offset of 4 with range 0 .. 13 */
#define CAAM_CTX1        CAAM_BASE + 0x8100
#define CAAM_CTRIV       CAAM_CTX1 + 8 /* AES-CTR iv is in 2 and 3 */
#define CAAM_CBCIV       CAAM_CTX1     /* AES-CBC iv is in 1 and 2 */


/* instantiate RNG and create JDKEK, TDKEK, and TDSK key */
static unsigned int wc_rng_start[] = {
    CAAM_HEAD | 0x00000006,
    CAAM_OP | CAAM_CLASS1 | CAAM_RNG | 0x00000004, /* Instantiate RNG handle 0 with TRNG */
    CAAM_JUMP | 0x02000001,  /* wait for Class1 RNG and jump to next cmd */
    CAAM_LOAD | 0x00880004,  /* Load to clear written register */
    0x00000001, /* reset done interrupt */
    CAAM_OP | CAAM_CLASS1 | CAAM_RNG | 0x00001000   /* Generate secure keys */
};

#endif /* CAAM_DRIVER_H */
