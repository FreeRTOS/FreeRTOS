/* des3.c
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

#ifndef NO_DES3

#include <cyassl/ctaocrypt/des3.h>

#ifdef NO_INLINE
    #include <cyassl/ctaocrypt/misc.h>
#else
    #include <ctaocrypt/src/misc.c>
#endif


/* permuted choice table (key) */
static const byte pc1[] = {
       57, 49, 41, 33, 25, 17,  9,
        1, 58, 50, 42, 34, 26, 18,
       10,  2, 59, 51, 43, 35, 27,
       19, 11,  3, 60, 52, 44, 36,

       63, 55, 47, 39, 31, 23, 15,
        7, 62, 54, 46, 38, 30, 22,
       14,  6, 61, 53, 45, 37, 29,
       21, 13,  5, 28, 20, 12,  4
};

/* number left rotations of pc1 */
static const byte totrot[] = {
       1,2,4,6,8,10,12,14,15,17,19,21,23,25,27,28
};

/* permuted choice key (table) */
static const byte pc2[] = {
       14, 17, 11, 24,  1,  5,
        3, 28, 15,  6, 21, 10,
       23, 19, 12,  4, 26,  8,
       16,  7, 27, 20, 13,  2,
       41, 52, 31, 37, 47, 55,
       30, 40, 51, 45, 33, 48,
       44, 49, 39, 56, 34, 53,
       46, 42, 50, 36, 29, 32
};

/* End of DES-defined tables */

/* bit 0 is left-most in byte */
static const int bytebit[] = {
       0200,0100,040,020,010,04,02,01
};

const word32 Spbox[8][64] = {
{
0x01010400,0x00000000,0x00010000,0x01010404,
0x01010004,0x00010404,0x00000004,0x00010000,
0x00000400,0x01010400,0x01010404,0x00000400,
0x01000404,0x01010004,0x01000000,0x00000004,
0x00000404,0x01000400,0x01000400,0x00010400,
0x00010400,0x01010000,0x01010000,0x01000404,
0x00010004,0x01000004,0x01000004,0x00010004,
0x00000000,0x00000404,0x00010404,0x01000000,
0x00010000,0x01010404,0x00000004,0x01010000,
0x01010400,0x01000000,0x01000000,0x00000400,
0x01010004,0x00010000,0x00010400,0x01000004,
0x00000400,0x00000004,0x01000404,0x00010404,
0x01010404,0x00010004,0x01010000,0x01000404,
0x01000004,0x00000404,0x00010404,0x01010400,
0x00000404,0x01000400,0x01000400,0x00000000,
0x00010004,0x00010400,0x00000000,0x01010004},
{
0x80108020,0x80008000,0x00008000,0x00108020,
0x00100000,0x00000020,0x80100020,0x80008020,
0x80000020,0x80108020,0x80108000,0x80000000,
0x80008000,0x00100000,0x00000020,0x80100020,
0x00108000,0x00100020,0x80008020,0x00000000,
0x80000000,0x00008000,0x00108020,0x80100000,
0x00100020,0x80000020,0x00000000,0x00108000,
0x00008020,0x80108000,0x80100000,0x00008020,
0x00000000,0x00108020,0x80100020,0x00100000,
0x80008020,0x80100000,0x80108000,0x00008000,
0x80100000,0x80008000,0x00000020,0x80108020,
0x00108020,0x00000020,0x00008000,0x80000000,
0x00008020,0x80108000,0x00100000,0x80000020,
0x00100020,0x80008020,0x80000020,0x00100020,
0x00108000,0x00000000,0x80008000,0x00008020,
0x80000000,0x80100020,0x80108020,0x00108000},
{
0x00000208,0x08020200,0x00000000,0x08020008,
0x08000200,0x00000000,0x00020208,0x08000200,
0x00020008,0x08000008,0x08000008,0x00020000,
0x08020208,0x00020008,0x08020000,0x00000208,
0x08000000,0x00000008,0x08020200,0x00000200,
0x00020200,0x08020000,0x08020008,0x00020208,
0x08000208,0x00020200,0x00020000,0x08000208,
0x00000008,0x08020208,0x00000200,0x08000000,
0x08020200,0x08000000,0x00020008,0x00000208,
0x00020000,0x08020200,0x08000200,0x00000000,
0x00000200,0x00020008,0x08020208,0x08000200,
0x08000008,0x00000200,0x00000000,0x08020008,
0x08000208,0x00020000,0x08000000,0x08020208,
0x00000008,0x00020208,0x00020200,0x08000008,
0x08020000,0x08000208,0x00000208,0x08020000,
0x00020208,0x00000008,0x08020008,0x00020200},
{
0x00802001,0x00002081,0x00002081,0x00000080,
0x00802080,0x00800081,0x00800001,0x00002001,
0x00000000,0x00802000,0x00802000,0x00802081,
0x00000081,0x00000000,0x00800080,0x00800001,
0x00000001,0x00002000,0x00800000,0x00802001,
0x00000080,0x00800000,0x00002001,0x00002080,
0x00800081,0x00000001,0x00002080,0x00800080,
0x00002000,0x00802080,0x00802081,0x00000081,
0x00800080,0x00800001,0x00802000,0x00802081,
0x00000081,0x00000000,0x00000000,0x00802000,
0x00002080,0x00800080,0x00800081,0x00000001,
0x00802001,0x00002081,0x00002081,0x00000080,
0x00802081,0x00000081,0x00000001,0x00002000,
0x00800001,0x00002001,0x00802080,0x00800081,
0x00002001,0x00002080,0x00800000,0x00802001,
0x00000080,0x00800000,0x00002000,0x00802080},
{
0x00000100,0x02080100,0x02080000,0x42000100,
0x00080000,0x00000100,0x40000000,0x02080000,
0x40080100,0x00080000,0x02000100,0x40080100,
0x42000100,0x42080000,0x00080100,0x40000000,
0x02000000,0x40080000,0x40080000,0x00000000,
0x40000100,0x42080100,0x42080100,0x02000100,
0x42080000,0x40000100,0x00000000,0x42000000,
0x02080100,0x02000000,0x42000000,0x00080100,
0x00080000,0x42000100,0x00000100,0x02000000,
0x40000000,0x02080000,0x42000100,0x40080100,
0x02000100,0x40000000,0x42080000,0x02080100,
0x40080100,0x00000100,0x02000000,0x42080000,
0x42080100,0x00080100,0x42000000,0x42080100,
0x02080000,0x00000000,0x40080000,0x42000000,
0x00080100,0x02000100,0x40000100,0x00080000,
0x00000000,0x40080000,0x02080100,0x40000100},
{
0x20000010,0x20400000,0x00004000,0x20404010,
0x20400000,0x00000010,0x20404010,0x00400000,
0x20004000,0x00404010,0x00400000,0x20000010,
0x00400010,0x20004000,0x20000000,0x00004010,
0x00000000,0x00400010,0x20004010,0x00004000,
0x00404000,0x20004010,0x00000010,0x20400010,
0x20400010,0x00000000,0x00404010,0x20404000,
0x00004010,0x00404000,0x20404000,0x20000000,
0x20004000,0x00000010,0x20400010,0x00404000,
0x20404010,0x00400000,0x00004010,0x20000010,
0x00400000,0x20004000,0x20000000,0x00004010,
0x20000010,0x20404010,0x00404000,0x20400000,
0x00404010,0x20404000,0x00000000,0x20400010,
0x00000010,0x00004000,0x20400000,0x00404010,
0x00004000,0x00400010,0x20004010,0x00000000,
0x20404000,0x20000000,0x00400010,0x20004010},
{
0x00200000,0x04200002,0x04000802,0x00000000,
0x00000800,0x04000802,0x00200802,0x04200800,
0x04200802,0x00200000,0x00000000,0x04000002,
0x00000002,0x04000000,0x04200002,0x00000802,
0x04000800,0x00200802,0x00200002,0x04000800,
0x04000002,0x04200000,0x04200800,0x00200002,
0x04200000,0x00000800,0x00000802,0x04200802,
0x00200800,0x00000002,0x04000000,0x00200800,
0x04000000,0x00200800,0x00200000,0x04000802,
0x04000802,0x04200002,0x04200002,0x00000002,
0x00200002,0x04000000,0x04000800,0x00200000,
0x04200800,0x00000802,0x00200802,0x04200800,
0x00000802,0x04000002,0x04200802,0x04200000,
0x00200800,0x00000000,0x00000002,0x04200802,
0x00000000,0x00200802,0x04200000,0x00000800,
0x04000002,0x04000800,0x00000800,0x00200002},
{
0x10001040,0x00001000,0x00040000,0x10041040,
0x10000000,0x10001040,0x00000040,0x10000000,
0x00040040,0x10040000,0x10041040,0x00041000,
0x10041000,0x00041040,0x00001000,0x00000040,
0x10040000,0x10000040,0x10001000,0x00001040,
0x00041000,0x00040040,0x10040040,0x10041000,
0x00001040,0x00000000,0x00000000,0x10040040,
0x10000040,0x10001000,0x00041040,0x00040000,
0x00041040,0x00040000,0x10041000,0x00001000,
0x00000040,0x10040040,0x00001000,0x00041040,
0x10001000,0x00000040,0x10000040,0x10040000,
0x10040040,0x10000000,0x00040000,0x10001040,
0x00000000,0x10041040,0x00040040,0x10000040,
0x10040000,0x10001000,0x10001040,0x00000000,
0x10041040,0x00041000,0x00041000,0x00001040,
0x00001040,0x00040040,0x10000000,0x10041000}
};


static INLINE void IPERM(word32* left, word32* right)
{
    word32 work;

    *right = rotlFixed(*right, 4U);
    work = (*left ^ *right) & 0xf0f0f0f0;
    *left ^= work;

    *right = rotrFixed(*right^work, 20U);
    work = (*left ^ *right) & 0xffff0000;
    *left ^= work;

    *right = rotrFixed(*right^work, 18U);
    work = (*left ^ *right) & 0x33333333;
    *left ^= work;

    *right = rotrFixed(*right^work, 6U);
    work = (*left ^ *right) & 0x00ff00ff;
    *left ^= work;

    *right = rotlFixed(*right^work, 9U);
    work = (*left ^ *right) & 0xaaaaaaaa;
    *left = rotlFixed(*left^work, 1U);
    *right ^= work;
}


static INLINE void FPERM(word32* left, word32* right)
{
    word32 work;

    *right = rotrFixed(*right, 1U);
    work = (*left ^ *right) & 0xaaaaaaaa;
    *right ^= work;

    *left = rotrFixed(*left^work, 9U);
    work = (*left ^ *right) & 0x00ff00ff;
    *right ^= work;

    *left = rotlFixed(*left^work, 6U);
    work = (*left ^ *right) & 0x33333333;
    *right ^= work;

    *left = rotlFixed(*left^work, 18U);
    work = (*left ^ *right) & 0xffff0000;
    *right ^= work;

    *left = rotlFixed(*left^work, 20U);
    work = (*left ^ *right) & 0xf0f0f0f0;
    *right ^= work;

    *left = rotrFixed(*left^work, 4U);
}


static void DesSetKey(const byte* key, int dir, word32* out)
{
    byte buffer[56+56+8];
    byte *const pc1m = buffer;                 /* place to modify pc1 into */
    byte *const pcr = pc1m + 56;               /* place to rotate pc1 into */
    byte *const ks = pcr + 56;
    register int i,j,l;
    int m;

    for (j = 0; j < 56; j++) {          /* convert pc1 to bits of key */
        l = pc1[j] - 1;                 /* integer bit location  */
        m = l & 07;                     /* find bit              */
        pc1m[j] = (key[l >> 3] &        /* find which key byte l is in */
            bytebit[m])                 /* and which bit of that byte */
            ? 1 : 0;                    /* and store 1-bit result */
    }
    for (i = 0; i < 16; i++) {          /* key chunk for each iteration */
        XMEMSET(ks, 0, 8);               /* Clear key schedule */
        for (j = 0; j < 56; j++)        /* rotate pc1 the right amount */
            pcr[j] = pc1m[(l = j + totrot[i]) < (j < 28 ? 28 : 56) ? l: l-28];
        /* rotate left and right halves independently */
        for (j = 0; j < 48; j++){   /* select bits individually */
            /* check bit that goes to ks[j] */
            if (pcr[pc2[j] - 1]){
                /* mask it in if it's there */
                l= j % 6;
                ks[j/6] |= bytebit[l] >> 2;
            }
        }
        /* Now convert to odd/even interleaved form for use in F */
        out[2*i] = ((word32)ks[0] << 24)
            | ((word32)ks[2] << 16)
            | ((word32)ks[4] << 8)
            | ((word32)ks[6]);
        out[2*i + 1] = ((word32)ks[1] << 24)
            | ((word32)ks[3] << 16)
            | ((word32)ks[5] << 8)
            | ((word32)ks[7]);
    }
    
    /* reverse key schedule order */
    if (dir == DES_DECRYPTION)
        for (i = 0; i < 16; i += 2) {
            word32 swap = out[i];
            out[i] = out[DES_KS_SIZE - 2 - i];
            out[DES_KS_SIZE - 2 - i] = swap;

            swap = out[i + 1];
            out[i + 1] = out[DES_KS_SIZE - 1 - i];
            out[DES_KS_SIZE - 1 - i] = swap;
        }
   
}


static INLINE int Reverse(int dir)
{
    return !dir;
}


void Des_SetIV(Des* des, const byte* iv)
{
    if (des && iv)
        XMEMCPY(des->reg, iv, DES_BLOCK_SIZE);
}


void Des3_SetIV(Des3* des, const byte* iv)
{
    if (des && iv)
        XMEMCPY(des->reg, iv, DES_BLOCK_SIZE);
}


void Des_SetKey(Des* des, const byte* key, const byte* iv, int dir)
{
    DesSetKey(key, dir, des->key);

    Des_SetIV(des, iv);
}


void Des3_SetKey(Des3* des, const byte* key, const byte* iv, int dir)
{
    DesSetKey(key + (dir == DES_ENCRYPTION ? 0 : 16), dir, des->key[0]);
    DesSetKey(key + 8, Reverse(dir), des->key[1]);
    DesSetKey(key + (dir == DES_DECRYPTION ? 0 : 16), dir, des->key[2]);

    Des3_SetIV(des, iv);  
}


static void DesRawProcessBlock(word32* lIn, word32* rIn, const word32* kptr)
{
    word32 l = *lIn, r = *rIn, i;

    for (i=0; i<8; i++)
    {
        word32 work = rotrFixed(r, 4U) ^ kptr[4*i+0];
        l ^= Spbox[6][(work) & 0x3f]
          ^  Spbox[4][(work >> 8) & 0x3f]
          ^  Spbox[2][(work >> 16) & 0x3f]
          ^  Spbox[0][(work >> 24) & 0x3f];
        work = r ^ kptr[4*i+1];
        l ^= Spbox[7][(work) & 0x3f]
          ^  Spbox[5][(work >> 8) & 0x3f]
          ^  Spbox[3][(work >> 16) & 0x3f]
          ^  Spbox[1][(work >> 24) & 0x3f];

        work = rotrFixed(l, 4U) ^ kptr[4*i+2];
        r ^= Spbox[6][(work) & 0x3f]
          ^  Spbox[4][(work >> 8) & 0x3f]
          ^  Spbox[2][(work >> 16) & 0x3f]
          ^  Spbox[0][(work >> 24) & 0x3f];
        work = l ^ kptr[4*i+3];
        r ^= Spbox[7][(work) & 0x3f]
          ^  Spbox[5][(work >> 8) & 0x3f]
          ^  Spbox[3][(work >> 16) & 0x3f]
          ^  Spbox[1][(work >> 24) & 0x3f];
    }

    *lIn = l; *rIn = r;
}


static void DesProcessBlock(Des* des, const byte* in, byte* out)
{
    word32 l, r;

    XMEMCPY(&l, in, sizeof(l));
    XMEMCPY(&r, in + sizeof(l), sizeof(r));
    #ifdef LITTLE_ENDIAN_ORDER
        l = ByteReverseWord32(l);
        r = ByteReverseWord32(r);
    #endif
    IPERM(&l,&r);
    
    DesRawProcessBlock(&l, &r, des->key);   

    FPERM(&l,&r);
    #ifdef LITTLE_ENDIAN_ORDER
        l = ByteReverseWord32(l);
        r = ByteReverseWord32(r);
    #endif
    XMEMCPY(out, &r, sizeof(r));
    XMEMCPY(out + sizeof(r), &l, sizeof(l));
}


static void Des3ProcessBlock(Des3* des, const byte* in, byte* out)
{
    word32 l, r;

    XMEMCPY(&l, in, sizeof(l));
    XMEMCPY(&r, in + sizeof(l), sizeof(r));
    #ifdef LITTLE_ENDIAN_ORDER
        l = ByteReverseWord32(l);
        r = ByteReverseWord32(r);
    #endif
    IPERM(&l,&r);
    
    DesRawProcessBlock(&l, &r, des->key[0]);   
    DesRawProcessBlock(&r, &l, des->key[1]);   
    DesRawProcessBlock(&l, &r, des->key[2]);   

    FPERM(&l,&r);
    #ifdef LITTLE_ENDIAN_ORDER
        l = ByteReverseWord32(l);
        r = ByteReverseWord32(r);
    #endif
    XMEMCPY(out, &r, sizeof(r));
    XMEMCPY(out + sizeof(r), &l, sizeof(l));
}


void Des_CbcEncrypt(Des* des, byte* out, const byte* in, word32 sz)
{
    word32 blocks = sz / DES_BLOCK_SIZE;

    while (blocks--) {
        xorbuf((byte*)des->reg, in, DES_BLOCK_SIZE);
        DesProcessBlock(des, (byte*)des->reg, (byte*)des->reg);
        XMEMCPY(out, des->reg, DES_BLOCK_SIZE);

        out += DES_BLOCK_SIZE;
        in  += DES_BLOCK_SIZE; 
    }
}


void Des_CbcDecrypt(Des* des, byte* out, const byte* in, word32 sz)
{
    word32 blocks = sz / DES_BLOCK_SIZE;
    byte   hold[16];

    while (blocks--) {
        XMEMCPY(des->tmp, in, DES_BLOCK_SIZE);
        DesProcessBlock(des, (byte*)des->tmp, out);
        xorbuf(out, (byte*)des->reg, DES_BLOCK_SIZE);

        XMEMCPY(hold, des->reg, DES_BLOCK_SIZE);
        XMEMCPY(des->reg, des->tmp, DES_BLOCK_SIZE);
        XMEMCPY(des->tmp, hold, DES_BLOCK_SIZE);

        out += DES_BLOCK_SIZE;
        in  += DES_BLOCK_SIZE; 
    }
}


void Des3_CbcEncrypt(Des3* des, byte* out, const byte* in, word32 sz)
{
    word32 blocks = sz / DES_BLOCK_SIZE;

    while (blocks--) {
        xorbuf((byte*)des->reg, in, DES_BLOCK_SIZE);
        Des3ProcessBlock(des, (byte*)des->reg, (byte*)des->reg);
        XMEMCPY(out, des->reg, DES_BLOCK_SIZE);

        out += DES_BLOCK_SIZE;
        in  += DES_BLOCK_SIZE; 
    }
}


void Des3_CbcDecrypt(Des3* des, byte* out, const byte* in, word32 sz)
{
    word32 blocks = sz / DES_BLOCK_SIZE;

    while (blocks--) {
        XMEMCPY(des->tmp, in, DES_BLOCK_SIZE);
        Des3ProcessBlock(des, (byte*)des->tmp, out);
        xorbuf(out, (byte*)des->reg, DES_BLOCK_SIZE);
        XMEMCPY(des->reg, des->tmp, DES_BLOCK_SIZE);

        out += DES_BLOCK_SIZE;
        in  += DES_BLOCK_SIZE; 
    }
}

#ifdef CYASSL_DES_ECB

/* One block, compatibility only */
void Des_EcbEncrypt(Des* des, byte* out, const byte* in, word32 sz)
{
    word32 blocks = sz / DES_BLOCK_SIZE;

    while (blocks--) {
        DesProcessBlock(des, in, out);

        out += DES_BLOCK_SIZE;
        in  += DES_BLOCK_SIZE; 
    }
}

#endif /* CYASSL_DES_ECB */


#endif /* NO_DES3 */
