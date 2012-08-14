/* coding.c
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

#include <cyassl/ctaocrypt/coding.h>
#include <cyassl/ctaocrypt/error.h>
#include <cyassl/ctaocrypt/logging.h>


enum {
    BAD         = 0xFF,  /* invalid encoding */
    PAD         = '=',
    PEM_LINE_SZ = 64
};


static
const byte base64Decode[] = { 62, BAD, BAD, BAD, 63,   /* + starts at 0x2B */
                              52, 53, 54, 55, 56, 57, 58, 59, 60, 61,
                              BAD, BAD, BAD, BAD, BAD, BAD, BAD,
                              0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
                              10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
                              20, 21, 22, 23, 24, 25,
                              BAD, BAD, BAD, BAD, BAD, BAD,
                              26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
                              36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
                              46, 47, 48, 49, 50, 51
                            };


int Base64_Decode(const byte* in, word32 inLen, byte* out, word32* outLen)
{
    word32 i = 0;
    word32 j = 0;
    word32 plainSz = inLen - ((inLen + (PEM_LINE_SZ - 1)) / PEM_LINE_SZ );
    const byte maxIdx = (byte)sizeof(base64Decode) + 0x2B - 1;

    plainSz = (plainSz * 3 + 3) / 4;
    if (plainSz > *outLen) return BAD_FUNC_ARG;

    while (inLen > 3) {
        byte b1, b2, b3;
        byte e1 = in[j++];
        byte e2 = in[j++];
        byte e3 = in[j++];
        byte e4 = in[j++];

        int pad3 = 0;
        int pad4 = 0;

        if (e1 == 0)            /* end file 0's */
            break;
        if (e3 == PAD)
            pad3 = 1;
        if (e4 == PAD)
            pad4 = 1;

        if (e1 < 0x2B || e2 < 0x2B || e3 < 0x2B || e4 < 0x2B) {
            CYASSL_MSG("Bad Base64 Decode data, too small");
            return ASN_INPUT_E;
        }

        if (e1 > maxIdx || e2 > maxIdx || e3 > maxIdx || e4 > maxIdx) {
            CYASSL_MSG("Bad Base64 Decode data, too big");
            return ASN_INPUT_E;
        }

        e1 = base64Decode[e1 - 0x2B];
        e2 = base64Decode[e2 - 0x2B];
        e3 = (e3 == PAD) ? 0 : base64Decode[e3 - 0x2B];
        e4 = (e4 == PAD) ? 0 : base64Decode[e4 - 0x2B];

        b1 = (e1 << 2) | (e2 >> 4);
        b2 = ((e2 & 0xF) << 4) | (e3 >> 2);
        b3 = ((e3 & 0x3) << 6) | e4;

        out[i++] = b1;
        if (!pad3)
            out[i++] = b2;
        if (!pad4)
            out[i++] = b3;
        else
            break;
        
        inLen -= 4;
        if (in[j] == ' ' || in[j] == '\r' || in[j] == '\n') {
            byte endLine = in[j++];
            inLen--;
            while (endLine == ' ') {   /* allow trailing whitespace */
                endLine = in[j++];
                inLen--;
            }
            if (endLine == '\r') {
                endLine = in[j++];
                inLen--;
            }
            if (endLine != '\n') {
                CYASSL_MSG("Bad end of line in Base64 Decode");
                return ASN_INPUT_E;
            }
        }
    }
    *outLen = i;

    return 0;
}


#if defined(OPENSSL_EXTRA) || defined (SESSION_CERTS) || defined(CYASSL_KEY_GEN) || defined(CYASSL_CERT_GEN) || defined(HAVE_WEBSERVER)

static
const byte base64Encode[] = { 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J',
                              'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T',
                              'U', 'V', 'W', 'X', 'Y', 'Z',
                              'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j',
                              'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't',
                              'u', 'v', 'w', 'x', 'y', 'z',
                              '0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
                              '+', '/'
                            };


/* porting assistance from yaSSL by Raphael HUCK */
int Base64_Encode(const byte* in, word32 inLen, byte* out, word32* outLen)
{
    word32 i = 0,
           j = 0,
           n = 0;   /* new line counter */

    word32 outSz = (inLen + 3 - 1) / 3 * 4;
    outSz += (outSz + PEM_LINE_SZ - 1) / PEM_LINE_SZ;  /* new lines */

    if (outSz > *outLen) return BAD_FUNC_ARG;
    
    while (inLen > 2) {
        byte b1 = in[j++];
        byte b2 = in[j++];
        byte b3 = in[j++];

        /* encoded idx */
        byte e1 = b1 >> 2;
        byte e2 = ((b1 & 0x3) << 4) | (b2 >> 4);
        byte e3 = ((b2 & 0xF) << 2) | (b3 >> 6);
        byte e4 = b3 & 0x3F;

        /* store */
        out[i++] = base64Encode[e1];
        out[i++] = base64Encode[e2];
        out[i++] = base64Encode[e3];
        out[i++] = base64Encode[e4];

        inLen -= 3;

        if ((++n % (PEM_LINE_SZ / 4)) == 0 && inLen)
            out[i++] = '\n';
    }

    /* last integral */
    if (inLen) {
        int twoBytes = (inLen == 2);

        byte b1 = in[j++];
        byte b2 = (twoBytes) ? in[j++] : 0;

        byte e1 = b1 >> 2;
        byte e2 = ((b1 & 0x3) << 4) | (b2 >> 4);
        byte e3 =  (b2 & 0xF) << 2;

        out[i++] = base64Encode[e1];
        out[i++] = base64Encode[e2];
        out[i++] = (twoBytes) ? base64Encode[e3] : PAD;
        out[i++] = PAD;
    } 

    out[i++] = '\n';
    if (i != outSz)
        return ASN_INPUT_E; 
    *outLen = outSz;

    return 0; 
}


static
const byte hexDecode[] = { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
                           BAD, BAD, BAD, BAD, BAD, BAD, BAD,
                           10, 11, 12, 13, 14, 15 
                         };  /* A starts at 0x41 not 0x3A */

int Base16_Decode(const byte* in, word32 inLen, byte* out, word32* outLen)
{
    word32 inIdx  = 0;
    word32 outIdx = 0;

    if (inLen == 1 && *outLen && in) {
        byte b = in[inIdx++] - 0x30;  /* 0 starts at 0x30 */

        /* sanity check */
        if (b >=  sizeof(hexDecode)/sizeof(hexDecode[0]))
            return ASN_INPUT_E;

        b  = hexDecode[b];

        if (b == BAD)
            return ASN_INPUT_E;
        
        out[outIdx++] = b;

        *outLen = outIdx;
        return 0;
    }

    if (inLen % 2)
        return BAD_FUNC_ARG;

    if (*outLen < (inLen / 2))
        return BAD_FUNC_ARG;

    while (inLen) {
        byte b  = in[inIdx++] - 0x30;  /* 0 starts at 0x30 */
        byte b2 = in[inIdx++] - 0x30;

        /* sanity checks */
        if (b >=  sizeof(hexDecode)/sizeof(hexDecode[0]))
            return ASN_INPUT_E;
        if (b2 >= sizeof(hexDecode)/sizeof(hexDecode[0]))
            return ASN_INPUT_E;

        b  = hexDecode[b];
        b2 = hexDecode[b2];

        if (b == BAD || b2 == BAD)
            return ASN_INPUT_E;
        
        out[outIdx++] = (b << 4) | b2;
        inLen -= 2;
    }

    *outLen = outIdx;
    return 0;
}


#endif  /* OPENSSL_EXTRA */
