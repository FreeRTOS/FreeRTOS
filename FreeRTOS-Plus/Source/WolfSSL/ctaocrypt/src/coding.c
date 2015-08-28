/* coding.c
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

#ifndef NO_CODING

#include <cyassl/ctaocrypt/coding.h>
#include <cyassl/ctaocrypt/error-crypt.h>
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

        b1 = (byte)((e1 << 2) | (e2 >> 4));
        b2 = (byte)(((e2 & 0xF) << 4) | (e3 >> 2));
        b3 = (byte)(((e3 & 0x3) << 6) | e4);

        out[i++] = b1;
        if (!pad3)
            out[i++] = b2;
        if (!pad4)
            out[i++] = b3;
        else
            break;
        
        inLen -= 4;
        if (inLen && (in[j] == ' ' || in[j] == '\r' || in[j] == '\n')) {
            byte endLine = in[j++];
            inLen--;
            while (inLen && endLine == ' ') {   /* allow trailing whitespace */
                endLine = in[j++];
                inLen--;
            }
            if (endLine == '\r') {
                if (inLen) {
                    endLine = in[j++];
                    inLen--;
                }
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


/* make sure *i (idx) won't exceed max, store and possibly escape to out,
 * raw means use e w/o decode,  0 on success */
static int CEscape(int escaped, byte e, byte* out, word32* i, word32 max,
                  int raw)
{
    int    doEscape = 0;
    word32 needed = 1;
    word32 idx = *i;

    byte basic;
    byte plus    = 0;
    byte equals  = 0;
    byte newline = 0;

    if (raw)
        basic = e;
    else
        basic = base64Encode[e];

    /* check whether to escape */
    if (escaped) {
        switch ((char)basic) {
            case '+' :
                plus     = 1;
                doEscape = 1;
                needed  += 2;
                break;
            case '=' :
                equals   = 1;
                doEscape = 1;
                needed  += 2;
                break;
            case '\n' :
                newline  = 1;
                doEscape = 1;
                needed  += 2;
                break;
            default:
                /* do nothing */
                break;
        }
    }

    /* check size */
    if ( (idx+needed) > max) {
        CYASSL_MSG("Escape buffer max too small");
        return BUFFER_E;
    }

    /* store it */
    if (doEscape == 0) {
        out[idx++] = basic;
    }
    else {
        out[idx++] = '%';  /* start escape */

        if (plus) {
            out[idx++] = '2';
            out[idx++] = 'B';
        }
        else if (equals) {
            out[idx++] = '3';
            out[idx++] = 'D';
        }
        else if (newline) {
            out[idx++] = '0';
            out[idx++] = 'A';
        }

    }
    *i = idx;

    return 0;
}


/* internal worker, handles both escaped and normal line endings */
static int DoBase64_Encode(const byte* in, word32 inLen, byte* out,
                           word32* outLen, int escaped)
{
    int    ret = 0;
    word32 i = 0,
           j = 0,
           n = 0;   /* new line counter */

    word32 outSz = (inLen + 3 - 1) / 3 * 4;
    word32 addSz = (outSz + PEM_LINE_SZ - 1) / PEM_LINE_SZ;  /* new lines */

    if (escaped)
        addSz *= 3;   /* instead of just \n, we're doing %0A triplet */

    outSz += addSz;

    /* if escaped we can't predetermine size for one pass encoding, but
     * make sure we have enough if no escapes are in input */
    if (outSz > *outLen) return BAD_FUNC_ARG;
    
    while (inLen > 2) {
        byte b1 = in[j++];
        byte b2 = in[j++];
        byte b3 = in[j++];

        /* encoded idx */
        byte e1 = b1 >> 2;
        byte e2 = (byte)(((b1 & 0x3) << 4) | (b2 >> 4));
        byte e3 = (byte)(((b2 & 0xF) << 2) | (b3 >> 6));
        byte e4 = b3 & 0x3F;

        /* store */
        ret = CEscape(escaped, e1, out, &i, *outLen, 0);
        if (ret != 0) break;
        ret = CEscape(escaped, e2, out, &i, *outLen, 0);
        if (ret != 0) break;
        ret = CEscape(escaped, e3, out, &i, *outLen, 0);
        if (ret != 0) break;
        ret = CEscape(escaped, e4, out, &i, *outLen, 0);
        if (ret != 0) break;

        inLen -= 3;

        if ((++n % (PEM_LINE_SZ / 4)) == 0 && inLen) {
            ret = CEscape(escaped, '\n', out, &i, *outLen, 1);
            if (ret != 0) break;
        }
    }

    /* last integral */
    if (inLen && ret == 0) {
        int twoBytes = (inLen == 2);

        byte b1 = in[j++];
        byte b2 = (twoBytes) ? in[j++] : 0;

        byte e1 = b1 >> 2;
        byte e2 = (byte)(((b1 & 0x3) << 4) | (b2 >> 4));
        byte e3 = (byte)((b2 & 0xF) << 2);

        ret = CEscape(escaped, e1, out, &i, *outLen, 0);
        if (ret == 0) 
            ret = CEscape(escaped, e2, out, &i, *outLen, 0);
        if (ret == 0) {
            /* third */
            if (twoBytes)
                ret = CEscape(escaped, e3, out, &i, *outLen, 0);
            else 
                ret = CEscape(escaped, '=', out, &i, *outLen, 1);
        }
        /* fourth always pad */
        if (ret == 0)
            ret = CEscape(escaped, '=', out, &i, *outLen, 1);
    } 

    if (ret == 0) 
        ret = CEscape(escaped, '\n', out, &i, *outLen, 1);

    if (i != outSz && escaped == 0 && ret == 0)
        return ASN_INPUT_E; 

    *outLen = i;
    return ret; 
}


/* Base64 Encode, PEM style, with \n line endings */
int Base64_Encode(const byte* in, word32 inLen, byte* out, word32* outLen)
{
    return DoBase64_Encode(in, inLen, out, outLen, 0);
}


/* Base64 Encode, with %0A esacped line endings instead of \n */
int Base64_EncodeEsc(const byte* in, word32 inLen, byte* out, word32* outLen)
{
    return DoBase64_Encode(in, inLen, out, outLen, 1);
}


#endif  /* defined(OPENSSL_EXTRA) || defined (SESSION_CERTS) || defined(CYASSL_KEY_GEN) || defined(CYASSL_CERT_GEN) || defined(HAVE_WEBSERVER) */


#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER) || defined(HAVE_FIPS)

static
const byte hexDecode[] = { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
                           BAD, BAD, BAD, BAD, BAD, BAD, BAD,
                           10, 11, 12, 13, 14, 15,  /* upper case A-F */
                           BAD, BAD, BAD, BAD, BAD, BAD, BAD, BAD,
                           BAD, BAD, BAD, BAD, BAD, BAD, BAD, BAD,
                           BAD, BAD, BAD, BAD, BAD, BAD, BAD, BAD,
                           BAD, BAD,  /* G - ` */
                           10, 11, 12, 13, 14, 15   /* lower case a-f */
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
        
        out[outIdx++] = (byte)((b << 4) | b2);
        inLen -= 2;
    }

    *outLen = outIdx;
    return 0;
}


#endif /* (OPENSSL_EXTRA) || (HAVE_WEBSERVER) || (HAVE_FIPS) */

#endif /* NO_CODING */
