/* coding.c
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
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


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifndef NO_CODING

#include <wolfssl/wolfcrypt/coding.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/logging.h>
#ifndef NO_ASN
    #include <wolfssl/wolfcrypt/asn.h> /* For PEM_LINE_SZ */
#endif

enum {
    BAD         = 0xFF,  /* invalid encoding */
    PAD         = '=',
    BASE64_MIN  = 0x2B,
    BASE16_MIN  = 0x30,
};


#ifndef BASE64_LINE_SZ
    #ifdef NO_ASN
        #define BASE64_LINE_SZ 64
    #else
        #define BASE64_LINE_SZ PEM_LINE_SZ
    #endif
#endif

#ifdef WOLFSSL_BASE64_DECODE

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

static WC_INLINE int Base64_SkipNewline(const byte* in, word32 *inLen, word32 *outJ)
{
    word32 len = *inLen;
    word32 j = *outJ;
    if (len && (in[j] == ' ' || in[j] == '\r' || in[j] == '\n')) {
        byte endLine = in[j++];
        len--;
        while (len && endLine == ' ') {   /* allow trailing whitespace */
            endLine = in[j++];
            len--;
        }
        if (endLine == '\r') {
            if (len) {
                endLine = in[j++];
                len--;
            }
        }
        if (endLine != '\n') {
            WOLFSSL_MSG("Bad end of line in Base64 Decode");
            return ASN_INPUT_E;
        }
    }
    if (!len) {
        return BUFFER_E;
    }
    *inLen = len;
    *outJ = j;
    return 0;
}

int Base64_Decode(const byte* in, word32 inLen, byte* out, word32* outLen)
{
    word32 i = 0;
    word32 j = 0;
    word32 plainSz = inLen - ((inLen + (BASE64_LINE_SZ - 1)) / BASE64_LINE_SZ );
    int ret;
    const byte maxIdx = (byte)sizeof(base64Decode) + BASE64_MIN - 1;

    plainSz = (plainSz * 3 + 3) / 4;
    if (plainSz > *outLen) return BAD_FUNC_ARG;

    while (inLen > 3) {
        int pad3 = 0;
        int pad4 = 0;

        byte b1, b2, b3;
        byte e1, e2, e3, e4;
        if ((ret = Base64_SkipNewline(in, &inLen, &j)) != 0) {
            if (ret == BUFFER_E) {
                /* Running out of buffer here is not an error */
                break;
            }
            return ret;
        }
        e1 = in[j++];
        if (e1 == '\0') {
            break;
        }
        inLen--;
        if ((ret = Base64_SkipNewline(in, &inLen, &j)) != 0) {
            return ret;
        }
        e2 = in[j++];
        inLen--;
        if ((ret = Base64_SkipNewline(in, &inLen, &j)) != 0) {
            return ret;
        }
        e3 = in[j++];
        inLen--;
        if ((ret = Base64_SkipNewline(in, &inLen, &j)) != 0) {
            return ret;
        }
        e4 = in[j++];
        inLen--;

        if (e3 == PAD)
            pad3 = 1;
        if (e4 == PAD)
            pad4 = 1;

        if (e1 < BASE64_MIN || e2 < BASE64_MIN || e3 < BASE64_MIN || e4 < BASE64_MIN) {
            WOLFSSL_MSG("Bad Base64 Decode data, too small");
            return ASN_INPUT_E;
        }

        if (e1 > maxIdx || e2 > maxIdx || e3 > maxIdx || e4 > maxIdx) {
            WOLFSSL_MSG("Bad Base64 Decode data, too big");
            return ASN_INPUT_E;
        }

        if (i + 1 + !pad3 + !pad4 > *outLen) {
            WOLFSSL_MSG("Bad Base64 Decode out buffer, too small");
            return BAD_FUNC_ARG;
        }

        e1 = base64Decode[e1 - BASE64_MIN];
        e2 = base64Decode[e2 - BASE64_MIN];
        e3 = (e3 == PAD) ? 0 : base64Decode[e3 - BASE64_MIN];
        e4 = (e4 == PAD) ? 0 : base64Decode[e4 - BASE64_MIN];

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
    }
/* If the output buffer has a room for an extra byte, add a null terminator */
    if (out && *outLen > i)
        out[i]= '\0';

    *outLen = i;

    return 0;
}

#endif /* WOLFSSL_BASE64_DECODE */

#if defined(WOLFSSL_BASE64_ENCODE)

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
                  int raw, int getSzOnly)
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

    /* check whether to escape. Only escape for EncodeEsc */
    if (escaped == WC_ESC_NL_ENC) {
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
    if ( (idx+needed) > max && !getSzOnly) {
        WOLFSSL_MSG("Escape buffer max too small");
        return BUFFER_E;
    }

    /* store it */
    if (doEscape == 0) {
        if(getSzOnly)
            idx++;
        else
            out[idx++] = basic;
    }
    else {
        if(getSzOnly)
            idx+=3;
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
    }
    *i = idx;

    return 0;
}


/* internal worker, handles both escaped and normal line endings.
   If out buffer is NULL, will return sz needed in outLen */
static int DoBase64_Encode(const byte* in, word32 inLen, byte* out,
                           word32* outLen, int escaped)
{
    int    ret = 0;
    word32 i = 0,
           j = 0,
           n = 0;   /* new line counter */

    int    getSzOnly = (out == NULL);

    word32 outSz = (inLen + 3 - 1) / 3 * 4;
    word32 addSz = (outSz + BASE64_LINE_SZ - 1) / BASE64_LINE_SZ;  /* new lines */

    if (escaped == WC_ESC_NL_ENC)
        addSz *= 3;   /* instead of just \n, we're doing %0A triplet */
    else if (escaped == WC_NO_NL_ENC)
        addSz = 0;    /* encode without \n */

    outSz += addSz;

    /* if escaped we can't predetermine size for one pass encoding, but
     * make sure we have enough if no escapes are in input
     * Also need to ensure outLen valid before dereference */
    if (!outLen || (outSz > *outLen && !getSzOnly)) return BAD_FUNC_ARG;

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
        ret = CEscape(escaped, e1, out, &i, *outLen, 0, getSzOnly);
        if (ret != 0) break;
        ret = CEscape(escaped, e2, out, &i, *outLen, 0, getSzOnly);
        if (ret != 0) break;
        ret = CEscape(escaped, e3, out, &i, *outLen, 0, getSzOnly);
        if (ret != 0) break;
        ret = CEscape(escaped, e4, out, &i, *outLen, 0, getSzOnly);
        if (ret != 0) break;

        inLen -= 3;

        /* Insert newline after BASE64_LINE_SZ, unless no \n requested */
        if (escaped != WC_NO_NL_ENC && (++n % (BASE64_LINE_SZ/4)) == 0 && inLen) {
            ret = CEscape(escaped, '\n', out, &i, *outLen, 1, getSzOnly);
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

        ret = CEscape(escaped, e1, out, &i, *outLen, 0, getSzOnly);
        if (ret == 0)
            ret = CEscape(escaped, e2, out, &i, *outLen, 0, getSzOnly);
        if (ret == 0) {
            /* third */
            if (twoBytes)
                ret = CEscape(escaped, e3, out, &i, *outLen, 0, getSzOnly);
            else
                ret = CEscape(escaped, '=', out, &i, *outLen, 1, getSzOnly);
        }
        /* fourth always pad */
        if (ret == 0)
            ret = CEscape(escaped, '=', out, &i, *outLen, 1, getSzOnly);
    }

    if (ret == 0 && escaped != WC_NO_NL_ENC)
        ret = CEscape(escaped, '\n', out, &i, *outLen, 1, getSzOnly);

    if (i != outSz && escaped != 1 && ret == 0)
        return ASN_INPUT_E;
/* If the output buffer has a room for an extra byte, add a null terminator */
    if (out && *outLen > i)
        out[i]= '\0';

    *outLen = i;

    if (ret == 0)
        return getSzOnly ? LENGTH_ONLY_E : 0;

    return ret;
}


/* Base64 Encode, PEM style, with \n line endings */
int Base64_Encode(const byte* in, word32 inLen, byte* out, word32* outLen)
{
    return DoBase64_Encode(in, inLen, out, outLen, WC_STD_ENC);
}


/* Base64 Encode, with %0A escaped line endings instead of \n */
int Base64_EncodeEsc(const byte* in, word32 inLen, byte* out, word32* outLen)
{
    return DoBase64_Encode(in, inLen, out, outLen, WC_ESC_NL_ENC);
}

int Base64_Encode_NoNl(const byte* in, word32 inLen, byte* out, word32* outLen)
{
    return DoBase64_Encode(in, inLen, out, outLen, WC_NO_NL_ENC);
}

#endif /* WOLFSSL_BASE64_ENCODE */


#ifdef WOLFSSL_BASE16

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

    if (in == NULL || out == NULL || outLen == NULL)
        return BAD_FUNC_ARG;

    if (inLen == 1 && *outLen && in) {
        byte b = in[inIdx++] - BASE16_MIN;  /* 0 starts at 0x30 */

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
        byte b  = in[inIdx++] - BASE16_MIN;  /* 0 starts at 0x30 */
        byte b2 = in[inIdx++] - BASE16_MIN;

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

int Base16_Encode(const byte* in, word32 inLen, byte* out, word32* outLen)
{
    word32 outIdx = 0;
    word32 i;
    byte   hb, lb;

    if (in == NULL || out == NULL || outLen == NULL)
        return BAD_FUNC_ARG;

    if (*outLen < (2 * inLen + 1))
        return BAD_FUNC_ARG;

    for (i = 0; i < inLen; i++) {
        hb = in[i] >> 4;
        lb = in[i] & 0x0f;

        /* ASCII value */
        hb += '0';
        if (hb > '9')
            hb += 7;

        /* ASCII value */
        lb += '0';
        if (lb>'9')
            lb += 7;

        out[outIdx++] = hb;
        out[outIdx++] = lb;
    }

    /* force 0 at this end */
    out[outIdx++] = 0;

    *outLen = outIdx;
    return 0;
}

#endif /* WOLFSSL_BASE16 */

#endif /* !NO_CODING */
