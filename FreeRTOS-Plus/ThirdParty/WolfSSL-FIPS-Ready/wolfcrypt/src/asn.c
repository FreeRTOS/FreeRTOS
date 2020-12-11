/* asn.c
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

/*

DESCRIPTION
This library provides the interface to Abstract Syntax Notation One (ASN.1) objects.
ASN.1 is a standard interface description language for defining data structures
that can be serialized and deserialized in a cross-platform way.

*/
#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

/*
ASN Options:
 * NO_ASN_TIME: Disables time parts of the ASN code for systems without an RTC
    or wishing to save space.
 * IGNORE_NAME_CONSTRAINTS: Skip ASN name checks.
 * ASN_DUMP_OID: Allows dump of OID information for debugging.
 * RSA_DECODE_EXTRA: Decodes extra information in RSA public key.
 * WOLFSSL_CERT_GEN: Cert generation. Saves extra certificate info in GetName.
 * WOLFSSL_NO_ASN_STRICT: Disable strict RFC compliance checks to
    restore 3.13.0 behavior.
 * WOLFSSL_NO_OCSP_OPTIONAL_CERTS: Skip optional OCSP certs (responder issuer
    must still be trusted)
 * WOLFSSL_NO_TRUSTED_CERTS_VERIFY: Workaround for situation where entire cert
    chain is not loaded. This only matches on subject and public key and
    does not perform a PKI validation, so it is not a secure solution.
    Only enabled for OCSP.
 * WOLFSSL_NO_OCSP_ISSUER_CHECK: Can be defined for backwards compatibility to
    disable checking of OCSP subject hash with issuer hash.
 * WOLFSSL_SMALL_CERT_VERIFY: Verify the certificate signature without using
    DecodedCert. Doubles up on some code but allows smaller dynamic memory
    usage.
 * WOLFSSL_NO_OCSP_DATE_CHECK: Disable date checks for OCSP responses. This
    may be required when the system's real-time clock is not very accurate.
    It is recommended to enforce the nonce check instead if possible.
 * WOLFSSL_FORCE_OCSP_NONCE_CHECK: Require nonces to be available in OCSP
    responses. The nonces are optional and may not be supported by all
    responders. If it can be ensured that the used responder sends nonces this
    option may improve security.
*/

#ifndef NO_ASN

#include <wolfssl/wolfcrypt/asn.h>
#include <wolfssl/wolfcrypt/coding.h>
#include <wolfssl/wolfcrypt/md2.h>
#include <wolfssl/wolfcrypt/hmac.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/pwdbased.h>
#include <wolfssl/wolfcrypt/des3.h>
#include <wolfssl/wolfcrypt/aes.h>
#include <wolfssl/wolfcrypt/wc_encrypt.h>
#include <wolfssl/wolfcrypt/logging.h>

#include <wolfssl/wolfcrypt/random.h>
#include <wolfssl/wolfcrypt/hash.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

#ifndef NO_RC4
    #include <wolfssl/wolfcrypt/arc4.h>
#endif

#ifdef HAVE_NTRU
    #include "libntruencrypt/ntru_crypto.h"
#endif

#if defined(WOLFSSL_SHA512) || defined(WOLFSSL_SHA384)
    #include <wolfssl/wolfcrypt/sha512.h>
#endif

#ifndef NO_SHA256
    #include <wolfssl/wolfcrypt/sha256.h>
#endif

#ifdef HAVE_ECC
    #include <wolfssl/wolfcrypt/ecc.h>
#endif

#ifdef HAVE_ED25519
    #include <wolfssl/wolfcrypt/ed25519.h>
#endif

#ifdef HAVE_ED448
    #include <wolfssl/wolfcrypt/ed448.h>
#endif

#ifndef NO_RSA
    #include <wolfssl/wolfcrypt/rsa.h>
#if defined(WOLFSSL_XILINX_CRYPT) || defined(WOLFSSL_CRYPTOCELL)
extern int wc_InitRsaHw(RsaKey* key);
#endif
#endif

#ifdef WOLF_CRYPTO_CB
    #include <wolfssl/wolfcrypt/cryptocb.h>
#endif

#if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
    #include <wolfssl/openssl/objects.h>
#endif

#ifdef _MSC_VER
    /* 4996 warning to use MS extensions e.g., strcpy_s instead of XSTRNCPY */
    #pragma warning(disable: 4996)
#endif

#define ERROR_OUT(err, eLabel) { ret = (err); goto eLabel; }

#if !defined(NO_SKID) && (!defined(HAVE_FIPS) || !defined(HAVE_FIPS_VERSION))
    #if !defined(HAVE_SELFTEST) || (defined(HAVE_SELFTEST) && \
                                   (!defined(HAVE_SELFTEST_VERSION) || \
                                    HAVE_SELFTEST_VERSION < 2))
    #ifndef WOLFSSL_AES_KEY_SIZE_ENUM
    #define WOLFSSL_AES_KEY_SIZE_ENUM
    enum Asn_Misc {
        AES_IV_SIZE         = 16,
        AES_128_KEY_SIZE    = 16,
        AES_192_KEY_SIZE    = 24,
        AES_256_KEY_SIZE    = 32
    };
    #endif
    #endif /* HAVE_SELFTEST */
#endif
#ifdef WOLFSSL_RENESAS_TSIP_TLS
void tsip_inform_key_position(const word32 key_n_start,
                const word32 key_n_len, const word32 key_e_start,
                const word32 key_e_len);
int tsip_tls_CertVerify(const byte *cert, word32 certSz,
                        const byte *signature, word32 sigSz,
                        word32 key_n_start, word32 key_n_len,
                        word32 key_e_start, word32 key_e_len,
                        byte *tsip_encRsaKeyIdx);
#endif
int GetLength(const byte* input, word32* inOutIdx, int* len,
                           word32 maxIdx)
{
    return GetLength_ex(input, inOutIdx, len, maxIdx, 1);
}


/* give option to check length value found against index. 1 to check 0 to not */
int GetLength_ex(const byte* input, word32* inOutIdx, int* len,
                           word32 maxIdx, int check)
{
    int     length = 0;
    word32  idx = *inOutIdx;
    byte    b;

    *len = 0;    /* default length */

    if ((idx + 1) > maxIdx) {   /* for first read */
        WOLFSSL_MSG("GetLength bad index on input");
        return BUFFER_E;
    }

    b = input[idx++];
    if (b >= ASN_LONG_LENGTH) {
        word32 bytes = b & 0x7F;

        if ((idx + bytes) > maxIdx) {   /* for reading bytes */
            WOLFSSL_MSG("GetLength bad long length");
            return BUFFER_E;
        }

        if (bytes > sizeof(length)) {
            return ASN_PARSE_E;
        }
        while (bytes--) {
            b = input[idx++];
            length = (length << 8) | b;
        }
        if (length < 0) {
            return ASN_PARSE_E;
        }
    }
    else
        length = b;

    if (check && (idx + length) > maxIdx) {   /* for user of length */
        WOLFSSL_MSG("GetLength value exceeds buffer length");
        return BUFFER_E;
    }

    *inOutIdx = idx;
    if (length > 0)
        *len = length;

    return length;
}


/* input : buffer to read from
 * inOutIdx : index to start reading from, gets advanced by 1 if successful
 * maxIdx : maximum index value
 * tag : ASN tag value found
 *
 * returns 0 on success
 */
int GetASNTag(const byte* input, word32* inOutIdx, byte* tag, word32 maxIdx)
{
    word32 idx;

    if (tag == NULL || inOutIdx == NULL || input == NULL) {
        return BAD_FUNC_ARG;
    }

    idx = *inOutIdx;
    if (idx + ASN_TAG_SZ > maxIdx) {
        WOLFSSL_MSG("Buffer too small for ASN tag");
        return BUFFER_E;
    }

    *tag = input[idx];
    *inOutIdx = idx + ASN_TAG_SZ;
    return 0;
}


static int GetASNHeader_ex(const byte* input, byte tag, word32* inOutIdx, int* len,
                        word32 maxIdx, int check)
{
    word32 idx = *inOutIdx;
    byte   tagFound;
    int    length;

    if (GetASNTag(input, &idx, &tagFound, maxIdx) != 0)
        return ASN_PARSE_E;

    if (tagFound != tag)
        return ASN_PARSE_E;

    if (GetLength_ex(input, &idx, &length, maxIdx, check) < 0)
        return ASN_PARSE_E;

    *len      = length;
    *inOutIdx = idx;
    return length;
}


/* Get the DER/BER encoding of an ASN.1 header.
 *
 * input     Buffer holding DER/BER encoded data.
 * tag       ASN.1 tag value expected in header.
 * inOutIdx  Current index into buffer to parse.
 * len       The number of bytes in the ASN.1 data.
 * maxIdx    Length of data in buffer.
 * returns BUFFER_E when there is not enough data to parse.
 *         ASN_PARSE_E when the expected tag is not found or length is invalid.
 *         Otherwise, the number of bytes in the ASN.1 data.
 */
static int GetASNHeader(const byte* input, byte tag, word32* inOutIdx, int* len,
                        word32 maxIdx)
{
    return GetASNHeader_ex(input, tag, inOutIdx, len, maxIdx, 1);
}

static int GetHeader(const byte* input, byte* tag, word32* inOutIdx, int* len,
                     word32 maxIdx, int check)
{
    word32 idx = *inOutIdx;
    int    length;

    if ((idx + 1) > maxIdx)
        return BUFFER_E;

    *tag = input[idx++];

    if (GetLength_ex(input, &idx, &length, maxIdx, check) < 0)
        return ASN_PARSE_E;

    *len      = length;
    *inOutIdx = idx;
    return length;
}

int GetSequence(const byte* input, word32* inOutIdx, int* len,
                           word32 maxIdx)
{
    return GetASNHeader(input, ASN_SEQUENCE | ASN_CONSTRUCTED, inOutIdx, len,
                        maxIdx);
}


int GetSequence_ex(const byte* input, word32* inOutIdx, int* len,
                           word32 maxIdx, int check)
{
    return GetASNHeader_ex(input, ASN_SEQUENCE | ASN_CONSTRUCTED, inOutIdx, len,
                        maxIdx, check);
}


int GetSet(const byte* input, word32* inOutIdx, int* len,
                        word32 maxIdx)
{
    return GetASNHeader(input, ASN_SET | ASN_CONSTRUCTED, inOutIdx, len,
                        maxIdx);
}


int GetSet_ex(const byte* input, word32* inOutIdx, int* len,
                        word32 maxIdx, int check)
{
    return GetASNHeader_ex(input, ASN_SET | ASN_CONSTRUCTED, inOutIdx, len,
                        maxIdx, check);
}

/* Get the DER/BER encoded ASN.1 NULL element.
 * Ensure that the all fields are as expected and move index past the element.
 *
 * input     Buffer holding DER/BER encoded data.
 * inOutIdx  Current index into buffer to parse.
 * maxIdx    Length of data in buffer.
 * returns BUFFER_E when there is not enough data to parse.
 *         ASN_TAG_NULL_E when the NULL tag is not found.
 *         ASN_EXPECT_0_E when the length is not zero.
 *         Otherwise, 0 to indicate success.
 */
static int GetASNNull(const byte* input, word32* inOutIdx, word32 maxIdx)
{
    word32 idx = *inOutIdx;
    byte   b;

    if ((idx + 2) > maxIdx)
        return BUFFER_E;

    b = input[idx++];
    if (b != ASN_TAG_NULL)
        return ASN_TAG_NULL_E;

    if (input[idx++] != 0)
        return ASN_EXPECT_0_E;

    *inOutIdx = idx;
    return 0;
}

/* Set the DER/BER encoding of the ASN.1 NULL element.
 *
 * output  Buffer to write into.
 * returns the number of bytes added to the buffer.
 */
static int SetASNNull(byte* output)
{
    output[0] = ASN_TAG_NULL;
    output[1] = 0;

    return 2;
}

/* Get the DER/BER encoding of an ASN.1 BOOLEAN.
 *
 * input     Buffer holding DER/BER encoded data.
 * inOutIdx  Current index into buffer to parse.
 * maxIdx    Length of data in buffer.
 * returns BUFFER_E when there is not enough data to parse.
 *         ASN_PARSE_E when the BOOLEAN tag is not found or length is not 1.
 *         Otherwise, 0 to indicate the value was false and 1 to indicate true.
 */
static int GetBoolean(const byte* input, word32* inOutIdx, word32 maxIdx)
{
    word32 idx = *inOutIdx;
    byte   b;

    if ((idx + 3) > maxIdx)
        return BUFFER_E;

    b = input[idx++];
    if (b != ASN_BOOLEAN)
        return ASN_PARSE_E;

    if (input[idx++] != 1)
        return ASN_PARSE_E;

    b = input[idx++] != 0;

    *inOutIdx = idx;
    return b;
}

#ifdef ASN1_SET_BOOLEAN
/* Set the DER/BER encoding of the ASN.1 NULL element.
 * Note: Function not required as yet.
 *
 * val     Boolean value to encode.
 * output  Buffer to write into.
 * returns the number of bytes added to the buffer.
 */
static int SetBoolean(int val, byte* output)
{
    output[0] = ASN_BOOLEAN;
    output[1] = 1;
    output[2] = val ? -1 : 0;

    return 3;
}
#endif

/* Get the DER/BER encoding of an ASN.1 OCTET_STRING header.
 *
 * input     Buffer holding DER/BER encoded data.
 * inOutIdx  Current index into buffer to parse.
 * len       The number of bytes in the ASN.1 data.
 * maxIdx    Length of data in buffer.
 * returns BUFFER_E when there is not enough data to parse.
 *         ASN_PARSE_E when the OCTET_STRING tag is not found or length is
 *         invalid.
 *         Otherwise, the number of bytes in the ASN.1 data.
 */
int GetOctetString(const byte* input, word32* inOutIdx, int* len,
                          word32 maxIdx)
{
    return GetASNHeader(input, ASN_OCTET_STRING, inOutIdx, len, maxIdx);
}

/* Get the DER/BER encoding of an ASN.1 INTEGER header.
 * Removes the leading zero byte when found.
 *
 * input     Buffer holding DER/BER encoded data.
 * inOutIdx  Current index into buffer to parse.
 * len       The number of bytes in the ASN.1 data (excluding any leading zero).
 * maxIdx    Length of data in buffer.
 * returns BUFFER_E when there is not enough data to parse.
 *         ASN_PARSE_E when the INTEGER tag is not found, length is invalid,
 *         or invalid use of or missing leading zero.
 *         Otherwise, 0 to indicate success.
 */
static int GetASNInt(const byte* input, word32* inOutIdx, int* len,
                     word32 maxIdx)
{
    int    ret;

    ret = GetASNHeader(input, ASN_INTEGER, inOutIdx, len, maxIdx);
    if (ret < 0)
        return ret;

    if (*len > 0) {
        /* remove leading zero, unless there is only one 0x00 byte */
        if ((input[*inOutIdx] == 0x00) && (*len > 1)) {
            (*inOutIdx)++;
            (*len)--;

#ifndef WOLFSSL_ASN_INT_LEAD_0_ANY
            if (*len > 0 && (input[*inOutIdx] & 0x80) == 0)
                return ASN_PARSE_E;
#endif
        }
    }

    return 0;
}

/* Get the DER/BER encoding of an ASN.1 INTEGER that has a value of no more than
 * 7 bits.
 *
 * input     Buffer holding DER/BER encoded data.
 * inOutIdx  Current index into buffer to parse.
 * maxIdx    Length of data in buffer.
 * returns BUFFER_E when there is not enough data to parse.
 *         ASN_PARSE_E when the INTEGER tag is not found or length is invalid.
 *         Otherwise, the 7-bit value.
 */
static int GetInteger7Bit(const byte* input, word32* inOutIdx, word32 maxIdx)
{
    word32 idx = *inOutIdx;
    byte   b;

    if ((idx + 3) > maxIdx)
        return BUFFER_E;

    if (GetASNTag(input, &idx, &b, maxIdx) != 0)
        return ASN_PARSE_E;
    if (b != ASN_INTEGER)
        return ASN_PARSE_E;
    if (input[idx++] != 1)
        return ASN_PARSE_E;
    b = input[idx++];

    *inOutIdx = idx;
    return b;
}


#if !defined(NO_DSA) && !defined(NO_SHA)
static const char sigSha1wDsaName[] = "SHAwDSA";
#endif /* NO_DSA */
#ifndef NO_RSA
#ifdef WOLFSSL_MD2
    static const char  sigMd2wRsaName[] = "md2WithRSAEncryption";
#endif
#ifndef NO_MD5
    static const char  sigMd5wRsaName[] = "md5WithRSAEncryption";
#endif
#ifndef NO_SHA
    static const char  sigSha1wRsaName[] = "sha1WithRSAEncryption";
#endif
#ifdef WOLFSSL_SHA224
    static const char sigSha224wRsaName[] = "sha224WithRSAEncryption";
#endif
#ifndef NO_SHA256
    static const char sigSha256wRsaName[] = "sha256WithRSAEncryption";
#endif
#ifdef WOLFSSL_SHA384
    static const char sigSha384wRsaName[] = "sha384WithRSAEncryption";
#endif
#ifdef WOLFSSL_SHA512
    static const char sigSha512wRsaName[] = "sha512WithRSAEncryption";
#endif
#endif /* NO_RSA */
#ifdef HAVE_ECC
#ifndef NO_SHA
    static const char sigSha1wEcdsaName[] = "SHAwECDSA";
#endif
#ifdef WOLFSSL_SHA224
    static const char sigSha224wEcdsaName[] = "SHA224wECDSA";
#endif
#ifndef NO_SHA256
    static const char sigSha256wEcdsaName[] = "SHA256wECDSA";
#endif
#ifdef WOLFSSL_SHA384
    static const char sigSha384wEcdsaName[] = "SHA384wECDSA";
#endif
#ifdef WOLFSSL_SHA512
    static const char sigSha512wEcdsaName[] = "SHA512wECDSA";
#endif
#endif /* HAVE_ECC */
static const char sigUnknownName[] = "Unknown";


/* Get the human readable string for a signature type
 *
 * oid  Oid value for signature
 */
const char* GetSigName(int oid) {
    switch (oid) {
    #if !defined(NO_DSA) && !defined(NO_SHA)
        case CTC_SHAwDSA:
            return sigSha1wDsaName;
    #endif /* NO_DSA && NO_SHA */
    #ifndef NO_RSA
        #ifdef WOLFSSL_MD2
        case CTC_MD2wRSA:
            return sigMd2wRsaName;
        #endif
        #ifndef NO_MD5
        case CTC_MD5wRSA:
            return sigMd5wRsaName;
        #endif
        #ifndef NO_SHA
        case CTC_SHAwRSA:
            return sigSha1wRsaName;
        #endif
        #ifdef WOLFSSL_SHA224
        case CTC_SHA224wRSA:
            return sigSha224wRsaName;
        #endif
        #ifndef NO_SHA256
        case CTC_SHA256wRSA:
            return sigSha256wRsaName;
        #endif
        #ifdef WOLFSSL_SHA384
        case CTC_SHA384wRSA:
            return sigSha384wRsaName;
        #endif
        #ifdef WOLFSSL_SHA512
        case CTC_SHA512wRSA:
            return sigSha512wRsaName;
        #endif
    #endif /* NO_RSA */
    #ifdef HAVE_ECC
        #ifndef NO_SHA
        case CTC_SHAwECDSA:
            return sigSha1wEcdsaName;
        #endif
        #ifdef WOLFSSL_SHA224
        case CTC_SHA224wECDSA:
            return sigSha224wEcdsaName;
        #endif
        #ifndef NO_SHA256
        case CTC_SHA256wECDSA:
            return sigSha256wEcdsaName;
        #endif
        #ifdef WOLFSSL_SHA384
        case CTC_SHA384wECDSA:
            return sigSha384wEcdsaName;
        #endif
        #ifdef WOLFSSL_SHA512
        case CTC_SHA512wECDSA:
            return sigSha512wEcdsaName;
        #endif
    #endif /* HAVE_ECC */
        default:
            return sigUnknownName;
    }
}


#if !defined(NO_DSA) || defined(HAVE_ECC) || !defined(NO_CERTS) || \
   (!defined(NO_RSA) && \
        (defined(WOLFSSL_CERT_GEN) || \
        ((defined(WOLFSSL_KEY_GEN) || defined(OPENSSL_EXTRA)) && !defined(HAVE_USER_RSA))))
/* Set the DER/BER encoding of the ASN.1 INTEGER header.
 *
 * len        Length of data to encode.
 * firstByte  First byte of data, most significant byte of integer, to encode.
 * output     Buffer to write into.
 * returns the number of bytes added to the buffer.
 */
static int SetASNInt(int len, byte firstByte, byte* output)
{
    word32 idx = 0;

    if (output)
        output[idx] = ASN_INTEGER;
    idx++;
    if (firstByte & 0x80)
        len++;
    idx += SetLength(len, output ? output + idx : NULL);
    if (firstByte & 0x80) {
        if (output)
            output[idx] = 0x00;
        idx++;
    }

    return idx;
}
#endif

#if !defined(NO_DSA) || defined(HAVE_ECC) || (defined(WOLFSSL_CERT_GEN) && \
    !defined(NO_RSA)) || ((defined(WOLFSSL_KEY_GEN) || \
    defined(OPENSSL_EXTRA)) && !defined(NO_RSA) && !defined(HAVE_USER_RSA))
/* Set the DER/BER encoding of the ASN.1 INTEGER element with an mp_int.
 * The number is assumed to be positive.
 *
 * n       Multi-precision integer to encode.
 * maxSz   Maximum size of the encoded integer.
 *         A negative value indicates no check of length requested.
 * output  Buffer to write into.
 * returns BUFFER_E when the data is too long for the buffer.
 *         MP_TO_E when encoding the integer fails.
 *         Otherwise, the number of bytes added to the buffer.
 */
static int SetASNIntMP(mp_int* n, int maxSz, byte* output)
{
    int idx = 0;
    int leadingBit;
    int length;
    int err;

    leadingBit = mp_leading_bit(n);
    length = mp_unsigned_bin_size(n);
    idx = SetASNInt(length, leadingBit ? 0x80 : 0x00, output);
    if (maxSz >= 0 && (idx + length) > maxSz)
        return BUFFER_E;

    if (output) {
        err = mp_to_unsigned_bin(n, output + idx);
        if (err != MP_OKAY)
            return MP_TO_E;
    }
    idx += length;

    return idx;
}
#endif

#if !defined(NO_RSA) && defined(HAVE_USER_RSA) && \
    (defined(WOLFSSL_CERT_GEN) || defined(OPENSSL_EXTRA))
/* Set the DER/BER encoding of the ASN.1 INTEGER element with an mp_int from
 * an RSA key.
 * The number is assumed to be positive.
 *
 * n       Multi-precision integer to encode.
 * output  Buffer to write into.
 * returns BUFFER_E when the data is too long for the buffer.
 *         MP_TO_E when encoding the integer fails.
 *         Otherwise, the number of bytes added to the buffer.
 */
static int SetASNIntRSA(void* n, byte* output)
{
    int idx = 0;
    int leadingBit;
    int length;
    int err;

    leadingBit = wc_Rsa_leading_bit(n);
    length = wc_Rsa_unsigned_bin_size(n);
    idx = SetASNInt(length, leadingBit ? 0x80 : 0x00, output);
    if ((idx + length) > MAX_RSA_INT_SZ)
        return BUFFER_E;

    if (output) {
        err = wc_Rsa_to_unsigned_bin(n, output + idx, length);
        if (err != MP_OKAY)
            return MP_TO_E;
    }
    idx += length;

    return idx;
}
#endif /* !NO_RSA && HAVE_USER_RSA && WOLFSSL_CERT_GEN */

/* Windows header clash for WinCE using GetVersion */
int GetMyVersion(const byte* input, word32* inOutIdx,
                               int* version, word32 maxIdx)
{
    word32 idx = *inOutIdx;
    byte   tag;

    if ((idx + MIN_VERSION_SZ) > maxIdx)
        return ASN_PARSE_E;

    if (GetASNTag(input, &idx, &tag, maxIdx) != 0)
        return ASN_PARSE_E;

    if (tag != ASN_INTEGER)
        return ASN_PARSE_E;

    if (input[idx++] != 0x01)
        return ASN_VERSION_E;

    *version  = input[idx++];
    *inOutIdx = idx;

    return *version;
}


#ifndef NO_PWDBASED
/* Get small count integer, 32 bits or less */
int GetShortInt(const byte* input, word32* inOutIdx, int* number, word32 maxIdx)
{
    word32 idx = *inOutIdx;
    word32 len;
    byte   tag;

    *number = 0;

    /* check for type and length bytes */
    if ((idx + 2) > maxIdx)
        return BUFFER_E;

    if (GetASNTag(input, &idx, &tag, maxIdx) != 0)
        return ASN_PARSE_E;

    if (tag != ASN_INTEGER)
        return ASN_PARSE_E;

    len = input[idx++];
    if (len > 4)
        return ASN_PARSE_E;

    if (len + idx > maxIdx)
        return ASN_PARSE_E;

    while (len--) {
        *number  = *number << 8 | input[idx++];
    }

    *inOutIdx = idx;

    return *number;
}


/* Set small integer, 32 bits or less. DER encoding with no leading 0s
 * returns total amount written including ASN tag and length byte on success */
int SetShortInt(byte* input, word32* inOutIdx, word32 number, word32 maxIdx)
{
    word32 idx = *inOutIdx;
    word32 len = 0;
    int    i;
    byte ar[MAX_LENGTH_SZ];

    /* check for room for type and length bytes */
    if ((idx + 2) > maxIdx)
        return BUFFER_E;

    input[idx++] = ASN_INTEGER;
    idx++; /* place holder for length byte */
    if (MAX_LENGTH_SZ + idx > maxIdx)
        return ASN_PARSE_E;

    /* find first non zero byte */
    XMEMSET(ar, 0, MAX_LENGTH_SZ);
    c32toa(number, ar);
    for (i = 0; i < MAX_LENGTH_SZ; i++) {
        if (ar[i] != 0) {
            break;
        }
    }

    /* handle case of 0 */
    if (i == MAX_LENGTH_SZ) {
        input[idx++] = 0; len++;
    }

    for (; i < MAX_LENGTH_SZ && idx < maxIdx; i++) {
        input[idx++] = ar[i]; len++;
    }

    /* jump back to beginning of input buffer using unaltered inOutIdx value
     * and set number of bytes for integer, then update the index value */
    input[*inOutIdx + 1] = (byte)len;
    *inOutIdx = idx;

    return len + 2; /* size of integer bytes plus ASN TAG and length byte */
}
#endif /* !NO_PWDBASED */

/* May not have one, not an error */
static int GetExplicitVersion(const byte* input, word32* inOutIdx, int* version,
                              word32 maxIdx)
{
    word32 idx = *inOutIdx;
    byte tag;

    WOLFSSL_ENTER("GetExplicitVersion");

    if (GetASNTag(input, &idx, &tag, maxIdx) != 0)
        return ASN_PARSE_E;

    if (tag == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED)) {
        int ret;

        *inOutIdx = ++idx;  /* skip header */
        ret = GetMyVersion(input, inOutIdx, version, maxIdx);
        if (ret >= 0) {
            /* check if version is expected value rfc 5280 4.1 {0, 1, 2} */
            if (*version > MAX_X509_VERSION || *version < MIN_X509_VERSION) {
                WOLFSSL_MSG("Unexpected certificate version");
                ret = ASN_VERSION_E;
            }
        }
        return ret;
    }

    /* go back as is */
    *version = 0;

    return 0;
}

int GetInt(mp_int* mpi, const byte* input, word32* inOutIdx, word32 maxIdx)
{
    word32 idx = *inOutIdx;
    int    ret;
    int    length;

    ret = GetASNInt(input, &idx, &length, maxIdx);
    if (ret != 0)
        return ret;

    if (mp_init(mpi) != MP_OKAY)
        return MP_INIT_E;

    if (mp_read_unsigned_bin(mpi, (byte*)input + idx, length) != 0) {
        mp_clear(mpi);
        return ASN_GETINT_E;
    }

#ifdef HAVE_WOLF_BIGINT
    if (wc_bigint_from_unsigned_bin(&mpi->raw, input + idx, length) != 0) {
        mp_clear(mpi);
        return ASN_GETINT_E;
    }
#endif /* HAVE_WOLF_BIGINT */

    *inOutIdx = idx + length;

    return 0;
}

#if (!defined(WOLFSSL_KEY_GEN) && !defined(OPENSSL_EXTRA) && defined(RSA_LOW_MEM)) \
    || defined(WOLFSSL_RSA_PUBLIC_ONLY) || (!defined(NO_DSA))
#if (!defined(NO_RSA) && !defined(HAVE_USER_RSA)) || !defined(NO_DSA)
static int SkipInt(const byte* input, word32* inOutIdx, word32 maxIdx)
{
    word32 idx = *inOutIdx;
    int    ret;
    int    length;

    ret = GetASNInt(input, &idx, &length, maxIdx);
    if (ret != 0)
        return ret;

    *inOutIdx = idx + length;

    return 0;
}
#endif
#endif

static int CheckBitString(const byte* input, word32* inOutIdx, int* len,
                          word32 maxIdx, int zeroBits, byte* unusedBits)
{
    word32 idx = *inOutIdx;
    int    length;
    byte   b;

    if (GetASNTag(input, &idx, &b, maxIdx) != 0) {
        return ASN_BITSTR_E;
    }

    if (b != ASN_BIT_STRING) {
        return ASN_BITSTR_E;
    }

    if (GetLength(input, &idx, &length, maxIdx) < 0)
        return ASN_PARSE_E;

    /* extra sanity check that length is greater than 0 */
    if (length <= 0) {
        WOLFSSL_MSG("Error length was 0 in CheckBitString");
        return BUFFER_E;
    }

    if (idx + 1 > maxIdx) {
        WOLFSSL_MSG("Attempted buffer read larger than input buffer");
        return BUFFER_E;
    }

    b = input[idx];
    if (zeroBits && b != 0x00)
        return ASN_EXPECT_0_E;
    if (b >= 0x08)
        return ASN_PARSE_E;
    if (b != 0) {
        if ((byte)(input[idx + length - 1] << (8 - b)) != 0)
            return ASN_PARSE_E;
    }
    idx++;
    length--; /* length has been checked for greater than 0 */

    *inOutIdx = idx;
    if (len != NULL)
        *len = length;
    if (unusedBits != NULL)
        *unusedBits = b;

    return 0;
}

/* RSA (with CertGen or KeyGen) OR ECC OR ED25519 OR ED448 (with CertGen or
 * KeyGen) */
#if (!defined(NO_RSA) && !defined(HAVE_USER_RSA) && \
        (defined(WOLFSSL_CERT_GEN) || defined(WOLFSSL_KEY_GEN) || defined(OPENSSL_EXTRA))) || \
    (defined(HAVE_ECC) && defined(HAVE_ECC_KEY_EXPORT)) || \
    ((defined(HAVE_ED25519) || defined(HAVE_ED448)) && \
        (defined(WOLFSSL_CERT_GEN) || defined(WOLFSSL_KEY_GEN) || defined(OPENSSL_EXTRA)))

/* Set the DER/BER encoding of the ASN.1 BIT_STRING header.
 *
 * len         Length of data to encode.
 * unusedBits  The number of unused bits in the last byte of data.
 *             That is, the number of least significant zero bits before a one.
 *             The last byte is the most-significant non-zero byte of a number.
 * output      Buffer to write into.
 * returns the number of bytes added to the buffer.
 */
word32 SetBitString(word32 len, byte unusedBits, byte* output)
{
    word32 idx = 0;

    if (output)
        output[idx] = ASN_BIT_STRING;
    idx++;

    idx += SetLength(len + 1, output ? output + idx : NULL);
    if (output)
        output[idx] = unusedBits;
    idx++;

    return idx;
}
#endif /* !NO_RSA || HAVE_ECC || HAVE_ED25519 || HAVE_ED448 */

#ifdef ASN_BER_TO_DER
/* Pull informtation from the ASN.1 BER encoded item header */
static int GetBerHeader(const byte* data, word32* idx, word32 maxIdx,
                        byte* pTag, word32* pLen, int* indef)
{
    int len = 0;
    byte tag;
    word32 i = *idx;

    *indef = 0;

    /* Check there is enough data for a minimal header */
    if (i + 2 > maxIdx) {
        return ASN_PARSE_E;
    }

    /* Retrieve tag */
    tag = data[i++];

    /* Indefinite length handled specially */
    if (data[i] == 0x80) {
        /* Check valid tag for indefinite */
        if (((tag & 0xc0) == 0) && ((tag & ASN_CONSTRUCTED) == 0x00)) {
            return ASN_PARSE_E;
        }
        i++;
        *indef = 1;
    }
    else if (GetLength(data, &i, &len, maxIdx) < 0) {
        return ASN_PARSE_E;
    }

    /* Return tag, length and index after BER item header */
    *pTag = tag;
    *pLen = len;
    *idx = i;
    return 0;
}

#ifndef INDEF_ITEMS_MAX
#define INDEF_ITEMS_MAX       20
#endif

/* Indef length item data */
typedef struct Indef {
    word32 start;
    int depth;
    int headerLen;
    word32 len;
} Indef;

/* Indef length items */
typedef struct IndefItems
{
    Indef len[INDEF_ITEMS_MAX];
    int cnt;
    int idx;
    int depth;
} IndefItems;


/* Get header length of current item */
static int IndefItems_HeaderLen(IndefItems* items)
{
    return items->len[items->idx].headerLen;
}

/* Get data length of current item */
static word32 IndefItems_Len(IndefItems* items)
{
    return items->len[items->idx].len;
}

/* Add a indefinite length item */
static int IndefItems_AddItem(IndefItems* items, word32 start)
{
    int ret = 0;
    int i;

    if (items->cnt == INDEF_ITEMS_MAX) {
        ret = MEMORY_E;
    }
    else {
        i = items->cnt++;
        items->len[i].start = start;
        items->len[i].depth = items->depth++;
        items->len[i].headerLen = 1;
        items->len[i].len = 0;
        items->idx = i;
    }

    return ret;
}

/* Increase data length of current item */
static void IndefItems_AddData(IndefItems* items, word32 length)
{
    items->len[items->idx].len += length;
}

/* Update header length of current item to reflect data length */
static void IndefItems_UpdateHeaderLen(IndefItems* items)
{
    items->len[items->idx].headerLen +=
                                    SetLength(items->len[items->idx].len, NULL);
}

/* Go to indefinite parent of current item */
static void IndefItems_Up(IndefItems* items)
{
    int i;
    int depth = items->len[items->idx].depth - 1;

    for (i = items->cnt - 1; i >= 0; i--) {
        if (items->len[i].depth == depth) {
            break;
        }
    }
    items->idx = i;
    items->depth = depth + 1;
}

/* Calculate final length by adding length of indefinite child items */
static void IndefItems_CalcLength(IndefItems* items)
{
    int i;
    int idx = items->idx;

    for (i = idx + 1; i < items->cnt; i++) {
        if (items->len[i].depth == items->depth) {
            items->len[idx].len += items->len[i].headerLen;
            items->len[idx].len += items->len[i].len;
        }
    }
    items->len[idx].headerLen += SetLength(items->len[idx].len, NULL);
}

/* Add more data to indefinite length item */
static void IndefItems_MoreData(IndefItems* items, word32 length)
{
    if (items->cnt > 0 && items->idx >= 0) {
        items->len[items->idx].len += length;
    }
}

/* Convert a BER encoding with indefinite length items to DER.
 *
 * ber    BER encoded data.
 * berSz  Length of BER encoded data.
 * der    Buffer to hold DER encoded version of data.
 *        NULL indicates only the length is required.
 * derSz  The size of the buffer to hold the DER encoded data.
 *        Will be set if der is NULL, otherwise the value is checked as der is
 *        filled.
 * returns ASN_PARSE_E if the BER data is invalid and BAD_FUNC_ARG if ber or
 * derSz are NULL.
 */
int wc_BerToDer(const byte* ber, word32 berSz, byte* der, word32* derSz)
{
    int ret = 0;
    word32 i, j;
#ifdef WOLFSSL_SMALL_STACK
    IndefItems* indefItems = NULL;
#else
    IndefItems indefItems[1];
#endif
    byte tag, basic;
    word32 length;
    int indef;

    if (ber == NULL || derSz == NULL)
        return BAD_FUNC_ARG;

#ifdef WOLFSSL_SMALL_STACK
    indefItems = XMALLOC(sizeof(IndefItems), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (indefItems == NULL) {
        ret = MEMORY_E;
        goto end;
    }
#endif

    XMEMSET(indefItems, 0, sizeof(*indefItems));

    /* Calculate indefinite item lengths */
    for (i = 0; i < berSz; ) {
        word32 start = i;

        /* Get next BER item */
        ret = GetBerHeader(ber, &i, berSz, &tag, &length, &indef);
        if (ret != 0) {
            goto end;
        }

        if (indef) {
            /* Indefinite item - add to list */
            ret = IndefItems_AddItem(indefItems, i);
            if (ret != 0) {
                goto end;
            }

            if ((tag & 0xC0) == 0 &&
                tag != (ASN_SEQUENCE | ASN_CONSTRUCTED) &&
                tag != (ASN_SET      | ASN_CONSTRUCTED)) {
                /* Constructed basic type - get repeating tag */
                basic = tag & (~ASN_CONSTRUCTED);

                /* Add up lengths of each item below */
                for (; i < berSz; ) {
                    /* Get next BER_item */
                    ret = GetBerHeader(ber, &i, berSz, &tag, &length, &indef);
                    if (ret != 0) {
                        goto end;
                    }

                    /* End of content closes item */
                    if (tag == ASN_EOC) {
                        /* Must be zero length */
                        if (length != 0) {
                            ret = ASN_PARSE_E;
                            goto end;
                        }
                        break;
                    }

                    /* Must not be indefinite and tag must match parent */
                    if (indef || tag != basic) {
                        ret = ASN_PARSE_E;
                        goto end;
                    }

                    /* Add to length */
                    IndefItems_AddData(indefItems, length);
                    /* Skip data */
                    i += length;
                }

                /* Ensure we got an EOC and not end of data */
                if (tag != ASN_EOC) {
                    ret = ASN_PARSE_E;
                    goto end;
                }

                /* Set the header length to include the length field */
                IndefItems_UpdateHeaderLen(indefItems);
                /* Go to indefinte parent item */
                IndefItems_Up(indefItems);
            }
        }
        else if (tag == ASN_EOC) {
            /* End-of-content must be 0 length */
            if (length != 0) {
                ret = ASN_PARSE_E;
                goto end;
            }
            /* Check there is an item to close - missing EOC */
            if (indefItems->depth == 0) {
                ret = ASN_PARSE_E;
                goto end;
            }

            /* Finish calculation of data length for indefinite item */
            IndefItems_CalcLength(indefItems);
            /* Go to indefinte parent item */
            IndefItems_Up(indefItems);
        }
        else {
            /* Known length item to add in - make sure enough data for it */
            if (i + length > berSz) {
                ret = ASN_PARSE_E;
                goto end;
            }

            /* Include all data - can't have indefinite inside definite */
            i += length;
            /* Add entire item to current indefinite item */
            IndefItems_MoreData(indefItems, i - start);
        }
    }
    /* Check we had a EOC for each indefinite item */
    if (indefItems->depth != 0) {
        ret = ASN_PARSE_E;
        goto end;
    }

    /* Write out DER */

    j = 0;
    /* Reset index */
    indefItems->idx = 0;
    for (i = 0; i < berSz; ) {
        word32 start = i;

        /* Get item - checked above */
        (void)GetBerHeader(ber, &i, berSz, &tag, &length, &indef);
        if (indef) {
            if (der != NULL) {
                /* Check enough space for header */
                if (j + IndefItems_HeaderLen(indefItems) > *derSz) {
                    ret = BUFFER_E;
                    goto end;
                }

                if ((tag & 0xC0) == 0 &&
                    tag != (ASN_SEQUENCE | ASN_CONSTRUCTED) &&
                    tag != (ASN_SET      | ASN_CONSTRUCTED)) {
                    /* Remove constructed tag for basic types */
                    tag &= ~ASN_CONSTRUCTED;
                }
                /* Add tag and length */
                der[j] = tag;
                (void)SetLength(IndefItems_Len(indefItems), der + j + 1);
            }
            /* Add header length of indefinite item */
            j += IndefItems_HeaderLen(indefItems);

            if ((tag & 0xC0) == 0 &&
                tag != (ASN_SEQUENCE | ASN_CONSTRUCTED) &&
                tag != (ASN_SET      | ASN_CONSTRUCTED)) {
                /* For basic type - get each child item and add data */
                for (; i < berSz; ) {
                    (void)GetBerHeader(ber, &i, berSz, &tag, &length, &indef);
                    if (tag == ASN_EOC) {
                        break;
                    }
                    if (der != NULL) {
                        if (j + length > *derSz) {
                            ret = BUFFER_E;
                            goto end;
                        }
                        XMEMCPY(der + j, ber + i, length);
                    }
                    j += length;
                    i += length;
                }
            }

            /* Move to next indef item in list */
            indefItems->idx++;
        }
        else if (tag == ASN_EOC) {
            /* End-Of-Content is not written out in DER */
        }
        else {
            /* Write out definite length item as is. */
            i += length;
            if (der != NULL) {
                /* Ensure space for item */
                if (j + i - start > *derSz) {
                    ret = BUFFER_E;
                    goto end;
                }
                /* Copy item as is */
                XMEMCPY(der + j, ber + start, i - start);
            }
            j += i - start;
        }
    }

    /* Return the length of the DER encoded ASN.1 */
    *derSz = j;
    if (der == NULL) {
        ret = LENGTH_ONLY_E;
    }
end:
#ifdef WOLFSSL_SMALL_STACK
    if (indefItems != NULL) {
        XFREE(indefItems, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif
    return ret;
}
#endif

#if defined(WOLFSSL_CERT_EXT) && defined(WOLFSSL_CERT_GEN)
/* Set the DER/BER encoding of the ASN.1 BIT_STRING with a 16-bit value.
 *
 * val         16-bit value to encode.
 * output      Buffer to write into.
 * returns the number of bytes added to the buffer.
 */
static word32 SetBitString16Bit(word16 val, byte* output)
{
    word32 idx;
    int    len;
    byte   lastByte;
    byte   unusedBits = 0;

    if ((val >> 8) != 0) {
        len = 2;
        lastByte = (byte)(val >> 8);
    }
    else {
        len = 1;
        lastByte = (byte)val;
    }

    while (((lastByte >> unusedBits) & 0x01) == 0x00)
        unusedBits++;

    idx = SetBitString(len, unusedBits, output);
    output[idx++] = (byte)val;
    if (len > 1)
        output[idx++] = (byte)(val >> 8);

    return idx;
}
#endif /* WOLFSSL_CERT_EXT || WOLFSSL_CERT_GEN */

/* hashType */
#ifdef WOLFSSL_MD2
    static const byte hashMd2hOid[] = {42, 134, 72, 134, 247, 13, 2, 2};
#endif
#ifndef NO_MD5
    static const byte hashMd5hOid[] = {42, 134, 72, 134, 247, 13, 2, 5};
#endif
#ifndef NO_SHA
    static const byte hashSha1hOid[] = {43, 14, 3, 2, 26};
#endif
#ifdef WOLFSSL_SHA224
    static const byte hashSha224hOid[] = {96, 134, 72, 1, 101, 3, 4, 2, 4};
#endif
#ifndef NO_SHA256
    static const byte hashSha256hOid[] = {96, 134, 72, 1, 101, 3, 4, 2, 1};
#endif
#ifdef WOLFSSL_SHA384
    static const byte hashSha384hOid[] = {96, 134, 72, 1, 101, 3, 4, 2, 2};
#endif
#ifdef WOLFSSL_SHA512
    static const byte hashSha512hOid[] = {96, 134, 72, 1, 101, 3, 4, 2, 3};
#endif

/* hmacType */
#ifndef NO_HMAC
    #ifdef WOLFSSL_SHA224
    static const byte hmacSha224Oid[] = {42, 134, 72, 134, 247, 13, 2, 8};
    #endif
    #ifndef NO_SHA256
    static const byte hmacSha256Oid[] = {42, 134, 72, 134, 247, 13, 2, 9};
    #endif
    #ifdef WOLFSSL_SHA384
    static const byte hmacSha384Oid[] = {42, 134, 72, 134, 247, 13, 2, 10};
    #endif
    #ifdef WOLFSSL_SHA512
    static const byte hmacSha512Oid[] = {42, 134, 72, 134, 247, 13, 2, 11};
    #endif
#endif

/* sigType */
#if !defined(NO_DSA) && !defined(NO_SHA)
    static const byte sigSha1wDsaOid[] = {42, 134, 72, 206, 56, 4, 3};
#endif /* NO_DSA */
#ifndef NO_RSA
    #ifdef WOLFSSL_MD2
    static const byte sigMd2wRsaOid[] = {42, 134, 72, 134, 247, 13, 1, 1, 2};
    #endif
    #ifndef NO_MD5
    static const byte sigMd5wRsaOid[] = {42, 134, 72, 134, 247, 13, 1, 1, 4};
    #endif
    #ifndef NO_SHA
    static const byte sigSha1wRsaOid[] = {42, 134, 72, 134, 247, 13, 1, 1, 5};
    #endif
    #ifdef WOLFSSL_SHA224
    static const byte sigSha224wRsaOid[] = {42, 134, 72, 134, 247, 13, 1, 1,14};
    #endif
    #ifndef NO_SHA256
    static const byte sigSha256wRsaOid[] = {42, 134, 72, 134, 247, 13, 1, 1,11};
    #endif
    #ifdef WOLFSSL_SHA384
    static const byte sigSha384wRsaOid[] = {42, 134, 72, 134, 247, 13, 1, 1,12};
    #endif
    #ifdef WOLFSSL_SHA512
    static const byte sigSha512wRsaOid[] = {42, 134, 72, 134, 247, 13, 1, 1,13};
    #endif
#endif /* NO_RSA */
#ifdef HAVE_ECC
    #ifndef NO_SHA
    static const byte sigSha1wEcdsaOid[] = {42, 134, 72, 206, 61, 4, 1};
    #endif
    #ifdef WOLFSSL_SHA224
    static const byte sigSha224wEcdsaOid[] = {42, 134, 72, 206, 61, 4, 3, 1};
    #endif
    #ifndef NO_SHA256
    static const byte sigSha256wEcdsaOid[] = {42, 134, 72, 206, 61, 4, 3, 2};
    #endif
    #ifdef WOLFSSL_SHA384
    static const byte sigSha384wEcdsaOid[] = {42, 134, 72, 206, 61, 4, 3, 3};
    #endif
    #ifdef WOLFSSL_SHA512
    static const byte sigSha512wEcdsaOid[] = {42, 134, 72, 206, 61, 4, 3, 4};
    #endif
#endif /* HAVE_ECC */
#ifdef HAVE_ED25519
    static const byte sigEd25519Oid[] = {43, 101, 112};
#endif /* HAVE_ED25519 */
#ifdef HAVE_ED448
    static const byte sigEd448Oid[] = {43, 101, 113};
#endif /* HAVE_ED448 */

/* keyType */
#ifndef NO_DSA
    static const byte keyDsaOid[] = {42, 134, 72, 206, 56, 4, 1};
#endif /* NO_DSA */
#ifndef NO_RSA
    static const byte keyRsaOid[] = {42, 134, 72, 134, 247, 13, 1, 1, 1};
#endif /* NO_RSA */
#ifdef HAVE_NTRU
    static const byte keyNtruOid[] = {43, 6, 1, 4, 1, 193, 22, 1, 1, 1, 1};
#endif /* HAVE_NTRU */
#ifdef HAVE_ECC
    static const byte keyEcdsaOid[] = {42, 134, 72, 206, 61, 2, 1};
#endif /* HAVE_ECC */
#ifdef HAVE_ED25519
    static const byte keyEd25519Oid[] = {43, 101, 112};
#endif /* HAVE_ED25519 */
#ifdef HAVE_ED448
    static const byte keyEd448Oid[] = {43, 101, 113};
#endif /* HAVE_ED448 */
#ifndef NO_DH
    static const byte keyDhOid[] = {42, 134, 72, 134, 247, 13, 1, 3, 1};
#endif /* !NO_DH */

/* curveType */
#ifdef HAVE_ECC
    /* See "ecc_sets" table in ecc.c */
#endif /* HAVE_ECC */

#ifdef HAVE_AES_CBC
/* blkType */
    #ifdef WOLFSSL_AES_128
    static const byte blkAes128CbcOid[] = {96, 134, 72, 1, 101, 3, 4, 1, 2};
    #endif
    #ifdef WOLFSSL_AES_192
    static const byte blkAes192CbcOid[] = {96, 134, 72, 1, 101, 3, 4, 1, 22};
    #endif
    #ifdef WOLFSSL_AES_256
    static const byte blkAes256CbcOid[] = {96, 134, 72, 1, 101, 3, 4, 1, 42};
    #endif
#endif /* HAVE_AES_CBC */
#ifdef HAVE_AESGCM
    #ifdef WOLFSSL_AES_128
    static const byte blkAes128GcmOid[] = {96, 134, 72, 1, 101, 3, 4, 1, 6};
    #endif
    #ifdef WOLFSSL_AES_192
    static const byte blkAes192GcmOid[] = {96, 134, 72, 1, 101, 3, 4, 1, 26};
    #endif
    #ifdef WOLFSSL_AES_256
    static const byte blkAes256GcmOid[] = {96, 134, 72, 1, 101, 3, 4, 1, 46};
    #endif
#endif /* HAVE_AESGCM */
#ifdef HAVE_AESCCM
    #ifdef WOLFSSL_AES_128
    static const byte blkAes128CcmOid[] = {96, 134, 72, 1, 101, 3, 4, 1, 7};
    #endif
    #ifdef WOLFSSL_AES_192
    static const byte blkAes192CcmOid[] = {96, 134, 72, 1, 101, 3, 4, 1, 27};
    #endif
    #ifdef WOLFSSL_AES_256
    static const byte blkAes256CcmOid[] = {96, 134, 72, 1, 101, 3, 4, 1, 47};
    #endif
#endif /* HAVE_AESCCM */

#ifndef NO_DES3
    static const byte blkDesCbcOid[]  = {43, 14, 3, 2, 7};
    static const byte blkDes3CbcOid[] = {42, 134, 72, 134, 247, 13, 3, 7};
#endif

/* keyWrapType */
#ifdef WOLFSSL_AES_128
    static const byte wrapAes128Oid[] = {96, 134, 72, 1, 101, 3, 4, 1, 5};
#endif
#ifdef WOLFSSL_AES_192
    static const byte wrapAes192Oid[] = {96, 134, 72, 1, 101, 3, 4, 1, 25};
#endif
#ifdef WOLFSSL_AES_256
    static const byte wrapAes256Oid[] = {96, 134, 72, 1, 101, 3, 4, 1, 45};
#endif
#ifdef HAVE_PKCS7
/* From RFC 3211 */
static const byte wrapPwriKekOid[] = {42, 134, 72, 134, 247, 13, 1, 9, 16, 3,9};
#endif

/* cmsKeyAgreeType */
#ifndef NO_SHA
    static const byte dhSinglePass_stdDH_sha1kdf_Oid[]   =
                                          {43, 129, 5, 16, 134, 72, 63, 0, 2};
#endif
#ifdef WOLFSSL_SHA224
    static const byte dhSinglePass_stdDH_sha224kdf_Oid[] = {43, 129, 4, 1, 11, 0};
#endif
#ifndef NO_SHA256
    static const byte dhSinglePass_stdDH_sha256kdf_Oid[] = {43, 129, 4, 1, 11, 1};
#endif
#ifdef WOLFSSL_SHA384
    static const byte dhSinglePass_stdDH_sha384kdf_Oid[] = {43, 129, 4, 1, 11, 2};
#endif
#ifdef WOLFSSL_SHA512
    static const byte dhSinglePass_stdDH_sha512kdf_Oid[] = {43, 129, 4, 1, 11, 3};
#endif

/* ocspType */
#ifdef HAVE_OCSP
    static const byte ocspBasicOid[] = {43, 6, 1, 5, 5, 7, 48, 1, 1};
    static const byte ocspNonceOid[] = {43, 6, 1, 5, 5, 7, 48, 1, 2};
#endif /* HAVE_OCSP */

/* certExtType */
static const byte extBasicCaOid[] = {85, 29, 19};
static const byte extAltNamesOid[] = {85, 29, 17};
static const byte extCrlDistOid[] = {85, 29, 31};
static const byte extAuthInfoOid[] = {43, 6, 1, 5, 5, 7, 1, 1};
static const byte extAuthKeyOid[] = {85, 29, 35};
static const byte extSubjKeyOid[] = {85, 29, 14};
static const byte extCertPolicyOid[] = {85, 29, 32};
static const byte extKeyUsageOid[] = {85, 29, 15};
static const byte extInhibitAnyOid[] = {85, 29, 54};
static const byte extExtKeyUsageOid[] = {85, 29, 37};
#ifndef IGNORE_NAME_CONSTRAINTS
    static const byte extNameConsOid[] = {85, 29, 30};
#endif

/* certAuthInfoType */
#ifdef HAVE_OCSP
    static const byte extAuthInfoOcspOid[] = {43, 6, 1, 5, 5, 7, 48, 1};
#endif
static const byte extAuthInfoCaIssuerOid[] = {43, 6, 1, 5, 5, 7, 48, 2};

/* certPolicyType */
static const byte extCertPolicyAnyOid[] = {85, 29, 32, 0};

/* certKeyUseType */
static const byte extAltNamesHwNameOid[] = {43, 6, 1, 5, 5, 7, 8, 4};

/* certKeyUseType */
static const byte extExtKeyUsageAnyOid[] = {85, 29, 37, 0};
static const byte extExtKeyUsageServerAuthOid[]   = {43, 6, 1, 5, 5, 7, 3, 1};
static const byte extExtKeyUsageClientAuthOid[]   = {43, 6, 1, 5, 5, 7, 3, 2};
static const byte extExtKeyUsageCodeSigningOid[]  = {43, 6, 1, 5, 5, 7, 3, 3};
static const byte extExtKeyUsageEmailProtectOid[] = {43, 6, 1, 5, 5, 7, 3, 4};
static const byte extExtKeyUsageTimestampOid[]    = {43, 6, 1, 5, 5, 7, 3, 8};
static const byte extExtKeyUsageOcspSignOid[]     = {43, 6, 1, 5, 5, 7, 3, 9};

/* kdfType */
static const byte pbkdf2Oid[] = {42, 134, 72, 134, 247, 13, 1, 5, 12};

/* PKCS5 */
#if !defined(NO_DES3) && !defined(NO_SHA)
static const byte pbeSha1Des[] = {42, 134, 72, 134, 247, 13, 1, 5, 10};
#endif
static const byte pbes2[] = {42, 134, 72, 134, 247, 13, 1, 5, 13};

/* PKCS12 */
#if !defined(NO_RC4) && !defined(NO_SHA)
static const byte pbeSha1RC4128[] = {42, 134, 72, 134, 247, 13, 1, 12, 1, 1};
#endif
#if !defined(NO_DES3) && !defined(NO_SHA)
static const byte pbeSha1Des3[] = {42, 134, 72, 134, 247, 13, 1, 12, 1, 3};
#endif

#ifdef HAVE_LIBZ
/* zlib compression */
static const byte zlibCompress[] = {42, 134, 72, 134, 247, 13, 1, 9, 16, 3, 8};
#endif
#ifdef WOLFSSL_APACHE_HTTPD
/* tlsExtType */
static const byte tlsFeatureOid[] = {43, 6, 1, 5, 5, 7, 1, 24};
/* certNameType */
static const byte dnsSRVOid[] = {43, 6, 1, 5, 5, 7, 8, 7};
#endif


/* returns a pointer to the OID string on success and NULL on fail */
const byte* OidFromId(word32 id, word32 type, word32* oidSz)
{
    const byte* oid = NULL;

    *oidSz = 0;

    switch (type) {

        case oidHashType:
            switch (id) {
            #ifdef WOLFSSL_MD2
                case MD2h:
                    oid = hashMd2hOid;
                    *oidSz = sizeof(hashMd2hOid);
                    break;
            #endif
            #ifndef NO_MD5
                case MD5h:
                    oid = hashMd5hOid;
                    *oidSz = sizeof(hashMd5hOid);
                    break;
            #endif
            #ifndef NO_SHA
                case SHAh:
                    oid = hashSha1hOid;
                    *oidSz = sizeof(hashSha1hOid);
                    break;
            #endif
            #ifdef WOLFSSL_SHA224
                case SHA224h:
                    oid = hashSha224hOid;
                    *oidSz = sizeof(hashSha224hOid);
                    break;
            #endif
            #ifndef NO_SHA256
                case SHA256h:
                    oid = hashSha256hOid;
                    *oidSz = sizeof(hashSha256hOid);
                    break;
            #endif
            #ifdef WOLFSSL_SHA384
                case SHA384h:
                    oid = hashSha384hOid;
                    *oidSz = sizeof(hashSha384hOid);
                    break;
            #endif
            #ifdef WOLFSSL_SHA512
                case SHA512h:
                    oid = hashSha512hOid;
                    *oidSz = sizeof(hashSha512hOid);
                    break;
            #endif
            }
            break;

        case oidSigType:
            switch (id) {
                #if !defined(NO_DSA) && !defined(NO_SHA)
                case CTC_SHAwDSA:
                    oid = sigSha1wDsaOid;
                    *oidSz = sizeof(sigSha1wDsaOid);
                    break;
                #endif /* NO_DSA */
                #ifndef NO_RSA
                #ifdef WOLFSSL_MD2
                case CTC_MD2wRSA:
                    oid = sigMd2wRsaOid;
                    *oidSz = sizeof(sigMd2wRsaOid);
                    break;
                #endif
                #ifndef NO_MD5
                case CTC_MD5wRSA:
                    oid = sigMd5wRsaOid;
                    *oidSz = sizeof(sigMd5wRsaOid);
                    break;
                #endif
                #ifndef NO_SHA
                case CTC_SHAwRSA:
                    oid = sigSha1wRsaOid;
                    *oidSz = sizeof(sigSha1wRsaOid);
                    break;
                #endif
                #ifdef WOLFSSL_SHA224
                case CTC_SHA224wRSA:
                    oid = sigSha224wRsaOid;
                    *oidSz = sizeof(sigSha224wRsaOid);
                    break;
                #endif
                #ifndef NO_SHA256
                case CTC_SHA256wRSA:
                    oid = sigSha256wRsaOid;
                    *oidSz = sizeof(sigSha256wRsaOid);
                    break;
                #endif
                #ifdef WOLFSSL_SHA384
                case CTC_SHA384wRSA:
                    oid = sigSha384wRsaOid;
                    *oidSz = sizeof(sigSha384wRsaOid);
                    break;
                #endif
                #ifdef WOLFSSL_SHA512
                case CTC_SHA512wRSA:
                    oid = sigSha512wRsaOid;
                    *oidSz = sizeof(sigSha512wRsaOid);
                    break;
                #endif /* WOLFSSL_SHA512 */
                #endif /* NO_RSA */
                #ifdef HAVE_ECC
                #ifndef NO_SHA
                case CTC_SHAwECDSA:
                    oid = sigSha1wEcdsaOid;
                    *oidSz = sizeof(sigSha1wEcdsaOid);
                    break;
                #endif
                #ifdef WOLFSSL_SHA224
                case CTC_SHA224wECDSA:
                    oid = sigSha224wEcdsaOid;
                    *oidSz = sizeof(sigSha224wEcdsaOid);
                    break;
                #endif
                #ifndef NO_SHA256
                case CTC_SHA256wECDSA:
                    oid = sigSha256wEcdsaOid;
                    *oidSz = sizeof(sigSha256wEcdsaOid);
                    break;
                #endif
                #ifdef WOLFSSL_SHA384
                case CTC_SHA384wECDSA:
                    oid = sigSha384wEcdsaOid;
                    *oidSz = sizeof(sigSha384wEcdsaOid);
                    break;
                #endif
                #ifdef WOLFSSL_SHA512
                case CTC_SHA512wECDSA:
                    oid = sigSha512wEcdsaOid;
                    *oidSz = sizeof(sigSha512wEcdsaOid);
                    break;
                #endif
                #endif /* HAVE_ECC */
                #ifdef HAVE_ED25519
                case CTC_ED25519:
                    oid = sigEd25519Oid;
                    *oidSz = sizeof(sigEd25519Oid);
                    break;
                #endif
                #ifdef HAVE_ED448
                case CTC_ED448:
                    oid = sigEd448Oid;
                    *oidSz = sizeof(sigEd448Oid);
                    break;
                #endif
                default:
                    break;
            }
            break;

        case oidKeyType:
            switch (id) {
                #ifndef NO_DSA
                case DSAk:
                    oid = keyDsaOid;
                    *oidSz = sizeof(keyDsaOid);
                    break;
                #endif /* NO_DSA */
                #ifndef NO_RSA
                case RSAk:
                    oid = keyRsaOid;
                    *oidSz = sizeof(keyRsaOid);
                    break;
                #endif /* NO_RSA */
                #ifdef HAVE_NTRU
                case NTRUk:
                    oid = keyNtruOid;
                    *oidSz = sizeof(keyNtruOid);
                    break;
                #endif /* HAVE_NTRU */
                #ifdef HAVE_ECC
                case ECDSAk:
                    oid = keyEcdsaOid;
                    *oidSz = sizeof(keyEcdsaOid);
                    break;
                #endif /* HAVE_ECC */
                #ifdef HAVE_ED25519
                case ED25519k:
                    oid = keyEd25519Oid;
                    *oidSz = sizeof(keyEd25519Oid);
                    break;
                #endif /* HAVE_ED25519 */
                #ifdef HAVE_ED448
                case ED448k:
                    oid = keyEd448Oid;
                    *oidSz = sizeof(keyEd448Oid);
                    break;
                #endif /* HAVE_ED448 */
                #ifndef NO_DH
                case DHk:
                    oid = keyDhOid;
                    *oidSz = sizeof(keyDhOid);
                    break;
                #endif /* !NO_DH */
                default:
                    break;
            }
            break;

        #ifdef HAVE_ECC
        case oidCurveType:
            if (wc_ecc_get_oid(id, &oid, oidSz) < 0) {
                WOLFSSL_MSG("ECC OID not found");
            }
            break;
        #endif /* HAVE_ECC */

        case oidBlkType:
            switch (id) {
    #ifdef HAVE_AES_CBC
        #ifdef WOLFSSL_AES_128
                case AES128CBCb:
                    oid = blkAes128CbcOid;
                    *oidSz = sizeof(blkAes128CbcOid);
                    break;
        #endif
        #ifdef WOLFSSL_AES_192
                case AES192CBCb:
                    oid = blkAes192CbcOid;
                    *oidSz = sizeof(blkAes192CbcOid);
                    break;
        #endif
        #ifdef WOLFSSL_AES_256
                case AES256CBCb:
                    oid = blkAes256CbcOid;
                    *oidSz = sizeof(blkAes256CbcOid);
                    break;
        #endif
    #endif /* HAVE_AES_CBC */
    #ifdef HAVE_AESGCM
        #ifdef WOLFSSL_AES_128
                case AES128GCMb:
                    oid = blkAes128GcmOid;
                    *oidSz = sizeof(blkAes128GcmOid);
                    break;
        #endif
        #ifdef WOLFSSL_AES_192
                case AES192GCMb:
                    oid = blkAes192GcmOid;
                    *oidSz = sizeof(blkAes192GcmOid);
                    break;
        #endif
        #ifdef WOLFSSL_AES_256
                case AES256GCMb:
                    oid = blkAes256GcmOid;
                    *oidSz = sizeof(blkAes256GcmOid);
                    break;
        #endif
    #endif /* HAVE_AESGCM */
    #ifdef HAVE_AESCCM
        #ifdef WOLFSSL_AES_128
                case AES128CCMb:
                    oid = blkAes128CcmOid;
                    *oidSz = sizeof(blkAes128CcmOid);
                    break;
        #endif
        #ifdef WOLFSSL_AES_192
                case AES192CCMb:
                    oid = blkAes192CcmOid;
                    *oidSz = sizeof(blkAes192CcmOid);
                    break;
        #endif
        #ifdef WOLFSSL_AES_256
                case AES256CCMb:
                    oid = blkAes256CcmOid;
                    *oidSz = sizeof(blkAes256CcmOid);
                    break;
        #endif
    #endif /* HAVE_AESCCM */
    #ifndef NO_DES3
                case DESb:
                    oid = blkDesCbcOid;
                    *oidSz = sizeof(blkDesCbcOid);
                    break;
                case DES3b:
                    oid = blkDes3CbcOid;
                    *oidSz = sizeof(blkDes3CbcOid);
                    break;
    #endif /* !NO_DES3 */
            }
            break;

        #ifdef HAVE_OCSP
        case oidOcspType:
            switch (id) {
                case OCSP_BASIC_OID:
                    oid = ocspBasicOid;
                    *oidSz = sizeof(ocspBasicOid);
                    break;
                case OCSP_NONCE_OID:
                    oid = ocspNonceOid;
                    *oidSz = sizeof(ocspNonceOid);
                    break;
            }
            break;
        #endif /* HAVE_OCSP */

        case oidCertExtType:
            switch (id) {
                case BASIC_CA_OID:
                    oid = extBasicCaOid;
                    *oidSz = sizeof(extBasicCaOid);
                    break;
                case ALT_NAMES_OID:
                    oid = extAltNamesOid;
                    *oidSz = sizeof(extAltNamesOid);
                    break;
                case CRL_DIST_OID:
                    oid = extCrlDistOid;
                    *oidSz = sizeof(extCrlDistOid);
                    break;
                case AUTH_INFO_OID:
                    oid = extAuthInfoOid;
                    *oidSz = sizeof(extAuthInfoOid);
                    break;
                case AUTH_KEY_OID:
                    oid = extAuthKeyOid;
                    *oidSz = sizeof(extAuthKeyOid);
                    break;
                case SUBJ_KEY_OID:
                    oid = extSubjKeyOid;
                    *oidSz = sizeof(extSubjKeyOid);
                    break;
                case CERT_POLICY_OID:
                    oid = extCertPolicyOid;
                    *oidSz = sizeof(extCertPolicyOid);
                    break;
                case KEY_USAGE_OID:
                    oid = extKeyUsageOid;
                    *oidSz = sizeof(extKeyUsageOid);
                    break;
                case INHIBIT_ANY_OID:
                    oid = extInhibitAnyOid;
                    *oidSz = sizeof(extInhibitAnyOid);
                    break;
                case EXT_KEY_USAGE_OID:
                    oid = extExtKeyUsageOid;
                    *oidSz = sizeof(extExtKeyUsageOid);
                    break;
            #ifndef IGNORE_NAME_CONSTRAINTS
                case NAME_CONS_OID:
                    oid = extNameConsOid;
                    *oidSz = sizeof(extNameConsOid);
                    break;
            #endif
            }
            break;

        case oidCrlExtType:
            #ifdef HAVE_CRL
            switch (id) {
                case AUTH_KEY_OID:
                    oid = extAuthKeyOid;
                    *oidSz = sizeof(extAuthKeyOid);
                    break;
            }
            #endif
            break;

        case oidCertAuthInfoType:
            switch (id) {
            #ifdef HAVE_OCSP
                case AIA_OCSP_OID:
                    oid = extAuthInfoOcspOid;
                    *oidSz = sizeof(extAuthInfoOcspOid);
                    break;
            #endif
                case AIA_CA_ISSUER_OID:
                    oid = extAuthInfoCaIssuerOid;
                    *oidSz = sizeof(extAuthInfoCaIssuerOid);
                    break;
            }
            break;

        case oidCertPolicyType:
            switch (id) {
                case CP_ANY_OID:
                    oid = extCertPolicyAnyOid;
                    *oidSz = sizeof(extCertPolicyAnyOid);
                    break;
            }
            break;

        case oidCertAltNameType:
            switch (id) {
                case HW_NAME_OID:
                    oid = extAltNamesHwNameOid;
                    *oidSz = sizeof(extAltNamesHwNameOid);
                    break;
            }
            break;

        case oidCertKeyUseType:
            switch (id) {
                case EKU_ANY_OID:
                    oid = extExtKeyUsageAnyOid;
                    *oidSz = sizeof(extExtKeyUsageAnyOid);
                    break;
                case EKU_SERVER_AUTH_OID:
                    oid = extExtKeyUsageServerAuthOid;
                    *oidSz = sizeof(extExtKeyUsageServerAuthOid);
                    break;
                case EKU_CLIENT_AUTH_OID:
                    oid = extExtKeyUsageClientAuthOid;
                    *oidSz = sizeof(extExtKeyUsageClientAuthOid);
                    break;
                case EKU_CODESIGNING_OID:
                    oid = extExtKeyUsageCodeSigningOid;
                    *oidSz = sizeof(extExtKeyUsageCodeSigningOid);
                    break;
                case EKU_EMAILPROTECT_OID:
                    oid = extExtKeyUsageEmailProtectOid;
                    *oidSz = sizeof(extExtKeyUsageEmailProtectOid);
                    break;
                case EKU_TIMESTAMP_OID:
                    oid = extExtKeyUsageTimestampOid;
                    *oidSz = sizeof(extExtKeyUsageTimestampOid);
                    break;
                case EKU_OCSP_SIGN_OID:
                    oid = extExtKeyUsageOcspSignOid;
                    *oidSz = sizeof(extExtKeyUsageOcspSignOid);
                    break;
            }
            break;

        case oidKdfType:
            switch (id) {
                case PBKDF2_OID:
                    oid = pbkdf2Oid;
                    *oidSz = sizeof(pbkdf2Oid);
                    break;
            }
            break;

        case oidPBEType:
            switch (id) {
        #if !defined(NO_SHA) && !defined(NO_RC4)
                case PBE_SHA1_RC4_128:
                    oid = pbeSha1RC4128;
                    *oidSz = sizeof(pbeSha1RC4128);
                    break;
        #endif
        #if !defined(NO_SHA) && !defined(NO_DES3)
                case PBE_SHA1_DES:
                    oid = pbeSha1Des;
                    *oidSz = sizeof(pbeSha1Des);
                    break;

        #endif
        #if !defined(NO_SHA) && !defined(NO_DES3)
                case PBE_SHA1_DES3:
                    oid = pbeSha1Des3;
                    *oidSz = sizeof(pbeSha1Des3);
                    break;
        #endif
                case PBES2:
                    oid = pbes2;
                    *oidSz = sizeof(pbes2);
                    break;
            }
            break;

        case oidKeyWrapType:
            switch (id) {
            #ifdef WOLFSSL_AES_128
                case AES128_WRAP:
                    oid = wrapAes128Oid;
                    *oidSz = sizeof(wrapAes128Oid);
                    break;
            #endif
            #ifdef WOLFSSL_AES_192
                case AES192_WRAP:
                    oid = wrapAes192Oid;
                    *oidSz = sizeof(wrapAes192Oid);
                    break;
            #endif
            #ifdef WOLFSSL_AES_256
                case AES256_WRAP:
                    oid = wrapAes256Oid;
                    *oidSz = sizeof(wrapAes256Oid);
                    break;
            #endif
            #ifdef HAVE_PKCS7
                case PWRI_KEK_WRAP:
                    oid = wrapPwriKekOid;
                    *oidSz = sizeof(wrapPwriKekOid);
                    break;
            #endif
            }
            break;

        case oidCmsKeyAgreeType:
            switch (id) {
            #ifndef NO_SHA
                case dhSinglePass_stdDH_sha1kdf_scheme:
                    oid = dhSinglePass_stdDH_sha1kdf_Oid;
                    *oidSz = sizeof(dhSinglePass_stdDH_sha1kdf_Oid);
                    break;
            #endif
            #ifdef WOLFSSL_SHA224
                case dhSinglePass_stdDH_sha224kdf_scheme:
                    oid = dhSinglePass_stdDH_sha224kdf_Oid;
                    *oidSz = sizeof(dhSinglePass_stdDH_sha224kdf_Oid);
                    break;
            #endif
            #ifndef NO_SHA256
                case dhSinglePass_stdDH_sha256kdf_scheme:
                    oid = dhSinglePass_stdDH_sha256kdf_Oid;
                    *oidSz = sizeof(dhSinglePass_stdDH_sha256kdf_Oid);
                    break;
            #endif
            #ifdef WOLFSSL_SHA384
                case dhSinglePass_stdDH_sha384kdf_scheme:
                    oid = dhSinglePass_stdDH_sha384kdf_Oid;
                    *oidSz = sizeof(dhSinglePass_stdDH_sha384kdf_Oid);
                    break;
            #endif
            #ifdef WOLFSSL_SHA512
                case dhSinglePass_stdDH_sha512kdf_scheme:
                    oid = dhSinglePass_stdDH_sha512kdf_Oid;
                    *oidSz = sizeof(dhSinglePass_stdDH_sha512kdf_Oid);
                    break;
            #endif
            }
            break;

#ifndef NO_HMAC
        case oidHmacType:
            switch (id) {
        #ifdef WOLFSSL_SHA224
                case HMAC_SHA224_OID:
                    oid = hmacSha224Oid;
                    *oidSz = sizeof(hmacSha224Oid);
                    break;
        #endif
        #ifndef NO_SHA256
                case HMAC_SHA256_OID:
                    oid = hmacSha256Oid;
                    *oidSz = sizeof(hmacSha256Oid);
                    break;
        #endif
        #ifdef WOLFSSL_SHA384
                case HMAC_SHA384_OID:
                    oid = hmacSha384Oid;
                    *oidSz = sizeof(hmacSha384Oid);
                    break;
        #endif
        #ifdef WOLFSSL_SHA512
                case HMAC_SHA512_OID:
                    oid = hmacSha512Oid;
                    *oidSz = sizeof(hmacSha512Oid);
                    break;
        #endif
            }
            break;
#endif /* !NO_HMAC */

#ifdef HAVE_LIBZ
        case oidCompressType:
            switch (id) {
                case ZLIBc:
                    oid = zlibCompress;
                    *oidSz = sizeof(zlibCompress);
                    break;
            }
            break;
#endif /* HAVE_LIBZ */
#ifdef WOLFSSL_APACHE_HTTPD
        case oidCertNameType:
            switch (id) {
                 case NID_id_on_dnsSRV:
                    oid = dnsSRVOid;
                    *oidSz = sizeof(dnsSRVOid);
                    break;
            }
            break;
        case oidTlsExtType:
            switch (id) {
                case TLS_FEATURE_OID:
                    oid = tlsFeatureOid;
                    *oidSz = sizeof(tlsFeatureOid);
                    break;
            }
            break;
#endif /* WOLFSSL_APACHE_HTTPD */
        case oidIgnoreType:
        default:
            break;
    }

    return oid;
}

#ifdef HAVE_OID_ENCODING
int EncodeObjectId(const word16* in, word32 inSz, byte* out, word32* outSz)
{
    int i, x, len;
    word32 d, t;

    /* check args */
    if (in == NULL || outSz == NULL) {
        return BAD_FUNC_ARG;
    }

    /* compute length of encoded OID */
    d = (in[0] * 40) + in[1];
    len = 0;
    for (i = 1; i < (int)inSz; i++) {
        x = 0;
        t = d;
        while (t) {
            x++;
            t >>= 1;
        }
        len += (x / 7) + ((x % 7) ? 1 : 0) + (d == 0 ? 1 : 0);

        if (i < (int)inSz - 1) {
            d = in[i + 1];
        }
    }

    if (out) {
        /* verify length */
        if ((int)*outSz < len) {
            return BUFFER_E; /* buffer provided is not large enough */
        }

        /* calc first byte */
        d = (in[0] * 40) + in[1];

        /* encode bytes */
        x = 0;
        for (i = 1; i < (int)inSz; i++) {
            if (d) {
                int y = x, z;
                byte mask = 0;
                while (d) {
                    out[x++] = (byte)((d & 0x7F) | mask);
                    d     >>= 7;
                    mask  |= 0x80;  /* upper bit is set on all but the last byte */
                }
                /* now swap bytes y...x-1 */
                z = x - 1;
                while (y < z) {
                    mask = out[y];
                    out[y] = out[z];
                    out[z] = mask;
                    ++y;
                    --z;
                }
            }
            else {
              out[x++] = 0x00; /* zero value */
            }

            /* next word */
            if (i < (int)inSz - 1) {
                d = in[i + 1];
            }
        }
    }

    /* return length */
    *outSz = len;

    return 0;
}
#endif /* HAVE_OID_ENCODING */

#ifdef HAVE_OID_DECODING
int DecodeObjectId(const byte* in, word32 inSz, word16* out, word32* outSz)
{
    int x = 0, y = 0;
    word32 t = 0;

    /* check args */
    if (in == NULL || outSz == NULL) {
        return BAD_FUNC_ARG;
    }

    /* decode bytes */
    while (inSz--) {
        t = (t << 7) | (in[x] & 0x7F);
        if (!(in[x] & 0x80)) {
            if (y >= (int)*outSz) {
                return BUFFER_E;
            }
            if (y == 0) {
                out[0] = (t / 40);
                out[1] = (t % 40);
                y = 2;
            }
            else {
                out[y++] = t;
            }
            t = 0; /* reset tmp */
        }
        x++;
    }

    /* return length */
    *outSz = y;

    return 0;
}
#endif /* HAVE_OID_DECODING */

/* Get the DER/BER encoding of an ASN.1 OBJECT_ID header.
 *
 * input     Buffer holding DER/BER encoded data.
 * inOutIdx  Current index into buffer to parse.
 * len       The number of bytes in the ASN.1 data.
 * maxIdx    Length of data in buffer.
 * returns BUFFER_E when there is not enough data to parse.
 *         ASN_OBJECt_ID_E when the OBJECT_ID tag is not found.
 *         ASN_PARSE_E when length is invalid.
 *         Otherwise, 0 to indicate success.
 */
int GetASNObjectId(const byte* input, word32* inOutIdx, int* len,
                          word32 maxIdx)
{
    word32 idx = *inOutIdx;
    int    length;
    byte   tag;

    if ((idx + 1) > maxIdx)
        return BUFFER_E;

    if (GetASNTag(input, &idx, &tag, maxIdx) != 0)
        return ASN_PARSE_E;

    if (tag != ASN_OBJECT_ID)
        return ASN_OBJECT_ID_E;

    if (GetLength(input, &idx, &length, maxIdx) < 0)
        return ASN_PARSE_E;

    *len = length;
    *inOutIdx = idx;
    return 0;
}

/* Set the DER/BER encoding of the ASN.1 OBJECT_ID header.
 *
 * len         Length of the OBJECT_ID data.
 * output      Buffer to write into.
 * returns the number of bytes added to the buffer.
 */
int SetObjectId(int len, byte* output)
{
    int idx = 0;

    output[idx++] = ASN_OBJECT_ID;
    idx += SetLength(len, output + idx);

    return idx;
}

int GetObjectId(const byte* input, word32* inOutIdx, word32* oid,
                                  word32 oidType, word32 maxIdx)
{
    int    ret = 0, length;
    word32 idx = *inOutIdx;
#ifndef NO_VERIFY_OID
    word32 actualOidSz = 0;
    const byte* actualOid;
#endif /* NO_VERIFY_OID */

    (void)oidType;
    WOLFSSL_ENTER("GetObjectId()");
    *oid = 0;

    ret = GetASNObjectId(input, &idx, &length, maxIdx);
    if (ret != 0)
        return ret;

#ifndef NO_VERIFY_OID
    actualOid = &input[idx];
    if (length > 0)
        actualOidSz = (word32)length;
#endif /* NO_VERIFY_OID */

    while (length--) {
        /* odd HC08 compiler behavior here when input[idx++] */
        *oid += (word32)input[idx];
        idx++;
    }
    /* just sum it up for now */

    *inOutIdx = idx;

#ifndef NO_VERIFY_OID
    {
        const byte* checkOid = NULL;
        word32 checkOidSz;
    #ifdef ASN_DUMP_OID
        word32 i;
    #endif

        if (oidType != oidIgnoreType) {
            checkOid = OidFromId(*oid, oidType, &checkOidSz);

        #ifdef ASN_DUMP_OID
            /* support for dumping OID information */
            printf("OID (Type %d, Sz %d, Sum %d): ", oidType, actualOidSz, *oid);
            for (i=0; i<actualOidSz; i++) {
                printf("%d, ", actualOid[i]);
            }
            printf("\n");
            #ifdef HAVE_OID_DECODING
            {
                word16 decOid[16];
                word32 decOidSz = sizeof(decOid);
                ret = DecodeObjectId(actualOid, actualOidSz, decOid, &decOidSz);
                if (ret == 0) {
                    printf("  Decoded (Sz %d): ", decOidSz);
                    for (i=0; i<decOidSz; i++) {
                        printf("%d.", decOid[i]);
                    }
                    printf("\n");
                }
                else {
                    printf("DecodeObjectId failed: %d\n", ret);
                }
            }
            #endif /* HAVE_OID_DECODING */
        #endif /* ASN_DUMP_OID */

            if (checkOid != NULL &&
                (checkOidSz != actualOidSz ||
                    XMEMCMP(actualOid, checkOid, checkOidSz) != 0)) {
                WOLFSSL_MSG("OID Check Failed");
                return ASN_UNKNOWN_OID_E;
            }
        }
    }
#endif /* NO_VERIFY_OID */

    return ret;
}

static int SkipObjectId(const byte* input, word32* inOutIdx, word32 maxIdx)
{
    word32 idx = *inOutIdx;
    int    length;
    int ret;

    ret = GetASNObjectId(input, &idx, &length, maxIdx);
    if (ret != 0)
        return ret;

    idx += length;
    *inOutIdx = idx;

    return 0;
}

int GetAlgoId(const byte* input, word32* inOutIdx, word32* oid,
                     word32 oidType, word32 maxIdx)
{
    int    length;
    word32 idx = *inOutIdx;
    int    ret;
    *oid = 0;

    WOLFSSL_ENTER("GetAlgoId");

    if (GetSequence(input, &idx, &length, maxIdx) < 0)
        return ASN_PARSE_E;

    if (GetObjectId(input, &idx, oid, oidType, maxIdx) < 0)
        return ASN_OBJECT_ID_E;

    /* could have NULL tag and 0 terminator, but may not */
    if (idx < maxIdx) {
        word32 localIdx = idx; /*use localIdx to not advance when checking tag*/
        byte   tag;

        if (GetASNTag(input, &localIdx, &tag, maxIdx) == 0) {
            if (tag == ASN_TAG_NULL) {
                ret = GetASNNull(input, &idx, maxIdx);
                if (ret != 0)
                    return ret;
            }
        }
    }

    *inOutIdx = idx;

    return 0;
}

#ifndef NO_RSA

#ifndef HAVE_USER_RSA
int wc_RsaPrivateKeyDecode(const byte* input, word32* inOutIdx, RsaKey* key,
                        word32 inSz)
{
    int version, length;

    if (inOutIdx == NULL || input == NULL || key == NULL) {
        return BAD_FUNC_ARG;
    }
    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

    if (GetMyVersion(input, inOutIdx, &version, inSz) < 0)
        return ASN_PARSE_E;

    key->type = RSA_PRIVATE;

    if (GetInt(&key->n,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->e,  input, inOutIdx, inSz) < 0 ||
#ifndef WOLFSSL_RSA_PUBLIC_ONLY
        GetInt(&key->d,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->p,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->q,  input, inOutIdx, inSz) < 0)
#else
        SkipInt(input, inOutIdx, inSz) < 0 ||
        SkipInt(input, inOutIdx, inSz) < 0 ||
        SkipInt(input, inOutIdx, inSz) < 0 )

#endif
            return ASN_RSA_KEY_E;
#if (defined(WOLFSSL_KEY_GEN) || defined(OPENSSL_EXTRA) || !defined(RSA_LOW_MEM)) \
    && !defined(WOLFSSL_RSA_PUBLIC_ONLY)
    if (GetInt(&key->dP, input, inOutIdx, inSz) < 0 ||
        GetInt(&key->dQ, input, inOutIdx, inSz) < 0 ||
        GetInt(&key->u,  input, inOutIdx, inSz) < 0 )  return ASN_RSA_KEY_E;
#else
    if (SkipInt(input, inOutIdx, inSz) < 0 ||
        SkipInt(input, inOutIdx, inSz) < 0 ||
        SkipInt(input, inOutIdx, inSz) < 0 )  return ASN_RSA_KEY_E;
#endif

#if defined(WOLFSSL_XILINX_CRYPT) || defined(WOLFSSL_CRYPTOCELL)
    if (wc_InitRsaHw(key) != 0) {
        return BAD_STATE_E;
    }
#endif

    return 0;
}
#endif /* HAVE_USER_RSA */
#endif /* NO_RSA */

#if defined(HAVE_PKCS8) || defined(HAVE_PKCS12)

/* Remove PKCS8 header, place inOutIdx at beginning of traditional,
 * return traditional length on success, negative on error */
int ToTraditionalInline_ex(const byte* input, word32* inOutIdx, word32 sz,
                           word32* algId)
{
    word32 idx;
    int    version, length;
    int    ret;
    byte   tag;

    if (input == NULL || inOutIdx == NULL)
        return BAD_FUNC_ARG;

    idx = *inOutIdx;

    if (GetSequence(input, &idx, &length, sz) < 0)
        return ASN_PARSE_E;

    if (GetMyVersion(input, &idx, &version, sz) < 0)
        return ASN_PARSE_E;

    if (GetAlgoId(input, &idx, algId, oidKeyType, sz) < 0)
        return ASN_PARSE_E;

    if (GetASNTag(input, &idx, &tag, sz) < 0)
        return ASN_PARSE_E;
    idx = idx - 1; /* reset idx after finding tag */

    if (tag == ASN_OBJECT_ID) {
        if (SkipObjectId(input, &idx, sz) < 0)
            return ASN_PARSE_E;
    }

    ret = GetOctetString(input, &idx, &length, sz);
    if (ret < 0) {
        if (ret == BUFFER_E)
            return ASN_PARSE_E;
        /* Some private keys don't expect an octet string */
        WOLFSSL_MSG("Couldn't find Octet string");
    }

    *inOutIdx = idx;

    return length;
}

int ToTraditionalInline(const byte* input, word32* inOutIdx, word32 sz)
{
    word32 oid;

    return ToTraditionalInline_ex(input, inOutIdx, sz, &oid);
}

/* Remove PKCS8 header, move beginning of traditional to beginning of input */
int ToTraditional_ex(byte* input, word32 sz, word32* algId)
{
    word32 inOutIdx = 0;
    int    length;

    if (input == NULL)
        return BAD_FUNC_ARG;

    length = ToTraditionalInline_ex(input, &inOutIdx, sz, algId);
    if (length < 0)
        return length;

    if (length + inOutIdx > sz)
        return BUFFER_E;

    XMEMMOVE(input, input + inOutIdx, length);

    return length;
}

int ToTraditional(byte* input, word32 sz)
{
    word32 oid;

    return ToTraditional_ex(input, sz, &oid);
}

#endif /* HAVE_PKCS8 || HAVE_PKCS12 */

#ifdef HAVE_PKCS8

/* find beginning of traditional key inside PKCS#8 unencrypted buffer
 * return traditional length on success, with inOutIdx at beginning of
 * traditional
 * return negative on failure/error */
int wc_GetPkcs8TraditionalOffset(byte* input, word32* inOutIdx, word32 sz)
{
    int length;
    word32 algId;

    if (input == NULL || inOutIdx == NULL || (*inOutIdx > sz))
        return BAD_FUNC_ARG;

    length = ToTraditionalInline_ex(input, inOutIdx, sz, &algId);

    return length;
}


/* PKCS#8 from RFC 5208
 * This function takes in a DER key and converts it to PKCS#8 format. Used
 * in creating PKCS#12 shrouded key bags.
 * Reverse of ToTraditional
 *
 * PrivateKeyInfo ::= SEQUENCE {
 *  version Version,
 *  privateKeyAlgorithm PrivateKeyAlgorithmIdentifier,
 *  privateKey          PrivateKey,
 *  attributes          optional
 *  }
 *  Version ::= INTEGER
 *  PrivateKeyAlgorithmIdentifier ::= AlgorithmIdentifier
 *  PrivateKey ::= OCTET STRING
 *
 * out      buffer to place result in
 * outSz    size of out buffer
 * key      buffer with DER key
 * keySz    size of key buffer
 * algoID   algorithm ID i.e. RSAk
 * curveOID ECC curve oid if used. Should be NULL for RSA keys.
 * oidSz    size of curve oid. Is set to 0 if curveOID is NULL.
 *
 * Returns the size of PKCS#8 placed into out. In error cases returns negative
 * values.
 */
int wc_CreatePKCS8Key(byte* out, word32* outSz, byte* key, word32 keySz,
        int algoID, const byte* curveOID, word32 oidSz)
{
        word32 keyIdx = 0;
        word32 tmpSz  = 0;
        word32 sz;


        /* If out is NULL then return the max size needed
         * + 2 for ASN_OBJECT_ID and ASN_OCTET_STRING tags */
        if (out == NULL && outSz != NULL) {
            *outSz = keySz + MAX_SEQ_SZ + MAX_VERSION_SZ + MAX_ALGO_SZ
                     + MAX_LENGTH_SZ + MAX_LENGTH_SZ + 2;

            if (curveOID != NULL)
                *outSz += oidSz + MAX_LENGTH_SZ + 1;

            WOLFSSL_MSG("Checking size of PKCS8");

            return LENGTH_ONLY_E;
        }

        WOLFSSL_ENTER("wc_CreatePKCS8Key()");

        if (key == NULL || out == NULL || outSz == NULL) {
            return BAD_FUNC_ARG;
        }

        /* check the buffer has enough room for largest possible size */
        if (curveOID != NULL) {
            if (*outSz < (keySz + MAX_SEQ_SZ + MAX_VERSION_SZ + MAX_ALGO_SZ
                   + MAX_LENGTH_SZ + MAX_LENGTH_SZ + 3 + oidSz + MAX_LENGTH_SZ))
                return BUFFER_E;
        }
        else {
            oidSz = 0; /* with no curveOID oid size must be 0 */
            if (*outSz < (keySz + MAX_SEQ_SZ + MAX_VERSION_SZ + MAX_ALGO_SZ
                      + MAX_LENGTH_SZ + MAX_LENGTH_SZ + 2))
                return BUFFER_E;
        }

        /* PrivateKeyInfo ::= SEQUENCE */
        keyIdx += MAX_SEQ_SZ; /* save room for sequence */

        /*  version Version
         *  no header information just INTEGER */
        sz = SetMyVersion(PKCS8v0, out + keyIdx, 0);
        tmpSz += sz; keyIdx += sz;

        /*  privateKeyAlgorithm PrivateKeyAlgorithmIdentifier */
        sz = 0; /* set sz to 0 and get privateKey oid buffer size needed */
        if (curveOID != NULL && oidSz > 0) {
            byte buf[MAX_LENGTH_SZ];
            sz = SetLength(oidSz, buf);
            sz += 1; /* plus one for ASN object id */
        }
        sz = SetAlgoID(algoID, out + keyIdx, oidKeyType, oidSz + sz);
        tmpSz += sz; keyIdx += sz;

        /*  privateKey          PrivateKey *
         * pkcs8 ecc uses slightly different format. Places curve oid in
         * buffer */
        if (curveOID != NULL && oidSz > 0) {
            sz = SetObjectId(oidSz, out + keyIdx);
            keyIdx += sz; tmpSz += sz;
            XMEMCPY(out + keyIdx, curveOID, oidSz);
            keyIdx += oidSz; tmpSz += oidSz;
        }

        sz = SetOctetString(keySz, out + keyIdx);
        keyIdx += sz; tmpSz += sz;
        XMEMCPY(out + keyIdx, key, keySz);
        tmpSz += keySz;

        /*  attributes          optional
         * No attributes currently added */

        /* rewind and add sequence */
        sz = SetSequence(tmpSz, out);
        XMEMMOVE(out + sz, out + MAX_SEQ_SZ, tmpSz);

        return tmpSz + sz;
}

#endif /* HAVE_PKCS8 */

#if defined(HAVE_PKCS12) || !defined(NO_CHECK_PRIVATE_KEY)
/* check that the private key is a pair for the public key in certificate
 * return 1 (true) on match
 * return 0 or negative value on failure/error
 *
 * key   : buffer holding DER format key
 * keySz : size of key buffer
 * der   : a initialized and parsed DecodedCert holding a certificate */
int wc_CheckPrivateKey(byte* key, word32 keySz, DecodedCert* der)
{
    int ret;
    (void)keySz;

    if (key == NULL || der == NULL) {
        return BAD_FUNC_ARG;
    }

    #if !defined(NO_RSA) && !defined(NO_ASN_CRYPT)
    /* test if RSA key */
    if (der->keyOID == RSAk) {
    #ifdef WOLFSSL_SMALL_STACK
        RsaKey* a;
        RsaKey* b = NULL;
    #else
        RsaKey a[1], b[1];
    #endif
        word32 keyIdx = 0;

    #ifdef WOLFSSL_SMALL_STACK
        a = (RsaKey*)XMALLOC(sizeof(RsaKey), NULL, DYNAMIC_TYPE_RSA);
        if (a == NULL)
            return MEMORY_E;
        b = (RsaKey*)XMALLOC(sizeof(RsaKey), NULL, DYNAMIC_TYPE_RSA);
        if (b == NULL) {
            XFREE(a, NULL, DYNAMIC_TYPE_RSA);
            return MEMORY_E;
        }
    #endif

        if ((ret = wc_InitRsaKey(a, NULL)) < 0) {
    #ifdef WOLFSSL_SMALL_STACK
            XFREE(b, NULL, DYNAMIC_TYPE_RSA);
            XFREE(a, NULL, DYNAMIC_TYPE_RSA);
    #endif
            return ret;
        }
        if ((ret = wc_InitRsaKey(b, NULL)) < 0) {
            wc_FreeRsaKey(a);
    #ifdef WOLFSSL_SMALL_STACK
            XFREE(b, NULL, DYNAMIC_TYPE_RSA);
            XFREE(a, NULL, DYNAMIC_TYPE_RSA);
    #endif
            return ret;
        }
        if ((ret = wc_RsaPrivateKeyDecode(key, &keyIdx, a, keySz)) == 0) {
            WOLFSSL_MSG("Checking RSA key pair");
            keyIdx = 0; /* reset to 0 for parsing public key */

            if ((ret = wc_RsaPublicKeyDecode(der->publicKey, &keyIdx, b,
                                                       der->pubKeySize)) == 0) {
                /* limit for user RSA crypto because of RsaKey
                 * dereference. */
            #if defined(HAVE_USER_RSA)
                WOLFSSL_MSG("Cannot verify RSA pair with user RSA");
                ret = 1; /* return first RSA cert as match */
            #else
                /* both keys extracted successfully now check n and e
                 * values are the same. This is dereferencing RsaKey */
                if (mp_cmp(&(a->n), &(b->n)) != MP_EQ ||
                    mp_cmp(&(a->e), &(b->e)) != MP_EQ) {
                    ret = MP_CMP_E;
                }
                else
                    ret = 1;
            #endif
            }
        }
        wc_FreeRsaKey(b);
        wc_FreeRsaKey(a);
    #ifdef WOLFSSL_SMALL_STACK
        XFREE(b, NULL, DYNAMIC_TYPE_RSA);
        XFREE(a, NULL, DYNAMIC_TYPE_RSA);
    #endif
    }
    else
    #endif /* !NO_RSA && !NO_ASN_CRYPT */

    #if defined(HAVE_ECC) && defined(HAVE_ECC_KEY_EXPORT) && !defined(NO_ASN_CRYPT)
    if (der->keyOID == ECDSAk) {
    #ifdef WOLFSSL_SMALL_STACK
        ecc_key* key_pair;
        byte*    privDer;
    #else
        ecc_key  key_pair[1];
        byte     privDer[MAX_ECC_BYTES];
    #endif
        word32   privSz = MAX_ECC_BYTES;
        word32   keyIdx = 0;

    #ifdef WOLFSSL_SMALL_STACK
        key_pair = (ecc_key*)XMALLOC(sizeof(ecc_key), NULL, DYNAMIC_TYPE_ECC);
        if (key_pair == NULL)
            return MEMORY_E;
        privDer = (byte*)XMALLOC(MAX_ECC_BYTES, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (privDer == NULL) {
            XFREE(key_pair, NULL, DYNAMIC_TYPE_ECC);
            return MEMORY_E;
        }
    #endif

        if ((ret = wc_ecc_init(key_pair)) < 0) {
    #ifdef WOLFSSL_SMALL_STACK
            XFREE(privDer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(key_pair, NULL, DYNAMIC_TYPE_ECC);
    #endif
            return ret;
        }

        if ((ret = wc_EccPrivateKeyDecode(key, &keyIdx, key_pair,
                                                                 keySz)) == 0) {
            WOLFSSL_MSG("Checking ECC key pair");

            if ((ret = wc_ecc_export_private_only(key_pair, privDer, &privSz))
                                                                         == 0) {
                wc_ecc_free(key_pair);
                ret = wc_ecc_init(key_pair);
                if (ret == 0) {
                    ret = wc_ecc_import_private_key((const byte*)privDer,
                                            privSz, (const byte*)der->publicKey,
                                            der->pubKeySize, key_pair);
                }

                /* public and private extracted successfully now check if is
                 * a pair and also do sanity checks on key. wc_ecc_check_key
                 * checks that private * base generator equals pubkey */
                if (ret == 0) {
                    if ((ret = wc_ecc_check_key(key_pair)) == 0) {
                        ret = 1;
                    }
                }
                ForceZero(privDer, privSz);
            }
        }
        wc_ecc_free(key_pair);
    #ifdef WOLFSSL_SMALL_STACK
        XFREE(privDer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(key_pair, NULL, DYNAMIC_TYPE_ECC);
    #endif
    }
    else
    #endif /* HAVE_ECC && HAVE_ECC_KEY_EXPORT && !NO_ASN_CRYPT */

    #if defined(HAVE_ED25519) && !defined(NO_ASN_CRYPT)
    if (der->keyOID == ED25519k) {
    #ifdef WOLFSSL_SMALL_STACK
        ed25519_key* key_pair;
    #else
        ed25519_key  key_pair[1];
    #endif
        word32       keyIdx = 0;

    #ifdef WOLFSSL_SMALL_STACK
        key_pair = (ed25519_key*)XMALLOC(sizeof(ed25519_key), NULL,
                                                          DYNAMIC_TYPE_ED25519);
        if (key_pair == NULL)
            return MEMORY_E;
    #endif

        if ((ret = wc_ed25519_init(key_pair)) < 0) {
    #ifdef WOLFSSL_SMALL_STACK
            XFREE(key_pair, NULL, DYNAMIC_TYPE_ED25519);
    #endif
            return ret;
        }
        if ((ret = wc_Ed25519PrivateKeyDecode(key, &keyIdx, key_pair,
                                                                 keySz)) == 0) {
            WOLFSSL_MSG("Checking ED25519 key pair");
            keyIdx = 0;
            if ((ret = wc_ed25519_import_public(der->publicKey, der->pubKeySize,
                                                              key_pair)) == 0) {
                /* public and private extracted successfully no check if is
                 * a pair and also do sanity checks on key. wc_ecc_check_key
                 * checks that private * base generator equals pubkey */
                if ((ret = wc_ed25519_check_key(key_pair)) == 0)
                    ret = 1;
            }
        }
        wc_ed25519_free(key_pair);
    #ifdef WOLFSSL_SMALL_STACK
        XFREE(key_pair, NULL, DYNAMIC_TYPE_ED25519);
    #endif
    }
    else
    #endif /* HAVE_ED25519 && !NO_ASN_CRYPT */

    #if defined(HAVE_ED448) && !defined(NO_ASN_CRYPT)
    if (der->keyOID == ED448k) {
    #ifdef WOLFSSL_SMALL_STACK
        ed448_key* key_pair = NULL;
    #else
        ed448_key  key_pair[1];
    #endif
        word32     keyIdx = 0;

    #ifdef WOLFSSL_SMALL_STACK
        key_pair = (ed448_key*)XMALLOC(sizeof(ed448_key), NULL,
                                                            DYNAMIC_TYPE_ED448);
        if (key_pair == NULL)
            return MEMORY_E;
    #endif

        if ((ret = wc_ed448_init(key_pair)) < 0) {
    #ifdef WOLFSSL_SMALL_STACK
            XFREE(key_pair, NULL, DYNAMIC_TYPE_ED448);
    #endif
            return ret;
        }
        if ((ret = wc_Ed448PrivateKeyDecode(key, &keyIdx, key_pair,
                                                                 keySz)) == 0) {
            WOLFSSL_MSG("Checking ED448 key pair");
            keyIdx = 0;
            if ((ret = wc_ed448_import_public(der->publicKey, der->pubKeySize,
                                                              key_pair)) == 0) {
                /* public and private extracted successfully no check if is
                 * a pair and also do sanity checks on key. wc_ecc_check_key
                 * checks that private * base generator equals pubkey */
                if ((ret = wc_ed448_check_key(key_pair)) == 0)
                    ret = 1;
            }
        }
        wc_ed448_free(key_pair);
    #ifdef WOLFSSL_SMALL_STACK
        XFREE(key_pair, NULL, DYNAMIC_TYPE_ED448);
    #endif
    }
    else
    #endif /* HAVE_ED448 && !NO_ASN_CRYPT */
    {
        ret = 0;
    }

    (void)keySz;

    return ret;
}

#endif /* HAVE_PKCS12 || !NO_CHECK_PRIVATE_KEY */

#ifndef NO_PWDBASED

#if defined(HAVE_PKCS8) || defined(HAVE_PKCS12)
/* Check To see if PKCS version algo is supported, set id if it is return 0
   < 0 on error */
static int CheckAlgo(int first, int second, int* id, int* version, int* blockSz)
{
    *id      = ALGO_ID_E;
    *version = PKCS5;   /* default */
    if (blockSz) *blockSz = 8; /* default */

    if (first == 1) {
        switch (second) {
#if !defined(NO_SHA)
    #ifndef NO_RC4
        case PBE_SHA1_RC4_128:
            *id = PBE_SHA1_RC4_128;
            *version = PKCS12v1;
            return 0;
    #endif
    #ifndef NO_DES3
        case PBE_SHA1_DES3:
            *id = PBE_SHA1_DES3;
            *version = PKCS12v1;
            if (blockSz) *blockSz = DES_BLOCK_SIZE;
            return 0;
        case PBE_SHA1_DES:
            *id = PBE_SHA1_DES;
            *version = PKCS12v1;
            if (blockSz) *blockSz = DES_BLOCK_SIZE;
            return 0;
    #endif
#endif /* !NO_SHA */
        default:
            return ALGO_ID_E;
        }
    }

    if (first != PKCS5)
        return ASN_INPUT_E;  /* VERSION ERROR */

    if (second == PBES2) {
        *version = PKCS5v2;
        return 0;
    }

    switch (second) {
#ifndef NO_DES3
    #ifndef NO_MD5
    case 3:                   /* see RFC 2898 for ids */
        *id = PBE_MD5_DES;
        if (blockSz) *blockSz = DES_BLOCK_SIZE;
        return 0;
    #endif
    #ifndef NO_SHA
    case 10:
        *id = PBE_SHA1_DES;
        if (blockSz) *blockSz = DES_BLOCK_SIZE;
        return 0;
    #endif
#endif /* !NO_DES3 */
    default:
        return ALGO_ID_E;

    }
}

/* Check To see if PKCS v2 algo is supported, set id if it is return 0
   < 0 on error */
static int CheckAlgoV2(int oid, int* id, int* blockSz)
{
    if (blockSz) *blockSz = 8; /* default */
    (void)id; /* not used if AES and DES3 disabled */
    switch (oid) {
#if !defined(NO_DES3) && !defined(NO_SHA)
    case DESb:
        *id = PBE_SHA1_DES;
        if (blockSz) *blockSz = DES_BLOCK_SIZE;
        return 0;
    case DES3b:
        *id = PBE_SHA1_DES3;
        if (blockSz) *blockSz = DES_BLOCK_SIZE;
        return 0;
#endif
#ifdef WOLFSSL_AES_256
    case AES256CBCb:
        *id = PBE_AES256_CBC;
        if (blockSz) *blockSz = AES_BLOCK_SIZE;
        return 0;
#endif
#ifdef WOLFSSL_AES_128
    case AES128CBCb:
        *id = PBE_AES128_CBC;
        if (blockSz) *blockSz = AES_BLOCK_SIZE;
        return 0;
#endif
    default:
        WOLFSSL_MSG("No PKCS v2 algo found");
        return ALGO_ID_E;

    }
}

#endif /* HAVE_PKCS8 || HAVE_PKCS12 */

#ifdef HAVE_PKCS8

int wc_GetKeyOID(byte* key, word32 keySz, const byte** curveOID, word32* oidSz,
        int* algoID, void* heap)
{
    word32 tmpIdx = 0;

    if (key == NULL || algoID == NULL)
        return BAD_FUNC_ARG;

    *algoID = 0;

    #if !defined(NO_RSA) && !defined(NO_ASN_CRYPT)
    {
        RsaKey rsa;

        wc_InitRsaKey(&rsa, heap);
        if (wc_RsaPrivateKeyDecode(key, &tmpIdx, &rsa, keySz) == 0) {
            *algoID = RSAk;
        }
        else {
            WOLFSSL_MSG("Not RSA DER key");
        }
        wc_FreeRsaKey(&rsa);
    }
    #endif /* !NO_RSA && !NO_ASN_CRYPT */
    #if defined(HAVE_ECC) && !defined(NO_ASN_CRYPT)
    if (*algoID == 0) {
        ecc_key ecc;

        tmpIdx = 0;
        wc_ecc_init_ex(&ecc, heap, INVALID_DEVID);
        if (wc_EccPrivateKeyDecode(key, &tmpIdx, &ecc, keySz) == 0) {
            *algoID = ECDSAk;

            /* now find oid */
            if (wc_ecc_get_oid(ecc.dp->oidSum, curveOID, oidSz) < 0) {
                WOLFSSL_MSG("Error getting ECC curve OID");
                wc_ecc_free(&ecc);
                return BAD_FUNC_ARG;
            }
        }
        else {
            WOLFSSL_MSG("Not ECC DER key either");
        }
        wc_ecc_free(&ecc);
    }
#endif /* HAVE_ECC && !NO_ASN_CRYPT */
#if defined(HAVE_ED25519) && !defined(NO_ASN_CRYPT)
    if (*algoID != RSAk && *algoID != ECDSAk) {
        ed25519_key ed25519;

        tmpIdx = 0;
        if (wc_ed25519_init(&ed25519) == 0) {
            if (wc_Ed25519PrivateKeyDecode(key, &tmpIdx, &ed25519, keySz)
                                                                         == 0) {
                *algoID = ED25519k;
            }
            else {
                WOLFSSL_MSG("Not ED25519 DER key");
            }
            wc_ed25519_free(&ed25519);
        }
        else {
            WOLFSSL_MSG("GetKeyOID wc_ed25519_init failed");
        }
    }
#endif /* HAVE_ED25519 && !NO_ASN_CRYPT */
#if defined(HAVE_ED448) && !defined(NO_ASN_CRYPT)
    if (*algoID != RSAk && *algoID != ECDSAk && *algoID != ED25519k) {
        ed448_key ed448;

        tmpIdx = 0;
        if (wc_ed448_init(&ed448) == 0) {
            if (wc_Ed448PrivateKeyDecode(key, &tmpIdx, &ed448, keySz) == 0) {
                *algoID = ED448k;
            }
            else {
                WOLFSSL_MSG("Not ED448 DER key");
            }
            wc_ed448_free(&ed448);
        }
        else {
            WOLFSSL_MSG("GetKeyOID wc_ed448_init failed");
        }
    }
#endif /* HAVE_ED448 && !NO_ASN_CRYPT */

    /* if flag is not set then is neither RSA or ECC key that could be
     * found */
    if (*algoID == 0) {
        WOLFSSL_MSG("Bad key DER or compile options");
        return BAD_FUNC_ARG;
    }

    (void)tmpIdx;
    (void)curveOID;
    (void)oidSz;
    (void)keySz;
    (void)heap;

    return 1;
}

#endif /* HAVE_PKCS8 */

#if defined(HAVE_PKCS8) || defined(HAVE_PKCS12)

#define PKCS8_MIN_BLOCK_SIZE 8
static int Pkcs8Pad(byte* buf, int sz, int blockSz)
{
    int i, padSz;

    /* calculate pad size */
    padSz = blockSz - (sz & (blockSz - 1));

    /* pad with padSz value */
    if (buf) {
        for (i = 0; i < padSz; i++) {
            buf[sz+i] = (byte)(padSz & 0xFF);
        }
    }

    /* return adjusted length */
    return sz + padSz;
}

#endif /* HAVE_PKCS8 || HAVE_PKCS12 */

#ifdef HAVE_PKCS8

/*
 * Used when creating PKCS12 shrouded key bags
 * vPKCS is the version of PKCS to use
 * vAlgo is the algorithm version to use
 *
 * if salt is NULL a random number is generated
 *
 * returns the size of encrypted data on success
 */
int UnTraditionalEnc(byte* key, word32 keySz, byte* out, word32* outSz,
        const char* password, int passwordSz, int vPKCS, int vAlgo,
        byte* salt, word32 saltSz, int itt, WC_RNG* rng, void* heap)
{
    int algoID = 0;
    byte*  tmp;
    word32 tmpSz = 0;
    word32 sz;
    word32 seqSz;
    word32 inOutIdx = 0;
    word32 totalSz = 0;
    int    version, id;
    int    ret;
    int    blockSz = 0;

    const byte* curveOID = NULL;
    word32 oidSz   = 0;

#ifdef WOLFSSL_SMALL_STACK
    byte*  saltTmp = NULL;
    byte*  cbcIv   = NULL;
#else
    byte   saltTmp[MAX_IV_SIZE];
    byte   cbcIv[MAX_IV_SIZE];
#endif

    WOLFSSL_ENTER("UnTraditionalEnc()");

    if (saltSz > MAX_SALT_SIZE)
        return ASN_PARSE_E;


    inOutIdx += MAX_SEQ_SZ; /* leave room for size of finished shroud */
    if (CheckAlgo(vPKCS, vAlgo, &id, &version, &blockSz) < 0) {
        WOLFSSL_MSG("Bad/Unsupported algorithm ID");
        return ASN_INPUT_E;  /* Algo ID error */
    }

    if (out != NULL) {
        if (*outSz < inOutIdx + MAX_ALGO_SZ + MAX_SALT_SIZE + MAX_SEQ_SZ + 1 +
                MAX_LENGTH_SZ + MAX_SHORT_SZ + 1)
                return BUFFER_E;

        if (version == PKCS5v2) {
            WOLFSSL_MSG("PKCS5v2 Not supported yet\n");
            return ASN_VERSION_E;
        }

        if (salt == NULL || saltSz == 0) {
            saltSz = 8;
        #ifdef WOLFSSL_SMALL_STACK
            saltTmp = (byte*)XMALLOC(saltSz, heap, DYNAMIC_TYPE_TMP_BUFFER);
            if (saltTmp == NULL)
                return MEMORY_E;
        #endif
            salt = saltTmp;

            if ((ret = wc_RNG_GenerateBlock(rng, saltTmp, saltSz)) != 0) {
                WOLFSSL_MSG("Error generating random salt");
            #ifdef WOLFSSL_SMALL_STACK
                if (saltTmp != NULL)
                    XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
            #endif
                return ret;
            }
        }


        /* leave room for a sequence (contains salt and iterations int) */
        inOutIdx += MAX_SEQ_SZ; sz = 0;
        inOutIdx += MAX_ALGO_SZ;

        /* place salt in buffer */
        out[inOutIdx++] = ASN_OCTET_STRING; sz++;
        tmpSz = SetLength(saltSz, out + inOutIdx);
        inOutIdx += tmpSz; sz += tmpSz;
        XMEMCPY(out + inOutIdx, salt, saltSz);
        inOutIdx += saltSz; sz += saltSz;

        /* place iteration count in buffer */
        ret = SetShortInt(out, &inOutIdx, itt, *outSz);
        if (ret < 0) {
        #ifdef WOLFSSL_SMALL_STACK
            if (saltTmp != NULL)
                XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
        #endif
            return ret;
        }
        sz += (word32)ret;

        /* wind back index and set sequence then clean up buffer */
        inOutIdx -= (sz + MAX_SEQ_SZ);
        tmpSz = SetSequence(sz, out + inOutIdx);
        XMEMMOVE(out + inOutIdx + tmpSz, out + inOutIdx + MAX_SEQ_SZ, sz);
        totalSz += tmpSz + sz; sz += tmpSz;

        /* add in algo ID */
        inOutIdx -= MAX_ALGO_SZ;
        tmpSz =  SetAlgoID(id, out + inOutIdx, oidPBEType, sz);
        XMEMMOVE(out + inOutIdx + tmpSz, out + inOutIdx + MAX_ALGO_SZ, sz);
        totalSz += tmpSz; inOutIdx += tmpSz + sz;

        /* octet string containing encrypted key */
        out[inOutIdx++] = ASN_OCTET_STRING; totalSz++;
    }

    /* check key type and get OID if ECC */
    if ((ret = wc_GetKeyOID(key, keySz, &curveOID, &oidSz, &algoID, heap))< 0) {
        WOLFSSL_MSG("Error getting key OID");
    #ifdef WOLFSSL_SMALL_STACK
        if (saltTmp != NULL)
            XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        return ret;
    }

    /* PKCS#8 wrapping around key */
    if (wc_CreatePKCS8Key(NULL, &tmpSz, key, keySz, algoID, curveOID, oidSz)
            != LENGTH_ONLY_E) {
    #ifdef WOLFSSL_SMALL_STACK
        if (saltTmp != NULL)
            XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        return MEMORY_E;
    }

    /* check if should return max size */
    if (out == NULL) {
        /* account for salt size */
        if (salt == NULL || saltSz == 0) {
            tmpSz += MAX_SALT_SIZE;
        }
        else {
            tmpSz += saltSz;
        }

        /* plus 3 for tags */
        *outSz = tmpSz + MAX_ALGO_SZ + MAX_LENGTH_SZ +MAX_LENGTH_SZ + MAX_SEQ_SZ
            + MAX_LENGTH_SZ + MAX_SEQ_SZ + 3;
    #ifdef WOLFSSL_SMALL_STACK
        if (saltTmp != NULL)
            XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        return LENGTH_ONLY_E;
    }

    /* reserve buffer for crypto and make sure it supports full blocks */
    tmp = (byte*)XMALLOC(tmpSz + (blockSz-1), heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (tmp == NULL) {
    #ifdef WOLFSSL_SMALL_STACK
        if (saltTmp != NULL)
            XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        return MEMORY_E;
    }

    if ((ret = wc_CreatePKCS8Key(tmp, &tmpSz, key, keySz, algoID, curveOID,
                    oidSz)) < 0) {
        XFREE(tmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
        WOLFSSL_MSG("Error wrapping key with PKCS#8");
    #ifdef WOLFSSL_SMALL_STACK
        if (saltTmp != NULL)
            XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        return ret;
    }
    tmpSz = ret;

    /* adjust size to pad */
    tmpSz = Pkcs8Pad(tmp, tmpSz, blockSz);

#ifdef WOLFSSL_SMALL_STACK
    cbcIv = (byte*)XMALLOC(MAX_IV_SIZE, heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (cbcIv == NULL) {
        if (saltTmp != NULL)
            XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(tmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
#endif

    /* encrypt PKCS#8 wrapped key */
    if ((ret = wc_CryptKey(password, passwordSz, salt, saltSz, itt, id,
               tmp, tmpSz, version, cbcIv, 1, 0)) < 0) {
        XFREE(tmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
        WOLFSSL_MSG("Error encrypting key");
    #ifdef WOLFSSL_SMALL_STACK
        if (saltTmp != NULL)
            XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
        if (cbcIv != NULL)
            XFREE(cbcIv, heap, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        return ret;  /* encryption failure */
    }
    totalSz += tmpSz;

#ifdef WOLFSSL_SMALL_STACK
    if (saltTmp != NULL)
        XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (cbcIv != NULL)
        XFREE(cbcIv, heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    if (*outSz < inOutIdx + tmpSz + MAX_LENGTH_SZ) {
        XFREE(tmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
        return BUFFER_E;
    }

    /* set length of key and copy over encrypted key */
    seqSz = SetLength(tmpSz, out + inOutIdx);
    inOutIdx += seqSz; totalSz += seqSz;
    XMEMCPY(out + inOutIdx, tmp, tmpSz);
    XFREE(tmp, heap, DYNAMIC_TYPE_TMP_BUFFER);

    /* set total size at beginning */
    sz = SetSequence(totalSz, out);
    XMEMMOVE(out + sz, out + MAX_SEQ_SZ, totalSz);

    (void)rng;

    return totalSz + sz;
}

static int GetAlgoV2(int encAlgId, const byte** oid, int *len, int* id,
                     int *blkSz)
{
    int ret = 0;

    switch (encAlgId) {
#if !defined(NO_DES3) && !defined(NO_SHA)
    case DESb:
        *len = sizeof(blkDesCbcOid);
        *oid = blkDesCbcOid;
        *id = PBE_SHA1_DES;
        *blkSz = 8;
        break;
    case DES3b:
        *len = sizeof(blkDes3CbcOid);
        *oid = blkDes3CbcOid;
        *id = PBE_SHA1_DES3;
        *blkSz = 8;
        break;
#endif
#if defined(WOLFSSL_AES_256) && defined(HAVE_AES_CBC)
    case AES256CBCb:
        *len = sizeof(blkAes256CbcOid);
        *oid = blkAes256CbcOid;
        *id = PBE_AES256_CBC;
        *blkSz = 16;
        break;
#endif
    default:
        (void)len;
        (void)oid;
        (void)id;
        (void)blkSz;
        ret = ALGO_ID_E;
    }

    return ret;
}

/* Converts Encrypted PKCS#8 to 'traditional' (i.e. PKCS#8 removed from
 * decrypted key.)
 */
int TraditionalEnc(byte* key, word32 keySz, byte* out, word32* outSz,
        const char* password, int passwordSz, int vPKCS, int vAlgo,
        int encAlgId, byte* salt, word32 saltSz, int itt, WC_RNG* rng,
        void* heap)
{
    int ret = 0;
    int version, blockSz, id;
    word32 idx = 0, encIdx;
#ifdef WOLFSSL_SMALL_STACK
    byte* saltTmp = NULL;
#else
    byte saltTmp[MAX_SALT_SIZE];
#endif
    byte cbcIv[MAX_IV_SIZE];
    byte *pkcs8Key = NULL;
    word32 pkcs8KeySz = 0, padSz = 0;
    int algId = 0;
    const byte* curveOid = NULL;
    word32 curveOidSz = 0;
    const byte* pbeOid = NULL;
    word32 pbeOidSz = 0;
    const byte* encOid = NULL;
    int encOidSz = 0;
    word32 pbeLen = 0, kdfLen = 0, encLen = 0;
    word32 innerLen = 0, outerLen;

    ret = CheckAlgo(vPKCS, vAlgo, &id, &version, &blockSz);
    /* create random salt if one not provided */
    if (ret == 0 && (salt == NULL || saltSz == 0)) {
        saltSz = 8;
    #ifdef WOLFSSL_SMALL_STACK
        saltTmp = (byte*)XMALLOC(saltSz, heap, DYNAMIC_TYPE_TMP_BUFFER);
        if (saltTmp == NULL)
            return MEMORY_E;
    #endif
        salt = saltTmp;

        if ((ret = wc_RNG_GenerateBlock(rng, saltTmp, saltSz)) != 0) {
            WOLFSSL_MSG("Error generating random salt");
        #ifdef WOLFSSL_SMALL_STACK
            XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
        #endif
            return ret;
        }
    }

    if (ret == 0) {
        /* check key type and get OID if ECC */
        ret = wc_GetKeyOID(key, keySz, &curveOid, &curveOidSz, &algId, heap);
        if (ret == 1)
            ret = 0;
    }
    if (ret == 0) {
        ret = wc_CreatePKCS8Key(NULL, &pkcs8KeySz, key, keySz, algId, curveOid,
                                                                    curveOidSz);
        if (ret == LENGTH_ONLY_E)
            ret = 0;
    }
    if (ret == 0) {
        pkcs8Key = (byte*)XMALLOC(pkcs8KeySz, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (pkcs8Key == NULL)
            ret = MEMORY_E;
    }
    if (ret == 0) {
        ret = wc_CreatePKCS8Key(pkcs8Key, &pkcs8KeySz, key, keySz, algId,
                                                          curveOid, curveOidSz);
        if (ret >= 0) {
            pkcs8KeySz = ret;
            ret = 0;
        }
    }

    if (ret == 0 && version == PKCS5v2)
        ret = GetAlgoV2(encAlgId, &encOid, &encOidSz, &id, &blockSz);

    if (ret == 0) {
        padSz = (blockSz - (pkcs8KeySz & (blockSz - 1))) & (blockSz - 1);
        /* inner = OCT salt INT itt */
        innerLen = 2 + saltSz + 2 + (itt < 256 ? 1 : 2);

        if (version != PKCS5v2) {
            pbeOid = OidFromId(id, oidPBEType, &pbeOidSz);
            /* pbe = OBJ pbse1 SEQ [ inner ] */
            pbeLen = 2 + pbeOidSz + 2 + innerLen;
        }
        else {
            pbeOid = pbes2;
            pbeOidSz = sizeof(pbes2);
            /* kdf = OBJ pbkdf2 [ SEQ innerLen ] */
            kdfLen = 2 + sizeof(pbkdf2Oid) + 2 + innerLen;
            /* enc = OBJ enc_alg OCT iv */
            encLen = 2 + encOidSz + 2 + blockSz;
            /* pbe = OBJ pbse2 SEQ [ SEQ [ kdf ] SEQ [ enc ] ] */
            pbeLen = 2 + sizeof(pbes2) + 2 + 2 + kdfLen + 2 + encLen;

            ret = wc_RNG_GenerateBlock(rng, cbcIv, blockSz);
        }
    }
    if (ret == 0) {
        /* outer = SEQ [ pbe ] OCT encrypted_PKCS#8_key */
        outerLen = 2 + pbeLen;
        outerLen += SetOctetString(pkcs8KeySz + padSz, out);
        outerLen += pkcs8KeySz + padSz;

        idx += SetSequence(outerLen, out + idx);

        encIdx = idx + outerLen - pkcs8KeySz - padSz;
        /* Put Encrypted content in place. */
        XMEMCPY(out + encIdx, pkcs8Key, pkcs8KeySz);
        if (padSz > 0) {
            XMEMSET(out + encIdx + pkcs8KeySz, padSz, padSz);
            pkcs8KeySz += padSz;
        }
        ret = wc_CryptKey(password, passwordSz, salt, saltSz, itt, id,
                                out + encIdx, pkcs8KeySz, version, cbcIv, 1, 0);
    }
    if (ret == 0) {
        if (version != PKCS5v2) {
            /* PBE algorithm */
            idx += SetSequence(pbeLen, out + idx);
            idx += SetObjectId(pbeOidSz, out + idx);
            XMEMCPY(out + idx, pbeOid, pbeOidSz);
            idx += pbeOidSz;
        }
        else {
            /* PBES2 algorithm identifier */
            idx += SetSequence(pbeLen, out + idx);
            idx += SetObjectId(pbeOidSz, out + idx);
            XMEMCPY(out + idx, pbeOid, pbeOidSz);
            idx += pbeOidSz;
            /* PBES2 Parameters: SEQ [ kdf ] SEQ [ enc ] */
            idx += SetSequence(2 + kdfLen + 2 + encLen, out + idx);
            /* KDF Algorithm Identifier */
            idx += SetSequence(kdfLen, out + idx);
            idx += SetObjectId(sizeof(pbkdf2Oid), out + idx);
            XMEMCPY(out + idx, pbkdf2Oid, sizeof(pbkdf2Oid));
            idx += sizeof(pbkdf2Oid);
        }
        idx += SetSequence(innerLen, out + idx);
        idx += SetOctetString(saltSz, out + idx);
        XMEMCPY(out + idx, salt, saltSz); idx += saltSz;
        ret = SetShortInt(out, &idx, itt, *outSz);
        if (ret > 0)
            ret = 0;
    }
    if (ret == 0) {
        if (version == PKCS5v2) {
            /* Encryption Algorithm Identifier */
            idx += SetSequence(encLen, out + idx);
            idx += SetObjectId(encOidSz, out + idx);
            XMEMCPY(out + idx, encOid, encOidSz);
            idx += encOidSz;
            /* Encryption Algorithm Parameter: CBC IV */
            idx += SetOctetString(blockSz, out + idx);
            XMEMCPY(out + idx, cbcIv, blockSz);
            idx += blockSz;
        }
        idx += SetOctetString(pkcs8KeySz, out + idx);
        /* Default PRF - no need to write out OID */
        idx += pkcs8KeySz;

        ret = idx;
    }

    if (pkcs8Key != NULL) {
        ForceZero(pkcs8Key, pkcs8KeySz);
        XFREE(pkcs8Key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#ifdef WOLFSSL_SMALL_STACK
    if (saltTmp != NULL) {
        XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    (void)rng;

    return ret;
}

#endif /* HAVE_PKCS8 */

#if defined(HAVE_PKCS8) || defined(HAVE_PKCS12)
/* decrypt PKCS
 *
 * NOTE: input buffer is overwritten with decrypted data!
 *
 * input[in/out] data to decrypt and results are written to
 * sz            size of input buffer
 * password      password if used. Can be NULL for no password
 * passwordSz    size of password buffer
 *
 * returns the total size of decrypted content on success.
 */
int DecryptContent(byte* input, word32 sz, const char* password, int passwordSz)
{
    word32 inOutIdx = 0, seqEnd, oid, shaOid = 0;
    int    ret = 0, first, second, length = 0, version, saltSz, id;
    int    iterations = 0, keySz = 0;
#ifdef WOLFSSL_SMALL_STACK
    byte*  salt = NULL;
    byte*  cbcIv = NULL;
#else
    byte   salt[MAX_SALT_SIZE];
    byte   cbcIv[MAX_IV_SIZE];
#endif
    byte   tag;

    if (passwordSz < 0) {
        WOLFSSL_MSG("Bad password size");
        return BAD_FUNC_ARG;
    }

    if (GetAlgoId(input, &inOutIdx, &oid, oidIgnoreType, sz) < 0) {
        ERROR_OUT(ASN_PARSE_E, exit_dc);
    }

    first  = input[inOutIdx - 2];   /* PKCS version always 2nd to last byte */
    second = input[inOutIdx - 1];   /* version.algo, algo id last byte */

    if (CheckAlgo(first, second, &id, &version, NULL) < 0) {
        ERROR_OUT(ASN_INPUT_E, exit_dc); /* Algo ID error */
    }

    if (version == PKCS5v2) {
        if (GetSequence(input, &inOutIdx, &length, sz) < 0) {
            ERROR_OUT(ASN_PARSE_E, exit_dc);
        }

        if (GetAlgoId(input, &inOutIdx, &oid, oidKdfType, sz) < 0) {
            ERROR_OUT(ASN_PARSE_E, exit_dc);
        }

        if (oid != PBKDF2_OID) {
            ERROR_OUT(ASN_PARSE_E, exit_dc);
        }
    }

    if (GetSequence(input, &inOutIdx, &length, sz) <= 0) {
        ERROR_OUT(ASN_PARSE_E, exit_dc);
    }
    /* Find the end of this SEQUENCE so we can check for the OPTIONAL and
     * DEFAULT items. */
    seqEnd = inOutIdx + length;

    ret = GetOctetString(input, &inOutIdx, &saltSz, sz);
    if (ret < 0)
        goto exit_dc;

    if (saltSz > MAX_SALT_SIZE) {
        ERROR_OUT(ASN_PARSE_E, exit_dc);
    }

#ifdef WOLFSSL_SMALL_STACK
    salt = (byte*)XMALLOC(MAX_SALT_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (salt == NULL) {
        ERROR_OUT(MEMORY_E, exit_dc);
    }
#endif

    XMEMCPY(salt, &input[inOutIdx], saltSz);
    inOutIdx += saltSz;

    if (GetShortInt(input, &inOutIdx, &iterations, sz) < 0) {
        ERROR_OUT(ASN_PARSE_E, exit_dc);
    }

    /* OPTIONAL key length */
    if (seqEnd > inOutIdx) {
        word32 localIdx = inOutIdx;

        if (GetASNTag(input, &localIdx, &tag, sz) < 0) {
            ERROR_OUT(ASN_PARSE_E, exit_dc);
        }

        if (tag == ASN_INTEGER &&
                GetShortInt(input, &inOutIdx, &keySz, sz) < 0) {
            ERROR_OUT(ASN_PARSE_E, exit_dc);
        }
    }

    /* DEFAULT HMAC is SHA-1 */
    if (seqEnd > inOutIdx) {
        if (GetAlgoId(input, &inOutIdx, &oid, oidHmacType, sz) < 0) {
            ERROR_OUT(ASN_PARSE_E, exit_dc);
        }

        shaOid = oid;
    }

#ifdef WOLFSSL_SMALL_STACK
    cbcIv = (byte*)XMALLOC(MAX_IV_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (cbcIv == NULL) {
        ERROR_OUT(MEMORY_E, exit_dc);
    }
#endif

    if (version == PKCS5v2) {
        /* get encryption algo */
        if (GetAlgoId(input, &inOutIdx, &oid, oidBlkType, sz) < 0) {
            ERROR_OUT(ASN_PARSE_E, exit_dc);
        }

        if (CheckAlgoV2(oid, &id, NULL) < 0) {
            ERROR_OUT(ASN_PARSE_E, exit_dc); /* PKCS v2 algo id error */
        }

        if (shaOid == 0)
            shaOid = oid;

        ret = GetOctetString(input, &inOutIdx, &length, sz);
        if (ret < 0)
            goto exit_dc;

        if (length > MAX_IV_SIZE) {
            ERROR_OUT(ASN_PARSE_E, exit_dc);
        }

        XMEMCPY(cbcIv, &input[inOutIdx], length);
        inOutIdx += length;
    }

    if (GetASNTag(input, &inOutIdx, &tag, sz) < 0) {
        ERROR_OUT(ASN_PARSE_E, exit_dc);
    }

    if (tag != (ASN_CONTEXT_SPECIFIC | 0) && tag != ASN_OCTET_STRING) {
        ERROR_OUT(ASN_PARSE_E, exit_dc);
    }

    if (GetLength(input, &inOutIdx, &length, sz) < 0) {
        ERROR_OUT(ASN_PARSE_E, exit_dc);
    }

    ret = wc_CryptKey(password, passwordSz, salt, saltSz, iterations, id,
                   input + inOutIdx, length, version, cbcIv, 0, shaOid);

exit_dc:
#ifdef WOLFSSL_SMALL_STACK
    XFREE(salt,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(cbcIv, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    if (ret == 0) {
        XMEMMOVE(input, input + inOutIdx, length);
        ret = length;
    }

    return ret;
}


/* Remove Encrypted PKCS8 header, move beginning of traditional to beginning
   of input */
int ToTraditionalEnc(byte* input, word32 sz,const char* password,
                     int passwordSz, word32* algId)
{
    int ret, length;
    word32 inOutIdx = 0;

    if (GetSequence(input, &inOutIdx, &length, sz) < 0) {
        ret = ASN_PARSE_E;
    }
    else {
        ret = DecryptContent(input + inOutIdx, sz - inOutIdx, password,
                passwordSz);
        if (ret > 0) {
            XMEMMOVE(input, input + inOutIdx, ret);
            ret = ToTraditional_ex(input, ret, algId);
        }
    }

    return ret;
}

#endif /* HAVE_PKCS8 || HAVE_PKCS12 */

#ifdef HAVE_PKCS12

/* encrypt PKCS 12 content
 *
 * NOTE: if out is NULL then outSz is set with the total buffer size needed and
 *       the error value LENGTH_ONLY_E is returned.
 *
 * input      data to encrypt
 * inputSz    size of input buffer
 * out        buffer to hold the result
 * outSz      size of out buffer
 * password   password if used. Can be NULL for no password
 * passwordSz size of password buffer
 * vPKCS      version of PKCS i.e. PKCS5v2
 * vAlgo      algorithm version
 * salt       buffer holding salt if used. If NULL then a random salt is created
 * saltSz     size of salt buffer if it is not NULL
 * itt        number of iterations used
 * rng        random number generator to use
 * heap       possible heap hint for mallocs/frees
 *
 * returns the total size of encrypted content on success.
 *
 * data returned is :
 * [ seq - obj [ seq -salt,itt]] , construct with encrypted data
 */
int EncryptContent(byte* input, word32 inputSz, byte* out, word32* outSz,
        const char* password, int passwordSz, int vPKCS, int vAlgo,
        byte* salt, word32 saltSz, int itt, WC_RNG* rng, void* heap)
{
    word32 sz;
    word32 inOutIdx = 0;
    word32 tmpIdx   = 0;
    word32 totalSz  = 0;
    word32 seqSz;
    word32 innerSz;
    int    ret;
    int    version, id, blockSz = 0;
#ifdef WOLFSSL_SMALL_STACK
    byte*  saltTmp = NULL;
    byte*  cbcIv   = NULL;
#else
    byte   saltTmp[MAX_SALT_SIZE];
    byte   cbcIv[MAX_IV_SIZE];
#endif
    byte   seq[MAX_SEQ_SZ];
    byte   shr[MAX_SHORT_SZ];
    word32 maxShr = MAX_SHORT_SZ;
    word32 algoSz;
    const  byte* algoName;

    (void)heap;

    WOLFSSL_ENTER("EncryptContent()");

    if (CheckAlgo(vPKCS, vAlgo, &id, &version, &blockSz) < 0)
        return ASN_INPUT_E;  /* Algo ID error */

    if (version == PKCS5v2) {
        WOLFSSL_MSG("PKCS#5 version 2 not supported yet");
        return BAD_FUNC_ARG;
    }

    if (saltSz > MAX_SALT_SIZE)
        return ASN_PARSE_E;

    if (outSz == NULL) {
        return BAD_FUNC_ARG;
    }

    /* calculate size */
    /* size of constructed string at end */
    sz = Pkcs8Pad(NULL, inputSz, blockSz);
    totalSz  = ASN_TAG_SZ;
    totalSz += SetLength(sz, seq);
    totalSz += sz;

    /* size of sequence holding object id and sub sequence of salt and itt */
    algoName = OidFromId(id, oidPBEType, &algoSz);
    if (algoName == NULL) {
        WOLFSSL_MSG("Unknown Algorithm");
        return 0;
    }
    innerSz = SetObjectId(algoSz, seq);
    innerSz += algoSz;

    /* get subsequence of salt and itt */
    if (salt == NULL || saltSz == 0) {
        sz = 8;
    }
    else {
        sz = saltSz;
    }
    seqSz  = SetOctetString(sz, seq);
    seqSz += sz;

    tmpIdx = 0;
    seqSz += SetShortInt(shr, &tmpIdx, itt, maxShr);
    innerSz += seqSz + SetSequence(seqSz, seq);
    totalSz += innerSz + SetSequence(innerSz, seq);

    if (out == NULL) {
        *outSz = totalSz;
        return LENGTH_ONLY_E;
    }

    inOutIdx = 0;
    if (totalSz > *outSz)
        return BUFFER_E;

    inOutIdx += SetSequence(innerSz, out + inOutIdx);
    inOutIdx += SetObjectId(algoSz, out + inOutIdx);
    XMEMCPY(out + inOutIdx, algoName, algoSz);
    inOutIdx += algoSz;
    inOutIdx += SetSequence(seqSz, out + inOutIdx);

    /* create random salt if one not provided */
    if (salt == NULL || saltSz == 0) {
        saltSz = 8;
    #ifdef WOLFSSL_SMALL_STACK
        saltTmp = (byte*)XMALLOC(saltSz, heap, DYNAMIC_TYPE_TMP_BUFFER);
        if (saltTmp == NULL)
            return MEMORY_E;
    #endif
        salt = saltTmp;

        if ((ret = wc_RNG_GenerateBlock(rng, saltTmp, saltSz)) != 0) {
            WOLFSSL_MSG("Error generating random salt");
        #ifdef WOLFSSL_SMALL_STACK
            XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
        #endif
            return ret;
        }
    }
    inOutIdx += SetOctetString(saltSz, out + inOutIdx);
    if (saltSz + inOutIdx > *outSz) {
    #ifdef WOLFSSL_SMALL_STACK
        XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        return BUFFER_E;
    }
    XMEMCPY(out + inOutIdx, salt, saltSz);
    inOutIdx += saltSz;

    /* place iteration setting in buffer */
    ret = SetShortInt(out, &inOutIdx, itt, *outSz);
    if (ret < 0) {
    #ifdef WOLFSSL_SMALL_STACK
        XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        return ret;
    }

    if (inOutIdx + 1 > *outSz) {
    #ifdef WOLFSSL_SMALL_STACK
        XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        return BUFFER_E;
    }
    out[inOutIdx++] = ASN_CONTEXT_SPECIFIC | 0;

    /* get pad size and verify buffer room */
    sz = Pkcs8Pad(NULL, inputSz, blockSz);
    if (sz + inOutIdx > *outSz) {
    #ifdef WOLFSSL_SMALL_STACK
        XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        return BUFFER_E;
    }
    inOutIdx += SetLength(sz, out + inOutIdx);

    /* copy input to output buffer and pad end */
    XMEMCPY(out + inOutIdx, input, inputSz);
    sz = Pkcs8Pad(out + inOutIdx, inputSz, blockSz);
#ifdef WOLFSSL_SMALL_STACK
    cbcIv = (byte*)XMALLOC(MAX_IV_SIZE, heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (cbcIv == NULL) {
        XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
#endif

    /* encrypt */
    if ((ret = wc_CryptKey(password, passwordSz, salt, saltSz, itt, id,
                   out + inOutIdx, sz, version, cbcIv, 1, 0)) < 0) {

    #ifdef WOLFSSL_SMALL_STACK
        XFREE(cbcIv,   heap, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        return ret;  /* encrypt failure */
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(cbcIv,   heap, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(saltTmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    (void)rng;

    return inOutIdx + sz;
}


#endif /* HAVE_PKCS12 */
#endif /* NO_PWDBASED */

#ifndef NO_RSA

#ifndef HAVE_USER_RSA
#ifdef WOLFSSL_RENESAS_TSIP
/* This function is to retrieve key position information in a cert.*
 * The information will be used to call TSIP TLS-linked API for    *
 * certificate verification.                                       */
static int RsaPublicKeyDecodeRawIndex(const byte* input, word32* inOutIdx,
                                      word32 inSz, word32* key_n,
                                      word32* key_n_len, word32* key_e,
                                      word32* key_e_len)
{

    int ret = 0;
    int length = 0;
#if defined(OPENSSL_EXTRA) || defined(RSA_DECODE_EXTRA)
    byte b;
#endif

    if (input == NULL || inOutIdx == NULL)
        return BAD_FUNC_ARG;

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

#if defined(OPENSSL_EXTRA) || defined(RSA_DECODE_EXTRA)
    if ((*inOutIdx + 1) > inSz)
        return BUFFER_E;

    b = input[*inOutIdx];
    if (b != ASN_INTEGER) {
        /* not from decoded cert, will have algo id, skip past */
        if (GetSequence(input, inOutIdx, &length, inSz) < 0)
            return ASN_PARSE_E;

        if (SkipObjectId(input, inOutIdx, inSz) < 0)
            return ASN_PARSE_E;

        /* Option NULL ASN.1 tag */
        if (*inOutIdx  >= inSz) {
            return BUFFER_E;
        }
        if (input[*inOutIdx] == ASN_TAG_NULL) {
            ret = GetASNNull(input, inOutIdx, inSz);
            if (ret != 0)
                return ret;
        }

        /* should have bit tag length and seq next */
        ret = CheckBitString(input, inOutIdx, NULL, inSz, 1, NULL);
        if (ret != 0)
            return ret;

        if (GetSequence(input, inOutIdx, &length, inSz) < 0)
            return ASN_PARSE_E;
    }
#endif /* OPENSSL_EXTRA */

    /* Get modulus */
    ret = GetASNInt(input, inOutIdx, &length, inSz);
    *key_n += *inOutIdx;
    if (ret < 0) {
        return ASN_RSA_KEY_E;
    }
    if (key_n_len)
        *key_n_len = length;
    *inOutIdx += length;

    /* Get exponent */
    ret = GetASNInt(input, inOutIdx, &length, inSz);
    *key_e += *inOutIdx;
    if (ret < 0) {
        return ASN_RSA_KEY_E;
    }
    if (key_e_len)
        *key_e_len = length;

    return ret;
}
#endif /* WOLFSSL_RENESAS_TSIP */

int wc_RsaPublicKeyDecode_ex(const byte* input, word32* inOutIdx, word32 inSz,
    const byte** n, word32* nSz, const byte** e, word32* eSz)
{
    int ret = 0;
    int length = 0;
#if defined(OPENSSL_EXTRA) || defined(RSA_DECODE_EXTRA)
    word32 localIdx;
    byte   tag;
#endif

    if (input == NULL || inOutIdx == NULL)
        return BAD_FUNC_ARG;

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

#if defined(OPENSSL_EXTRA) || defined(RSA_DECODE_EXTRA)
    localIdx = *inOutIdx;
    if (GetASNTag(input, &localIdx, &tag, inSz) < 0)
        return BUFFER_E;

    if (tag != ASN_INTEGER) {
        /* not from decoded cert, will have algo id, skip past */
        if (GetSequence(input, inOutIdx, &length, inSz) < 0)
            return ASN_PARSE_E;

        if (SkipObjectId(input, inOutIdx, inSz) < 0)
            return ASN_PARSE_E;

        /* Option NULL ASN.1 tag */
        if (*inOutIdx  >= inSz) {
            return BUFFER_E;
        }

        localIdx = *inOutIdx;
        if (GetASNTag(input, &localIdx, &tag, inSz) < 0)
            return ASN_PARSE_E;

        if (tag == ASN_TAG_NULL) {
            ret = GetASNNull(input, inOutIdx, inSz);
            if (ret != 0)
                return ret;
        }

        /* should have bit tag length and seq next */
        ret = CheckBitString(input, inOutIdx, NULL, inSz, 1, NULL);
        if (ret != 0)
            return ret;

        if (GetSequence(input, inOutIdx, &length, inSz) < 0)
            return ASN_PARSE_E;
    }
#endif /* OPENSSL_EXTRA */

    /* Get modulus */
    ret = GetASNInt(input, inOutIdx, &length, inSz);
    if (ret < 0) {
        return ASN_RSA_KEY_E;
    }
    if (nSz)
        *nSz = length;
    if (n)
        *n = &input[*inOutIdx];
    *inOutIdx += length;

    /* Get exponent */
    ret = GetASNInt(input, inOutIdx, &length, inSz);
    if (ret < 0) {
        return ASN_RSA_KEY_E;
    }
    if (eSz)
        *eSz = length;
    if (e)
        *e = &input[*inOutIdx];
    *inOutIdx += length;

    return ret;
}

int wc_RsaPublicKeyDecode(const byte* input, word32* inOutIdx, RsaKey* key,
                       word32 inSz)
{
    int ret;
    const byte *n = NULL, *e = NULL;
    word32 nSz = 0, eSz = 0;

    if (key == NULL)
        return BAD_FUNC_ARG;

    ret = wc_RsaPublicKeyDecode_ex(input, inOutIdx, inSz, &n, &nSz, &e, &eSz);
    if (ret == 0) {
        ret = wc_RsaPublicKeyDecodeRaw(n, nSz, e, eSz, key);
    }

    return ret;
}

/* import RSA public key elements (n, e) into RsaKey structure (key) */
int wc_RsaPublicKeyDecodeRaw(const byte* n, word32 nSz, const byte* e,
                             word32 eSz, RsaKey* key)
{
    if (n == NULL || e == NULL || key == NULL)
        return BAD_FUNC_ARG;

    key->type = RSA_PUBLIC;

    if (mp_init(&key->n) != MP_OKAY)
        return MP_INIT_E;

    if (mp_read_unsigned_bin(&key->n, n, nSz) != 0) {
        mp_clear(&key->n);
        return ASN_GETINT_E;
    }
#ifdef HAVE_WOLF_BIGINT
    if ((int)nSz > 0 && wc_bigint_from_unsigned_bin(&key->n.raw, n, nSz) != 0) {
        mp_clear(&key->n);
        return ASN_GETINT_E;
    }
#endif /* HAVE_WOLF_BIGINT */

    if (mp_init(&key->e) != MP_OKAY) {
        mp_clear(&key->n);
        return MP_INIT_E;
    }

    if (mp_read_unsigned_bin(&key->e, e, eSz) != 0) {
        mp_clear(&key->n);
        mp_clear(&key->e);
        return ASN_GETINT_E;
    }
#ifdef HAVE_WOLF_BIGINT
    if ((int)eSz > 0 && wc_bigint_from_unsigned_bin(&key->e.raw, e, eSz) != 0) {
        mp_clear(&key->n);
        mp_clear(&key->e);
        return ASN_GETINT_E;
    }
#endif /* HAVE_WOLF_BIGINT */

#ifdef WOLFSSL_XILINX_CRYPT
    if (wc_InitRsaHw(key) != 0) {
        return BAD_STATE_E;
    }
#endif

    return 0;
}
#endif /* HAVE_USER_RSA */
#endif /* !NO_RSA */

#ifndef NO_DH
/* Supports either:
 * - DH params G/P (PKCS#3 DH) file or 
 * - DH key file (if WOLFSSL_DH_EXTRA enabled) */
/* The wc_DhParamsLoad function also loads DH params, but directly into buffers, not DhKey */
int wc_DhKeyDecode(const byte* input, word32* inOutIdx, DhKey* key, word32 inSz)
{
    int ret = 0;
    int length;
#ifdef WOLFSSL_DH_EXTRA
    #if !defined(HAVE_FIPS) || \
        (defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION > 2))
    word32 oid = 0, temp = 0;
    #endif
#endif

    WOLFSSL_ENTER("wc_DhKeyDecode");

    if (inOutIdx == NULL)
        return BAD_FUNC_ARG;

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

#ifdef WOLFSSL_DH_EXTRA
    #if !defined(HAVE_FIPS) || \
        (defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION > 2))
    temp = *inOutIdx;
    #endif
#endif
    /* Assume input started after 1.2.840.113549.1.3.1 dhKeyAgreement */
    if (GetInt(&key->p,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->g,  input, inOutIdx, inSz) < 0) {
        ret = ASN_DH_KEY_E;
    }

#ifdef WOLFSSL_DH_EXTRA
    #if !defined(HAVE_FIPS) || \
        (defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION > 2))
    /* If ASN_DH_KEY_E: Check if input started at beginning of key */
    if (ret == ASN_DH_KEY_E) {
        *inOutIdx = temp;

        /* the version (0) */
        if (GetASNInt(input, inOutIdx, &length, inSz) < 0) {
            return ASN_PARSE_E;
        }
        *inOutIdx += length;

        /* Size of dhKeyAgreement section */
        if (GetSequence(input, inOutIdx, &length, inSz) < 0)
            return ASN_PARSE_E;

        /* Check for dhKeyAgreement */
        ret = GetObjectId(input, inOutIdx, &oid, oidKeyType, inSz);
        if (oid != DHk || ret < 0)
            return ASN_DH_KEY_E;

        if (GetSequence(input, inOutIdx, &length, inSz) < 0)
            return ASN_PARSE_E;

        if (GetInt(&key->p, input, inOutIdx, inSz) < 0 ||
            GetInt(&key->g, input, inOutIdx, inSz) < 0) {
            return ASN_DH_KEY_E;
        }
    }

    temp = *inOutIdx;
    ret = (CheckBitString(input, inOutIdx, &length, inSz, 0, NULL) == 0);
    if (ret > 0) {
        /* Found Bit String */
        if (GetInt(&key->pub, input, inOutIdx, inSz) == 0) {
            WOLFSSL_MSG("Found Public Key");
            ret = 0;
        }
    } else {
        *inOutIdx = temp;
        ret = (GetOctetString(input, inOutIdx, &length, inSz) >= 0);
        if (ret > 0) {
            /* Found Octet String */
            if (GetInt(&key->priv, input, inOutIdx, inSz) == 0) {
                WOLFSSL_MSG("Found Private Key");

                /* Compute public */
                ret = mp_exptmod(&key->g, &key->priv, &key->p, &key->pub);
            }
        } else {
            /* Don't use length from failed CheckBitString/GetOctetString */
            *inOutIdx = temp;
            ret = 0;
        }
    }
    #endif /* !HAVE_FIPS || HAVE_FIPS_VERSION > 2 */
#endif /* WOLFSSL_DH_EXTRA */

    WOLFSSL_LEAVE("wc_DhKeyDecode", ret);

    return ret;
}

int wc_DhParamsLoad(const byte* input, word32 inSz, byte* p, word32* pInOutSz,
                 byte* g, word32* gInOutSz)
{
    word32 idx = 0;
    int    ret;
    int    length;

    if (GetSequence(input, &idx, &length, inSz) <= 0)
        return ASN_PARSE_E;

    ret = GetASNInt(input, &idx, &length, inSz);
    if (ret != 0)
        return ret;

    if (length <= (int)*pInOutSz) {
        XMEMCPY(p, &input[idx], length);
        *pInOutSz = length;
    }
    else {
        return BUFFER_E;
    }
    idx += length;

    ret = GetASNInt(input, &idx, &length, inSz);
    if (ret != 0)
        return ret;

    if (length <= (int)*gInOutSz) {
        XMEMCPY(g, &input[idx], length);
        *gInOutSz = length;
    }
    else {
        return BUFFER_E;
    }

    return 0;
}
#endif /* !NO_DH */


#ifndef NO_DSA

int DsaPublicKeyDecode(const byte* input, word32* inOutIdx, DsaKey* key,
                        word32 inSz)
{
    int    length;
    int    ret = 0;
    word32 oid;

    if (input == NULL || inOutIdx == NULL || key == NULL)
        return BAD_FUNC_ARG;

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

    if (GetInt(&key->p,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->q,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->g,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->y,  input, inOutIdx, inSz) < 0 )
        ret = ASN_DH_KEY_E;

    if (ret != 0) {
        if (GetSequence(input, inOutIdx, &length, inSz) < 0)
            return ASN_PARSE_E;

        ret = GetObjectId(input, inOutIdx, &oid, oidIgnoreType, inSz);
        if (ret != 0)
            return ret;

        if (GetSequence(input, inOutIdx, &length, inSz) < 0)
            return ASN_PARSE_E;

        if (GetInt(&key->p,  input, inOutIdx, inSz) < 0 ||
            GetInt(&key->q,  input, inOutIdx, inSz) < 0 ||
            GetInt(&key->g,  input, inOutIdx, inSz) < 0)
            return ASN_DH_KEY_E;

        if (CheckBitString(input, inOutIdx, &length, inSz, 0, NULL) < 0)
            return ASN_PARSE_E;

        if (GetInt(&key->y,  input, inOutIdx, inSz) < 0 )
            return ASN_DH_KEY_E;

        ret = 0;
    }

    key->type = DSA_PUBLIC;
    return ret;
}


int DsaPrivateKeyDecode(const byte* input, word32* inOutIdx, DsaKey* key,
                        word32 inSz)
{
    int    length, version, ret = 0, temp = 0;

    /* Sanity checks on input */
    if (input == NULL || inOutIdx == NULL || key == NULL) {
        return BAD_FUNC_ARG;
    }

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

    temp = (int)*inOutIdx;

    /* Default case expects a certificate with OctetString but no version ID */
    ret = GetInt(&key->p, input, inOutIdx, inSz);
    if (ret < 0) {
        mp_clear(&key->p);
        ret = ASN_PARSE_E;
    }
    else {
        ret = GetInt(&key->q, input, inOutIdx, inSz);
        if (ret < 0) {
            mp_clear(&key->p);
            mp_clear(&key->q);
            ret = ASN_PARSE_E;
        }
        else {
            ret = GetInt(&key->g, input, inOutIdx, inSz);
            if (ret < 0) {
                mp_clear(&key->p);
                mp_clear(&key->q);
                mp_clear(&key->g);
                ret = ASN_PARSE_E;
            }
            else {
                ret = GetOctetString(input, inOutIdx, &length, inSz);
                if (ret < 0) {
                    mp_clear(&key->p);
                    mp_clear(&key->q);
                    mp_clear(&key->g);
                    ret = ASN_PARSE_E;
                }
                else {
                    ret = GetInt(&key->y, input, inOutIdx, inSz);
                    if (ret < 0) {
                        mp_clear(&key->p);
                        mp_clear(&key->q);
                        mp_clear(&key->g);
                        mp_clear(&key->y);
                        ret = ASN_PARSE_E;
                    }
                }
            }
        }
    }
    /* An alternate pass if default certificate fails parsing */
    if (ret == ASN_PARSE_E) {
        *inOutIdx = temp;
        if (GetMyVersion(input, inOutIdx, &version, inSz) < 0)
            return ASN_PARSE_E;

        if (GetInt(&key->p,  input, inOutIdx, inSz) < 0 ||
            GetInt(&key->q,  input, inOutIdx, inSz) < 0 ||
            GetInt(&key->g,  input, inOutIdx, inSz) < 0 ||
            GetInt(&key->y,  input, inOutIdx, inSz) < 0 ||
            GetInt(&key->x,  input, inOutIdx, inSz) < 0 )
            return ASN_DH_KEY_E;
    }

    key->type = DSA_PRIVATE;
    return 0;
}

static mp_int* GetDsaInt(DsaKey* key, int idx)
{
    if (idx == 0)
        return &key->p;
    if (idx == 1)
        return &key->q;
    if (idx == 2)
        return &key->g;
    if (idx == 3)
        return &key->y;
    if (idx == 4)
        return &key->x;

    return NULL;
}

/* Release Tmp DSA resources */
static WC_INLINE void FreeTmpDsas(byte** tmps, void* heap)
{
    int i;

    for (i = 0; i < DSA_INTS; i++)
        XFREE(tmps[i], heap, DYNAMIC_TYPE_DSA);

    (void)heap;
}

#if !defined(HAVE_SELFTEST) && defined(WOLFSSL_KEY_GEN)
/* Write a public DSA key to output */
int wc_SetDsaPublicKey(byte* output, DsaKey* key,
                           int outLen, int with_header)
{
    /* p, g, q = DSA params, y = public exponent */
#ifdef WOLFSSL_SMALL_STACK
    byte* p = NULL;
    byte* g = NULL;
    byte* q = NULL;
    byte* y = NULL;
#else
    byte p[MAX_DSA_INT_SZ];
    byte g[MAX_DSA_INT_SZ];
    byte q[MAX_DSA_INT_SZ];
    byte y[MAX_DSA_INT_SZ];
#endif
    byte innerSeq[MAX_SEQ_SZ];
    byte outerSeq[MAX_SEQ_SZ];
    byte bitString[1 + MAX_LENGTH_SZ + 1];
    int  idx, pSz, gSz, qSz, ySz, innerSeqSz, outerSeqSz, bitStringSz = 0;

    WOLFSSL_ENTER("wc_SetDsaPublicKey");

    if (output == NULL || key == NULL || outLen < MAX_SEQ_SZ) {
        return BAD_FUNC_ARG;
    }

    /* p */
#ifdef WOLFSSL_SMALL_STACK
    p = (byte*)XMALLOC(MAX_DSA_INT_SZ, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (p == NULL)
        return MEMORY_E;
#endif
    if ((pSz = SetASNIntMP(&key->p, MAX_DSA_INT_SZ, p)) < 0) {
        WOLFSSL_MSG("SetASNIntMP Error with p");
#ifdef WOLFSSL_SMALL_STACK
        XFREE(p, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return pSz;
    }

    /* q */
#ifdef WOLFSSL_SMALL_STACK
    q = (byte*)XMALLOC(MAX_DSA_INT_SZ, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (q == NULL)
        return MEMORY_E;
#endif
    if ((qSz = SetASNIntMP(&key->q, MAX_DSA_INT_SZ, q)) < 0) {
        WOLFSSL_MSG("SetASNIntMP Error with q");
#ifdef WOLFSSL_SMALL_STACK
        XFREE(p, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(q, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return qSz;
    }

    /* g */
#ifdef WOLFSSL_SMALL_STACK
    g = (byte*)XMALLOC(MAX_DSA_INT_SZ, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (g == NULL)
        return MEMORY_E;
#endif
    if ((gSz = SetASNIntMP(&key->g, MAX_DSA_INT_SZ, g)) < 0) {
        WOLFSSL_MSG("SetASNIntMP Error with g");
#ifdef WOLFSSL_SMALL_STACK
        XFREE(p, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(q, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(g, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return gSz;
    }

    /* y */
#ifdef WOLFSSL_SMALL_STACK
    y = (byte*)XMALLOC(MAX_DSA_INT_SZ, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (y == NULL)
        return MEMORY_E;
#endif
    if ((ySz = SetASNIntMP(&key->y, MAX_DSA_INT_SZ, y)) < 0) {
        WOLFSSL_MSG("SetASNIntMP Error with y");
#ifdef WOLFSSL_SMALL_STACK
        XFREE(p, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(q, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(g, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(y, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ySz;
    }

    innerSeqSz  = SetSequence(pSz + qSz + gSz, innerSeq);

    /* check output size */
    if ((innerSeqSz + pSz + qSz + gSz) > outLen) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(p,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(q,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(g,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(y,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        WOLFSSL_MSG("Error, output size smaller than outlen");
        return BUFFER_E;
    }

    if (with_header) {
        int algoSz;
#ifdef WOLFSSL_SMALL_STACK
        byte* algo = NULL;

        algo = (byte*)XMALLOC(MAX_ALGO_SZ, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        if (algo == NULL) {
            XFREE(p,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(q,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(g,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(y,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            return MEMORY_E;
        }
#else
        byte algo[MAX_ALGO_SZ];
#endif
        algoSz = SetAlgoID(DSAk, algo, oidKeyType, 0);
        bitStringSz  = SetBitString(ySz, 0, bitString);
        outerSeqSz = SetSequence(algoSz + innerSeqSz + pSz + qSz + gSz,
                                                                      outerSeq);

        idx = SetSequence(algoSz + innerSeqSz + pSz + qSz + gSz + bitStringSz +
                                                      ySz + outerSeqSz, output);

        /* check output size */
        if ((idx + algoSz + bitStringSz + innerSeqSz + pSz + qSz + gSz + ySz) >
                                                                       outLen) {
            #ifdef WOLFSSL_SMALL_STACK
                XFREE(p,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
                XFREE(q,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
                XFREE(g,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
                XFREE(y,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
                XFREE(algo, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            #endif
            WOLFSSL_MSG("Error, output size smaller than outlen");
            return BUFFER_E;
        }

        /* outerSeq */
        XMEMCPY(output + idx, outerSeq, outerSeqSz);
        idx += outerSeqSz;
        /* algo */
        XMEMCPY(output + idx, algo, algoSz);
        idx += algoSz;
#ifdef WOLFSSL_SMALL_STACK
        XFREE(algo, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
    } else {
        idx = 0;
    }

    /* innerSeq */
    XMEMCPY(output + idx, innerSeq, innerSeqSz);
    idx += innerSeqSz;
    /* p */
    XMEMCPY(output + idx, p, pSz);
    idx += pSz;
    /* q */
    XMEMCPY(output + idx, q, qSz);
    idx += qSz;
    /* g */
    XMEMCPY(output + idx, g, gSz);
    idx += gSz;
    /* bit string */
    XMEMCPY(output + idx, bitString, bitStringSz);
    idx += bitStringSz;
    /* y */
    XMEMCPY(output + idx, y, ySz);
    idx += ySz;

#ifdef WOLFSSL_SMALL_STACK
    XFREE(p,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(q,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(g,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(y,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
    return idx;
}

/* Convert DSA Public key to DER format, write to output (inLen), return bytes
   written */
int wc_DsaKeyToPublicDer(DsaKey* key, byte* output, word32 inLen)
{
    return wc_SetDsaPublicKey(output, key, inLen, 1);
}
#endif /* !HAVE_SELFTEST && WOLFSSL_KEY_GEN */

/* Convert private DsaKey key to DER format, write to output (inLen),
   return bytes written */
int wc_DsaKeyToDer(DsaKey* key, byte* output, word32 inLen)
{
    word32 seqSz, verSz, rawLen, intTotalLen = 0;
    word32 sizes[DSA_INTS];
    int    i, j, outLen, ret = 0, mpSz;

    byte  seq[MAX_SEQ_SZ];
    byte  ver[MAX_VERSION_SZ];
    byte* tmps[DSA_INTS];

    if (!key || !output)
        return BAD_FUNC_ARG;

    if (key->type != DSA_PRIVATE)
        return BAD_FUNC_ARG;

    for (i = 0; i < DSA_INTS; i++)
        tmps[i] = NULL;

    /* write all big ints from key to DER tmps */
    for (i = 0; i < DSA_INTS; i++) {
        mp_int* keyInt = GetDsaInt(key, i);

        rawLen = mp_unsigned_bin_size(keyInt) + 1;
        tmps[i] = (byte*)XMALLOC(rawLen + MAX_SEQ_SZ, key->heap,
                                                              DYNAMIC_TYPE_DSA);
        if (tmps[i] == NULL) {
            ret = MEMORY_E;
            break;
        }

        mpSz = SetASNIntMP(keyInt, -1, tmps[i]);
        if (mpSz < 0) {
            ret = mpSz;
            break;
        }
        intTotalLen += (sizes[i] = mpSz);
    }

    if (ret != 0) {
        FreeTmpDsas(tmps, key->heap);
        return ret;
    }

    /* make headers */
    verSz = SetMyVersion(0, ver, FALSE);
    seqSz = SetSequence(verSz + intTotalLen, seq);

    outLen = seqSz + verSz + intTotalLen;
    if (outLen > (int)inLen) {
        FreeTmpDsas(tmps, key->heap);
        return BAD_FUNC_ARG;
    }

    /* write to output */
    XMEMCPY(output, seq, seqSz);
    j = seqSz;
    XMEMCPY(output + j, ver, verSz);
    j += verSz;

    for (i = 0; i < DSA_INTS; i++) {
        XMEMCPY(output + j, tmps[i], sizes[i]);
        j += sizes[i];
    }
    FreeTmpDsas(tmps, key->heap);

    return outLen;
}

#endif /* NO_DSA */

void InitDecodedCert(DecodedCert* cert,
                     const byte* source, word32 inSz, void* heap)
{
    if (cert != NULL) {
        XMEMSET(cert, 0, sizeof(DecodedCert));

        cert->subjectCNEnc    = CTC_UTF8;
        cert->issuer[0]       = '\0';
        cert->subject[0]      = '\0';
        cert->source          = source;  /* don't own */
        cert->maxIdx          = inSz;    /* can't go over this index */
        cert->heap            = heap;
        cert->maxPathLen      = WOLFSSL_MAX_PATH_LEN;
    #ifdef WOLFSSL_CERT_GEN
        cert->subjectSNEnc    = CTC_UTF8;
        cert->subjectCEnc     = CTC_PRINTABLE;
        cert->subjectLEnc     = CTC_UTF8;
        cert->subjectSTEnc    = CTC_UTF8;
        cert->subjectOEnc     = CTC_UTF8;
        cert->subjectOUEnc    = CTC_UTF8;
    #endif /* WOLFSSL_CERT_GEN */

    #ifndef NO_CERTS
        InitSignatureCtx(&cert->sigCtx, heap, INVALID_DEVID);
    #endif
    }
}


void FreeAltNames(DNS_entry* altNames, void* heap)
{
    (void)heap;

    while (altNames) {
        DNS_entry* tmp = altNames->next;

        XFREE(altNames->name, heap, DYNAMIC_TYPE_ALTNAME);
        XFREE(altNames,       heap, DYNAMIC_TYPE_ALTNAME);
        altNames = tmp;
    }
}

#ifndef IGNORE_NAME_CONSTRAINTS

void FreeNameSubtrees(Base_entry* names, void* heap)
{
    (void)heap;

    while (names) {
        Base_entry* tmp = names->next;

        XFREE(names->name, heap, DYNAMIC_TYPE_ALTNAME);
        XFREE(names,       heap, DYNAMIC_TYPE_ALTNAME);
        names = tmp;
    }
}

#endif /* IGNORE_NAME_CONSTRAINTS */

void FreeDecodedCert(DecodedCert* cert)
{
    if (cert == NULL)
        return;
    if (cert->subjectCNStored == 1)
        XFREE(cert->subjectCN, cert->heap, DYNAMIC_TYPE_SUBJECT_CN);
    if (cert->pubKeyStored == 1)
        XFREE((void*)cert->publicKey, cert->heap, DYNAMIC_TYPE_PUBLIC_KEY);
    if (cert->weOwnAltNames && cert->altNames)
        FreeAltNames(cert->altNames, cert->heap);
#ifndef IGNORE_NAME_CONSTRAINTS
    if (cert->altEmailNames)
        FreeAltNames(cert->altEmailNames, cert->heap);
    if (cert->permittedNames)
        FreeNameSubtrees(cert->permittedNames, cert->heap);
    if (cert->excludedNames)
        FreeNameSubtrees(cert->excludedNames, cert->heap);
#endif /* IGNORE_NAME_CONSTRAINTS */
#ifdef WOLFSSL_SEP
    XFREE(cert->deviceType, cert->heap, DYNAMIC_TYPE_X509_EXT);
    XFREE(cert->hwType, cert->heap, DYNAMIC_TYPE_X509_EXT);
    XFREE(cert->hwSerialNum, cert->heap, DYNAMIC_TYPE_X509_EXT);
#endif /* WOLFSSL_SEP */
#if (defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)) && \
    !defined(WOLFCRYPT_ONLY)
    if (cert->issuerName != NULL)
        wolfSSL_X509_NAME_free((WOLFSSL_X509_NAME*)cert->issuerName);
    if (cert->subjectName != NULL)
        wolfSSL_X509_NAME_free((WOLFSSL_X509_NAME*)cert->subjectName);
#endif /* OPENSSL_EXTRA */
#ifdef WOLFSSL_RENESAS_TSIP_TLS
    if (cert->tsip_encRsaKeyIdx != NULL)
        XFREE(cert->tsip_encRsaKeyIdx, cert->heap, DYNAMIC_TYPE_RSA);
#endif
#ifndef NO_CERTS
    FreeSignatureCtx(&cert->sigCtx);
#endif
}

static int GetCertHeader(DecodedCert* cert)
{
    int ret = 0, len;

    if (GetSequence(cert->source, &cert->srcIdx, &len, cert->maxIdx) < 0)
        return ASN_PARSE_E;

    /* Reset the max index for the size indicated in the outer wrapper. */
    cert->maxIdx = len + cert->srcIdx;
    cert->certBegin = cert->srcIdx;

    if (GetSequence(cert->source, &cert->srcIdx, &len, cert->maxIdx) < 0)
        return ASN_PARSE_E;

    cert->sigIndex = len + cert->srcIdx;
    if (cert->sigIndex > cert->maxIdx)
        return ASN_PARSE_E;

    if (GetExplicitVersion(cert->source, &cert->srcIdx, &cert->version,
                                                            cert->sigIndex) < 0)
        return ASN_PARSE_E;

    if (GetSerialNumber(cert->source, &cert->srcIdx, cert->serial,
                                           &cert->serialSz, cert->sigIndex) < 0)
        return ASN_PARSE_E;

    return ret;
}

#if !defined(NO_RSA)
/* Store Rsa Key, may save later, Dsa could use in future */
static int StoreRsaKey(DecodedCert* cert, word32 bitStringEnd)
{
    int    length;
    word32 recvd = cert->srcIdx;

    if (GetSequence(cert->source, &cert->srcIdx, &length, bitStringEnd) < 0)
        return ASN_PARSE_E;

    recvd = cert->srcIdx - recvd;
    length += recvd;

    while (recvd--)
       cert->srcIdx--;
#if defined(WOLFSSL_RENESAS_TSIP)
    cert->sigCtx.pubkey_n_start = cert->sigCtx.pubkey_e_start = cert->srcIdx;
#endif
    cert->pubKeySize = length;
    cert->publicKey = cert->source + cert->srcIdx;
    cert->srcIdx += length;

    return 0;
}
#endif /* !NO_RSA */

#ifdef HAVE_ECC

    /* return 0 on success if the ECC curve oid sum is supported */
    static int CheckCurve(word32 oid)
    {
        int ret = 0;
        word32 oidSz = 0;

        ret = wc_ecc_get_oid(oid, NULL, &oidSz);
        if (ret < 0 || oidSz == 0) {
            WOLFSSL_MSG("CheckCurve not found");
            ret = ALGO_ID_E;
        }

        return ret;
    }

#endif /* HAVE_ECC */

static int GetKey(DecodedCert* cert)
{
    int length;
#ifndef NO_DSA
    int tmpLen;
#endif
#if defined(HAVE_ECC) || defined(HAVE_NTRU) || !defined(NO_DSA)
    int tmpIdx = cert->srcIdx;
#endif

    if (GetSequence(cert->source, &cert->srcIdx, &length, cert->maxIdx) < 0)
        return ASN_PARSE_E;

#ifndef NO_DSA
    tmpLen = length + 4;
#endif

    if (GetAlgoId(cert->source, &cert->srcIdx,
                  &cert->keyOID, oidKeyType, cert->maxIdx) < 0)
        return ASN_PARSE_E;

    switch (cert->keyOID) {
   #ifndef NO_RSA
        case RSAk:
        {
            int ret;

            ret = CheckBitString(cert->source, &cert->srcIdx, &length,
                                 cert->maxIdx, 1, NULL);
            if (ret != 0)
                return ret;

            #ifdef HAVE_OCSP
                ret = CalcHashId(cert->source + cert->srcIdx, length,
                        cert->subjectKeyHash);
                if (ret != 0)
                    return ret;
            #endif

            return StoreRsaKey(cert, cert->srcIdx + length);
        }

    #endif /* NO_RSA */
    #ifdef HAVE_NTRU
        case NTRUk:
        {
            const byte* key = &cert->source[tmpIdx];
            byte*       next = (byte*)key;
            word16      keyLen;
            word32      rc;
            word32      remaining = cert->maxIdx - cert->srcIdx;
            byte*       publicKey;
#ifdef WOLFSSL_SMALL_STACK
            byte*       keyBlob = NULL;
#else
            byte        keyBlob[MAX_NTRU_KEY_SZ];
#endif
            rc = ntru_crypto_ntru_encrypt_subjectPublicKeyInfo2PublicKey(key,
                                &keyLen, NULL, &next, &remaining);
            if (rc != NTRU_OK)
                return ASN_NTRU_KEY_E;
            if (keyLen > MAX_NTRU_KEY_SZ)
                return ASN_NTRU_KEY_E;

#ifdef WOLFSSL_SMALL_STACK
            keyBlob = (byte*)XMALLOC(MAX_NTRU_KEY_SZ, cert->heap,
                                     DYNAMIC_TYPE_TMP_BUFFER);
            if (keyBlob == NULL)
                return MEMORY_E;
#endif

            rc = ntru_crypto_ntru_encrypt_subjectPublicKeyInfo2PublicKey(key,
                                &keyLen, keyBlob, &next, &remaining);
            if (rc != NTRU_OK) {
#ifdef WOLFSSL_SMALL_STACK
                XFREE(keyBlob, cert->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return ASN_NTRU_KEY_E;
            }

            if ( (next - key) < 0) {
#ifdef WOLFSSL_SMALL_STACK
                XFREE(keyBlob, cert->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return ASN_NTRU_KEY_E;
            }

            cert->srcIdx = tmpIdx + (int)(next - key);

            publicKey = (byte*)XMALLOC(keyLen, cert->heap,
                                       DYNAMIC_TYPE_PUBLIC_KEY);
            if (publicKey == NULL) {
#ifdef WOLFSSL_SMALL_STACK
                XFREE(keyBlob, cert->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return MEMORY_E;
            }
            XMEMCPY(publicKey, keyBlob, keyLen);
            cert->publicKey = publicKey;
            cert->pubKeyStored = 1;
            cert->pubKeySize   = keyLen;

#ifdef WOLFSSL_SMALL_STACK
            XFREE(keyBlob, cert->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif

            return 0;
        }
    #endif /* HAVE_NTRU */
    #ifdef HAVE_ECC
        case ECDSAk:
        {
            int ret;
            byte seq[5];
            int pubLen = length + 1 + SetLength(length, seq);
            word32 localIdx;
            byte* publicKey;
            byte  tag;

            localIdx = cert->srcIdx;
            if (GetASNTag(cert->source, &localIdx, &tag, cert->maxIdx) < 0)
                return ASN_PARSE_E;

            if (tag != (ASN_SEQUENCE | ASN_CONSTRUCTED)) {
                if (GetObjectId(cert->source, &cert->srcIdx,
                            &cert->pkCurveOID, oidCurveType, cert->maxIdx) < 0)
                    return ASN_PARSE_E;

                if (CheckCurve(cert->pkCurveOID) < 0)
                    return ECC_CURVE_OID_E;

                /* key header */
                ret = CheckBitString(cert->source, &cert->srcIdx, &length,
                                                         cert->maxIdx, 1, NULL);
                if (ret != 0)
                    return ret;
            #ifdef HAVE_OCSP
                ret = CalcHashId(cert->source + cert->srcIdx, length,
                        cert->subjectKeyHash);
                if (ret != 0)
                    return ret;
            #endif
            }

            publicKey = (byte*)XMALLOC(pubLen, cert->heap,
                                       DYNAMIC_TYPE_PUBLIC_KEY);
            if (publicKey == NULL)
                return MEMORY_E;
            XMEMCPY(publicKey, &cert->source[tmpIdx], pubLen);
            cert->publicKey = publicKey;
            cert->pubKeyStored = 1;
            cert->pubKeySize   = pubLen;

            cert->srcIdx = tmpIdx + pubLen;

            return 0;
        }
    #endif /* HAVE_ECC */
    #ifdef HAVE_ED25519
        case ED25519k:
        {
            byte* publicKey;
            int ret;

            cert->pkCurveOID = ED25519k;

            ret = CheckBitString(cert->source, &cert->srcIdx, &length,
                                 cert->maxIdx, 1, NULL);
            if (ret != 0)
                return ret;

            #ifdef HAVE_OCSP
                ret = CalcHashId(cert->source + cert->srcIdx, length,
                        cert->subjectKeyHash);
                if (ret != 0)
                    return ret;
            #endif

            publicKey = (byte*) XMALLOC(length, cert->heap,
                                        DYNAMIC_TYPE_PUBLIC_KEY);
            if (publicKey == NULL)
                return MEMORY_E;
            XMEMCPY(publicKey, &cert->source[cert->srcIdx], length);
            cert->publicKey = publicKey;
            cert->pubKeyStored = 1;
            cert->pubKeySize   = length;

            cert->srcIdx += length;

            return 0;
        }
    #endif /* HAVE_ED25519 */
    #ifdef HAVE_ED448
        case ED448k:
        {
            byte* publicKey;
            int ret;

            cert->pkCurveOID = ED448k;

            ret = CheckBitString(cert->source, &cert->srcIdx, &length,
                                 cert->maxIdx, 1, NULL);
            if (ret != 0)
                return ret;

            #ifdef HAVE_OCSP
                ret = CalcHashId(cert->source + cert->srcIdx, length,
                                 cert->subjectKeyHash);
                if (ret != 0)
                    return ret;
            #endif

            publicKey = (byte*) XMALLOC(length, cert->heap,
                                        DYNAMIC_TYPE_PUBLIC_KEY);
            if (publicKey == NULL)
                return MEMORY_E;
            XMEMCPY(publicKey, &cert->source[cert->srcIdx], length);
            cert->publicKey = publicKey;
            cert->pubKeyStored = 1;
            cert->pubKeySize   = length;

            cert->srcIdx += length;

            return 0;
        }
    #endif /* HAVE_ED448 */
    #ifndef NO_DSA
        case DSAk:
        {
            int ret;
            ret = GetSequence(cert->source, &cert->srcIdx, &length,
                           cert->maxIdx);
            if (ret < 0)
                return ret;

            ret = SkipInt(cert->source, &cert->srcIdx, cert->maxIdx);
            if (ret != 0)
                return ret;
            ret = SkipInt(cert->source, &cert->srcIdx, cert->maxIdx);
            if (ret != 0)
                return ret;
            ret = SkipInt(cert->source, &cert->srcIdx, cert->maxIdx);
            if (ret != 0)
                return ret;

            ret = CheckBitString(cert->source, &cert->srcIdx, &length,
                                                         cert->maxIdx, 1, NULL);
            if (ret != 0)
                return ret;

            ret = GetASNInt(cert->source, &cert->srcIdx, &length, cert->maxIdx);
            if (ret !=0)
                return ASN_PARSE_E;

            cert->publicKey = cert->source + tmpIdx;
            cert->pubKeySize = tmpLen;
            cert->srcIdx += length;
            return 0;
        }
    #endif /* NO_DSA */
        default:
            return ASN_UNKNOWN_OID_E;
    }
}

#if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
#if defined(HAVE_ECC)
/* Converts ECC curve enum values in ecc_curve_id to the associated OpenSSL NID
    value */
WOLFSSL_API int EccEnumToNID(int n)
{
    WOLFSSL_ENTER("EccEnumToNID()");

    switch(n) {
        case ECC_SECP192R1:
            return NID_X9_62_prime192v1;
        case ECC_PRIME192V2:
            return NID_X9_62_prime192v2;
        case ECC_PRIME192V3:
            return NID_X9_62_prime192v3;
        case ECC_PRIME239V1:
            return NID_X9_62_prime239v1;
        case ECC_PRIME239V2:
            return NID_X9_62_prime239v2;
        case ECC_PRIME239V3:
            return NID_X9_62_prime239v3;
        case ECC_SECP256R1:
            return NID_X9_62_prime256v1;
        case ECC_SECP112R1:
            return NID_secp112r1;
        case ECC_SECP112R2:
            return NID_secp112r2;
        case ECC_SECP128R1:
            return NID_secp128r1;
        case ECC_SECP128R2:
            return NID_secp128r2;
        case ECC_SECP160R1:
            return NID_secp160r1;
        case ECC_SECP160R2:
            return NID_secp160r2;
        case ECC_SECP224R1:
            return NID_secp224r1;
        case ECC_SECP384R1:
            return NID_secp384r1;
        case ECC_SECP521R1:
            return NID_secp521r1;
        case ECC_SECP160K1:
            return NID_secp160k1;
        case ECC_SECP192K1:
            return NID_secp192k1;
        case ECC_SECP224K1:
            return NID_secp224k1;
        case ECC_SECP256K1:
            return NID_secp256k1;
        case ECC_BRAINPOOLP160R1:
            return NID_brainpoolP160r1;
        case ECC_BRAINPOOLP192R1:
            return NID_brainpoolP192r1;
        case ECC_BRAINPOOLP224R1:
            return NID_brainpoolP224r1;
        case ECC_BRAINPOOLP256R1:
            return NID_brainpoolP256r1;
        case ECC_BRAINPOOLP320R1:
            return NID_brainpoolP320r1;
        case ECC_BRAINPOOLP384R1:
            return NID_brainpoolP384r1;
        case ECC_BRAINPOOLP512R1:
            return NID_brainpoolP512r1;
        default:
            WOLFSSL_MSG("NID not found");
            return -1;
    }
}
#endif /* HAVE_ECC */
#endif /* OPENSSL_EXTRA || OPENSSL_EXTRA_X509_SMALL */

#if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
int wc_OBJ_sn2nid(const char *sn)
{
    const struct {
        const char *sn;
        int  nid;
    } sn2nid[] = {
        {WOLFSSL_COMMON_NAME, NID_commonName},
        {WOLFSSL_COUNTRY_NAME, NID_countryName},
        {WOLFSSL_LOCALITY_NAME, NID_localityName},
        {WOLFSSL_STATE_NAME, NID_stateOrProvinceName},
        {WOLFSSL_ORG_NAME, NID_organizationName},
        {WOLFSSL_ORGUNIT_NAME, NID_organizationalUnitName},
        {WOLFSSL_EMAIL_ADDR, NID_emailAddress},
        {NULL, -1}};

    int i;
    #ifdef HAVE_ECC
    int eccEnum;
    #endif
    WOLFSSL_ENTER("OBJ_sn2nid");
    for(i=0; sn2nid[i].sn != NULL; i++) {
        if(XSTRNCMP(sn, sn2nid[i].sn, XSTRLEN(sn2nid[i].sn)) == 0) {
            return sn2nid[i].nid;
        }
    }
    #ifdef HAVE_ECC
    /* Nginx uses this OpenSSL string. */
    if (XSTRNCMP(sn, "prime256v1", 10) == 0)
        sn = "SECP256R1";
    if (XSTRNCMP(sn, "secp384r1", 10) == 0)
        sn = "SECP384R1";
    /* find based on name and return NID */
    for (i = 0; ecc_sets[i].size != 0 && ecc_sets[i].name != NULL; i++) {
        if (XSTRNCMP(sn, ecc_sets[i].name, ECC_MAXNAME) == 0) {
            eccEnum = ecc_sets[i].id;
            /* Convert enum value in ecc_curve_id to OpenSSL NID */
            return EccEnumToNID(eccEnum);
        }
    }
    #endif

    return NID_undef;
}
#endif

/* Routine for calculating hashId */
int CalcHashId(const byte* data, word32 len, byte* hash)
{
    int ret;

#ifdef WOLF_CRYPTO_CB
    /* try to use a registered crypto callback */
    ret = wc_CryptoCb_Sha256Hash(NULL, data, len, hash);
    if (ret != CRYPTOCB_UNAVAILABLE)
        return ret;
    /* fall-through when unavailable */
#endif

#if defined(NO_SHA) && !defined(NO_SHA256)
    ret = wc_Sha256Hash(data, len, hash);
#elif !defined(NO_SHA)
    ret = wc_ShaHash(data, len, hash);
#else
    ret = NOT_COMPILED_IN;
#endif

    return ret;
}

/* process NAME, either issuer or subject
 * returns 0 on success and negative values on fail */
int GetName(DecodedCert* cert, int nameType, int maxIdx)
{
    int    length;  /* length of all distinguished names */
    int    dummy;
    int    ret;
    char*  full;
    byte*  hash;
    word32 idx, localIdx = 0;
    byte   tag;
#if (defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)) && \
            !defined(WOLFCRYPT_ONLY)
    WOLFSSL_X509_NAME* dName;
#endif /* OPENSSL_EXTRA */

    WOLFSSL_MSG("Getting Cert Name");

    if (nameType == ISSUER) {
        full = cert->issuer;
        hash = cert->issuerHash;
    }
    else {
        full = cert->subject;
        hash = cert->subjectHash;
    }

    if (cert->srcIdx >= (word32)maxIdx) {
        return BUFFER_E;
    }

    localIdx = cert->srcIdx;
    if (GetASNTag(cert->source, &localIdx, &tag, maxIdx) < 0) {
        return ASN_PARSE_E;
    }

    if (tag == ASN_OBJECT_ID) {
        WOLFSSL_MSG("Trying optional prefix...");

        if (SkipObjectId(cert->source, &cert->srcIdx, maxIdx) < 0)
            return ASN_PARSE_E;
        WOLFSSL_MSG("Got optional prefix");
    }

    /* For OCSP, RFC2560 section 4.1.1 states the issuer hash should be
     * calculated over the entire DER encoding of the Name field, including
     * the tag and length. */
    idx = cert->srcIdx;
    if (GetSequence(cert->source, &cert->srcIdx, &length, maxIdx) < 0)
        return ASN_PARSE_E;

    ret = CalcHashId(&cert->source[idx], length + cert->srcIdx - idx, hash);
    if (ret != 0)
        return ret;

    length += cert->srcIdx;
    idx = 0;

#if defined(HAVE_PKCS7) || defined(WOLFSSL_CERT_EXT)
    /* store pointer to raw issuer */
    if (nameType == ISSUER) {
        cert->issuerRaw = &cert->source[cert->srcIdx];
        cert->issuerRawLen = length - cert->srcIdx;
    }
#endif
#ifndef IGNORE_NAME_CONSTRAINTS
    if (nameType == SUBJECT) {
        cert->subjectRaw = &cert->source[cert->srcIdx];
        cert->subjectRawLen = length - cert->srcIdx;
    }
#endif
#if (defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)) && \
    !defined(WOLFCRYPT_ONLY)
    dName = wolfSSL_X509_NAME_new();
    if (dName == NULL) {
        return MEMORY_E;
    }
#endif /* OPENSSL_EXTRA */

    while (cert->srcIdx < (word32)length) {
        byte        b       = 0;
        byte        joint[3];
        byte        tooBig  = FALSE;
        int         oidSz;
        const char* copy    = NULL;
        int         copyLen = 0;
        int         strLen  = 0;
        byte        id      = 0;
    #if (defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)) \
                && !defined(WOLFCRYPT_ONLY)
         int        nid = NID_undef;
    #endif /* OPENSSL_EXTRA */

        if (GetSet(cert->source, &cert->srcIdx, &dummy, maxIdx) < 0) {
            WOLFSSL_MSG("Cert name lacks set header, trying sequence");
        }

        if (GetSequence(cert->source, &cert->srcIdx, &dummy, maxIdx) <= 0) {
        #if (defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)) && \
            !defined(WOLFCRYPT_ONLY)
            wolfSSL_X509_NAME_free(dName);
        #endif /* OPENSSL_EXTRA */
            return ASN_PARSE_E;
        }

        ret = GetASNObjectId(cert->source, &cert->srcIdx, &oidSz, maxIdx);
        if (ret != 0) {
        #if (defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)) && \
            !defined(WOLFCRYPT_ONLY)
            wolfSSL_X509_NAME_free(dName);
        #endif /* OPENSSL_EXTRA */
            return ret;
        }

        /* make sure there is room for joint */
        if ((cert->srcIdx + sizeof(joint)) > (word32)maxIdx) {
        #if (defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)) && \
            !defined(WOLFCRYPT_ONLY)
            wolfSSL_X509_NAME_free(dName);
        #endif /* OPENSSL_EXTRA */
            return ASN_PARSE_E;
        }

        XMEMCPY(joint, &cert->source[cert->srcIdx], sizeof(joint));

        /* v1 name types */
        if (joint[0] == 0x55 && joint[1] == 0x04) {
            cert->srcIdx += 3;
            id = joint[2];
            if (GetHeader(cert->source, &b, &cert->srcIdx, &strLen,
                          maxIdx, 1) < 0) {
            #if (defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)) && \
            !defined(WOLFCRYPT_ONLY)
                wolfSSL_X509_NAME_free(dName);
            #endif /* OPENSSL_EXTRA */
                return ASN_PARSE_E;
            }

            if (id == ASN_COMMON_NAME) {
                if (nameType == SUBJECT) {
                    cert->subjectCN = (char *)&cert->source[cert->srcIdx];
                    cert->subjectCNLen = strLen;
                    cert->subjectCNEnc = b;
                }

                copy = WOLFSSL_COMMON_NAME;
                copyLen = sizeof(WOLFSSL_COMMON_NAME) - 1;
            #if (defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)) \
                && !defined(WOLFCRYPT_ONLY)
                nid = NID_commonName;
            #endif /* OPENSSL_EXTRA */
            }
            else if (id == ASN_SUR_NAME) {
                copy = WOLFSSL_SUR_NAME;
                copyLen = sizeof(WOLFSSL_SUR_NAME) - 1;
                #ifdef WOLFSSL_CERT_GEN
                    if (nameType == SUBJECT) {
                        cert->subjectSN = (char*)&cert->source[cert->srcIdx];
                        cert->subjectSNLen = strLen;
                        cert->subjectSNEnc = b;
                    }
                #endif /* WOLFSSL_CERT_GEN */
                #if (defined(OPENSSL_EXTRA) || \
                        defined(OPENSSL_EXTRA_X509_SMALL)) \
                        && !defined(WOLFCRYPT_ONLY)
                    nid = NID_surname;
                #endif /* OPENSSL_EXTRA */
            }
            else if (id == ASN_COUNTRY_NAME) {
                copy = WOLFSSL_COUNTRY_NAME;
                copyLen = sizeof(WOLFSSL_COUNTRY_NAME) - 1;
                #ifdef WOLFSSL_CERT_GEN
                    if (nameType == SUBJECT) {
                        cert->subjectC = (char*)&cert->source[cert->srcIdx];
                        cert->subjectCLen = strLen;
                        cert->subjectCEnc = b;
                    }
                #endif /* WOLFSSL_CERT_GEN */
                #if (defined(OPENSSL_EXTRA) || \
                        defined(OPENSSL_EXTRA_X509_SMALL)) \
                        && !defined(WOLFCRYPT_ONLY)
                    nid = NID_countryName;
                #endif /* OPENSSL_EXTRA */
            }
            else if (id == ASN_LOCALITY_NAME) {
                copy = WOLFSSL_LOCALITY_NAME;
                copyLen = sizeof(WOLFSSL_LOCALITY_NAME) - 1;
                #ifdef WOLFSSL_CERT_GEN
                    if (nameType == SUBJECT) {
                        cert->subjectL = (char*)&cert->source[cert->srcIdx];
                        cert->subjectLLen = strLen;
                        cert->subjectLEnc = b;
                    }
                #endif /* WOLFSSL_CERT_GEN */
                #if (defined(OPENSSL_EXTRA) || \
                        defined(OPENSSL_EXTRA_X509_SMALL)) \
                        && !defined(WOLFCRYPT_ONLY)
                    nid = NID_localityName;
                #endif /* OPENSSL_EXTRA */
            }
            else if (id == ASN_STATE_NAME) {
                copy = WOLFSSL_STATE_NAME;
                copyLen = sizeof(WOLFSSL_STATE_NAME) - 1;
                #ifdef WOLFSSL_CERT_GEN
                    if (nameType == SUBJECT) {
                        cert->subjectST = (char*)&cert->source[cert->srcIdx];
                        cert->subjectSTLen = strLen;
                        cert->subjectSTEnc = b;
                    }
                #endif /* WOLFSSL_CERT_GEN */
                #if (defined(OPENSSL_EXTRA) || \
                        defined(OPENSSL_EXTRA_X509_SMALL)) \
                        && !defined(WOLFCRYPT_ONLY)
                    nid = NID_stateOrProvinceName;
                #endif /* OPENSSL_EXTRA */
            }
            else if (id == ASN_ORG_NAME) {
                copy = WOLFSSL_ORG_NAME;
                copyLen = sizeof(WOLFSSL_ORG_NAME) - 1;
                #ifdef WOLFSSL_CERT_GEN
                    if (nameType == SUBJECT) {
                        cert->subjectO = (char*)&cert->source[cert->srcIdx];
                        cert->subjectOLen = strLen;
                        cert->subjectOEnc = b;
                    }
                #endif /* WOLFSSL_CERT_GEN */
                #if (defined(OPENSSL_EXTRA) || \
                        defined(OPENSSL_EXTRA_X509_SMALL)) \
                        && !defined(WOLFCRYPT_ONLY)
                    nid = NID_organizationName;
                #endif /* OPENSSL_EXTRA */
            }
            else if (id == ASN_ORGUNIT_NAME) {
                copy = WOLFSSL_ORGUNIT_NAME;
                copyLen = sizeof(WOLFSSL_ORGUNIT_NAME) - 1;
                #ifdef WOLFSSL_CERT_GEN
                    if (nameType == SUBJECT) {
                        cert->subjectOU = (char*)&cert->source[cert->srcIdx];
                        cert->subjectOULen = strLen;
                        cert->subjectOUEnc = b;
                    }
                #endif /* WOLFSSL_CERT_GEN */
                #if (defined(OPENSSL_EXTRA) || \
                        defined(OPENSSL_EXTRA_X509_SMALL)) \
                        && !defined(WOLFCRYPT_ONLY)
                    nid = NID_organizationalUnitName;
                #endif /* OPENSSL_EXTRA */
            }
            else if (id == ASN_SERIAL_NUMBER) {
                copy = WOLFSSL_SERIAL_NUMBER;
                copyLen = sizeof(WOLFSSL_SERIAL_NUMBER) - 1;
                #ifdef WOLFSSL_CERT_GEN
                    if (nameType == SUBJECT) {
                        cert->subjectSND = (char*)&cert->source[cert->srcIdx];
                        cert->subjectSNDLen = strLen;
                        cert->subjectSNDEnc = b;
                    }
                #endif /* WOLFSSL_CERT_GEN */
                #if (defined(OPENSSL_EXTRA) || \
                        defined(OPENSSL_EXTRA_X509_SMALL)) \
                        && !defined(WOLFCRYPT_ONLY)
                    nid = NID_serialNumber;
                #endif /* OPENSSL_EXTRA */
            }
        #ifdef WOLFSSL_CERT_EXT
            else if (id == ASN_BUS_CAT) {
                copy = WOLFSSL_BUS_CAT;
                copyLen = sizeof(WOLFSSL_BUS_CAT) - 1;
            #ifdef WOLFSSL_CERT_GEN
                if (nameType == SUBJECT) {
                    cert->subjectBC = (char*)&cert->source[cert->srcIdx];
                    cert->subjectBCLen = strLen;
                    cert->subjectBCEnc = b;
                }
            #endif /* WOLFSSL_CERT_GEN */
            #if (defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)) \
                        && !defined(WOLFCRYPT_ONLY)
                nid = NID_businessCategory;
            #endif /* OPENSSL_EXTRA */
            }
        #endif /* WOLFSSL_CERT_EXT */
        }
    #ifdef WOLFSSL_CERT_EXT
        else if ((cert->srcIdx + ASN_JOI_PREFIX_SZ + 2 <= (word32)maxIdx) &&
                 (0 == XMEMCMP(&cert->source[cert->srcIdx], ASN_JOI_PREFIX,
                               ASN_JOI_PREFIX_SZ)) &&
                 ((cert->source[cert->srcIdx+ASN_JOI_PREFIX_SZ] == ASN_JOI_C) ||
                  (cert->source[cert->srcIdx+ASN_JOI_PREFIX_SZ] == ASN_JOI_ST)))
        {
            cert->srcIdx += ASN_JOI_PREFIX_SZ;
            id = cert->source[cert->srcIdx++];
            b = cert->source[cert->srcIdx++]; /* encoding */

            if (GetLength(cert->source, &cert->srcIdx, &strLen,
                          maxIdx) < 0) {
            #if (defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)) && \
            !defined(WOLFCRYPT_ONLY)
                wolfSSL_X509_NAME_free(dName);
            #endif /* OPENSSL_EXTRA */
                return ASN_PARSE_E;
            }

            /* Check for jurisdiction of incorporation country name */
            if (id == ASN_JOI_C) {
                copy = WOLFSSL_JOI_C;
                copyLen = sizeof(WOLFSSL_JOI_C) - 1;
                #ifdef WOLFSSL_CERT_GEN
                    if (nameType == SUBJECT) {
                        cert->subjectJC = (char*)&cert->source[cert->srcIdx];
                        cert->subjectJCLen = strLen;
                        cert->subjectJCEnc = b;
                    }
                #endif /* WOLFSSL_CERT_GEN */
                #if (defined(OPENSSL_EXTRA) || \
                        defined(OPENSSL_EXTRA_X509_SMALL)) \
                        && !defined(WOLFCRYPT_ONLY)
                    nid = NID_jurisdictionCountryName;
                #endif /* OPENSSL_EXTRA */
            }

            /* Check for jurisdiction of incorporation state name */
            else if (id == ASN_JOI_ST) {
                copy = WOLFSSL_JOI_ST;
                copyLen = sizeof(WOLFSSL_JOI_ST) - 1;
                #ifdef WOLFSSL_CERT_GEN
                    if (nameType == SUBJECT) {
                        cert->subjectJS = (char*)&cert->source[cert->srcIdx];
                        cert->subjectJSLen = strLen;
                        cert->subjectJSEnc = b;
                    }
                #endif /* WOLFSSL_CERT_GEN */
                #if (defined(OPENSSL_EXTRA) || \
                        defined(OPENSSL_EXTRA_X509_SMALL)) \
                        && !defined(WOLFCRYPT_ONLY)
                    nid = NID_jurisdictionStateOrProvinceName;
                #endif /* OPENSSL_EXTRA */
            }

            if ((strLen + copyLen) > (int)(ASN_NAME_MAX - idx)) {
                WOLFSSL_MSG("ASN Name too big, skipping");
                tooBig = TRUE;
            }
        }
    #endif /* WOLFSSL_CERT_EXT */
        else {
            /* skip */
            byte email = FALSE;
            byte pilot = FALSE;

            if (joint[0] == 0x2a && joint[1] == 0x86) {  /* email id hdr */
                id = ASN_EMAIL_NAME;
                email = TRUE;
            }

            if (joint[0] == 0x9  && joint[1] == 0x92) { /* uid id hdr */
                /* last value of OID is the type of pilot attribute */
                id    = cert->source[cert->srcIdx + oidSz - 1];
                pilot = TRUE;
            }

            cert->srcIdx += oidSz + 1;

            if (GetLength(cert->source, &cert->srcIdx, &strLen, maxIdx) < 0) {
            #if (defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)) && \
            !defined(WOLFCRYPT_ONLY)
                wolfSSL_X509_NAME_free(dName);
            #endif /* OPENSSL_EXTRA */
                return ASN_PARSE_E;
            }

            if (strLen > (int)(ASN_NAME_MAX - idx)) {
                WOLFSSL_MSG("ASN name too big, skipping");
                tooBig = TRUE;
            }

            if (email) {
                copyLen = sizeof(WOLFSSL_EMAIL_ADDR) - 1;
                if ((copyLen + strLen) > (int)(ASN_NAME_MAX - idx)) {
                    WOLFSSL_MSG("ASN name too big, skipping");
                    tooBig = TRUE;
                }
                else {
                    copy = WOLFSSL_EMAIL_ADDR;
                }

                #ifdef WOLFSSL_CERT_GEN
                    if (nameType == SUBJECT) {
                        cert->subjectEmail = (char*)&cert->source[cert->srcIdx];
                        cert->subjectEmailLen = strLen;
                    }
                #endif /* WOLFSSL_CERT_GEN */
                #if (defined(OPENSSL_EXTRA) || \
                        defined(OPENSSL_EXTRA_X509_SMALL)) \
                        && !defined(WOLFCRYPT_ONLY)
                    nid = NID_emailAddress;
                #endif /* OPENSSL_EXTRA */
                #ifndef IGNORE_NAME_CONSTRAINTS
                    {
                        DNS_entry* emailName;

                        emailName = (DNS_entry*)XMALLOC(sizeof(DNS_entry),
                                              cert->heap, DYNAMIC_TYPE_ALTNAME);
                        if (emailName == NULL) {
                            WOLFSSL_MSG("\tOut of Memory");
                        #if (defined(OPENSSL_EXTRA) || \
                                defined(OPENSSL_EXTRA_X509_SMALL)) && \
                                !defined(WOLFCRYPT_ONLY)
                            wolfSSL_X509_NAME_free(dName);
                        #endif /* OPENSSL_EXTRA */
                            return MEMORY_E;
                        }
                        emailName->type = 0;
                        emailName->name = (char*)XMALLOC(strLen + 1,
                                              cert->heap, DYNAMIC_TYPE_ALTNAME);
                        if (emailName->name == NULL) {
                            WOLFSSL_MSG("\tOut of Memory");
                            XFREE(emailName, cert->heap, DYNAMIC_TYPE_ALTNAME);
                        #if (defined(OPENSSL_EXTRA) || \
                                defined(OPENSSL_EXTRA_X509_SMALL)) && \
                                !defined(WOLFCRYPT_ONLY)
                            wolfSSL_X509_NAME_free(dName);
                        #endif /* OPENSSL_EXTRA */
                            return MEMORY_E;
                        }
                        emailName->len = strLen;
                        XMEMCPY(emailName->name, &cert->source[cert->srcIdx],
                                                                        strLen);
                        emailName->name[strLen] = '\0';

                        emailName->next = cert->altEmailNames;
                        cert->altEmailNames = emailName;
                    }
                #endif /* IGNORE_NAME_CONSTRAINTS */
            }

            if (pilot) {
                switch (id) {
                    case ASN_USER_ID:
                        copy = WOLFSSL_USER_ID;
                        copyLen = sizeof(WOLFSSL_USER_ID) - 1;
                    #if (defined(OPENSSL_EXTRA) || \
                        defined(OPENSSL_EXTRA_X509_SMALL)) \
                        && !defined(WOLFCRYPT_ONLY)
                        nid = NID_userId;
                    #endif /* OPENSSL_EXTRA */
                        break;

                    case ASN_DOMAIN_COMPONENT:
                        copy = WOLFSSL_DOMAIN_COMPONENT;
                        copyLen = sizeof(WOLFSSL_DOMAIN_COMPONENT) - 1;
                    #if (defined(OPENSSL_EXTRA) || \
                        defined(OPENSSL_EXTRA_X509_SMALL)) \
                        && !defined(WOLFCRYPT_ONLY)
                        nid = NID_domainComponent;
                    #endif /* OPENSSL_EXTRA */
                        break;

                    default:
                        WOLFSSL_MSG("Unknown pilot attribute type");
                    #if (defined(OPENSSL_EXTRA) || \
                                defined(OPENSSL_EXTRA_X509_SMALL)) && \
                                !defined(WOLFCRYPT_ONLY)
                        wolfSSL_X509_NAME_free(dName);
                    #endif /* OPENSSL_EXTRA */
                        return ASN_PARSE_E;
                }
            }
        }
        if ((copyLen + strLen) > (int)(ASN_NAME_MAX - idx))
        {
            WOLFSSL_MSG("ASN Name too big, skipping");
            tooBig = TRUE;
        }
        if ((copy != NULL) && !tooBig) {
            XMEMCPY(&full[idx], copy, copyLen);
            idx += copyLen;
            XMEMCPY(&full[idx], &cert->source[cert->srcIdx], strLen);
            idx += strLen;
        }
        #if (defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)) && \
            !defined(WOLFCRYPT_ONLY)
        if (nid != NID_undef) {
            if (wolfSSL_X509_NAME_add_entry_by_NID(dName, nid, MBSTRING_UTF8,
                            &cert->source[cert->srcIdx], strLen, -1, -1) !=
                            WOLFSSL_SUCCESS) {
                wolfSSL_X509_NAME_free(dName);
                return ASN_PARSE_E;
            }
        }
        #endif /* OPENSSL_EXTRA */
        cert->srcIdx += strLen;
    }
    full[idx++] = 0;


#if (defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)) && \
            !defined(WOLFCRYPT_ONLY)
    if (nameType == ISSUER) {
        cert->issuerName = dName;
    }
    else {
        cert->subjectName = dName;
    }
#endif
    return 0;
}


#ifndef NO_ASN_TIME

/* two byte date/time, add to value */
static WC_INLINE int GetTime(int* value, const byte* date, int* idx)
{
    int i = *idx;

    if (date[i] < 0x30 || date[i] > 0x39 || date[i+1] < 0x30 ||
                                                             date[i+1] > 0x39) {
        return ASN_PARSE_E;
    }

    *value += btoi(date[i++]) * 10;
    *value += btoi(date[i++]);

    *idx = i;

    return 0;
}

int ExtractDate(const unsigned char* date, unsigned char format,
                                                  struct tm* certTime, int* idx)
{
    XMEMSET(certTime, 0, sizeof(struct tm));

    if (format == ASN_UTC_TIME) {
        if (btoi(date[*idx]) >= 5)
            certTime->tm_year = 1900;
        else
            certTime->tm_year = 2000;
    }
    else  { /* format == GENERALIZED_TIME */
        if (GetTime(&certTime->tm_year, date, idx) != 0) return 0;
        certTime->tm_year *= 100;
    }

#ifdef AVR
    /* Extract the time from the struct tm and adjust tm_year, tm_mon */
    /* AVR libc stores these as uint8_t instead of int */
    /* AVR time_t also offsets from midnight 1 Jan 2000 */
    int tm_year = certTime->tm_year - 2000;
    int tm_mon  = certTime->tm_mon - 1;
    int tm_mday = certTime->tm_mday;
    int tm_hour = certTime->tm_hour;
    int tm_min  = certTime->tm_min;
    int tm_sec  = certTime->tm_sec;

    if (GetTime(&tm_year, date, idx) != 0) return 0;
    if (GetTime(&tm_mon , date, idx) != 0) return 0;
    if (GetTime(&tm_mday, date, idx) != 0) return 0;
    if (GetTime(&tm_hour, date, idx) != 0) return 0;
    if (GetTime(&tm_min , date, idx) != 0) return 0;
    if (GetTime(&tm_sec , date, idx) != 0) return 0;

    /* Re-populate certTime with computed values */
    certTime->tm_year = tm_year;
    certTime->tm_mon  = tm_mon;
    certTime->tm_mday = tm_mday;
    certTime->tm_hour = tm_hour;
    certTime->tm_min  = tm_min;
    certTime->tm_sec  = tm_sec;
#else
    /* adjust tm_year, tm_mon */
    if (GetTime(&certTime->tm_year, date, idx) != 0) return 0;
    certTime->tm_year -= 1900;
    if (GetTime(&certTime->tm_mon , date, idx) != 0) return 0;
    certTime->tm_mon  -= 1;
    if (GetTime(&certTime->tm_mday, date, idx) != 0) return 0;
    if (GetTime(&certTime->tm_hour, date, idx) != 0) return 0;
    if (GetTime(&certTime->tm_min , date, idx) != 0) return 0;
    if (GetTime(&certTime->tm_sec , date, idx) != 0) return 0;
#endif

    return 1;
}


#if defined(OPENSSL_ALL) || defined(WOLFSSL_MYSQL_COMPATIBLE) || \
    defined(OPENSSL_EXTRA) || defined(WOLFSSL_NGINX) || defined(WOLFSSL_HAPROXY)
int GetTimeString(byte* date, int format, char* buf, int len)
{
    struct tm t;
    int idx = 0;

    if (!ExtractDate(date, (unsigned char)format, &t, &idx)) {
        return 0;
    }

    if (date[idx] != 'Z') {
        WOLFSSL_MSG("UTCtime, not Zulu") ;
        return 0;
    }

    /* place month in buffer */
    buf[0] = '\0';
    switch(t.tm_mon) {
        case 0:  XSTRNCAT(buf, "Jan ", 5); break;
        case 1:  XSTRNCAT(buf, "Feb ", 5); break;
        case 2:  XSTRNCAT(buf, "Mar ", 5); break;
        case 3:  XSTRNCAT(buf, "Apr ", 5); break;
        case 4:  XSTRNCAT(buf, "May ", 5); break;
        case 5:  XSTRNCAT(buf, "Jun ", 5); break;
        case 6:  XSTRNCAT(buf, "Jul ", 5); break;
        case 7:  XSTRNCAT(buf, "Aug ", 5); break;
        case 8:  XSTRNCAT(buf, "Sep ", 5); break;
        case 9:  XSTRNCAT(buf, "Oct ", 5); break;
        case 10: XSTRNCAT(buf, "Nov ", 5); break;
        case 11: XSTRNCAT(buf, "Dec ", 5); break;
        default:
            return 0;

    }
    idx = 4; /* use idx now for char buffer */

    XSNPRINTF(buf + idx, len - idx, "%2d %02d:%02d:%02d %d GMT",
              t.tm_mday, t.tm_hour, t.tm_min, t.tm_sec, t.tm_year + 1900);

    return 1;
}
#endif /* OPENSSL_ALL || WOLFSSL_MYSQL_COMPATIBLE || WOLFSSL_NGINX || WOLFSSL_HAPROXY */


#if !defined(NO_ASN_TIME) && defined(HAVE_PKCS7)

/* Set current time string, either UTC or GeneralizedTime.
 * (void*) tm should be a pointer to time_t, output is placed in buf.
 *
 * Return time string length placed in buf on success, negative on error */
int GetAsnTimeString(void* currTime, byte* buf, word32 len)
{
    struct tm* ts      = NULL;
    struct tm* tmpTime = NULL;
#if defined(NEED_TMP_TIME)
    struct tm tmpTimeStorage;
    tmpTime = &tmpTimeStorage;
#else
    (void)tmpTime;
#endif
    byte* data_ptr  = buf;
    word32 data_len = 0;
    int year, mon, day, hour, mini, sec;

    WOLFSSL_ENTER("SetAsnTimeString");

    if (buf == NULL || len == 0)
        return BAD_FUNC_ARG;

    ts = (struct tm *)XGMTIME((time_t*)currTime, tmpTime);
    if (ts == NULL){
        WOLFSSL_MSG("failed to get time data.");
        return ASN_TIME_E;
    }

    /* Note ASN_UTC_TIME_SIZE and ASN_GENERALIZED_TIME_SIZE include space for
     * the null terminator. ASN encoded values leave off the terminator. */

    if (ts->tm_year >= 50 && ts->tm_year < 150) {
        /* UTC Time */
        char utc_str[ASN_UTC_TIME_SIZE];
        data_len = ASN_UTC_TIME_SIZE - 1 + 2;

        if (len < data_len)
            return BUFFER_E;

        if (ts->tm_year >= 50 && ts->tm_year < 100) {
            year = ts->tm_year;
        } else if (ts->tm_year >= 100 && ts->tm_year < 150) {
            year = ts->tm_year - 100;
        }
        else {
            WOLFSSL_MSG("unsupported year range");
            return BAD_FUNC_ARG;
        }
        mon  = ts->tm_mon + 1;
        day  = ts->tm_mday;
        hour = ts->tm_hour;
        mini = ts->tm_min;
        sec  = ts->tm_sec;
        XSNPRINTF((char *)utc_str, ASN_UTC_TIME_SIZE,
                  "%02d%02d%02d%02d%02d%02dZ", year, mon, day, hour, mini, sec);
        *data_ptr = (byte) ASN_UTC_TIME; data_ptr++;
        /* -1 below excludes null terminator */
        *data_ptr = (byte) ASN_UTC_TIME_SIZE - 1; data_ptr++;
        XMEMCPY(data_ptr,(byte *)utc_str, ASN_UTC_TIME_SIZE - 1);

    } else {
        /* GeneralizedTime */
        char gt_str[ASN_GENERALIZED_TIME_SIZE];
        data_len = ASN_GENERALIZED_TIME_SIZE - 1 + 2;

        if (len < data_len)
            return BUFFER_E;

        year = ts->tm_year + 1900;
        mon  = ts->tm_mon + 1;
        day  = ts->tm_mday;
        hour = ts->tm_hour;
        mini = ts->tm_min;
        sec  = ts->tm_sec;
        XSNPRINTF((char *)gt_str, ASN_GENERALIZED_TIME_SIZE,
                  "%4d%02d%02d%02d%02d%02dZ", year, mon, day, hour, mini, sec);
        *data_ptr = (byte) ASN_GENERALIZED_TIME; data_ptr++;
        /* -1 below excludes null terminator */
        *data_ptr = (byte) ASN_GENERALIZED_TIME_SIZE - 1; data_ptr++;
        XMEMCPY(data_ptr,(byte *)gt_str, ASN_GENERALIZED_TIME_SIZE - 1);
    }

    return data_len;
}

#endif /* !NO_ASN_TIME && HAVE_PKCS7 */


#if defined(USE_WOLF_VALIDDATE)

/* to the second */
int DateGreaterThan(const struct tm* a, const struct tm* b)
{
    if (a->tm_year > b->tm_year)
        return 1;

    if (a->tm_year == b->tm_year && a->tm_mon > b->tm_mon)
        return 1;

    if (a->tm_year == b->tm_year && a->tm_mon == b->tm_mon &&
           a->tm_mday > b->tm_mday)
        return 1;

    if (a->tm_year == b->tm_year && a->tm_mon == b->tm_mon &&
        a->tm_mday == b->tm_mday && a->tm_hour > b->tm_hour)
        return 1;

    if (a->tm_year == b->tm_year && a->tm_mon == b->tm_mon &&
        a->tm_mday == b->tm_mday && a->tm_hour == b->tm_hour &&
        a->tm_min > b->tm_min)
        return 1;

    if (a->tm_year == b->tm_year && a->tm_mon == b->tm_mon &&
        a->tm_mday == b->tm_mday && a->tm_hour == b->tm_hour &&
        a->tm_min  == b->tm_min  && a->tm_sec > b->tm_sec)
        return 1;

    return 0; /* false */
}


static WC_INLINE int DateLessThan(const struct tm* a, const struct tm* b)
{
    return DateGreaterThan(b,a);
}

/* like atoi but only use first byte */
/* Make sure before and after dates are valid */
int wc_ValidateDate(const byte* date, byte format, int dateType)
{
    time_t ltime;
    struct tm  certTime;
    struct tm* localTime;
    struct tm* tmpTime;
    int    i = 0;
    int    timeDiff = 0 ;
    int    diffHH = 0 ; int diffMM = 0 ;
    int    diffSign = 0 ;

#if defined(NEED_TMP_TIME)
    struct tm tmpTimeStorage;
    tmpTime = &tmpTimeStorage;
#else
    tmpTime = NULL;
#endif
    (void)tmpTime;

    ltime = XTIME(0);

#ifdef WOLFSSL_BEFORE_DATE_CLOCK_SKEW
    if (dateType == BEFORE) {
        WOLFSSL_MSG("Skewing local time for before date check");
        ltime += WOLFSSL_BEFORE_DATE_CLOCK_SKEW;
    }
#endif

#ifdef WOLFSSL_AFTER_DATE_CLOCK_SKEW
    if (dateType == AFTER) {
        WOLFSSL_MSG("Skewing local time for after date check");
        ltime -= WOLFSSL_AFTER_DATE_CLOCK_SKEW;
    }
#endif

    if (!ExtractDate(date, format, &certTime, &i)) {
        WOLFSSL_MSG("Error extracting the date");
        return 0;
    }

    if ((date[i] == '+') || (date[i] == '-')) {
        WOLFSSL_MSG("Using time differential, not Zulu") ;
        diffSign = date[i++] == '+' ? 1 : -1 ;
        if (GetTime(&diffHH, date, &i) != 0)
            return 0;
        if (GetTime(&diffMM, date, &i) != 0)
            return 0;
        timeDiff = diffSign * (diffHH*60 + diffMM) * 60 ;
    } else if (date[i] != 'Z') {
        WOLFSSL_MSG("UTCtime, neither Zulu or time differential") ;
        return 0;
    }

    ltime -= (time_t)timeDiff ;
    localTime = XGMTIME(&ltime, tmpTime);

    if (localTime == NULL) {
        WOLFSSL_MSG("XGMTIME failed");
        return 0;
    }

    if (dateType == BEFORE) {
        if (DateLessThan(localTime, &certTime)) {
            WOLFSSL_MSG("Date BEFORE check failed");
            return 0;
        }
    }
    else {  /* dateType == AFTER */
        if (DateGreaterThan(localTime, &certTime)) {
            WOLFSSL_MSG("Date AFTER check failed");
            return 0;
        }
    }

    return 1;
}
#endif /* USE_WOLF_VALIDDATE */

int wc_GetTime(void* timePtr, word32 timeSize)
{
    time_t* ltime = (time_t*)timePtr;

    if (timePtr == NULL) {
        return BAD_FUNC_ARG;
    }

    if ((word32)sizeof(time_t) > timeSize) {
        return BUFFER_E;
    }

    *ltime = XTIME(0);

    return 0;
}

#endif /* !NO_ASN_TIME */


/* Get date buffer, format and length. Returns 0=success or error */
static int GetDateInfo(const byte* source, word32* idx, const byte** pDate,
                        byte* pFormat, int* pLength, word32 maxIdx)
{
    int length;
    byte format;

    if (source == NULL || idx == NULL)
        return BAD_FUNC_ARG;

    /* get ASN format header */
    if (*idx+1 > maxIdx)
        return BUFFER_E;
    format = source[*idx];
    *idx += 1;
    if (format != ASN_UTC_TIME && format != ASN_GENERALIZED_TIME)
        return ASN_TIME_E;

    /* get length */
    if (GetLength(source, idx, &length, maxIdx) < 0)
        return ASN_PARSE_E;
    if (length > MAX_DATE_SIZE || length < MIN_DATE_SIZE)
        return ASN_DATE_SZ_E;

    /* return format, date and length */
    if (pFormat)
        *pFormat = format;
    if (pDate)
        *pDate = &source[*idx];
    if (pLength)
        *pLength = length;

    *idx += length;

    return 0;
}

static int GetDate(DecodedCert* cert, int dateType, int verify, int maxIdx)
{
    int    ret, length;
    const byte *datePtr = NULL;
    byte   date[MAX_DATE_SIZE];
    byte   format;
    word32 startIdx = 0;

    if (dateType == BEFORE)
        cert->beforeDate = &cert->source[cert->srcIdx];
    else
        cert->afterDate = &cert->source[cert->srcIdx];
    startIdx = cert->srcIdx;

    ret = GetDateInfo(cert->source, &cert->srcIdx, &datePtr, &format,
                      &length, maxIdx);
    if (ret < 0)
        return ret;

    XMEMSET(date, 0, MAX_DATE_SIZE);
    XMEMCPY(date, datePtr, length);

    if (dateType == BEFORE)
        cert->beforeDateLen = cert->srcIdx - startIdx;
    else
        cert->afterDateLen  = cert->srcIdx - startIdx;

#ifndef NO_ASN_TIME
    if (verify != NO_VERIFY && verify != VERIFY_SKIP_DATE &&
            !XVALIDATE_DATE(date, format, dateType)) {
        if (dateType == BEFORE)
            return ASN_BEFORE_DATE_E;
        else
            return ASN_AFTER_DATE_E;
    }
#else
    (void)verify;
#endif

    return 0;
}

static int GetValidity(DecodedCert* cert, int verify, int maxIdx)
{
    int length;
    int badDate = 0;

    if (GetSequence(cert->source, &cert->srcIdx, &length, maxIdx) < 0)
        return ASN_PARSE_E;

    maxIdx = cert->srcIdx + length;

    if (GetDate(cert, BEFORE, verify, maxIdx) < 0)
        badDate = ASN_BEFORE_DATE_E; /* continue parsing */

    if (GetDate(cert, AFTER, verify, maxIdx) < 0)
        return ASN_AFTER_DATE_E;

    if (badDate != 0)
        return badDate;

    return 0;
}


int wc_GetDateInfo(const byte* certDate, int certDateSz, const byte** date,
    byte* format, int* length)
{
    int ret;
    word32 idx = 0;

    ret = GetDateInfo(certDate, &idx, date, format, length, certDateSz);
    if (ret < 0)
        return ret;

    return 0;
}

#ifndef NO_ASN_TIME
int wc_GetDateAsCalendarTime(const byte* date, int length, byte format,
    struct tm* timearg)
{
    int idx = 0;
    (void)length;
    if (!ExtractDate(date, format, timearg, &idx))
        return ASN_TIME_E;
    return 0;
}

#if defined(WOLFSSL_CERT_GEN) && defined(WOLFSSL_ALT_NAMES)
int wc_GetCertDates(Cert* cert, struct tm* before, struct tm* after)
{
    int ret = 0;
    const byte* date;
    byte format;
    int length;

    if (cert == NULL)
        return BAD_FUNC_ARG;

    if (before && cert->beforeDateSz > 0) {
        ret = wc_GetDateInfo(cert->beforeDate, cert->beforeDateSz, &date,
                             &format, &length);
        if (ret == 0)
            ret = wc_GetDateAsCalendarTime(date, length, format, before);
    }
    if (after && cert->afterDateSz > 0) {
        ret = wc_GetDateInfo(cert->afterDate, cert->afterDateSz, &date,
                             &format, &length);
        if (ret == 0)
            ret = wc_GetDateAsCalendarTime(date, length, format, after);
    }

    return ret;
}
#endif /* WOLFSSL_CERT_GEN && WOLFSSL_ALT_NAMES */
#endif /* !NO_ASN_TIME */

/* parses certificate up to point of X.509 public key
 *
 * if cert date is invalid then badDate gets set to error value, otherwise is 0
 *
 * returns a negative value on fail case
 */
int wc_GetPubX509(DecodedCert* cert, int verify, int* badDate)
{
    int ret;

    if (cert == NULL || badDate == NULL)
        return BAD_FUNC_ARG;

    *badDate = 0;
    if ( (ret = GetCertHeader(cert)) < 0)
        return ret;

    WOLFSSL_MSG("Got Cert Header");

    /* Using the sigIndex as the upper bound because that's where the
     * actual certificate data ends. */
    if ( (ret = GetAlgoId(cert->source, &cert->srcIdx, &cert->signatureOID,
                          oidSigType, cert->sigIndex)) < 0)
        return ret;

    WOLFSSL_MSG("Got Algo ID");

    if ( (ret = GetName(cert, ISSUER, cert->sigIndex)) < 0)
        return ret;

    if ( (ret = GetValidity(cert, verify, cert->sigIndex)) < 0)
        *badDate = ret;

    if ( (ret = GetName(cert, SUBJECT, cert->sigIndex)) < 0)
        return ret;

    WOLFSSL_MSG("Got Subject Name");
    return ret;
}

int DecodeToKey(DecodedCert* cert, int verify)
{
    int badDate = 0;
    int ret;

    if ( (ret = wc_GetPubX509(cert, verify, &badDate)) < 0)
        return ret;

    /* Determine if self signed */
    cert->selfSigned = XMEMCMP(cert->issuerHash,
                               cert->subjectHash,
                               KEYID_SIZE) == 0 ? 1 : 0;

    if ( (ret = GetKey(cert)) < 0)
        return ret;

    WOLFSSL_MSG("Got Key");

    if (badDate != 0)
        return badDate;

    return ret;
}

static int GetSignature(DecodedCert* cert)
{
    int length;
    int ret;
    ret = CheckBitString(cert->source, &cert->srcIdx, &length, cert->maxIdx, 1,
                         NULL);
    if (ret != 0)
        return ret;

    cert->sigLength = length;
    cert->signature = &cert->source[cert->srcIdx];
    cert->srcIdx += cert->sigLength;

    return 0;
}

static word32 SetOctetString8Bit(word32 len, byte* output)
{
    output[0] = ASN_OCTET_STRING;
    output[1] = (byte)len;
    return 2;
}

static word32 SetDigest(const byte* digest, word32 digSz, byte* output)
{
    word32 idx = SetOctetString8Bit(digSz, output);
    XMEMCPY(&output[idx], digest, digSz);

    return idx + digSz;
}


static word32 BytePrecision(word32 value)
{
    word32 i;
    for (i = sizeof(value); i; --i)
        if (value >> ((i - 1) * WOLFSSL_BIT_SIZE))
            break;

    return i;
}


word32 SetLength(word32 length, byte* output)
{
    word32 i = 0, j;

    if (length < ASN_LONG_LENGTH) {
        if (output)
            output[i] = (byte)length;
        i++;
    }
    else {
        if (output)
            output[i] = (byte)(BytePrecision(length) | ASN_LONG_LENGTH);
        i++;

        for (j = BytePrecision(length); j; --j) {
            if (output)
                output[i] = (byte)(length >> ((j - 1) * WOLFSSL_BIT_SIZE));
            i++;
        }
    }

    return i;
}

word32 SetSequence(word32 len, byte* output)
{
    if (output)
        output[0] = ASN_SEQUENCE | ASN_CONSTRUCTED;
    return SetLength(len, output ? output + 1 : NULL) + 1;
}

word32 SetOctetString(word32 len, byte* output)
{
    output[0] = ASN_OCTET_STRING;
    return SetLength(len, output + 1) + 1;
}

/* Write a set header to output */
word32 SetSet(word32 len, byte* output)
{
    output[0] = ASN_SET | ASN_CONSTRUCTED;
    return SetLength(len, output + 1) + 1;
}

word32 SetImplicit(byte tag, byte number, word32 len, byte* output)
{

    output[0] = ((tag == ASN_SEQUENCE || tag == ASN_SET) ? ASN_CONSTRUCTED : 0)
                    | ASN_CONTEXT_SPECIFIC | number;
    return SetLength(len, output + 1) + 1;
}

word32 SetExplicit(byte number, word32 len, byte* output)
{
    output[0] = ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | number;
    return SetLength(len, output + 1) + 1;
}


#if defined(HAVE_ECC) && defined(HAVE_ECC_KEY_EXPORT)

static int SetCurve(ecc_key* key, byte* output)
{
#ifdef HAVE_OID_ENCODING
    int ret;
#endif
    int idx = 0;
    word32 oidSz = 0;

    /* validate key */
    if (key == NULL || key->dp == NULL) {
        return BAD_FUNC_ARG;
    }

#ifdef HAVE_OID_ENCODING
    ret = EncodeObjectId(key->dp->oid, key->dp->oidSz, NULL, &oidSz);
    if (ret != 0) {
        return ret;
    }
#else
    oidSz = key->dp->oidSz;
#endif

    idx += SetObjectId(oidSz, output);

#ifdef HAVE_OID_ENCODING
    ret = EncodeObjectId(key->dp->oid, key->dp->oidSz, output+idx, &oidSz);
    if (ret != 0) {
        return ret;
    }
#else
    XMEMCPY(output+idx, key->dp->oid, oidSz);
#endif
    idx += oidSz;

    return idx;
}

#endif /* HAVE_ECC && HAVE_ECC_KEY_EXPORT */


#ifdef HAVE_ECC
static WC_INLINE int IsSigAlgoECDSA(int algoOID)
{
    /* ECDSA sigAlgo must not have ASN1 NULL parameters */
    if (algoOID == CTC_SHAwECDSA || algoOID == CTC_SHA256wECDSA ||
        algoOID == CTC_SHA384wECDSA || algoOID == CTC_SHA512wECDSA) {
        return 1;
    }

    return 0;
}
#endif

word32 SetAlgoID(int algoOID, byte* output, int type, int curveSz)
{
    word32 tagSz, idSz, seqSz, algoSz = 0;
    const  byte* algoName = 0;
    byte   ID_Length[1 + MAX_LENGTH_SZ];
    byte   seqArray[MAX_SEQ_SZ + 1];  /* add object_id to end */
    int    length = 0;

    tagSz = (type == oidHashType ||
             (type == oidSigType
        #ifdef HAVE_ECC
              && !IsSigAlgoECDSA(algoOID)
        #endif
        #ifdef HAVE_ED25519
              && algoOID != ED25519k
        #endif
        #ifdef HAVE_ED448
              && algoOID != ED448k
        #endif
              ) ||
             (type == oidKeyType && algoOID == RSAk)) ? 2 : 0;

    algoName = OidFromId(algoOID, type, &algoSz);

    if (algoName == NULL) {
        WOLFSSL_MSG("Unknown Algorithm");
        return 0;
    }

    idSz  = SetObjectId(algoSz, ID_Length);
    seqSz = SetSequence(idSz + algoSz + tagSz + curveSz, seqArray);

    /* Copy only algo to output for DSA keys */
    if (algoOID == DSAk && output) {
        XMEMCPY(output, ID_Length, idSz);
        XMEMCPY(output + idSz, algoName, algoSz);
        if (tagSz == 2)
            SetASNNull(&output[seqSz + idSz + algoSz]);
    }
    else if (output) {
        XMEMCPY(output, seqArray, seqSz);
        XMEMCPY(output + seqSz, ID_Length, idSz);
        XMEMCPY(output + seqSz + idSz, algoName, algoSz);
        if (tagSz == 2)
            SetASNNull(&output[seqSz + idSz + algoSz]);
    }

    if (algoOID == DSAk)
        length = idSz + algoSz + tagSz;
    else
        length = seqSz + idSz + algoSz + tagSz;

    return length;
}


word32 wc_EncodeSignature(byte* out, const byte* digest, word32 digSz,
                          int hashOID)
{
    byte digArray[MAX_ENCODED_DIG_SZ];
    byte algoArray[MAX_ALGO_SZ];
    byte seqArray[MAX_SEQ_SZ];
    word32 encDigSz, algoSz, seqSz;

    encDigSz = SetDigest(digest, digSz, digArray);
    algoSz   = SetAlgoID(hashOID, algoArray, oidHashType, 0);
    seqSz    = SetSequence(encDigSz + algoSz, seqArray);

    XMEMCPY(out, seqArray, seqSz);
    XMEMCPY(out + seqSz, algoArray, algoSz);
    XMEMCPY(out + seqSz + algoSz, digArray, encDigSz);

    return encDigSz + algoSz + seqSz;
}


#ifndef NO_CERTS

int wc_GetCTC_HashOID(int type)
{
    int ret;
    enum wc_HashType hType;

    hType = wc_HashTypeConvert(type);
    ret = wc_HashGetOID(hType);
    if (ret < 0)
        ret = 0; /* backwards compatibility */

    return ret;
}

void InitSignatureCtx(SignatureCtx* sigCtx, void* heap, int devId)
{
    if (sigCtx) {
        XMEMSET(sigCtx, 0, sizeof(SignatureCtx));
        sigCtx->devId = devId;
        sigCtx->heap = heap;
    }
}

void FreeSignatureCtx(SignatureCtx* sigCtx)
{
    if (sigCtx == NULL)
        return;

    if (sigCtx->digest) {
        XFREE(sigCtx->digest, sigCtx->heap, DYNAMIC_TYPE_DIGEST);
        sigCtx->digest = NULL;
    }
#ifndef NO_RSA
    if (sigCtx->plain) {
        XFREE(sigCtx->plain, sigCtx->heap, DYNAMIC_TYPE_SIGNATURE);
        sigCtx->plain = NULL;
    }
#endif
#ifndef NO_ASN_CRYPT
    if (sigCtx->key.ptr) {
        switch (sigCtx->keyOID) {
        #ifndef NO_RSA
            case RSAk:
                wc_FreeRsaKey(sigCtx->key.rsa);
                XFREE(sigCtx->key.ptr, sigCtx->heap, DYNAMIC_TYPE_RSA);
                break;
        #endif /* !NO_RSA */
        #ifdef HAVE_ECC
            case ECDSAk:
                wc_ecc_free(sigCtx->key.ecc);
                XFREE(sigCtx->key.ecc, sigCtx->heap, DYNAMIC_TYPE_ECC);
                break;
        #endif /* HAVE_ECC */
        #ifdef HAVE_ED25519
            case ED25519k:
                wc_ed25519_free(sigCtx->key.ed25519);
                XFREE(sigCtx->key.ed25519, sigCtx->heap, DYNAMIC_TYPE_ED25519);
                break;
        #endif /* HAVE_ED25519 */
        #ifdef HAVE_ED448
            case ED448k:
                wc_ed448_free(sigCtx->key.ed448);
                XFREE(sigCtx->key.ed448, sigCtx->heap, DYNAMIC_TYPE_ED448);
                break;
        #endif /* HAVE_ED448 */
            default:
                break;
        } /* switch (keyOID) */
        sigCtx->key.ptr = NULL;
    }
#endif

    /* reset state, we are done */
    sigCtx->state = SIG_STATE_BEGIN;
}

#ifndef NO_ASN_CRYPT
static int HashForSignature(const byte* buf, word32 bufSz, word32 sigOID,
                            byte* digest, int* typeH, int* digestSz, int verify)
{
    int ret = 0;

    (void)verify;

    switch (sigOID) {
    #if defined(WOLFSSL_MD2)
        case CTC_MD2wRSA:
            if (!verify) {
                ret = HASH_TYPE_E;
                WOLFSSL_MSG("MD2 not supported for signing");
            }
            else if ((ret = wc_Md2Hash(buf, bufSz, digest)) == 0) {
                *typeH    = MD2h;
                *digestSz = MD2_DIGEST_SIZE;
            }
        break;
    #endif
    #ifndef NO_MD5
        case CTC_MD5wRSA:
            if ((ret = wc_Md5Hash(buf, bufSz, digest)) == 0) {
                *typeH    = MD5h;
                *digestSz = WC_MD5_DIGEST_SIZE;
            }
            break;
    #endif
    #ifndef NO_SHA
        case CTC_SHAwRSA:
        case CTC_SHAwDSA:
        case CTC_SHAwECDSA:
            if ((ret = wc_ShaHash(buf, bufSz, digest)) == 0) {
                *typeH    = SHAh;
                *digestSz = WC_SHA_DIGEST_SIZE;
            }
            break;
    #endif
    #ifdef WOLFSSL_SHA224
        case CTC_SHA224wRSA:
        case CTC_SHA224wECDSA:
            if ((ret = wc_Sha224Hash(buf, bufSz, digest)) == 0) {
                *typeH    = SHA224h;
                *digestSz = WC_SHA224_DIGEST_SIZE;
            }
            break;
    #endif
    #ifndef NO_SHA256
        case CTC_SHA256wRSA:
        case CTC_SHA256wECDSA:
            if ((ret = wc_Sha256Hash(buf, bufSz, digest)) == 0) {
                *typeH    = SHA256h;
                *digestSz = WC_SHA256_DIGEST_SIZE;
            }
            break;
    #endif
    #ifdef WOLFSSL_SHA384
        case CTC_SHA384wRSA:
        case CTC_SHA384wECDSA:
            if ((ret = wc_Sha384Hash(buf, bufSz, digest)) == 0) {
                *typeH    = SHA384h;
                *digestSz = WC_SHA384_DIGEST_SIZE;
            }
            break;
    #endif
    #ifdef WOLFSSL_SHA512
        case CTC_SHA512wRSA:
        case CTC_SHA512wECDSA:
            if ((ret = wc_Sha512Hash(buf, bufSz, digest)) == 0) {
                *typeH    = SHA512h;
                *digestSz = WC_SHA512_DIGEST_SIZE;
            }
            break;
    #endif
    #ifdef HAVE_ED25519
        case CTC_ED25519:
            /* Hashes done in signing operation.
             * Two dependent hashes with prefixes performed.
             */
            break;
    #endif
    #ifdef HAVE_ED448
        case CTC_ED448:
            /* Hashes done in signing operation.
             * Two dependent hashes with prefixes performed.
             */
            break;
    #endif
        default:
            ret = HASH_TYPE_E;
            WOLFSSL_MSG("Hash for Signature has unsupported type");
    }

    return ret;
}
#endif /* !NO_ASN_CRYPT */

/* Return codes: 0=Success, Negative (see error-crypt.h), ASN_SIG_CONFIRM_E */
static int ConfirmSignature(SignatureCtx* sigCtx,
    const byte* buf, word32 bufSz,
    const byte* key, word32 keySz, word32 keyOID,
    const byte* sig, word32 sigSz, word32 sigOID, byte* rsaKeyIdx)
{
    int ret = 0;
#ifndef WOLFSSL_RENESAS_TSIP_TLS
    (void)rsaKeyIdx;
#endif
    if (sigCtx == NULL || buf == NULL || bufSz == 0 || key == NULL ||
        keySz == 0 || sig == NULL || sigSz == 0) {
        return BAD_FUNC_ARG;
    }

    (void)key;
    (void)keySz;
    (void)sig;
    (void)sigSz;

    WOLFSSL_ENTER("ConfirmSignature");

#ifndef NO_ASN_CRYPT
    switch (sigCtx->state) {
        case SIG_STATE_BEGIN:
        {
            sigCtx->keyOID = keyOID; /* must set early for cleanup */

            sigCtx->digest = (byte*)XMALLOC(WC_MAX_DIGEST_SIZE, sigCtx->heap,
                                                    DYNAMIC_TYPE_DIGEST);
            if (sigCtx->digest == NULL) {
                ERROR_OUT(MEMORY_E, exit_cs);
            }

            sigCtx->state = SIG_STATE_HASH;
        } /* SIG_STATE_BEGIN */
        FALL_THROUGH;

        case SIG_STATE_HASH:
        {
            ret = HashForSignature(buf, bufSz, sigOID, sigCtx->digest,
                                   &sigCtx->typeH, &sigCtx->digestSz, 1);
            if (ret != 0) {
                goto exit_cs;
            }

            sigCtx->state = SIG_STATE_KEY;
        } /* SIG_STATE_HASH */
        FALL_THROUGH;

        case SIG_STATE_KEY:
        {
            switch (keyOID) {
            #ifndef NO_RSA
                case RSAk:
                {
                    word32 idx = 0;

                    sigCtx->key.rsa = (RsaKey*)XMALLOC(sizeof(RsaKey),
                                                sigCtx->heap, DYNAMIC_TYPE_RSA);
                    sigCtx->plain = (byte*)XMALLOC(MAX_ENCODED_SIG_SZ,
                                         sigCtx->heap, DYNAMIC_TYPE_SIGNATURE);
                    if (sigCtx->key.rsa == NULL || sigCtx->plain == NULL) {
                        ERROR_OUT(MEMORY_E, exit_cs);
                    }
                    if ((ret = wc_InitRsaKey_ex(sigCtx->key.rsa, sigCtx->heap,
                                                        sigCtx->devId)) != 0) {
                        goto exit_cs;
                    }
                    if (sigSz > MAX_ENCODED_SIG_SZ) {
                        WOLFSSL_MSG("Verify Signature is too big");
                        ERROR_OUT(BUFFER_E, exit_cs);
                    }
                    if ((ret = wc_RsaPublicKeyDecode(key, &idx, sigCtx->key.rsa,
                                                                 keySz)) != 0) {
                        WOLFSSL_MSG("ASN Key decode error RSA");
                        goto exit_cs;
                    }
                    XMEMCPY(sigCtx->plain, sig, sigSz);
                    sigCtx->out = NULL;

                #ifdef WOLFSSL_ASYNC_CRYPT
                    sigCtx->asyncDev = &sigCtx->key.rsa->asyncDev;
                #endif
                    break;
                }
            #endif /* !NO_RSA */
            #ifdef HAVE_ECC
                case ECDSAk:
                {
                    word32 idx = 0;

                    sigCtx->verify = 0;
                    sigCtx->key.ecc = (ecc_key*)XMALLOC(sizeof(ecc_key),
                                                sigCtx->heap, DYNAMIC_TYPE_ECC);
                    if (sigCtx->key.ecc == NULL) {
                        ERROR_OUT(MEMORY_E, exit_cs);
                    }
                    if ((ret = wc_ecc_init_ex(sigCtx->key.ecc, sigCtx->heap,
                                                          sigCtx->devId)) < 0) {
                        goto exit_cs;
                    }
                    ret = wc_EccPublicKeyDecode(key, &idx, sigCtx->key.ecc,
                                                                         keySz);
                    if (ret < 0) {
                        WOLFSSL_MSG("ASN Key import error ECC");
                        goto exit_cs;
                    }
                #ifdef WOLFSSL_ASYNC_CRYPT
                    sigCtx->asyncDev = &sigCtx->key.ecc->asyncDev;
                #endif
                    break;
                }
            #endif /* HAVE_ECC */
            #ifdef HAVE_ED25519
                case ED25519k:
                {
                    sigCtx->verify = 0;
                    sigCtx->key.ed25519 = (ed25519_key*)XMALLOC(
                                              sizeof(ed25519_key), sigCtx->heap,
                                              DYNAMIC_TYPE_ED25519);
                    if (sigCtx->key.ed25519 == NULL) {
                        ERROR_OUT(MEMORY_E, exit_cs);
                    }
                    if ((ret = wc_ed25519_init(sigCtx->key.ed25519)) < 0) {
                        goto exit_cs;
                    }
                    if ((ret = wc_ed25519_import_public(key, keySz,
                                                    sigCtx->key.ed25519)) < 0) {
                        WOLFSSL_MSG("ASN Key import error ED25519");
                        goto exit_cs;
                    }
                #ifdef WOLFSSL_ASYNC_CRYPT
                    sigCtx->asyncDev = &sigCtx->key.ed25519->asyncDev;
                #endif
                    break;
                }
            #endif
            #ifdef HAVE_ED448
                case ED448k:
                {
                    sigCtx->verify = 0;
                    sigCtx->key.ed448 = (ed448_key*)XMALLOC(
                                                sizeof(ed448_key), sigCtx->heap,
                                                DYNAMIC_TYPE_ED448);
                    if (sigCtx->key.ed448 == NULL) {
                        ERROR_OUT(MEMORY_E, exit_cs);
                    }
                    if ((ret = wc_ed448_init(sigCtx->key.ed448)) < 0) {
                        goto exit_cs;
                    }
                    if ((ret = wc_ed448_import_public(key, keySz,
                                                      sigCtx->key.ed448)) < 0) {
                        WOLFSSL_MSG("ASN Key import error ED448");
                        goto exit_cs;
                    }
                #ifdef WOLFSSL_ASYNC_CRYPT
                    sigCtx->asyncDev = &sigCtx->key.ed448->asyncDev;
                #endif
                    break;
                }
            #endif
                default:
                    WOLFSSL_MSG("Verify Key type unknown");
                    ret = ASN_UNKNOWN_OID_E;
                    break;
            } /* switch (keyOID) */

            if (ret != 0) {
                goto exit_cs;
            }

            sigCtx->state = SIG_STATE_DO;

        #ifdef WOLFSSL_ASYNC_CRYPT
            if (sigCtx->devId != INVALID_DEVID && sigCtx->asyncDev && sigCtx->asyncCtx) {
                /* make sure event is initialized */
                WOLF_EVENT* event = &sigCtx->asyncDev->event;
                ret = wolfAsync_EventInit(event, WOLF_EVENT_TYPE_ASYNC_WOLFSSL,
                    sigCtx->asyncCtx, WC_ASYNC_FLAG_CALL_AGAIN);
            }
        #endif
        } /* SIG_STATE_KEY */
        FALL_THROUGH;

        case SIG_STATE_DO:
        {
            switch (keyOID) {
            #ifndef NO_RSA
                case RSAk:
                {
                #ifdef HAVE_PK_CALLBACKS
                    if (sigCtx->pkCbRsa) {
                        ret = sigCtx->pkCbRsa(
                                sigCtx->plain, sigSz, &sigCtx->out,
                                key, keySz,
                                sigCtx->pkCtxRsa);
                    }
                    else
                #endif /* HAVE_PK_CALLBACKS */
                    {
                     #ifdef WOLFSSL_RENESAS_TSIP_TLS
                        if (rsaKeyIdx != NULL)
                        {
                            ret = tsip_tls_CertVerify(buf, bufSz, sigCtx->plain,
                                sigSz,
                                sigCtx->pubkey_n_start - sigCtx->certBegin,
                                sigCtx->pubkey_n_len - 1,
                                sigCtx->pubkey_e_start - sigCtx->certBegin,
                                sigCtx->pubkey_e_len - 1,
                                rsaKeyIdx);

                            if (ret == 0){
                                sigCtx->verifyByTSIP = 1;
                                ret = 0;
                            } else {
                                WOLFSSL_MSG("RSA Verify by tsip didn't match");
                                ret = ASN_SIG_CONFIRM_E;
                            }
                        } else
                    #endif
                        ret = wc_RsaSSL_VerifyInline(sigCtx->plain, sigSz,
                                                 &sigCtx->out, sigCtx->key.rsa);
                    }
                    break;
                }
            #endif /* !NO_RSA */
            #if defined(HAVE_ECC)
                case ECDSAk:
                {
                #ifdef HAVE_PK_CALLBACKS
                    if (sigCtx->pkCbEcc) {
                        ret = sigCtx->pkCbEcc(
                                sig, sigSz,
                                sigCtx->digest, sigCtx->digestSz,
                                key, keySz, &sigCtx->verify,
                                sigCtx->pkCtxEcc);
                    }
                    else
                #endif /* HAVE_PK_CALLBACKS */
                    {
                        ret = wc_ecc_verify_hash(sig, sigSz, sigCtx->digest,
                                            sigCtx->digestSz, &sigCtx->verify,
                                            sigCtx->key.ecc);
                    }
                    break;
                }
            #endif /* HAVE_ECC */
            #ifdef HAVE_ED25519
                case ED25519k:
                {
                    ret = wc_ed25519_verify_msg(sig, sigSz, buf, bufSz,
                                          &sigCtx->verify, sigCtx->key.ed25519);
                    break;
                }
            #endif
            #ifdef HAVE_ED448
                case ED448k:
                {
                    ret = wc_ed448_verify_msg(sig, sigSz, buf, bufSz,
                                             &sigCtx->verify, sigCtx->key.ed448,
                                             NULL, 0);
                    break;
                }
            #endif
                default:
                    break;
            }  /* switch (keyOID) */

        #ifdef WOLFSSL_ASYNC_CRYPT
            if (ret == WC_PENDING_E) {
                goto exit_cs;
            }
        #endif

            if (ret < 0) {
                /* treat all RSA errors as ASN_SIG_CONFIRM_E */
                ret = ASN_SIG_CONFIRM_E;
                goto exit_cs;
            }

            sigCtx->state = SIG_STATE_CHECK;
        } /* SIG_STATE_DO */
        FALL_THROUGH;

        case SIG_STATE_CHECK:
        {
            switch (keyOID) {
            #ifndef NO_RSA
                case RSAk:
                {
                    int encodedSigSz, verifySz;
                #ifdef WOLFSSL_RENESAS_TSIP
                    if (sigCtx->verifyByTSIP == 1) break;
                #endif
                #ifdef WOLFSSL_SMALL_STACK
                    byte* encodedSig = (byte*)XMALLOC(MAX_ENCODED_SIG_SZ,
                                        sigCtx->heap, DYNAMIC_TYPE_TMP_BUFFER);
                    if (encodedSig == NULL) {
                        ERROR_OUT(MEMORY_E, exit_cs);
                    }
                #else
                    byte encodedSig[MAX_ENCODED_SIG_SZ];
                #endif

                    verifySz = ret;

                    /* make sure we're right justified */
                    encodedSigSz = wc_EncodeSignature(encodedSig,
                            sigCtx->digest, sigCtx->digestSz, sigCtx->typeH);
                    if (encodedSigSz == verifySz && sigCtx->out != NULL &&
                        XMEMCMP(sigCtx->out, encodedSig, encodedSigSz) == 0) {
                        ret = 0;
                    }
                    else {
                        WOLFSSL_MSG("RSA SSL verify match encode error");
                        ret = ASN_SIG_CONFIRM_E;
                    }

                #ifdef WOLFSSL_SMALL_STACK
                    XFREE(encodedSig, sigCtx->heap, DYNAMIC_TYPE_TMP_BUFFER);
                #endif
                    break;
                }
            #endif /* NO_RSA */
            #ifdef HAVE_ECC
                case ECDSAk:
                {
                    if (sigCtx->verify == 1) {
                        ret = 0;
                    }
                    else {
                        WOLFSSL_MSG("ECC Verify didn't match");
                        ret = ASN_SIG_CONFIRM_E;
                    }
                    break;
                }
            #endif /* HAVE_ECC */
            #ifdef HAVE_ED25519
                case ED25519k:
                {
                    if (sigCtx->verify == 1) {
                        ret = 0;
                    }
                    else {
                        WOLFSSL_MSG("ED25519 Verify didn't match");
                        ret = ASN_SIG_CONFIRM_E;
                    }
                    break;
                }
            #endif /* HAVE_ED25519 */
            #ifdef HAVE_ED448
                case ED448k:
                {
                    if (sigCtx->verify == 1) {
                        ret = 0;
                    }
                    else {
                        WOLFSSL_MSG("ED448 Verify didn't match");
                        ret = ASN_SIG_CONFIRM_E;
                    }
                    break;
                }
            #endif /* HAVE_ED448 */
                default:
                    break;
            }  /* switch (keyOID) */

            break;
        } /* SIG_STATE_CHECK */
    } /* switch (sigCtx->state) */

exit_cs:

#endif /* !NO_ASN_CRYPT */

    (void)keyOID;
    (void)sigOID;

    WOLFSSL_LEAVE("ConfirmSignature", ret);

#ifdef WOLFSSL_ASYNC_CRYPT
    if (ret == WC_PENDING_E)
        return ret;
#endif

    FreeSignatureCtx(sigCtx);

    return ret;
}


#ifndef IGNORE_NAME_CONSTRAINTS

static int MatchBaseName(int type, const char* name, int nameSz,
                         const char* base, int baseSz)
{
    if (base == NULL || baseSz <= 0 || name == NULL || nameSz <= 0 ||
            name[0] == '.' || nameSz < baseSz ||
            (type != ASN_RFC822_TYPE && type != ASN_DNS_TYPE))
        return 0;

    /* If an email type, handle special cases where the base is only
     * a domain, or is an email address itself. */
    if (type == ASN_RFC822_TYPE) {
        const char* p = NULL;
        int count = 0;

        if (base[0] != '.') {
            p = base;
            count = 0;

            /* find the '@' in the base */
            while (*p != '@' && count < baseSz) {
                count++;
                p++;
            }

            /* No '@' in base, reset p to NULL */
            if (count >= baseSz)
                p = NULL;
        }

        if (p == NULL) {
            /* Base isn't an email address, it is a domain name,
             * wind the name forward one character past its '@'. */
            p = name;
            count = 0;
            while (*p != '@' && count < baseSz) {
                count++;
                p++;
            }

            if (count < baseSz && *p == '@') {
                name = p + 1;
                nameSz -= count + 1;
            }
        }
    }

    if ((type == ASN_DNS_TYPE || type == ASN_RFC822_TYPE) && base[0] == '.') {
        int szAdjust = nameSz - baseSz;
        name += szAdjust;
        nameSz -= szAdjust;
    }

    while (nameSz > 0) {
        if (XTOLOWER((unsigned char)*name++) !=
                                               XTOLOWER((unsigned char)*base++))
            return 0;
        nameSz--;
    }

    return 1;
}


static int ConfirmNameConstraints(Signer* signer, DecodedCert* cert)
{
    if (signer == NULL || cert == NULL)
        return 0;

    /* Check against the excluded list */
    if (signer->excludedNames) {
        Base_entry* base = signer->excludedNames;

        while (base != NULL) {
            switch (base->type) {
                case ASN_DNS_TYPE:
                {
                    DNS_entry* name = cert->altNames;
                    while (name != NULL) {
                        if (MatchBaseName(ASN_DNS_TYPE,
                                          name->name, name->len,
                                          base->name, base->nameSz)) {
                            return 0;
                        }
                        name = name->next;
                    }
                    break;
                }
                case ASN_RFC822_TYPE:
                {
                    DNS_entry* name = cert->altEmailNames;
                    while (name != NULL) {
                        if (MatchBaseName(ASN_RFC822_TYPE,
                                          name->name, name->len,
                                          base->name, base->nameSz)) {
                            return 0;
                        }
                        name = name->next;
                    }
                    break;
                }
                case ASN_DIR_TYPE:
                {
                    /* allow permitted dirName smaller than actual subject */
                    if (cert->subjectRawLen >= base->nameSz &&
                        XMEMCMP(cert->subjectRaw, base->name,
                                                        base->nameSz) == 0) {
                        return 0;
                    }
                    break;
                }
            }; /* switch */
            base = base->next;
        }
    }

    /* Check against the permitted list */
    if (signer->permittedNames != NULL) {
        int needDns = 0;
        int matchDns = 0;
        int needEmail = 0;
        int matchEmail = 0;
        int needDir = 0;
        int matchDir = 0;
        Base_entry* base = signer->permittedNames;

        while (base != NULL) {
            switch (base->type) {
                case ASN_DNS_TYPE:
                {
                    DNS_entry* name = cert->altNames;

                    if (name != NULL)
                        needDns = 1;

                    while (name != NULL) {
                        matchDns = MatchBaseName(ASN_DNS_TYPE,
                                          name->name, name->len,
                                          base->name, base->nameSz);
                        name = name->next;
                    }
                    break;
                }
                case ASN_RFC822_TYPE:
                {
                    DNS_entry* name = cert->altEmailNames;

                    if (name != NULL)
                        needEmail = 1;

                    while (name != NULL) {
                        matchEmail = MatchBaseName(ASN_DNS_TYPE,
                                          name->name, name->len,
                                          base->name, base->nameSz);
                        name = name->next;
                    }
                    break;
                }
                case ASN_DIR_TYPE:
                {
                    /* allow permitted dirName smaller than actual subject */
                    needDir = 1;
                    if (cert->subjectRaw != NULL &&
                        cert->subjectRawLen >= base->nameSz &&
                        XMEMCMP(cert->subjectRaw, base->name,
                                                        base->nameSz) == 0) {
                        matchDir = 1;
                    }
                    break;
                }
            } /* switch */
            base = base->next;
        }

        if ((needDns   && !matchDns) ||
            (needEmail && !matchEmail) ||
            (needDir   && !matchDir)) {
            return 0;
        }
    }

    return 1;
}

#endif /* IGNORE_NAME_CONSTRAINTS */

static int DecodeAltNames(const byte* input, int sz, DecodedCert* cert)
{
    word32 idx = 0;
    int length = 0;

    WOLFSSL_ENTER("DecodeAltNames");

    if (GetSequence(input, &idx, &length, sz) < 0) {
        WOLFSSL_MSG("\tBad Sequence");
        return ASN_PARSE_E;
    }

    if (length == 0) {
        /* RFC 5280 4.2.1.6.  Subject Alternative Name
           If the subjectAltName extension is present, the sequence MUST
           contain at least one entry. */
        return ASN_PARSE_E;
    }

    cert->weOwnAltNames = 1;

    while (length > 0) {
        byte b = input[idx++];

        length--;

        /* Save DNS Type names in the altNames list. */
        /* Save Other Type names in the cert's OidMap */
        if (b == (ASN_CONTEXT_SPECIFIC | ASN_DNS_TYPE)) {
            DNS_entry* dnsEntry;
            int strLen;
            word32 lenStartIdx = idx;

            if (GetLength(input, &idx, &strLen, sz) < 0) {
                WOLFSSL_MSG("\tfail: str length");
                return ASN_PARSE_E;
            }
            length -= (idx - lenStartIdx);

            dnsEntry = (DNS_entry*)XMALLOC(sizeof(DNS_entry), cert->heap,
                                        DYNAMIC_TYPE_ALTNAME);
            if (dnsEntry == NULL) {
                WOLFSSL_MSG("\tOut of Memory");
                return MEMORY_E;
            }

            dnsEntry->type = ASN_DNS_TYPE;
            dnsEntry->name = (char*)XMALLOC(strLen + 1, cert->heap,
                                         DYNAMIC_TYPE_ALTNAME);
            if (dnsEntry->name == NULL) {
                WOLFSSL_MSG("\tOut of Memory");
                XFREE(dnsEntry, cert->heap, DYNAMIC_TYPE_ALTNAME);
                return MEMORY_E;
            }
            dnsEntry->len = strLen;
            XMEMCPY(dnsEntry->name, &input[idx], strLen);
            dnsEntry->name[strLen] = '\0';

            dnsEntry->next = cert->altNames;
            cert->altNames = dnsEntry;

            length -= strLen;
            idx    += strLen;
        }
    #ifndef IGNORE_NAME_CONSTRAINTS
        else if (b == (ASN_CONTEXT_SPECIFIC | ASN_RFC822_TYPE)) {
            DNS_entry* emailEntry;
            int strLen;
            word32 lenStartIdx = idx;

            if (GetLength(input, &idx, &strLen, sz) < 0) {
                WOLFSSL_MSG("\tfail: str length");
                return ASN_PARSE_E;
            }
            length -= (idx - lenStartIdx);

            emailEntry = (DNS_entry*)XMALLOC(sizeof(DNS_entry), cert->heap,
                                        DYNAMIC_TYPE_ALTNAME);
            if (emailEntry == NULL) {
                WOLFSSL_MSG("\tOut of Memory");
                return MEMORY_E;
            }

            emailEntry->type = ASN_RFC822_TYPE;
            emailEntry->name = (char*)XMALLOC(strLen + 1, cert->heap,
                                         DYNAMIC_TYPE_ALTNAME);
            if (emailEntry->name == NULL) {
                WOLFSSL_MSG("\tOut of Memory");
                XFREE(emailEntry, cert->heap, DYNAMIC_TYPE_ALTNAME);
                return MEMORY_E;
            }
            emailEntry->len = strLen;
            XMEMCPY(emailEntry->name, &input[idx], strLen);
            emailEntry->name[strLen] = '\0';

            emailEntry->next = cert->altEmailNames;
            cert->altEmailNames = emailEntry;

            length -= strLen;
            idx    += strLen;
        }
        else if (b == (ASN_CONTEXT_SPECIFIC | ASN_URI_TYPE)) {
            DNS_entry* uriEntry;
            int strLen;
            word32 lenStartIdx = idx;

            WOLFSSL_MSG("\tPutting URI into list but not using");
            if (GetLength(input, &idx, &strLen, sz) < 0) {
                WOLFSSL_MSG("\tfail: str length");
                return ASN_PARSE_E;
            }
            length -= (idx - lenStartIdx);

            /* check that strLen at index is not past input buffer */
            if (strLen + (int)idx > sz) {
                return BUFFER_E;
            }

        #ifndef WOLFSSL_NO_ASN_STRICT
            /* Verify RFC 5280 Sec 4.2.1.6 rule:
                "The name MUST NOT be a relative URI" */

            {
                int i;

                /* skip past scheme (i.e http,ftp,...) finding first ':' char */
                for (i = 0; i < strLen; i++) {
                    if (input[idx + i] == ':') {
                        break;
                    }
                    if (input[idx + i] == '/') {
                        i = strLen; /* error, found relative path since '/' was
                                     * encountered before ':'. Returning error
                                     * value in next if statement. */
                    }
                }

                /* test if no ':' char was found and test that the next two
                 * chars are // to match the pattern "://" */
                if (i >= strLen - 2 || (input[idx + i + 1] != '/' ||
                                        input[idx + i + 2] != '/')) {
                    WOLFSSL_MSG("\tAlt Name must be absolute URI");
                    return ASN_ALT_NAME_E;
                }
            }
        #endif

            uriEntry = (DNS_entry*)XMALLOC(sizeof(DNS_entry), cert->heap,
                                        DYNAMIC_TYPE_ALTNAME);
            if (uriEntry == NULL) {
                WOLFSSL_MSG("\tOut of Memory");
                return MEMORY_E;
            }

            uriEntry->type = ASN_URI_TYPE;
            uriEntry->name = (char*)XMALLOC(strLen + 1, cert->heap,
                                         DYNAMIC_TYPE_ALTNAME);
            if (uriEntry->name == NULL) {
                WOLFSSL_MSG("\tOut of Memory");
                XFREE(uriEntry, cert->heap, DYNAMIC_TYPE_ALTNAME);
                return MEMORY_E;
            }
            uriEntry->len = strLen;
            XMEMCPY(uriEntry->name, &input[idx], strLen);
            uriEntry->name[strLen] = '\0';

            uriEntry->next = cert->altNames;
            cert->altNames = uriEntry;

            length -= strLen;
            idx    += strLen;
        }
#if defined(WOLFSSL_QT) || defined(OPENSSL_ALL) || defined(WOLFSSL_IP_ALT_NAME)
        else if (b == (ASN_CONTEXT_SPECIFIC | ASN_IP_TYPE)) {
            DNS_entry* ipAddr;
            int strLen;
            word32 lenStartIdx = idx;
            WOLFSSL_MSG("Decoding Subject Alt. Name: IP Address");

            if (GetLength(input, &idx, &strLen, sz) < 0) {
                WOLFSSL_MSG("\tfail: str length");
                return ASN_PARSE_E;
            }
            length -= (idx - lenStartIdx);
            /* check that strLen at index is not past input buffer */
            if (strLen + (int)idx > sz) {
                return BUFFER_E;
            }

            ipAddr = (DNS_entry*)XMALLOC(sizeof(DNS_entry), cert->heap,
                                        DYNAMIC_TYPE_ALTNAME);
            if (ipAddr == NULL) {
                WOLFSSL_MSG("\tOut of Memory");
                return MEMORY_E;
            }

            ipAddr->type = ASN_IP_TYPE;
            ipAddr->name = (char*)XMALLOC(strLen + 1, cert->heap,
                                         DYNAMIC_TYPE_ALTNAME);
            if (ipAddr->name == NULL) {
                WOLFSSL_MSG("\tOut of Memory");
                XFREE(ipAddr, cert->heap, DYNAMIC_TYPE_ALTNAME);
                return MEMORY_E;
            }
            ipAddr->len = strLen;
            XMEMCPY(ipAddr->name, &input[idx], strLen);
            ipAddr->name[strLen] = '\0';

            ipAddr->next   = cert->altNames;
            cert->altNames = ipAddr;

            length -= strLen;
            idx    += strLen;
        }
#endif /* WOLFSSL_QT || OPENSSL_ALL */
#endif /* IGNORE_NAME_CONSTRAINTS */
#ifdef WOLFSSL_SEP
        else if (b == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | ASN_OTHER_TYPE))
        {
            int strLen;
            word32 lenStartIdx = idx;
            word32 oid = 0;
            int    ret;
            byte   tag;

            if (GetLength(input, &idx, &strLen, sz) < 0) {
                WOLFSSL_MSG("\tfail: other name length");
                return ASN_PARSE_E;
            }
            /* Consume the rest of this sequence. */
            length -= (strLen + idx - lenStartIdx);

            if (GetObjectId(input, &idx, &oid, oidCertAltNameType, sz) < 0) {
                WOLFSSL_MSG("\tbad OID");
                return ASN_PARSE_E;
            }

            if (oid != HW_NAME_OID) {
                WOLFSSL_MSG("\tincorrect OID");
                return ASN_PARSE_E;
            }

            if (GetASNTag(input, &idx, &tag, sz) < 0) {
                return ASN_PARSE_E;
            }

            if (tag != (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED)) {
                WOLFSSL_MSG("\twrong type");
                return ASN_PARSE_E;
            }

            if (GetLength(input, &idx, &strLen, sz) < 0) {
                WOLFSSL_MSG("\tfail: str len");
                return ASN_PARSE_E;
            }

            if (GetSequence(input, &idx, &strLen, sz) < 0) {
                WOLFSSL_MSG("\tBad Sequence");
                return ASN_PARSE_E;
            }

            ret = GetASNObjectId(input, &idx, &strLen, sz);
            if (ret != 0) {
                WOLFSSL_MSG("\tbad OID");
                return ret;
            }

            cert->hwType = (byte*)XMALLOC(strLen, cert->heap,
                                          DYNAMIC_TYPE_X509_EXT);
            if (cert->hwType == NULL) {
                WOLFSSL_MSG("\tOut of Memory");
                return MEMORY_E;
            }

            XMEMCPY(cert->hwType, &input[idx], strLen);
            cert->hwTypeSz = strLen;
            idx += strLen;

            ret = GetOctetString(input, &idx, &strLen, sz);
            if (ret < 0)
                return ret;

            cert->hwSerialNum = (byte*)XMALLOC(strLen + 1, cert->heap,
                                               DYNAMIC_TYPE_X509_EXT);
            if (cert->hwSerialNum == NULL) {
                WOLFSSL_MSG("\tOut of Memory");
                return MEMORY_E;
            }

            XMEMCPY(cert->hwSerialNum, &input[idx], strLen);
            cert->hwSerialNum[strLen] = '\0';
            cert->hwSerialNumSz = strLen;
            idx += strLen;
        }
    #endif /* WOLFSSL_SEP */
        else {
            int strLen;
            word32 lenStartIdx = idx;

            WOLFSSL_MSG("\tUnsupported name type, skipping");

            if (GetLength(input, &idx, &strLen, sz) < 0) {
                WOLFSSL_MSG("\tfail: unsupported name length");
                return ASN_PARSE_E;
            }
            length -= (strLen + idx - lenStartIdx);
            idx += strLen;
        }
    }
    return 0;
}

static int DecodeBasicCaConstraint(const byte* input, int sz, DecodedCert* cert)
{
    word32 idx = 0;
    int length = 0;
    int ret;

    WOLFSSL_ENTER("DecodeBasicCaConstraint");

    if (GetSequence(input, &idx, &length, sz) < 0) {
        WOLFSSL_MSG("\tfail: bad SEQUENCE");
        return ASN_PARSE_E;
    }

    if (length == 0)
        return 0;

    /* If the basic ca constraint is false, this extension may be named, but
     * left empty. So, if the length is 0, just return. */

    ret = GetBoolean(input, &idx, sz);

#ifndef WOLFSSL_X509_BASICCONS_INT
    if (ret < 0) {
        WOLFSSL_MSG("\tfail: constraint not valid BOOLEAN");
        return ret;
    }

    cert->isCA = (byte)ret;
#else
    if (ret < 0) {
        if(input[idx] == ASN_INTEGER) {
            /* For OpenSSL compatibility, if ASN_INTEGER it is valid format */
            cert->isCA = FALSE;
        } else return ret;
    } else
        cert->isCA = (byte)ret;
#endif

    /* If there isn't any more data, return. */
    if (idx >= (word32)sz) {
        return 0;
    }

    ret = GetInteger7Bit(input, &idx, sz);
    if (ret < 0)
        return ret;
    cert->pathLength = (byte)ret;
    cert->pathLengthSet = 1;

    return 0;
}


#define CRLDP_FULL_NAME 0
    /* From RFC3280 SS4.2.1.14, Distribution Point Name*/
#define GENERALNAME_URI 6
    /* From RFC3280 SS4.2.1.7, GeneralName */

static int DecodeCrlDist(const byte* input, int sz, DecodedCert* cert)
{
    word32 idx = 0, localIdx;
    int length = 0;
    byte tag   = 0;

    WOLFSSL_ENTER("DecodeCrlDist");

    /* Unwrap the list of Distribution Points*/
    if (GetSequence(input, &idx, &length, sz) < 0)
        return ASN_PARSE_E;

    /* Unwrap a single Distribution Point */
    if (GetSequence(input, &idx, &length, sz) < 0)
        return ASN_PARSE_E;

    /* The Distribution Point has three explicit optional members
     *  First check for a DistributionPointName
     */
    localIdx = idx;
    if (GetASNTag(input, &localIdx, &tag, sz) == 0 &&
            tag == (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 0))
    {
        idx++;
        if (GetLength(input, &idx, &length, sz) < 0)
            return ASN_PARSE_E;

        localIdx = idx;
        if (GetASNTag(input, &localIdx, &tag, sz) == 0 &&
                tag == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED |
                    CRLDP_FULL_NAME))
        {
            idx++;
            if (GetLength(input, &idx, &length, sz) < 0)
                return ASN_PARSE_E;

            localIdx = idx;
            if (GetASNTag(input, &localIdx, &tag, sz) == 0 &&
                    tag == (ASN_CONTEXT_SPECIFIC | GENERALNAME_URI))
            {
                idx++;
                if (GetLength(input, &idx, &length, sz) < 0)
                    return ASN_PARSE_E;

                cert->extCrlInfoSz = length;
                cert->extCrlInfo = input + idx;
                idx += length;
            }
            else
                /* This isn't a URI, skip it. */
                idx += length;
        }
        else {
            /* This isn't a FULLNAME, skip it. */
            idx += length;
        }
    }

    /* Check for reasonFlags */
    localIdx = idx;
    if (idx < (word32)sz &&
        GetASNTag(input, &localIdx, &tag, sz) == 0 &&
        tag == (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 1))
    {
        idx++;
        if (GetLength(input, &idx, &length, sz) < 0)
            return ASN_PARSE_E;
        idx += length;
    }

    /* Check for cRLIssuer */
    localIdx = idx;
    if (idx < (word32)sz &&
        GetASNTag(input, &localIdx, &tag, sz) == 0 &&
        tag == (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 2))
    {
        idx++;
        if (GetLength(input, &idx, &length, sz) < 0)
            return ASN_PARSE_E;
        idx += length;
    }

    if (idx < (word32)sz)
    {
        WOLFSSL_MSG("\tThere are more CRL Distribution Point records, "
                   "but we only use the first one.");
    }

    return 0;
}


static int DecodeAuthInfo(const byte* input, int sz, DecodedCert* cert)
/*
 *  Read Authority Information Access records. If there are
 *  any issues, return without saving the record.
 */
{
    word32 idx = 0;
    int length = 0;
    int count  = 0;
    byte b = 0;
    word32 oid;

    WOLFSSL_ENTER("DecodeAuthInfo");

    /* Unwrap the list of AIAs */
    if (GetSequence(input, &idx, &length, sz) < 0)
        return ASN_PARSE_E;

    while ((idx < (word32)sz) && (count < MAX_AIA_SZ)) {
        /* Unwrap a single AIA */
        if (GetSequence(input, &idx, &length, sz) < 0)
            return ASN_PARSE_E;

        oid = 0;
        if (GetObjectId(input, &idx, &oid, oidCertAuthInfoType, sz) < 0)
            return ASN_PARSE_E;

        /* Only supporting URIs right now. */
        if (GetASNTag(input, &idx, &b, sz) < 0)
            return ASN_PARSE_E;

        if (GetLength(input, &idx, &length, sz) < 0)
            return ASN_PARSE_E;

        /* Set ocsp entry */
        if (b == (ASN_CONTEXT_SPECIFIC | GENERALNAME_URI) &&
            oid == AIA_OCSP_OID)
        {
            cert->extAuthInfoSz = length;
            cert->extAuthInfo = input + idx;
            count++;
        #if !defined(OPENSSL_ALL) || !defined(WOLFSSL_QT)
            break;
        #endif
        }
        #if defined(OPENSSL_ALL) || defined(WOLFSSL_QT)
        /* Set CaIssuers entry */
        else if ((b == (ASN_CONTEXT_SPECIFIC | GENERALNAME_URI)) &&
            oid == AIA_CA_ISSUER_OID)
        {
            cert->extAuthInfoCaIssuerSz = length;
            cert->extAuthInfoCaIssuer = input + idx;
            count++;
        }
        #endif
        idx += length;
    }

    return 0;
}


static int DecodeAuthKeyId(const byte* input, int sz, DecodedCert* cert)
{
    word32 idx = 0;
    int length = 0, ret = 0;
    byte tag;

    WOLFSSL_ENTER("DecodeAuthKeyId");

    if (GetSequence(input, &idx, &length, sz) < 0) {
        WOLFSSL_MSG("\tfail: should be a SEQUENCE\n");
        return ASN_PARSE_E;
    }

    if (GetASNTag(input, &idx, &tag, sz) < 0) {
        return ASN_PARSE_E;
    }

    if (tag != (ASN_CONTEXT_SPECIFIC | 0)) {
        WOLFSSL_MSG("\tinfo: OPTIONAL item 0, not available\n");
        cert->extAuthKeyIdSet = 0;
        return 0;
    }

    if (GetLength(input, &idx, &length, sz) <= 0) {
        WOLFSSL_MSG("\tfail: extension data length");
        return ASN_PARSE_E;
    }

#if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
    cert->extAuthKeyIdSrc = &input[idx];
    cert->extAuthKeyIdSz = length;
#endif /* OPENSSL_EXTRA */

    if (length == KEYID_SIZE) {
        XMEMCPY(cert->extAuthKeyId, input + idx, length);
    }
    else
        ret = CalcHashId(input + idx, length, cert->extAuthKeyId);

    return ret;
}


static int DecodeSubjKeyId(const byte* input, int sz, DecodedCert* cert)
{
    word32 idx = 0;
    int length = 0, ret = 0;

    WOLFSSL_ENTER("DecodeSubjKeyId");

    if (sz <= 0)
        return ASN_PARSE_E;

    ret = GetOctetString(input, &idx, &length, sz);
    if (ret < 0)
        return ret;

    #if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
        cert->extSubjKeyIdSrc = &input[idx];
        cert->extSubjKeyIdSz = length;
    #endif /* OPENSSL_EXTRA */

    if (length == KEYID_SIZE) {
        XMEMCPY(cert->extSubjKeyId, input + idx, length);
    }
    else
        ret = CalcHashId(input + idx, length, cert->extSubjKeyId);

    return ret;
}


static int DecodeKeyUsage(const byte* input, int sz, DecodedCert* cert)
{
    word32 idx = 0;
    int length;
    int ret;
    WOLFSSL_ENTER("DecodeKeyUsage");

    ret = CheckBitString(input, &idx, &length, sz, 0, NULL);
    if (ret != 0)
        return ret;

    cert->extKeyUsage = (word16)(input[idx]);
    if (length == 2)
        cert->extKeyUsage |= (word16)(input[idx+1] << 8);

    return 0;
}


static int DecodeExtKeyUsage(const byte* input, int sz, DecodedCert* cert)
{
    word32 idx = 0, oid;
    int length, ret;

    WOLFSSL_MSG("DecodeExtKeyUsage");

    if (GetSequence(input, &idx, &length, sz) < 0) {
        WOLFSSL_MSG("\tfail: should be a SEQUENCE");
        return ASN_PARSE_E;
    }

#if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
    cert->extExtKeyUsageSrc = input + idx;
    cert->extExtKeyUsageSz = length;
#endif

    while (idx < (word32)sz) {
        ret = GetObjectId(input, &idx, &oid, oidCertKeyUseType, sz);
        if (ret == ASN_UNKNOWN_OID_E)
            continue;
        else if (ret < 0)
            return ret;

        switch (oid) {
            case EKU_ANY_OID:
                cert->extExtKeyUsage |= EXTKEYUSE_ANY;
                break;
            case EKU_SERVER_AUTH_OID:
                cert->extExtKeyUsage |= EXTKEYUSE_SERVER_AUTH;
                break;
            case EKU_CLIENT_AUTH_OID:
                cert->extExtKeyUsage |= EXTKEYUSE_CLIENT_AUTH;
                break;
            case EKU_CODESIGNING_OID:
                cert->extExtKeyUsage |= EXTKEYUSE_CODESIGN;
                break;
            case EKU_EMAILPROTECT_OID:
                cert->extExtKeyUsage |= EXTKEYUSE_EMAILPROT;
                break;
            case EKU_TIMESTAMP_OID:
                cert->extExtKeyUsage |= EXTKEYUSE_TIMESTAMP;
                break;
            case EKU_OCSP_SIGN_OID:
                cert->extExtKeyUsage |= EXTKEYUSE_OCSP_SIGN;
                break;
        }

    #if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
        cert->extExtKeyUsageCount++;
    #endif
    }

    return 0;
}


#ifndef IGNORE_NAME_CONSTRAINTS
#define ASN_TYPE_MASK 0xF
static int DecodeSubtree(const byte* input, int sz,
                         Base_entry** head, void* heap)
{
    word32 idx = 0;

    (void)heap;

    while (idx < (word32)sz) {
        int seqLength, strLength;
        word32 nameIdx;
        byte b, bType;

        if (GetSequence(input, &idx, &seqLength, sz) < 0) {
            WOLFSSL_MSG("\tfail: should be a SEQUENCE");
            return ASN_PARSE_E;
        }
        nameIdx = idx;
        b = input[nameIdx++];

        if (GetLength(input, &nameIdx, &strLength, sz) <= 0) {
            WOLFSSL_MSG("\tinvalid length");
            return ASN_PARSE_E;
        }

        /* Get type, LSB 4-bits */
        bType = (b & ASN_TYPE_MASK);

        if (bType == ASN_DNS_TYPE || bType == ASN_RFC822_TYPE ||
                                                        bType == ASN_DIR_TYPE) {
            Base_entry* entry;

            /* if constructed has leading sequence */
            if (b & ASN_CONSTRUCTED) {
                if (GetSequence(input, &nameIdx, &strLength, sz) < 0) {
                    WOLFSSL_MSG("\tfail: constructed be a SEQUENCE");
                    return ASN_PARSE_E;
                }
            }

            entry = (Base_entry*)XMALLOC(sizeof(Base_entry), heap,
                                                          DYNAMIC_TYPE_ALTNAME);
            if (entry == NULL) {
                WOLFSSL_MSG("allocate error");
                return MEMORY_E;
            }

            entry->name = (char*)XMALLOC(strLength, heap, DYNAMIC_TYPE_ALTNAME);
            if (entry->name == NULL) {
                WOLFSSL_MSG("allocate error");
                XFREE(entry, heap, DYNAMIC_TYPE_ALTNAME);
                return MEMORY_E;
            }

            XMEMCPY(entry->name, &input[nameIdx], strLength);
            entry->nameSz = strLength;
            entry->type = bType;

            entry->next = *head;
            *head = entry;
        }

        idx += seqLength;
    }

    return 0;
}


static int DecodeNameConstraints(const byte* input, int sz, DecodedCert* cert)
{
    word32 idx = 0;
    int length = 0;

    WOLFSSL_ENTER("DecodeNameConstraints");

    if (GetSequence(input, &idx, &length, sz) < 0) {
        WOLFSSL_MSG("\tfail: should be a SEQUENCE");
        return ASN_PARSE_E;
    }

    while (idx < (word32)sz) {
        byte b = input[idx++];
        Base_entry** subtree = NULL;

        if (GetLength(input, &idx, &length, sz) <= 0) {
            WOLFSSL_MSG("\tinvalid length");
            return ASN_PARSE_E;
        }

        if (b == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | 0))
            subtree = &cert->permittedNames;
        else if (b == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | 1))
            subtree = &cert->excludedNames;
        else {
            WOLFSSL_MSG("\tinvalid subtree");
            return ASN_PARSE_E;
        }

        if (DecodeSubtree(input + idx, length, subtree, cert->heap) < 0) {
            WOLFSSL_MSG("\terror parsing subtree");
            return ASN_PARSE_E;
        }

        idx += length;
    }

    return 0;
}
#endif /* IGNORE_NAME_CONSTRAINTS */

#if (defined(WOLFSSL_CERT_EXT) && !defined(WOLFSSL_SEP)) || \
    defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)

/* Decode ITU-T X.690 OID format to a string representation
 * return string length */
int DecodePolicyOID(char *out, word32 outSz, const byte *in, word32 inSz)
{
    word32 val, inIdx = 0, outIdx = 0;
    int w = 0;

    if (out == NULL || in == NULL || outSz < 4 || inSz < 2)
        return BAD_FUNC_ARG;

    /* The first byte expands into b/40 dot b%40. */
    val = in[inIdx++];

    w = XSNPRINTF(out, outSz, "%u.%u", val / 40, val % 40);
    if (w < 0)
        goto exit;
    outIdx += w;
    val = 0;

    while (inIdx < inSz && outIdx < outSz) {
        /* extract the next OID digit from in to val */
        /* first bit is used to set if value is coded on 1 or multiple bytes */
        if (in[inIdx] & 0x80) {
            val += in[inIdx] & 0x7F;
            val *= 128;
        }
        else {
            /* write val as text into out */
            val += in[inIdx];
            w = XSNPRINTF(out + outIdx, outSz - outIdx, ".%u", val);
            if (w < 0)
                goto exit;
            outIdx += w;
            val = 0;
        }
        inIdx++;
    }
    if (outIdx == outSz)
        outIdx--;
    out[outIdx] = 0;

    w = (int)outIdx;

exit:
    return w;
}
#endif /* WOLFSSL_CERT_EXT && !WOLFSSL_SEP */

#if defined(WOLFSSL_SEP) || defined(WOLFSSL_CERT_EXT) || defined(WOLFSSL_QT)
    /* Reference: https://tools.ietf.org/html/rfc5280#section-4.2.1.4 */
    static int DecodeCertPolicy(const byte* input, int sz, DecodedCert* cert)
    {
        word32 idx = 0;
        word32 oldIdx;
        int ret;
        int total_length = 0, policy_length = 0, length = 0;
    #if !defined(WOLFSSL_SEP) && defined(WOLFSSL_CERT_EXT) && \
        !defined(WOLFSSL_DUP_CERTPOL)
        int i;
    #endif

        WOLFSSL_ENTER("DecodeCertPolicy");
        #if defined(WOLFSSL_SEP) || defined(WOLFSSL_CERT_EXT)
        /* Check if cert is null before dereferencing below */
        if (cert == NULL)
            return BAD_FUNC_ARG;
        #endif

    #if defined(WOLFSSL_CERT_EXT)
         cert->extCertPoliciesNb = 0;
    #endif

        if (GetSequence(input, &idx, &total_length, sz) < 0) {
            WOLFSSL_MSG("\tGet CertPolicy total seq failed");
            return ASN_PARSE_E;
        }

        /* Validate total length */
        if (total_length > (sz - (int)idx)) {
            WOLFSSL_MSG("\tCertPolicy length mismatch");
            return ASN_PARSE_E;
        }

        /* Unwrap certificatePolicies */
        do {
            if (GetSequence(input, &idx, &policy_length, sz) < 0) {
                WOLFSSL_MSG("\tGet CertPolicy seq failed");
                return ASN_PARSE_E;
            }

            oldIdx = idx;
            ret = GetASNObjectId(input, &idx, &length, sz);
            if (ret != 0)
                return ret;
            policy_length -= idx - oldIdx;

            if (length > 0) {
                /* Verify length won't overrun buffer */
                if (length > (sz - (int)idx)) {
                    WOLFSSL_MSG("\tCertPolicy length exceeds input buffer");
                    return ASN_PARSE_E;
                }

        #if defined(WOLFSSL_SEP)
                cert->deviceType = (byte*)XMALLOC(length, cert->heap,
                                                         DYNAMIC_TYPE_X509_EXT);
                if (cert->deviceType == NULL) {
                    WOLFSSL_MSG("\tCouldn't alloc memory for deviceType");
                    return MEMORY_E;
                }
                cert->deviceTypeSz = length;
                XMEMCPY(cert->deviceType, input + idx, length);
                break;
        #elif defined(WOLFSSL_CERT_EXT)
                /* decode cert policy */
                if (DecodePolicyOID(cert->extCertPolicies[
                                       cert->extCertPoliciesNb], MAX_CERTPOL_SZ,
                                       input + idx, length) <= 0) {
                    WOLFSSL_MSG("\tCouldn't decode CertPolicy");
                    return ASN_PARSE_E;
                }
            #ifndef WOLFSSL_DUP_CERTPOL
                /* From RFC 5280 section 4.2.1.3 "A certificate policy OID MUST
                 * NOT appear more than once in a certificate policies
                 * extension". This is a sanity check for duplicates.
                 * extCertPolicies should only have OID values, additional
                 * qualifiers need to be stored in a separate array. */
                for (i = 0; i < cert->extCertPoliciesNb; i++) {
                    if (XMEMCMP(cert->extCertPolicies[i],
                            cert->extCertPolicies[cert->extCertPoliciesNb],
                            MAX_CERTPOL_SZ) == 0) {
                            WOLFSSL_MSG("Duplicate policy OIDs not allowed");
                            WOLFSSL_MSG("Use WOLFSSL_DUP_CERTPOL if wanted");
                            return CERTPOLICIES_E;
                    }
                }
            #endif /* !WOLFSSL_DUP_CERTPOL */
                cert->extCertPoliciesNb++;
        #else
                WOLFSSL_LEAVE("DecodeCertPolicy : unsupported mode", 0);
                return 0;
        #endif
            }
            idx += policy_length;
        } while((int)idx < total_length
    #if defined(WOLFSSL_CERT_EXT)
            && cert->extCertPoliciesNb < MAX_CERTPOL_NB
    #endif
        );

        WOLFSSL_LEAVE("DecodeCertPolicy", 0);
        return 0;
    }
#endif /* WOLFSSL_SEP */

/* Macro to check if bit is set, if not sets and return success.
    Otherwise returns failure */
/* Macro required here because bit-field operation */
#ifndef WOLFSSL_NO_ASN_STRICT
    #define VERIFY_AND_SET_OID(bit) \
        if (bit == 0) \
            bit = 1; \
        else \
            return ASN_OBJECT_ID_E;
#else
    /* With no strict defined, the verify is skipped */
#define VERIFY_AND_SET_OID(bit) bit = 1;
#endif

static int DecodeCertExtensions(DecodedCert* cert)
/*
 *  Processing the Certificate Extensions. This does not modify the current
 *  index. It is works starting with the recorded extensions pointer.
 */
{
    int ret = 0;
    word32 idx = 0;
    int sz = cert->extensionsSz;
    const byte* input = cert->extensions;
    int length;
    word32 oid;
    byte critical = 0;
    byte criticalFail = 0;
    byte tag = 0;

    WOLFSSL_ENTER("DecodeCertExtensions");

    if (input == NULL || sz == 0)
        return BAD_FUNC_ARG;

    if (GetASNTag(input, &idx, &tag, sz) < 0) {
        return ASN_PARSE_E;
    }

    if (tag != ASN_EXTENSIONS) {
        WOLFSSL_MSG("\tfail: should be an EXTENSIONS");
        return ASN_PARSE_E;
    }

    if (GetLength(input, &idx, &length, sz) < 0) {
        WOLFSSL_MSG("\tfail: invalid length");
        return ASN_PARSE_E;
    }

    if (GetSequence(input, &idx, &length, sz) < 0) {
        WOLFSSL_MSG("\tfail: should be a SEQUENCE (1)");
        return ASN_PARSE_E;
    }

    while (idx < (word32)sz) {
        word32 localIdx;

        if (GetSequence(input, &idx, &length, sz) < 0) {
            WOLFSSL_MSG("\tfail: should be a SEQUENCE");
            return ASN_PARSE_E;
        }

        oid = 0;
        if ((ret = GetObjectId(input, &idx, &oid, oidCertExtType, sz)) < 0) {
            WOLFSSL_MSG("\tfail: OBJECT ID");
            return ret;
        }

        /* check for critical flag */
        critical = 0;
        if ((idx + 1) > (word32)sz) {
            WOLFSSL_MSG("\tfail: malformed buffer");
            return BUFFER_E;
        }

        localIdx = idx;
        if (GetASNTag(input, &localIdx, &tag, sz) == 0) {
            if (tag == ASN_BOOLEAN) {
                ret = GetBoolean(input, &idx, sz);
                if (ret < 0) {
                    WOLFSSL_MSG("\tfail: critical boolean");
                    return ret;
                }

                critical = (byte)ret;
            }
        }

        /* process the extension based on the OID */
        ret = GetOctetString(input, &idx, &length, sz);
        if (ret < 0) {
            WOLFSSL_MSG("\tfail: bad OCTET STRING");
            return ret;
        }

        switch (oid) {
            case BASIC_CA_OID:
                VERIFY_AND_SET_OID(cert->extBasicConstSet);
                #if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
                    cert->extBasicConstCrit = critical;
                #endif
                if (DecodeBasicCaConstraint(&input[idx], length, cert) < 0)
                    return ASN_PARSE_E;
                break;

            case CRL_DIST_OID:
                VERIFY_AND_SET_OID(cert->extCRLdistSet);
                #if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
                    cert->extCRLdistCrit = critical;
                #endif
                if (DecodeCrlDist(&input[idx], length, cert) < 0)
                    return ASN_PARSE_E;
                break;

            case AUTH_INFO_OID:
                VERIFY_AND_SET_OID(cert->extAuthInfoSet);
                #if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
                    cert->extAuthInfoCrit = critical;
                #endif
                if (DecodeAuthInfo(&input[idx], length, cert) < 0)
                    return ASN_PARSE_E;
                break;

            case ALT_NAMES_OID:
                VERIFY_AND_SET_OID(cert->extSubjAltNameSet);
                #if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
                    cert->extSubjAltNameCrit = critical;
                #endif
                ret = DecodeAltNames(&input[idx], length, cert);
                if (ret < 0)
                    return ret;
                break;

            case AUTH_KEY_OID:
                VERIFY_AND_SET_OID(cert->extAuthKeyIdSet);
                #if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
                    cert->extAuthKeyIdCrit = critical;
                #endif
                #ifndef WOLFSSL_ALLOW_CRIT_SKID
                    /* This check is added due to RFC 5280 section 4.2.1.1
                     * stating that conforming CA's must mark this extension
                     * as non-critical. When parsing extensions check that
                     * certificate was made in compliance with this. */
                    if (critical) {
                        WOLFSSL_MSG("Critical Auth Key ID is not allowed");
                        WOLFSSL_MSG("Use macro WOLFSSL_ALLOW_CRIT_SKID if wanted");
                        return ASN_CRIT_EXT_E;
                    }
                #endif
                if (DecodeAuthKeyId(&input[idx], length, cert) < 0)
                    return ASN_PARSE_E;
                break;

            case SUBJ_KEY_OID:
                VERIFY_AND_SET_OID(cert->extSubjKeyIdSet);
                #if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
                    cert->extSubjKeyIdCrit = critical;
                #endif
                #ifndef WOLFSSL_ALLOW_CRIT_SKID
                    /* This check is added due to RFC 5280 section 4.2.1.2
                     * stating that conforming CA's must mark this extension
                     * as non-critical. When parsing extensions check that
                     * certificate was made in compliance with this. */
                    if (critical) {
                        WOLFSSL_MSG("Critical Subject Key ID is not allowed");
                        WOLFSSL_MSG("Use macro WOLFSSL_ALLOW_CRIT_SKID if wanted");
                        return ASN_CRIT_EXT_E;
                    }
                #endif

                if (DecodeSubjKeyId(&input[idx], length, cert) < 0)
                    return ASN_PARSE_E;
                break;

            case CERT_POLICY_OID:
                #if defined(WOLFSSL_SEP) || defined(WOLFSSL_QT)
                    VERIFY_AND_SET_OID(cert->extCertPolicySet);
                    #if defined(OPENSSL_EXTRA) || \
                        defined(OPENSSL_EXTRA_X509_SMALL)
                        cert->extCertPolicyCrit = critical;
                    #endif
                #endif
                #if defined(WOLFSSL_SEP) || defined(WOLFSSL_CERT_EXT) || \
                    defined(WOLFSSL_QT)
                    if (DecodeCertPolicy(&input[idx], length, cert) < 0) {
                        return ASN_PARSE_E;
                    }
                #else
                    WOLFSSL_MSG("Certificate Policy extension not supported yet.");
                #endif
                break;

            case KEY_USAGE_OID:
                VERIFY_AND_SET_OID(cert->extKeyUsageSet);
                #if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
                    cert->extKeyUsageCrit = critical;
                #endif
                if (DecodeKeyUsage(&input[idx], length, cert) < 0)
                    return ASN_PARSE_E;
                break;

            case EXT_KEY_USAGE_OID:
                VERIFY_AND_SET_OID(cert->extExtKeyUsageSet);
                #if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
                    cert->extExtKeyUsageCrit = critical;
                #endif
                if (DecodeExtKeyUsage(&input[idx], length, cert) < 0)
                    return ASN_PARSE_E;
                break;

            #ifndef IGNORE_NAME_CONSTRAINTS
            case NAME_CONS_OID:
            #ifndef WOLFSSL_NO_ASN_STRICT
                /* Verify RFC 5280 Sec 4.2.1.10 rule:
                    "The name constraints extension,
                    which MUST be used only in a CA certificate" */
                if (!cert->isCA) {
                    WOLFSSL_MSG("Name constraints allowed only for CA certs");
                    return ASN_NAME_INVALID_E;
                }
            #endif
                VERIFY_AND_SET_OID(cert->extNameConstraintSet);
                #if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
                    cert->extNameConstraintCrit = critical;
                #endif
                if (DecodeNameConstraints(&input[idx], length, cert) < 0)
                    return ASN_PARSE_E;
                break;
            #endif /* IGNORE_NAME_CONSTRAINTS */

            case INHIBIT_ANY_OID:
                VERIFY_AND_SET_OID(cert->inhibitAnyOidSet);
                WOLFSSL_MSG("Inhibit anyPolicy extension not supported yet.");
                break;

       #ifndef IGNORE_NETSCAPE_CERT_TYPE
            case NETSCAPE_CT_OID:
                WOLFSSL_MSG("Netscape certificate type extension not supported "
                            "yet.");
                if (CheckBitString(input, &idx, &length, idx + length, 0,
                                                                    NULL) < 0) {
                    return ASN_PARSE_E;
                }
                break;
        #endif

            default:
            #ifndef WOLFSSL_NO_ASN_STRICT
                /* While it is a failure to not support critical extensions,
                 * still parse the certificate ignoring the unsupported
                 * extension to allow caller to accept it with the verify
                 * callback. */
                if (critical)
                    criticalFail = 1;
            #endif
            break;
        }
        idx += length;
    }

    return criticalFail ? ASN_CRIT_EXT_E : 0;
}

int ParseCert(DecodedCert* cert, int type, int verify, void* cm)
{
    int   ret;
    char* ptr;

    ret = ParseCertRelative(cert, type, verify, cm);
    if (ret < 0)
        return ret;

    if (cert->subjectCNLen > 0) {
        ptr = (char*) XMALLOC(cert->subjectCNLen + 1, cert->heap,
                              DYNAMIC_TYPE_SUBJECT_CN);
        if (ptr == NULL)
            return MEMORY_E;
        XMEMCPY(ptr, cert->subjectCN, cert->subjectCNLen);
        ptr[cert->subjectCNLen] = '\0';
        cert->subjectCN = ptr;
        cert->subjectCNStored = 1;
    }

    if (cert->keyOID == RSAk &&
                          cert->publicKey != NULL  && cert->pubKeySize > 0) {
        ptr = (char*) XMALLOC(cert->pubKeySize, cert->heap,
                              DYNAMIC_TYPE_PUBLIC_KEY);
        if (ptr == NULL)
            return MEMORY_E;
        XMEMCPY(ptr, cert->publicKey, cert->pubKeySize);
        cert->publicKey = (byte *)ptr;
        cert->pubKeyStored = 1;
    }

    return ret;
}

/* from SSL proper, for locking can't do find here anymore */
#ifdef __cplusplus
    extern "C" {
#endif
    Signer* GetCA(void* signers, byte* hash);
    #ifndef NO_SKID
        Signer* GetCAByName(void* signers, byte* hash);
    #endif
#ifdef __cplusplus
    }
#endif

#if defined(WOLFCRYPT_ONLY) || defined(NO_CERTS)

/* dummy functions, not using wolfSSL so don't need actual ones */
Signer* GetCA(void* signers, byte* hash)
{
    (void)hash;

    return (Signer*)signers;
}

#ifndef NO_SKID
Signer* GetCAByName(void* signers, byte* hash)
{
    (void)hash;

    return (Signer*)signers;
}
#endif /* NO_SKID */

#endif /* WOLFCRYPT_ONLY || NO_CERTS */

#if defined(WOLFSSL_NO_TRUSTED_CERTS_VERIFY) && !defined(NO_SKID)
static Signer* GetCABySubjectAndPubKey(DecodedCert* cert, void* cm)
{
    Signer* ca = NULL;
    if (cert->extSubjKeyIdSet)
        ca = GetCA(cm, cert->extSubjKeyId);
    if (ca == NULL)
        ca = GetCAByName(cm, cert->subjectHash);
    if (ca) {
        if ((ca->pubKeySize == cert->pubKeySize) &&
               (XMEMCMP(ca->publicKey, cert->publicKey, ca->pubKeySize) == 0)) {
            return ca;
        }
    }
    return NULL;
}
#endif

#if defined(WOLFSSL_SMALL_CERT_VERIFY) || defined(OPENSSL_EXTRA)
/* Only quick step through the certificate to find fields that are then used
 * in certificate signature verification.
 * Must use the signature OID from the signed part of the certificate.
 *
 * This is only for minimizing dynamic memory usage during TLS certificate
 * chain processing.
 * Doesn't support:
 *   OCSP Only: alt lookup using subject and pub key w/o sig check
 */
static int CheckCertSignature_ex(const byte* cert, word32 certSz, void* heap,
        void* cm, const byte* pubKey, word32 pubKeySz, int pubKeyOID)
{
#ifndef WOLFSSL_SMALL_STACK
    SignatureCtx  sigCtx[1];
#else
    SignatureCtx* sigCtx;
#endif
    byte          hash[KEYID_SIZE];
    Signer*       ca = NULL;
    word32        idx = 0;
    int           len;
    word32        tbsCertIdx = 0;
    word32        sigIndex   = 0;
    word32        signatureOID = 0;
    word32        oid = 0;
    word32        issuerIdx = 0;
    word32        issuerSz  = 0;
#ifndef NO_SKID
    int           extLen = 0;
    word32        extIdx = 0;
    word32        extEndIdx = 0;
    int           extAuthKeyIdSet = 0;
#endif
    int           ret = 0;
    word32        localIdx;
    byte          tag;


    if (cert == NULL) {
        return BAD_FUNC_ARG;
    }

#ifdef WOLFSSL_SMALL_STACK
    sigCtx = (SignatureCtx*)XMALLOC(sizeof(*sigCtx), heap, DYNAMIC_TYPE_SIGNATURE);
    if (sigCtx == NULL)
        return MEMORY_E;
#endif
    InitSignatureCtx(sigCtx, heap, INVALID_DEVID);

    /* Certificate SEQUENCE */
    if (GetSequence(cert, &idx, &len, certSz) < 0)
        ret = ASN_PARSE_E;
    if (ret == 0) {
        tbsCertIdx = idx;

        /* TBSCertificate SEQUENCE */
        if (GetSequence(cert, &idx, &len, certSz) < 0)
            ret = ASN_PARSE_E;
    }
    if (ret == 0) {
        sigIndex = len + idx;

        if ((idx + 1) > certSz)
            ret = BUFFER_E;
    }
    if (ret == 0) {
        /* version - optional */
        localIdx = idx;
        if (GetASNTag(cert, &localIdx, &tag, certSz) == 0) {
            if (tag == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED)) {
                idx++;
                if (GetLength(cert, &idx, &len, certSz) < 0)
                    ret = ASN_PARSE_E;
                idx += len;
            }
        }
    }

    if (ret == 0) {
        /* serialNumber */
        if (GetASNHeader(cert, ASN_INTEGER, &idx, &len, certSz) < 0)
            ret = ASN_PARSE_E;
    }
    if (ret == 0) {
        idx += len;

        /* signature */
        if (GetAlgoId(cert, &idx, &signatureOID, oidSigType, certSz) < 0)
            ret = ASN_PARSE_E;
    }

    if (ret == 0) {
        issuerIdx = idx;
        /* issuer */
        if (GetSequence(cert, &idx, &len, certSz) < 0)
            ret = ASN_PARSE_E;
    }
    if (ret == 0) {
        issuerSz = len + idx - issuerIdx;
    }
#ifndef NO_SKID
    if (ret == 0) {
        idx += len;

        /* validity */
        if (GetSequence(cert, &idx, &len, certSz) < 0)
            ret = ASN_PARSE_E;
    }
    if (ret == 0) {
        idx += len;

        /* subject */
        if (GetSequence(cert, &idx, &len, certSz) < 0)
            ret = ASN_PARSE_E;
    }
    if (ret == 0) {
        idx += len;

        /* subjectPublicKeyInfo */
        if (GetSequence(cert, &idx, &len, certSz) < 0)
            ret = ASN_PARSE_E;
    }
    if (ret == 0) {
        idx += len;

        if ((idx + 1) > certSz)
            ret = BUFFER_E;
    }
    if (ret == 0) {
        /* issuerUniqueID - optional */
        localIdx = idx;
        if (GetASNTag(cert, &localIdx, &tag, certSz) == 0) {
            if (tag == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | 1)) {
                idx++;
                if (GetLength(cert, &idx, &len, certSz) < 0)
                    ret = ASN_PARSE_E;
                idx += len;
            }
        }
    }
    if (ret == 0) {
        if ((idx + 1) > certSz)
            ret = BUFFER_E;
    }
    if (ret == 0) {
        /* subjectUniqueID - optional */
        localIdx = idx;
        if (GetASNTag(cert, &localIdx, &tag, certSz) == 0) {
            if (tag == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | 2)) {
                idx++;
                if (GetLength(cert, &idx, &len, certSz) < 0)
                    ret = ASN_PARSE_E;
                idx += len;
            }
        }
    }

    if (ret == 0) {
        if ((idx + 1) > certSz)
            ret = BUFFER_E;
    }
    /* extensions - optional */
    localIdx = idx;
    if (ret == 0 && GetASNTag(cert, &localIdx, &tag, certSz) == 0 &&
            tag == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | 3)) {
        idx++;
        if (GetLength(cert, &idx, &extLen, certSz) < 0)
            ret = ASN_PARSE_E;
        if (ret == 0) {
            if (GetSequence(cert, &idx, &extLen, certSz) < 0)
                ret = ASN_PARSE_E;
        }
        if (ret == 0) {
            extEndIdx = idx + extLen;

            /* Check each extension for the ones we want. */
            while (ret == 0 && idx < extEndIdx) {
                if (GetSequence(cert, &idx, &len, certSz) < 0)
                    ret = ASN_PARSE_E;
                if (ret == 0) {
                    extIdx = idx;
                    if (GetObjectId(cert, &extIdx, &oid, oidCertExtType,
                                                                  certSz) < 0) {
                        ret = ASN_PARSE_E;
                    }

                    if (ret == 0) {
                        if ((extIdx + 1) > certSz)
                            ret = BUFFER_E;
                    }
                }

                if (ret == 0) {
                    localIdx = extIdx;
                    if (GetASNTag(cert, &localIdx, &tag, certSz) == 0 &&
                            tag == ASN_BOOLEAN) {
                        if (GetBoolean(cert, &extIdx, certSz) < 0)
                            ret = ASN_PARSE_E;
                    }
                }
                if (ret == 0) {
                    if (GetOctetString(cert, &extIdx, &extLen, certSz) < 0)
                        ret = ASN_PARSE_E;
                }

                if (ret == 0) {
                    switch (oid) {
                    case AUTH_KEY_OID:
                        if (GetSequence(cert, &extIdx, &extLen, certSz) < 0)
                            ret = ASN_PARSE_E;

                        if (ret == 0 && (extIdx + 1) >= certSz)
                            ret = BUFFER_E;

                        if (ret == 0 &&
                                GetASNTag(cert, &extIdx, &tag, certSz) == 0 &&
                                tag == (ASN_CONTEXT_SPECIFIC | 0)) {
                            if (GetLength(cert, &extIdx, &extLen, certSz) <= 0)
                                ret = ASN_PARSE_E;
                            if (ret == 0) {
                                extAuthKeyIdSet = 1;
                                if (extLen == KEYID_SIZE)
                                    XMEMCPY(hash, cert + extIdx, extLen);
                                else {
                                    ret = CalcHashId(cert + extIdx, extLen,
                                                                          hash);
                                }
                            }
                        }
                        break;

                    default:
                        break;
                    }
                }
                idx += len;
            }
        }
    }

    if (ret == 0 && pubKey == NULL) {
        if (extAuthKeyIdSet)
            ca = GetCA(cm, hash);
        if (ca == NULL) {
            ret = CalcHashId(cert + issuerIdx, issuerSz, hash);
            if (ret == 0)
                ca = GetCAByName(cm, hash);
        }
    }
#else
    if (ret == 0 && pubKey == NULL) {
        ret = CalcHashId(cert + issuerIdx, issuerSz, hash);
        if (ret == 0)
            ca = GetCA(cm, hash);
    }
#endif /* !NO_SKID */
    if (ca == NULL && pubKey == NULL)
        ret = ASN_NO_SIGNER_E;

    if (ret == 0) {
        idx = sigIndex;
        /* signatureAlgorithm */
        if (GetAlgoId(cert, &idx, &oid, oidSigType, certSz) < 0)
            ret = ASN_PARSE_E;
    }
    if (ret == 0) {
        if (oid != signatureOID)
            ret = ASN_SIG_OID_E;
    }
    if (ret == 0) {
        /* signatureValue */
        if (CheckBitString(cert, &idx, &len, certSz, 1, NULL) < 0)
            ret = ASN_PARSE_E;
    }

    if (ret == 0) {
        if (pubKey != NULL) {
            ret = ConfirmSignature(sigCtx, cert + tbsCertIdx,
                               sigIndex - tbsCertIdx,
                               pubKey, pubKeySz, pubKeyOID,
                               cert + idx, len, signatureOID, NULL);
        }
        else {
            ret = ConfirmSignature(sigCtx, cert + tbsCertIdx,
                               sigIndex - tbsCertIdx,
                               ca->publicKey, ca->pubKeySize, ca->keyOID,
                               cert + idx, len, signatureOID, NULL);
        }
        if (ret != 0) {
            WOLFSSL_MSG("Confirm signature failed");
        }
    }

    FreeSignatureCtx(sigCtx);
#ifdef WOLFSSL_SMALL_STACK
    if (sigCtx != NULL)
        XFREE(sigCtx, heap, DYNAMIC_TYPE_SIGNATURE);
#endif
    return ret;
}

#ifdef OPENSSL_EXTRA
/* Call CheckCertSignature_ex using a public key buffer for verification
 */
int CheckCertSignaturePubKey(const byte* cert, word32 certSz, void* heap,
        const byte* pubKey, word32 pubKeySz, int pubKeyOID)
{
    return CheckCertSignature_ex(cert, certSz, heap, NULL,
            pubKey, pubKeySz, pubKeyOID);
}
#endif /* OPENSSL_EXTRA */
#ifdef WOLFSSL_SMALL_CERT_VERIFY
/* Call CheckCertSignature_ex using a certificate manager (cm)
 */
int CheckCertSignature(const byte* cert, word32 certSz, void* heap, void* cm)
{
    return CheckCertSignature_ex(cert, certSz, heap, cm, NULL, 0, 0);
}
#endif /* WOLFSSL_SMALL_CERT_VERIFY */
#endif /* WOLFSSL_SMALL_CERT_VERIFY || OPENSSL_EXTRA */

int ParseCertRelative(DecodedCert* cert, int type, int verify, void* cm)
{
    int    ret = 0;
    int    checkPathLen = 0;
    int    decrementMaxPathLen = 0;
    word32 confirmOID;
#if defined(WOLFSSL_RENESAS_TSIP)
    int    idx = 0;
#endif
    byte*  tsip_encRsaKeyIdx;

    if (cert == NULL) {
        return BAD_FUNC_ARG;
    }

    if (cert->sigCtx.state == SIG_STATE_BEGIN) {
        cert->badDate = 0;
        cert->criticalExt = 0;
        if ((ret = DecodeToKey(cert, verify)) < 0) {
            if (ret == ASN_BEFORE_DATE_E || ret == ASN_AFTER_DATE_E)
                cert->badDate = ret;
            else
                return ret;
        }

        WOLFSSL_MSG("Parsed Past Key");

        if (cert->srcIdx < cert->sigIndex) {
        #ifndef ALLOW_V1_EXTENSIONS
            if (cert->version < 2) {
                WOLFSSL_MSG("\tv1 and v2 certs not allowed extensions");
                return ASN_VERSION_E;
            }
        #endif

            /* save extensions */
            cert->extensions    = &cert->source[cert->srcIdx];
            cert->extensionsSz  = cert->sigIndex - cert->srcIdx;
            cert->extensionsIdx = cert->srcIdx;   /* for potential later use */

            if ((ret = DecodeCertExtensions(cert)) < 0) {
                if (ret == ASN_CRIT_EXT_E)
                    cert->criticalExt = ret;
                else
                    return ret;
            }

            /* advance past extensions */
            cert->srcIdx = cert->sigIndex;
        }

        if ((ret = GetAlgoId(cert->source, &cert->srcIdx, &confirmOID,
                             oidSigType, cert->maxIdx)) < 0)
            return ret;

        if ((ret = GetSignature(cert)) < 0)
            return ret;

        if (confirmOID != cert->signatureOID)
            return ASN_SIG_OID_E;

    #ifndef NO_SKID
        if (cert->extSubjKeyIdSet == 0 && cert->publicKey != NULL &&
                                                         cert->pubKeySize > 0) {
            ret = CalcHashId(cert->publicKey, cert->pubKeySize,
                                                            cert->extSubjKeyId);
            if (ret != 0)
                return ret;
        }
    #endif /* !NO_SKID */

        if (!cert->selfSigned || (verify != NO_VERIFY && type != CA_TYPE &&
                                                   type != TRUSTED_PEER_TYPE)) {
            cert->ca = NULL;
    #ifndef NO_SKID
            if (cert->extAuthKeyIdSet) {
                cert->ca = GetCA(cm, cert->extAuthKeyId);
            }
            if (cert->ca == NULL && cert->extSubjKeyIdSet
                                 && verify != VERIFY_OCSP) {
                cert->ca = GetCA(cm, cert->extSubjKeyId);
            }
            if (cert->ca != NULL && XMEMCMP(cert->issuerHash,
                                  cert->ca->subjectNameHash, KEYID_SIZE) != 0) {
                cert->ca = NULL;
            }
            if (cert->ca == NULL) {
                cert->ca = GetCAByName(cm, cert->issuerHash);
                /* If AKID is available then this CA doesn't have the public
                 * key required */
                if (cert->ca && cert->extAuthKeyIdSet) {
                    WOLFSSL_MSG("CA SKID doesn't match AKID");
                    cert->ca = NULL;
                }
            }

            /* OCSP Only: alt lookup using subject and pub key w/o sig check */
        #ifdef WOLFSSL_NO_TRUSTED_CERTS_VERIFY
            if (cert->ca == NULL && verify == VERIFY_OCSP) {
                cert->ca = GetCABySubjectAndPubKey(cert, cm);
                if (cert->ca) {
                    ret = 0; /* success */
                    goto exit_pcr;
                }
            }
        #endif /* WOLFSSL_NO_TRUSTED_CERTS_VERIFY */
    #else
            cert->ca = GetCA(cm, cert->issuerHash);
    #endif /* !NO_SKID */

            if (cert->ca) {
                WOLFSSL_MSG("CA found");
            }
        }

        if (cert->selfSigned) {
            cert->maxPathLen = WOLFSSL_MAX_PATH_LEN;
        } else {
            /* RFC 5280 Section 4.2.1.9:
             *
             * load/receive check
             *
             * 1) Is CA boolean set?
             *      No  - SKIP CHECK
             *      Yes - Check key usage
             * 2) Is Key usage extension present?
             *      No  - goto 3
             *      Yes - check keyCertSign assertion
             *     2.a) Is keyCertSign asserted?
             *          No  - goto 4
             *          Yes - goto 3
             * 3) Is pathLen set?
             *      No  - goto 4
             *      Yes - check pathLen against maxPathLen.
             *      3.a) Is pathLen less than maxPathLen?
             *           No - goto 4
             *           Yes - set maxPathLen to pathLen and EXIT
             * 4) Is maxPathLen > 0?
             *      Yes - Reduce by 1
             *      No  - ERROR
             */

            if (cert->ca && cert->pathLengthSet) {
                cert->maxPathLen = cert->pathLength;
                if (cert->isCA) {
                    WOLFSSL_MSG("\tCA boolean set");
                    if (cert->extKeyUsageSet) {
                         WOLFSSL_MSG("\tExtension Key Usage Set");
                         if ((cert->extKeyUsage & KEYUSE_KEY_CERT_SIGN) != 0) {
                            checkPathLen = 1;
                         } else {
                            decrementMaxPathLen = 1;
                         }
                    } else {
                        checkPathLen = 1;
                    } /* !cert->ca check */
                } /* cert is not a CA (assuming entity cert) */

                if (checkPathLen && cert->pathLengthSet) {
                    if (cert->pathLength < cert->ca->maxPathLen) {
                        WOLFSSL_MSG("\tmaxPathLen status: set to pathLength");
                        cert->maxPathLen = cert->pathLength;
                    } else {
                        decrementMaxPathLen = 1;
                    }
                }

                if (decrementMaxPathLen && cert->ca->maxPathLen > 0) {
                    WOLFSSL_MSG("\tmaxPathLen status: reduce by 1");
                    cert->maxPathLen = cert->ca->maxPathLen - 1;
                    if (verify != NO_VERIFY && type != CA_TYPE &&
                                                    type != TRUSTED_PEER_TYPE) {
                        WOLFSSL_MSG("\tmaxPathLen status: OK");
                    }
                } else if (decrementMaxPathLen && cert->ca->maxPathLen == 0) {
                    cert->maxPathLen = 0;
                    if (verify != NO_VERIFY && type != CA_TYPE &&
                                                    type != TRUSTED_PEER_TYPE) {
                        WOLFSSL_MSG("\tNon-entity cert, maxPathLen is 0");
                        WOLFSSL_MSG("\tmaxPathLen status: ERROR");
                        return ASN_PATHLEN_INV_E;
                    }
                }
            } else if (cert->ca && cert->isCA) {
                /* case where cert->pathLength extension is not set */
                if (cert->ca->maxPathLen > 0) {
                    cert->maxPathLen = cert->ca->maxPathLen - 1;
                } else {
                    cert->maxPathLen = 0;
                    if (verify != NO_VERIFY && type != CA_TYPE &&
                                                    type != TRUSTED_PEER_TYPE) {
                        WOLFSSL_MSG("\tNon-entity cert, maxPathLen is 0");
                        WOLFSSL_MSG("\tmaxPathLen status: ERROR");
                        return ASN_PATHLEN_INV_E;
                    }
                }
            }
            #ifdef HAVE_OCSP
            if (verify != NO_VERIFY && type != CA_TYPE &&
                                                    type != TRUSTED_PEER_TYPE) {
                if (cert->ca) {
                    /* Need the CA's public key hash for OCSP */
                    XMEMCPY(cert->issuerKeyHash, cert->ca->subjectKeyHash,
                                                                    KEYID_SIZE);
                }

            }
            #endif /* HAVE_OCSP */
        }
    }
#if defined(WOLFSSL_RENESAS_TSIP)
    /* prepare for TSIP TLS cert verification API use */
    if (cert->keyOID == RSAk) {
        /* to call TSIP API, it needs keys position info in bytes */
        if ((ret = RsaPublicKeyDecodeRawIndex(cert->publicKey, (word32*)&idx,
                                   cert->pubKeySize,
                                   &cert->sigCtx.pubkey_n_start,
                                   &cert->sigCtx.pubkey_n_len,
                                   &cert->sigCtx.pubkey_e_start,
                                   &cert->sigCtx.pubkey_e_len)) != 0) {
            WOLFSSL_MSG("Decoding index from cert failed.");
            return ret;
        }
        cert->sigCtx.certBegin = cert->certBegin;
    }
    /* check if we can use TSIP for cert verification */
    /* if the ca is verified as tsip root ca.         */
    /* TSIP can only handle 2048 bits(256 byte) key.  */
    if (cert->ca && tsip_checkCA(cert->ca->cm_idx) != 0 &&
        cert->sigCtx.pubkey_n_len == 256) {

        /* assign memory to encrypted tsip Rsa key index */
        if (!cert->tsip_encRsaKeyIdx)
            cert->tsip_encRsaKeyIdx =
                            (byte*)XMALLOC(TSIP_TLS_ENCPUBKEY_SZ_BY_CERTVRFY,
                             cert->heap, DYNAMIC_TYPE_RSA);
        if (cert->tsip_encRsaKeyIdx == NULL)
                return MEMORY_E;
    } else {
        if (cert->ca) {
            /* TSIP isn't usable */
            if (tsip_checkCA(cert->ca->cm_idx) == 0)
                WOLFSSL_MSG("TSIP isn't usable because the ca isn't verified "
                            "by TSIP.");
            else if (cert->sigCtx.pubkey_n_len != 256)
                WOLFSSL_MSG("TSIP isn't usable because the ca isn't signed by "
                            "RSA 2048.");
            else
                WOLFSSL_MSG("TSIP isn't usable");
        }
        cert->tsip_encRsaKeyIdx = NULL;
    }

    tsip_encRsaKeyIdx = cert->tsip_encRsaKeyIdx;
#else
    tsip_encRsaKeyIdx = NULL;
#endif

    if (verify != NO_VERIFY && type != CA_TYPE && type != TRUSTED_PEER_TYPE) {
        if (cert->ca) {
            if (verify == VERIFY || verify == VERIFY_OCSP ||
                                                 verify == VERIFY_SKIP_DATE) {
                /* try to confirm/verify signature */
                if ((ret = ConfirmSignature(&cert->sigCtx,
                        cert->source + cert->certBegin,
                        cert->sigIndex - cert->certBegin,
                        cert->ca->publicKey, cert->ca->pubKeySize,
                        cert->ca->keyOID, cert->signature,
                        cert->sigLength, cert->signatureOID,
                        tsip_encRsaKeyIdx)) != 0) {
                    if (ret != 0 && ret != WC_PENDING_E) {
                        WOLFSSL_MSG("Confirm signature failed");
                    }
                    return ret;
                }
            }
        #ifndef IGNORE_NAME_CONSTRAINTS
            if (verify == VERIFY || verify == VERIFY_OCSP ||
                        verify == VERIFY_NAME || verify == VERIFY_SKIP_DATE) {
                /* check that this cert's name is permitted by the signer's
                 * name constraints */
                if (!ConfirmNameConstraints(cert->ca, cert)) {
                    WOLFSSL_MSG("Confirm name constraint failed");
                    return ASN_NAME_INVALID_E;
                }
            }
        #endif /* IGNORE_NAME_CONSTRAINTS */
        }
        else {
            /* no signer */
            WOLFSSL_MSG("No CA signer to verify with");
            return ASN_NO_SIGNER_E;
        }
    }

#if defined(WOLFSSL_NO_TRUSTED_CERTS_VERIFY) && !defined(NO_SKID)
exit_pcr:
#endif

    if (cert->badDate != 0) {
        if (verify != VERIFY_SKIP_DATE) {
            return cert->badDate;
        }
        WOLFSSL_MSG("Date error: Verify option is skipping");
    }

    if (cert->criticalExt != 0)
        return cert->criticalExt;

    return ret;
}

/* Create and init an new signer */
Signer* MakeSigner(void* heap)
{
    Signer* signer = (Signer*) XMALLOC(sizeof(Signer), heap,
                                       DYNAMIC_TYPE_SIGNER);
    if (signer) {
        XMEMSET(signer, 0, sizeof(Signer));
    }
    (void)heap;

    return signer;
}


/* Free an individual signer */
void FreeSigner(Signer* signer, void* heap)
{
    XFREE(signer->name, heap, DYNAMIC_TYPE_SUBJECT_CN);
    XFREE((void*)signer->publicKey, heap, DYNAMIC_TYPE_PUBLIC_KEY);
#ifndef IGNORE_NAME_CONSTRAINTS
    if (signer->permittedNames)
        FreeNameSubtrees(signer->permittedNames, heap);
    if (signer->excludedNames)
        FreeNameSubtrees(signer->excludedNames, heap);
#endif
#ifdef WOLFSSL_SIGNER_DER_CERT
    FreeDer(&signer->derCert);
#endif
    XFREE(signer, heap, DYNAMIC_TYPE_SIGNER);

    (void)heap;
}


/* Free the whole singer table with number of rows */
void FreeSignerTable(Signer** table, int rows, void* heap)
{
    int i;

    for (i = 0; i < rows; i++) {
        Signer* signer = table[i];
        while (signer) {
            Signer* next = signer->next;
            FreeSigner(signer, heap);
            signer = next;
        }
        table[i] = NULL;
    }
}

#ifdef WOLFSSL_TRUST_PEER_CERT
/* Free an individual trusted peer cert */
void FreeTrustedPeer(TrustedPeerCert* tp, void* heap)
{
    if (tp == NULL) {
        return;
    }

    if (tp->name) {
        XFREE(tp->name, heap, DYNAMIC_TYPE_SUBJECT_CN);
    }

    if (tp->sig) {
        XFREE(tp->sig, heap, DYNAMIC_TYPE_SIGNATURE);
    }
#ifndef IGNORE_NAME_CONSTRAINTS
    if (tp->permittedNames)
        FreeNameSubtrees(tp->permittedNames, heap);
    if (tp->excludedNames)
        FreeNameSubtrees(tp->excludedNames, heap);
#endif
    XFREE(tp, heap, DYNAMIC_TYPE_CERT);

    (void)heap;
}

/* Free the whole Trusted Peer linked list */
void FreeTrustedPeerTable(TrustedPeerCert** table, int rows, void* heap)
{
    int i;

    for (i = 0; i < rows; i++) {
        TrustedPeerCert* tp = table[i];
        while (tp) {
            TrustedPeerCert* next = tp->next;
            FreeTrustedPeer(tp, heap);
            tp = next;
        }
        table[i] = NULL;
    }
}
#endif /* WOLFSSL_TRUST_PEER_CERT */

int SetMyVersion(word32 version, byte* output, int header)
{
    int i = 0;

    if (output == NULL)
        return BAD_FUNC_ARG;

    if (header) {
        output[i++] = ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED;
        output[i++] = 3;
    }
    output[i++] = ASN_INTEGER;
    output[i++] = 0x01;
    output[i++] = (byte)version;

    return i;
}

int SetSerialNumber(const byte* sn, word32 snSz, byte* output,
    word32 outputSz, int maxSnSz)
{
    int i;
    int snSzInt = (int)snSz;

    if (sn == NULL || output == NULL || snSzInt < 0)
        return BAD_FUNC_ARG;

    /* remove leading zeros */
    while (snSzInt > 0 && sn[0] == 0) {
        snSzInt--;
        sn++;
    }
    /* RFC 5280 - 4.1.2.2:
     *   Serial numbers must be a positive value (and not zero) */
    if (snSzInt == 0)
        return BAD_FUNC_ARG;

    if (sn[0] & 0x80)
        maxSnSz--;
    /* truncate if input is too long */
    if (snSzInt > maxSnSz)
        snSzInt = maxSnSz;

    i = SetASNInt(snSzInt, sn[0], NULL);
    /* truncate if input is too long */
    if (snSzInt > (int)outputSz - i)
        snSzInt = (int)outputSz - i;
    /* sanity check number of bytes to copy */
    if (snSzInt <= 0) {
        return BUFFER_E;
    }

    /* write out ASN.1 Integer */
    (void)SetASNInt(snSzInt, sn[0], output);
    XMEMCPY(output + i, sn, snSzInt);

    /* compute final length */
    i += snSzInt;

    return i;
}

#endif /* !NO_CERTS */

int GetSerialNumber(const byte* input, word32* inOutIdx,
    byte* serial, int* serialSz, word32 maxIdx)
{
    int result = 0;
    int ret;

    WOLFSSL_ENTER("GetSerialNumber");

    if (serial == NULL || input == NULL || serialSz == NULL) {
        return BAD_FUNC_ARG;
    }

    /* First byte is ASN type */
    if ((*inOutIdx+1) > maxIdx) {
        WOLFSSL_MSG("Bad idx first");
        return BUFFER_E;
    }

    ret = GetASNInt(input, inOutIdx, serialSz, maxIdx);
    if (ret != 0)
        return ret;

    if (*serialSz > EXTERNAL_SERIAL_SIZE) {
        WOLFSSL_MSG("Serial size bad");
        return ASN_PARSE_E;
    }

    /* return serial */
    XMEMCPY(serial, &input[*inOutIdx], *serialSz);
    *inOutIdx += *serialSz;

    return result;
}

#ifndef NO_CERTS

int AllocDer(DerBuffer** pDer, word32 length, int type, void* heap)
{
    int ret = BAD_FUNC_ARG;
    if (pDer) {
        int dynType = 0;
        DerBuffer* der;

        /* Determine dynamic type */
        switch (type) {
            case CA_TYPE:   dynType = DYNAMIC_TYPE_CA;   break;
            case CERT_TYPE: dynType = DYNAMIC_TYPE_CERT; break;
            case CRL_TYPE:  dynType = DYNAMIC_TYPE_CRL;  break;
            case DSA_TYPE:  dynType = DYNAMIC_TYPE_DSA;  break;
            case ECC_TYPE:  dynType = DYNAMIC_TYPE_ECC;  break;
            case RSA_TYPE:  dynType = DYNAMIC_TYPE_RSA;  break;
            default:        dynType = DYNAMIC_TYPE_KEY;  break;
        }

        /* Setup new buffer */
        *pDer = (DerBuffer*)XMALLOC(sizeof(DerBuffer) + length, heap, dynType);
        if (*pDer == NULL) {
            return MEMORY_E;
        }
        XMEMSET(*pDer, 0, sizeof(DerBuffer) + length);

        der = *pDer;
        der->type = type;
        der->dynType = dynType; /* Cache this for FreeDer */
        der->heap = heap;
        der->buffer = (byte*)der + sizeof(DerBuffer);
        der->length = length;
        ret = 0; /* Success */
    }
    return ret;
}

void FreeDer(DerBuffer** pDer)
{
    if (pDer && *pDer)
    {
        DerBuffer* der = (DerBuffer*)*pDer;

        /* ForceZero private keys */
        if (der->type == PRIVATEKEY_TYPE) {
            ForceZero(der->buffer, der->length);
        }
        der->buffer = NULL;
        der->length = 0;
        XFREE(der, der->heap, der->dynType);

        *pDer = NULL;
    }
}

int wc_AllocDer(DerBuffer** pDer, word32 length, int type, void* heap)
{
    return AllocDer(pDer, length, type, heap);
}
void wc_FreeDer(DerBuffer** pDer)
{
    FreeDer(pDer);
}


#if defined(WOLFSSL_PEM_TO_DER) || defined(WOLFSSL_DER_TO_PEM)

/* Note: If items added make sure MAX_X509_HEADER_SZ is 
    updated to reflect maximum length */
wcchar BEGIN_CERT           = "-----BEGIN CERTIFICATE-----";
wcchar END_CERT             = "-----END CERTIFICATE-----";
#ifdef WOLFSSL_CERT_REQ
    wcchar BEGIN_CERT_REQ   = "-----BEGIN CERTIFICATE REQUEST-----";
    wcchar END_CERT_REQ     = "-----END CERTIFICATE REQUEST-----";
#endif
#ifndef NO_DH
    wcchar BEGIN_DH_PARAM   = "-----BEGIN DH PARAMETERS-----";
    wcchar END_DH_PARAM     = "-----END DH PARAMETERS-----";
#endif
#ifndef NO_DSA
    wcchar BEGIN_DSA_PARAM  = "-----BEGIN DSA PARAMETERS-----";
    wcchar END_DSA_PARAM    = "-----END DSA PARAMETERS-----";
#endif
wcchar BEGIN_X509_CRL       = "-----BEGIN X509 CRL-----";
wcchar END_X509_CRL         = "-----END X509 CRL-----";
wcchar BEGIN_RSA_PRIV       = "-----BEGIN RSA PRIVATE KEY-----";
wcchar END_RSA_PRIV         = "-----END RSA PRIVATE KEY-----";
wcchar BEGIN_PRIV_KEY       = "-----BEGIN PRIVATE KEY-----";
wcchar END_PRIV_KEY         = "-----END PRIVATE KEY-----";
wcchar BEGIN_ENC_PRIV_KEY   = "-----BEGIN ENCRYPTED PRIVATE KEY-----";
wcchar END_ENC_PRIV_KEY     = "-----END ENCRYPTED PRIVATE KEY-----";
#ifdef HAVE_ECC
    wcchar BEGIN_EC_PRIV    = "-----BEGIN EC PRIVATE KEY-----";
    wcchar END_EC_PRIV      = "-----END EC PRIVATE KEY-----";
#endif
#if defined(HAVE_ECC) || defined(HAVE_ED25519) || defined(HAVE_ED448) || \
                                                                !defined(NO_DSA)
    wcchar BEGIN_DSA_PRIV   = "-----BEGIN DSA PRIVATE KEY-----";
    wcchar END_DSA_PRIV     = "-----END DSA PRIVATE KEY-----";
#endif
#ifdef OPENSSL_EXTRA
    const char BEGIN_PRIV_KEY_PREFIX[] = "-----BEGIN";
    const char PRIV_KEY_SUFFIX[] = "PRIVATE KEY-----";
    const char END_PRIV_KEY_PREFIX[]   = "-----END";
#endif
wcchar BEGIN_PUB_KEY        = "-----BEGIN PUBLIC KEY-----";
wcchar END_PUB_KEY          = "-----END PUBLIC KEY-----";
#if defined(HAVE_ED25519) || defined(HAVE_ED448)
    wcchar BEGIN_EDDSA_PRIV = "-----BEGIN EDDSA PRIVATE KEY-----";
    wcchar END_EDDSA_PRIV   = "-----END EDDSA PRIVATE KEY-----";
#endif
#ifdef HAVE_CRL
    const char *const BEGIN_CRL = "-----BEGIN X509 CRL-----";
    wcchar END_CRL   = "-----END X509 CRL-----";
#endif


static WC_INLINE char* SkipEndOfLineChars(char* line, const char* endOfLine)
{
    /* eat end of line characters */
    while (line < endOfLine &&
              (line[0] == '\r' || line[0] == '\n')) {
        line++;
    }
    return line;
}

int wc_PemGetHeaderFooter(int type, const char** header, const char** footer)
{
    int ret = BAD_FUNC_ARG;

    switch (type) {
        case CA_TYPE:       /* same as below */
        case TRUSTED_PEER_TYPE:
        case CERT_TYPE:
            if (header) *header = BEGIN_CERT;
            if (footer) *footer = END_CERT;
            ret = 0;
            break;

        case CRL_TYPE:
            if (header) *header = BEGIN_X509_CRL;
            if (footer) *footer = END_X509_CRL;
            ret = 0;
            break;
    #ifndef NO_DH
        case DH_PARAM_TYPE:
            if (header) *header = BEGIN_DH_PARAM;
            if (footer) *footer = END_DH_PARAM;
            ret = 0;
            break;
    #endif
    #ifndef NO_DSA
        case DSA_PARAM_TYPE:
            if (header) *header = BEGIN_DSA_PARAM;
            if (footer) *footer = END_DSA_PARAM;
            ret = 0;
            break;
    #endif
    #ifdef WOLFSSL_CERT_REQ
        case CERTREQ_TYPE:
            if (header) *header = BEGIN_CERT_REQ;
            if (footer) *footer = END_CERT_REQ;
            ret = 0;
            break;
    #endif
    #ifndef NO_DSA
        case DSA_TYPE:
        case DSA_PRIVATEKEY_TYPE:
            if (header) *header = BEGIN_DSA_PRIV;
            if (footer) *footer = END_DSA_PRIV;
            ret = 0;
            break;
    #endif
    #ifdef HAVE_ECC
        case ECC_TYPE:
        case ECC_PRIVATEKEY_TYPE:
            if (header) *header = BEGIN_EC_PRIV;
            if (footer) *footer = END_EC_PRIV;
            ret = 0;
            break;
    #endif
        case RSA_TYPE:
        case PRIVATEKEY_TYPE:
            if (header) *header = BEGIN_RSA_PRIV;
            if (footer) *footer = END_RSA_PRIV;
            ret = 0;
            break;
    #ifdef HAVE_ED25519
        case ED25519_TYPE:
    #endif
    #ifdef HAVE_ED448
        case ED448_TYPE:
    #endif
    #if defined(HAVE_ED25519) || defined(HAVE_ED448)
        case EDDSA_PRIVATEKEY_TYPE:
            if (header) *header = BEGIN_EDDSA_PRIV;
            if (footer) *footer = END_EDDSA_PRIV;
            ret = 0;
            break;
    #endif
        case PUBLICKEY_TYPE:
        case ECC_PUBLICKEY_TYPE:
            if (header) *header = BEGIN_PUB_KEY;
            if (footer) *footer = END_PUB_KEY;
            ret = 0;
            break;
    #ifndef NO_DH
        case DH_PRIVATEKEY_TYPE:
    #endif
        case PKCS8_PRIVATEKEY_TYPE:
            if (header) *header = BEGIN_PRIV_KEY;
            if (footer) *footer = END_PRIV_KEY;
            ret = 0;
            break;
        case PKCS8_ENC_PRIVATEKEY_TYPE:
            if (header) *header = BEGIN_ENC_PRIV_KEY;
            if (footer) *footer = END_ENC_PRIV_KEY;
            ret = 0;
            break;
        default:
            break;
    }
    return ret;
}

#ifdef WOLFSSL_ENCRYPTED_KEYS

static wcchar kProcTypeHeader = "Proc-Type";
static wcchar kDecInfoHeader = "DEK-Info";

#ifdef WOLFSSL_PEM_TO_DER
#ifndef NO_DES3
    static wcchar kEncTypeDes = "DES-CBC";
    static wcchar kEncTypeDes3 = "DES-EDE3-CBC";
#endif
#if !defined(NO_AES) && defined(HAVE_AES_CBC) && defined(WOLFSSL_AES_128)
    static wcchar kEncTypeAesCbc128 = "AES-128-CBC";
#endif
#if !defined(NO_AES) && defined(HAVE_AES_CBC) && defined(WOLFSSL_AES_192)
    static wcchar kEncTypeAesCbc192 = "AES-192-CBC";
#endif
#if !defined(NO_AES) && defined(HAVE_AES_CBC) && defined(WOLFSSL_AES_256)
    static wcchar kEncTypeAesCbc256 = "AES-256-CBC";
#endif

int wc_EncryptedInfoGet(EncryptedInfo* info, const char* cipherInfo)
{
    int ret = 0;

    if (info == NULL || cipherInfo == NULL)
        return BAD_FUNC_ARG;

    /* determine cipher information */
#ifndef NO_DES3
    if (XSTRNCMP(cipherInfo, kEncTypeDes, XSTRLEN(kEncTypeDes)) == 0) {
        info->cipherType = WC_CIPHER_DES;
        info->keySz = DES_KEY_SIZE;
        if (info->ivSz == 0) info->ivSz  = DES_IV_SIZE;
    }
    else if (XSTRNCMP(cipherInfo, kEncTypeDes3, XSTRLEN(kEncTypeDes3)) == 0) {
        info->cipherType = WC_CIPHER_DES3;
        info->keySz = DES3_KEY_SIZE;
        if (info->ivSz == 0) info->ivSz  = DES_IV_SIZE;
    }
    else
#endif /* !NO_DES3 */
#if !defined(NO_AES) && defined(HAVE_AES_CBC) && defined(WOLFSSL_AES_128)
    if (XSTRNCMP(cipherInfo, kEncTypeAesCbc128, XSTRLEN(kEncTypeAesCbc128)) == 0) {
        info->cipherType = WC_CIPHER_AES_CBC;
        info->keySz = AES_128_KEY_SIZE;
        if (info->ivSz == 0) info->ivSz  = AES_IV_SIZE;
    }
    else
#endif
#if !defined(NO_AES) && defined(HAVE_AES_CBC) && defined(WOLFSSL_AES_192)
    if (XSTRNCMP(cipherInfo, kEncTypeAesCbc192, XSTRLEN(kEncTypeAesCbc192)) == 0) {
        info->cipherType = WC_CIPHER_AES_CBC;
        info->keySz = AES_192_KEY_SIZE;
        if (info->ivSz == 0) info->ivSz  = AES_IV_SIZE;
    }
    else
#endif
#if !defined(NO_AES) && defined(HAVE_AES_CBC) && defined(WOLFSSL_AES_256)
    if (XSTRNCMP(cipherInfo, kEncTypeAesCbc256, XSTRLEN(kEncTypeAesCbc256)) == 0) {
        info->cipherType = WC_CIPHER_AES_CBC;
        info->keySz = AES_256_KEY_SIZE;
        if (info->ivSz == 0) info->ivSz  = AES_IV_SIZE;
    }
    else
#endif
    {
        ret = NOT_COMPILED_IN;
    }
    return ret;
}

int wc_EncryptedInfoParse(EncryptedInfo* info, char** pBuffer, size_t bufSz)
{
    int err = 0;
    char*  bufferStart;
    char*  bufferEnd;
    char*  line;
    word32 lineSz;
    char*  finish;
    word32 finishSz;
    char*  start = NULL;
    word32 startSz;
    char*  newline = NULL;

    if (info == NULL || pBuffer == NULL || bufSz == 0)
        return BAD_FUNC_ARG;

    bufferStart = *pBuffer;
    bufferEnd = bufferStart + bufSz;

    /* find encrypted info marker */
    line = XSTRNSTR(bufferStart, kProcTypeHeader,
                    min((word32)bufSz, PEM_LINE_LEN));
    if (line != NULL) {
        if (line >= bufferEnd) {
            return BUFFER_E;
        }

        lineSz = (word32)(bufferEnd - line);

        /* find DEC-Info marker */
        start = XSTRNSTR(line, kDecInfoHeader, min(lineSz, PEM_LINE_LEN));

        if (start == NULL)
            return BUFFER_E;

        /* skip dec-info and ": " */
        start += XSTRLEN(kDecInfoHeader);
        if (start >= bufferEnd)
            return BUFFER_E;

        if (start[0] == ':') {
            start++;
            if (start >= bufferEnd)
                return BUFFER_E;
        }
        if (start[0] == ' ')
            start++;

        startSz = (word32)(bufferEnd - start);
        finish = XSTRNSTR(start, ",", min(startSz, PEM_LINE_LEN));

        if ((start != NULL) && (finish != NULL) && (start < finish)) {
            if (finish >= bufferEnd) {
                return BUFFER_E;
            }

            finishSz = (word32)(bufferEnd - finish);
            newline = XSTRNSTR(finish, "\r", min(finishSz, PEM_LINE_LEN));

            /* get cipher name */
            if (NAME_SZ < (finish - start)) /* buffer size of info->name */
                return BUFFER_E;
            if (XMEMCPY(info->name, start, finish - start) == NULL)
                return BUFFER_E;
            info->name[finish - start] = '\0'; /* null term */

            /* populate info */
            err = wc_EncryptedInfoGet(info, info->name);
            if (err != 0)
                return err;

            /* get IV */
            if (finishSz < info->ivSz + 1)
                return BUFFER_E;

            if (newline == NULL) {
                newline = XSTRNSTR(finish, "\n", min(finishSz,
                                                     PEM_LINE_LEN));
            }
            if ((newline != NULL) && (newline > finish)) {
                finish++;
                info->ivSz = (word32)(newline - finish);
                if (info->ivSz > IV_SZ)
                    return BUFFER_E;
                if (XMEMCPY(info->iv, finish, info->ivSz) == NULL)
                    return BUFFER_E;
                info->set = 1;
            }
            else
                return BUFFER_E;
        }
        else
            return BUFFER_E;

        /* eat end of line characters */
        newline = SkipEndOfLineChars(newline, bufferEnd);

        /* return new headerEnd */

        *pBuffer = newline;
    }

    return err;
}
#endif /* WOLFSSL_PEM_TO_DER */

#ifdef WOLFSSL_DER_TO_PEM
static int wc_EncryptedInfoAppend(char* dest, int destSz, char* cipherInfo)
{
    if (cipherInfo != NULL) {
        int cipherInfoStrLen = (int)XSTRLEN((char*)cipherInfo);

        if (cipherInfoStrLen > HEADER_ENCRYPTED_KEY_SIZE - (9+14+10+3))
            cipherInfoStrLen = HEADER_ENCRYPTED_KEY_SIZE - (9+14+10+3);

        if (destSz - (int)XSTRLEN(dest) >= cipherInfoStrLen + (9+14+8+2+2+1)) {
            /* strncat's src length needs to include the NULL */
            XSTRNCAT(dest, kProcTypeHeader, 10);
            XSTRNCAT(dest, ": 4,ENCRYPTED\n", 15);
            XSTRNCAT(dest, kDecInfoHeader, 9);
            XSTRNCAT(dest, ": ", 3);
            XSTRNCAT(dest, cipherInfo, destSz - (int)XSTRLEN(dest) - 1);
            XSTRNCAT(dest, "\n\n", 4);
        }
    }
    return 0;
}
#endif /* WOLFSSL_DER_TO_PEM */
#endif /* WOLFSSL_ENCRYPTED_KEYS */

#ifdef WOLFSSL_DER_TO_PEM

/* Used for compatibility API */
int wc_DerToPem(const byte* der, word32 derSz,
                byte* output, word32 outSz, int type)
{
    return wc_DerToPemEx(der, derSz, output, outSz, NULL, type);
}

/* convert der buffer to pem into output, can't do inplace, der and output
   need to be different */
int wc_DerToPemEx(const byte* der, word32 derSz, byte* output, word32 outSz,
             byte *cipher_info, int type)
{
    const char* headerStr = NULL;
    const char* footerStr = NULL;
#ifdef WOLFSSL_SMALL_STACK
    char* header = NULL;
    char* footer = NULL;
#else
    char header[MAX_X509_HEADER_SZ + HEADER_ENCRYPTED_KEY_SIZE];
    char footer[MAX_X509_HEADER_SZ];
#endif
    int headerLen = MAX_X509_HEADER_SZ + HEADER_ENCRYPTED_KEY_SIZE;
    int footerLen = MAX_X509_HEADER_SZ;
    int i;
    int err;
    int outLen;   /* return length or error */

    (void)cipher_info;

    if (der == output)      /* no in place conversion */
        return BAD_FUNC_ARG;

    err = wc_PemGetHeaderFooter(type, &headerStr, &footerStr);
    if (err != 0)
        return err;

#ifdef WOLFSSL_SMALL_STACK
    header = (char*)XMALLOC(headerLen, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (header == NULL)
        return MEMORY_E;

    footer = (char*)XMALLOC(footerLen, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (footer == NULL) {
        XFREE(header, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
#endif

    /* build header and footer based on type */
    XSTRNCPY(header, headerStr, headerLen - 1);
    header[headerLen - 2] = 0;
    XSTRNCPY(footer, footerStr, footerLen - 1);
    footer[footerLen - 2] = 0;

    /* add new line to end */
    XSTRNCAT(header, "\n", 2);
    XSTRNCAT(footer, "\n", 2);

#ifdef WOLFSSL_ENCRYPTED_KEYS
    err = wc_EncryptedInfoAppend(header, headerLen, (char*)cipher_info);
    if (err != 0) {
    #ifdef WOLFSSL_SMALL_STACK
        XFREE(header, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(footer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
        return err;
    }
#endif

    headerLen = (int)XSTRLEN(header);
    footerLen = (int)XSTRLEN(footer);

    /* if null output and 0 size passed in then return size needed */
    if (!output && outSz == 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(header, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(footer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        outLen = 0;
        if ((err = Base64_Encode(der, derSz, NULL, (word32*)&outLen))
                != LENGTH_ONLY_E) {
            return err;
        }
        return headerLen + footerLen + outLen;
    }

    if (!der || !output) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(header, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(footer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return BAD_FUNC_ARG;
    }

    /* don't even try if outSz too short */
    if (outSz < headerLen + footerLen + derSz) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(header, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(footer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return BAD_FUNC_ARG;
    }

    /* header */
    XMEMCPY(output, header, headerLen);
    i = headerLen;

#ifdef WOLFSSL_SMALL_STACK
    XFREE(header, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    /* body */
    outLen = outSz - (headerLen + footerLen);  /* input to Base64_Encode */
    if ( (err = Base64_Encode(der, derSz, output + i, (word32*)&outLen)) < 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(footer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return err;
    }
    i += outLen;

    /* footer */
    if ( (i + footerLen) > (int)outSz) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(footer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return BAD_FUNC_ARG;
    }
    XMEMCPY(output + i, footer, footerLen);

#ifdef WOLFSSL_SMALL_STACK
    XFREE(footer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return outLen + headerLen + footerLen;
}

#endif /* WOLFSSL_DER_TO_PEM */

#ifdef WOLFSSL_PEM_TO_DER

/* Remove PEM header/footer, convert to ASN1, store any encrypted data
   info->consumed tracks of PEM bytes consumed in case multiple parts */
int PemToDer(const unsigned char* buff, long longSz, int type,
              DerBuffer** pDer, void* heap, EncryptedInfo* info, int* keyFormat)
{
    const char* header      = NULL;
    const char* footer      = NULL;
    char*       headerEnd;
    char*       footerEnd;
    char*       consumedEnd;
    char*       bufferEnd   = (char*)(buff + longSz);
    long        neededSz;
    int         ret         = 0;
    int         sz          = (int)longSz;
    int         encrypted_key = 0;
    DerBuffer*  der;
#if defined(HAVE_PKCS8) || defined(WOLFSSL_ENCRYPTED_KEYS)
    word32      algId = 0;
    #if defined(WOLFSSL_ENCRYPTED_KEYS) && !defined(NO_DES3) && !defined(NO_WOLFSSL_SKIP_TRAILING_PAD)
        int     padVal = 0;
    #endif
#endif
#ifdef OPENSSL_EXTRA
    char        beginBuf[PEM_LINE_LEN + 1]; /* add 1 for null terminator */
    char        endBuf[PEM_LINE_LEN + 1];   /* add 1 for null terminator */
#endif

    WOLFSSL_ENTER("PemToDer");

    /* get PEM header and footer based on type */
    ret = wc_PemGetHeaderFooter(type, &header, &footer);
    if (ret != 0)
        return ret;

    /* map header if not found for type */
    for (;;) {
        headerEnd = XSTRNSTR((char*)buff, header, sz);

        if (headerEnd) {
            break;
        } else
        if (type == PRIVATEKEY_TYPE) {
            if (header == BEGIN_RSA_PRIV) {
                header =  BEGIN_PRIV_KEY;       footer = END_PRIV_KEY;
            } else
            if (header == BEGIN_PRIV_KEY) {
                header =  BEGIN_ENC_PRIV_KEY;   footer = END_ENC_PRIV_KEY;
            } else
    #ifdef HAVE_ECC
            if (header == BEGIN_ENC_PRIV_KEY) {
                header =  BEGIN_EC_PRIV;        footer = END_EC_PRIV;
            } else
            if (header == BEGIN_EC_PRIV) {
                header =  BEGIN_DSA_PRIV;       footer = END_DSA_PRIV;
            } else
    #endif
    #if defined(HAVE_ED25519) || defined(HAVE_ED448)
        #ifdef HAVE_ECC
            if (header == BEGIN_DSA_PRIV)
        #else
            if (header == BEGIN_ENC_PRIV_KEY)
        #endif
            {
                header =  BEGIN_EDDSA_PRIV;     footer = END_EDDSA_PRIV;
            } else
    #endif
            {
                break;
            }
        } else
#ifdef HAVE_CRL
        if ((type == CRL_TYPE) && (header != BEGIN_CRL)) {
            header =  BEGIN_CRL;                footer = END_CRL;
        } else
#endif
        {
            break;
        }
    }

    if (!headerEnd) {
#ifdef OPENSSL_EXTRA
        if (type == PRIVATEKEY_TYPE) {
            char* beginEnd;
            int endLen;
            /* see if there is a -----BEGIN * PRIVATE KEY----- header */
            headerEnd = XSTRNSTR((char*)buff, PRIV_KEY_SUFFIX, sz);
            if (headerEnd) {
                beginEnd = headerEnd + XSTR_SIZEOF(PRIV_KEY_SUFFIX);
                if (beginEnd >= (char*)buff + sz) {
                    return BUFFER_E;
                }

                /* back up to BEGIN_PRIV_KEY_PREFIX */
                while (headerEnd > (char*)buff &&
                        XSTRNCMP(headerEnd, BEGIN_PRIV_KEY_PREFIX,
                                XSTR_SIZEOF(BEGIN_PRIV_KEY_PREFIX)) != 0 &&
                        *headerEnd != '\n') {
                    headerEnd--;
                }
                if (headerEnd <= (char*)buff ||
                        XSTRNCMP(headerEnd, BEGIN_PRIV_KEY_PREFIX,
                        XSTR_SIZEOF(BEGIN_PRIV_KEY_PREFIX)) != 0 ||
                        beginEnd - headerEnd > PEM_LINE_LEN) {
                    WOLFSSL_MSG("Couldn't find PEM header");
                    return ASN_NO_PEM_HEADER;
                }

                /* headerEnd now points to beginning of header */
                XMEMCPY(beginBuf, headerEnd, beginEnd - headerEnd);
                beginBuf[beginEnd - headerEnd] = '\0';
                /* look for matching footer */
                footer = XSTRNSTR(beginEnd,
                                beginBuf + XSTR_SIZEOF(BEGIN_PRIV_KEY_PREFIX),
                                (unsigned int)((char*)buff + sz - beginEnd));
                if (!footer) {
                    WOLFSSL_MSG("Couldn't find PEM footer");
                    return ASN_NO_PEM_HEADER;
                }

                footer -= XSTR_SIZEOF(END_PRIV_KEY_PREFIX);
                if (footer > (char*)buff + sz - XSTR_SIZEOF(END_PRIV_KEY_PREFIX)
                        || XSTRNCMP(footer, END_PRIV_KEY_PREFIX,
                            XSTR_SIZEOF(END_PRIV_KEY_PREFIX)) != 0) {
                    WOLFSSL_MSG("Unexpected footer for PEM");
                    return BUFFER_E;
                }

                endLen = (unsigned int)(beginEnd - headerEnd -
                            (XSTR_SIZEOF(BEGIN_PRIV_KEY_PREFIX) -
                                    XSTR_SIZEOF(END_PRIV_KEY_PREFIX)));
                XMEMCPY(endBuf, footer, endLen);
                endBuf[endLen] = '\0';

                header = beginBuf;
                footer = endBuf;
                headerEnd = beginEnd;
            }
        }

        if (!headerEnd) {
            WOLFSSL_MSG("Couldn't find PEM header");
            return ASN_NO_PEM_HEADER;
        }
#else
        WOLFSSL_MSG("Couldn't find PEM header");
        return ASN_NO_PEM_HEADER;
#endif
    } else {
        headerEnd += XSTRLEN(header);
    }

    /* eat end of line characters */
    headerEnd = SkipEndOfLineChars(headerEnd, bufferEnd);

    if (type == PRIVATEKEY_TYPE) {
        /* keyFormat is Key_Sum enum */
        if (keyFormat) {
        #ifdef HAVE_ECC
            if (header == BEGIN_EC_PRIV)
                *keyFormat = ECDSAk;
        #endif
        #if !defined(NO_DSA)
            if (header == BEGIN_DSA_PRIV)
                *keyFormat = DSAk;
        #endif
        }
    }

#ifdef WOLFSSL_ENCRYPTED_KEYS
    if (info) {
        ret = wc_EncryptedInfoParse(info, &headerEnd, bufferEnd - headerEnd);
        if (ret < 0)
            return ret;
        if (info->set)
            encrypted_key = 1;
    }
#endif /* WOLFSSL_ENCRYPTED_KEYS */

    /* find footer */
    footerEnd = XSTRNSTR(headerEnd, footer, (unsigned int)((char*)buff + sz - headerEnd));
    if (!footerEnd) {
        if (info)
            info->consumed = longSz; /* No more certs if no footer */
        return BUFFER_E;
    }

    consumedEnd = footerEnd + XSTRLEN(footer);

    if (consumedEnd < bufferEnd) { /* handle no end of line on last line */
        /* eat end of line characters */
        consumedEnd = SkipEndOfLineChars(consumedEnd, bufferEnd);
        /* skip possible null term */
        if (consumedEnd < bufferEnd && consumedEnd[0] == '\0')
            consumedEnd++;
    }

    if (info)
        info->consumed = (long)(consumedEnd - (char*)buff);

    /* set up der buffer */
    neededSz = (long)(footerEnd - headerEnd);
    if (neededSz > sz || neededSz <= 0)
        return BUFFER_E;

    ret = AllocDer(pDer, (word32)neededSz, type, heap);
    if (ret < 0) {
        return ret;
    }
    der = *pDer;

    if (Base64_Decode((byte*)headerEnd, (word32)neededSz,
                      der->buffer, &der->length) < 0)
        return BUFFER_E;

    if ((header == BEGIN_PRIV_KEY
#ifdef OPENSSL_EXTRA
         || header == beginBuf
#endif
#ifdef HAVE_ECC
         || header == BEGIN_EC_PRIV
#endif
        ) && !encrypted_key)
    {
    #ifdef HAVE_PKCS8
        /* pkcs8 key, convert and adjust length */
        if ((ret = ToTraditional_ex(der->buffer, der->length, &algId)) > 0) {
            der->length = ret;
            if (keyFormat) {
                *keyFormat = algId;
            }
        }
        else {
            /* ignore failure here and assume key is not pkcs8 wrapped */
        }
    #endif

        return 0;
    }

#ifdef WOLFSSL_ENCRYPTED_KEYS
    if (encrypted_key || header == BEGIN_ENC_PRIV_KEY) {
        int   passwordSz = NAME_SZ;
    #ifdef WOLFSSL_SMALL_STACK
        char* password = NULL;
    #else
        char  password[NAME_SZ];
    #endif

        if (!info || !info->passwd_cb) {
            WOLFSSL_MSG("No password callback set");
            return NO_PASSWORD;
        }

    #ifdef WOLFSSL_SMALL_STACK
        password = (char*)XMALLOC(passwordSz, heap, DYNAMIC_TYPE_STRING);
        if (password == NULL)
            return MEMORY_E;
    #endif

        /* get password */
        ret = info->passwd_cb(password, passwordSz, PEM_PASS_READ,
            info->passwd_userdata);
        if (ret >= 0) {
            passwordSz = ret;

            /* convert and adjust length */
            if (header == BEGIN_ENC_PRIV_KEY) {
            #ifndef NO_PWDBASED
                ret = ToTraditionalEnc(der->buffer, der->length,
                                       password, passwordSz, &algId);

                if (ret >= 0) {
                    der->length = ret;
                    if (keyFormat) {
                        *keyFormat = algId;
                    }
                    ret = 0;
                }
            #else
                ret = NOT_COMPILED_IN;
            #endif
            }
            /* decrypt the key */
            else {
                if (passwordSz == 0) {
                    /* The key is encrypted but does not have a password */
                    WOLFSSL_MSG("No password for encrypted key");
                    ret = NO_PASSWORD;
                }
                else {
                    ret = wc_BufferKeyDecrypt(info, der->buffer, der->length,
                        (byte*)password, passwordSz, WC_MD5);

#ifndef NO_WOLFSSL_SKIP_TRAILING_PAD
                #ifndef NO_DES3
                    if (info->cipherType == WC_CIPHER_DES3) {
                        /* Assuming there is padding:
                         *      (der->length > 0 &&
                         *       (der->length % DES_BLOCK_SIZE) != 0)
                         * and assuming the last value signifies the number of
                         * padded bytes IE if last value is 0x08 then there are
                         * 8 bytes of padding:
                         *      padVal = der->buffer[der->length-1];
                         * then strip this padding before proceeding:
                         * der->length -= padVal;
                         */
                        if (der->length > 0 &&
                            (der->length % DES_BLOCK_SIZE) != 0) {
                            padVal = der->buffer[der->length-1];
                            if (padVal <= DES_BLOCK_SIZE) {
                                der->length -= padVal;
                            }
                        }
                    }
                #endif /* !NO_DES3 */
#endif /* !NO_WOLFSSL_SKIP_TRAILING_PAD */
                }
            }
#ifdef OPENSSL_EXTRA
            if (ret) {
                PEMerr(0, PEM_R_BAD_DECRYPT);
            }
#endif
            ForceZero(password, passwordSz);
        }
#ifdef OPENSSL_EXTRA
        else {
            PEMerr(0, PEM_R_BAD_PASSWORD_READ);
        }
#endif

    #ifdef WOLFSSL_SMALL_STACK
        XFREE(password, heap, DYNAMIC_TYPE_STRING);
    #endif
    }
#endif /* WOLFSSL_ENCRYPTED_KEYS */

    return ret;
}

int wc_PemToDer(const unsigned char* buff, long longSz, int type,
              DerBuffer** pDer, void* heap, EncryptedInfo* info, int* eccKey)
{
    return PemToDer(buff, longSz, type, pDer, heap, info, eccKey);
}


/* our KeyPemToDer password callback, password in userData */
static WC_INLINE int OurPasswordCb(char* passwd, int sz, int rw, void* userdata)
{
    (void)rw;

    if (userdata == NULL)
        return 0;

    XSTRNCPY(passwd, (char*)userdata, sz);
    return min((word32)sz, (word32)XSTRLEN((char*)userdata));
}

/* Return bytes written to buff or < 0 for error */
int wc_KeyPemToDer(const unsigned char* pem, int pemSz,
                        unsigned char* buff, int buffSz, const char* pass)
{
    int            eccKey = 0;
    int            ret;
    DerBuffer*     der = NULL;
#ifdef WOLFSSL_SMALL_STACK
    EncryptedInfo* info = NULL;
#else
    EncryptedInfo  info[1];
#endif

    WOLFSSL_ENTER("wc_KeyPemToDer");

    if (pem == NULL || buff == NULL || buffSz <= 0) {
        WOLFSSL_MSG("Bad pem der args");
        return BAD_FUNC_ARG;
    }

#ifdef WOLFSSL_SMALL_STACK
    info = (EncryptedInfo*)XMALLOC(sizeof(EncryptedInfo), NULL,
                                   DYNAMIC_TYPE_ENCRYPTEDINFO);
    if (info == NULL)
        return MEMORY_E;
#endif

    XMEMSET(info, 0, sizeof(EncryptedInfo));
    info->passwd_cb = OurPasswordCb;
    info->passwd_userdata = (void*)pass;

    ret = PemToDer(pem, pemSz, PRIVATEKEY_TYPE, &der, NULL, info, &eccKey);

#ifdef WOLFSSL_SMALL_STACK
    XFREE(info, NULL, DYNAMIC_TYPE_ENCRYPTEDINFO);
#endif

    if (ret < 0 || der == NULL) {
        WOLFSSL_MSG("Bad Pem To Der");
    }
    else {
        if (der->length <= (word32)buffSz) {
            XMEMCPY(buff, der->buffer, der->length);
            ret = der->length;
        }
        else {
            WOLFSSL_MSG("Bad der length");
            ret = BAD_FUNC_ARG;
        }
    }

    FreeDer(&der);
    return ret;
}


/* Return bytes written to buff or < 0 for error */
int wc_CertPemToDer(const unsigned char* pem, int pemSz,
                        unsigned char* buff, int buffSz, int type)
{
    int            eccKey = 0;
    int            ret;
    DerBuffer*     der = NULL;

    WOLFSSL_ENTER("wc_CertPemToDer");

    if (pem == NULL || buff == NULL || buffSz <= 0) {
        WOLFSSL_MSG("Bad pem der args");
        return BAD_FUNC_ARG;
    }

    if (type != CERT_TYPE && type != CA_TYPE && type != CERTREQ_TYPE) {
        WOLFSSL_MSG("Bad cert type");
        return BAD_FUNC_ARG;
    }


    ret = PemToDer(pem, pemSz, type, &der, NULL, NULL, &eccKey);
    if (ret < 0 || der == NULL) {
        WOLFSSL_MSG("Bad Pem To Der");
    }
    else {
        if (der->length <= (word32)buffSz) {
            XMEMCPY(buff, der->buffer, der->length);
            ret = der->length;
        }
        else {
            WOLFSSL_MSG("Bad der length");
            ret = BAD_FUNC_ARG;
        }
    }

    FreeDer(&der);
    return ret;
}

#endif /* WOLFSSL_PEM_TO_DER */
#endif /* WOLFSSL_PEM_TO_DER || WOLFSSL_DER_TO_PEM */


#ifdef WOLFSSL_PEM_TO_DER
#if defined(WOLFSSL_CERT_EXT) || defined(WOLFSSL_PUB_PEM_TO_DER)
/* Return bytes written to buff or < 0 for error */
int wc_PubKeyPemToDer(const unsigned char* pem, int pemSz,
                           unsigned char* buff, int buffSz)
{
    int ret;
    DerBuffer* der = NULL;

    WOLFSSL_ENTER("wc_PubKeyPemToDer");

    if (pem == NULL || buff == NULL || buffSz <= 0) {
        WOLFSSL_MSG("Bad pem der args");
        return BAD_FUNC_ARG;
    }

    ret = PemToDer(pem, pemSz, PUBLICKEY_TYPE, &der, NULL, NULL, NULL);
    if (ret < 0 || der == NULL) {
        WOLFSSL_MSG("Bad Pem To Der");
    }
    else {
        if (der->length <= (word32)buffSz) {
            XMEMCPY(buff, der->buffer, der->length);
            ret = der->length;
        }
        else {
            WOLFSSL_MSG("Bad der length");
            ret = BAD_FUNC_ARG;
        }
    }

    FreeDer(&der);
    return ret;
}
#endif /* WOLFSSL_CERT_EXT || WOLFSSL_PUB_PEM_TO_DER */
#endif /* WOLFSSL_PEM_TO_DER */

#ifndef NO_FILESYSTEM

#ifdef WOLFSSL_CERT_GEN
/* load pem cert from file into der buffer, return der size or error */
int wc_PemCertToDer(const char* fileName, unsigned char* derBuf, int derSz)
{
#ifdef WOLFSSL_SMALL_STACK
    byte   staticBuffer[1]; /* force XMALLOC */
#else
    byte   staticBuffer[FILE_BUFFER_SIZE];
#endif
    byte*  fileBuf = staticBuffer;
    int    dynamic = 0;
    int    ret     = 0;
    long   sz      = 0;
    XFILE  file;
    DerBuffer* converted = NULL;

    WOLFSSL_ENTER("wc_PemCertToDer");

    if (fileName == NULL) {
        ret = BAD_FUNC_ARG;
    }
    else {
        file = XFOPEN(fileName, "rb");
        if (file == XBADFILE) {
            ret = BUFFER_E;
        }
    }

    if (ret == 0) {
        if(XFSEEK(file, 0, XSEEK_END) != 0)
            ret = BUFFER_E;
        sz = XFTELL(file);
        XREWIND(file);

        if (sz <= 0) {
            ret = BUFFER_E;
        }
        else if (sz > (long)sizeof(staticBuffer)) {
        #ifdef WOLFSSL_STATIC_MEMORY
            WOLFSSL_MSG("File was larger then static buffer");
            return MEMORY_E;
        #endif
            fileBuf = (byte*)XMALLOC(sz, NULL, DYNAMIC_TYPE_FILE);
            if (fileBuf == NULL)
                ret = MEMORY_E;
            else
                dynamic = 1;
        }

        if (ret == 0) {
            if ( (ret = (int)XFREAD(fileBuf, 1, sz, file)) != sz) {
                ret = BUFFER_E;
            }
        #ifdef WOLFSSL_PEM_TO_DER
            else {
                ret = PemToDer(fileBuf, sz, CA_TYPE, &converted,  0, NULL,NULL);
            }
        #endif

            if (ret == 0) {
                if (converted->length < (word32)derSz) {
                    XMEMCPY(derBuf, converted->buffer, converted->length);
                    ret = converted->length;
                }
                else
                    ret = BUFFER_E;
            }

            FreeDer(&converted);
        }

        XFCLOSE(file);
        if (dynamic)
            XFREE(fileBuf, NULL, DYNAMIC_TYPE_FILE);
    }

    return ret;
}
#endif /* WOLFSSL_CERT_GEN */

#if defined(WOLFSSL_CERT_EXT) || defined(WOLFSSL_PUB_PEM_TO_DER)
/* load pem public key from file into der buffer, return der size or error */
int wc_PemPubKeyToDer(const char* fileName,
                           unsigned char* derBuf, int derSz)
{
#ifdef WOLFSSL_SMALL_STACK
    byte   staticBuffer[1]; /* force XMALLOC */
#else
    byte   staticBuffer[FILE_BUFFER_SIZE];
#endif
    byte*  fileBuf = staticBuffer;
    int    dynamic = 0;
    int    ret     = 0;
    long   sz      = 0;
    XFILE  file;
    DerBuffer* converted = NULL;

    WOLFSSL_ENTER("wc_PemPubKeyToDer");

    if (fileName == NULL) {
        ret = BAD_FUNC_ARG;
    }
    else {
        file = XFOPEN(fileName, "rb");
        if (file == XBADFILE) {
            ret = BUFFER_E;
        }
    }

    if (ret == 0) {
        if(XFSEEK(file, 0, XSEEK_END) != 0)
            ret = BUFFER_E;
        sz = XFTELL(file);
        XREWIND(file);

        if (sz <= 0) {
            ret = BUFFER_E;
        }
        else if (sz > (long)sizeof(staticBuffer)) {
        #ifdef WOLFSSL_STATIC_MEMORY
            WOLFSSL_MSG("File was larger then static buffer");
            return MEMORY_E;
        #endif
            fileBuf = (byte*)XMALLOC(sz, NULL, DYNAMIC_TYPE_FILE);
            if (fileBuf == NULL)
                ret = MEMORY_E;
            else
                dynamic = 1;
        }
        if (ret == 0) {
            if ( (ret = (int)XFREAD(fileBuf, 1, sz, file)) != sz) {
                ret = BUFFER_E;
            }
        #ifdef WOLFSSL_PEM_TO_DER
            else {
                ret = PemToDer(fileBuf, sz, PUBLICKEY_TYPE, &converted,
                               0, NULL, NULL);
            }
        #endif

            if (ret == 0) {
                if (converted->length < (word32)derSz) {
                    XMEMCPY(derBuf, converted->buffer, converted->length);
                    ret = converted->length;
                }
                else
                    ret = BUFFER_E;
            }

            FreeDer(&converted);
        }

        XFCLOSE(file);
        if (dynamic)
            XFREE(fileBuf, NULL, DYNAMIC_TYPE_FILE);
    }

    return ret;
}
#endif /* WOLFSSL_CERT_EXT || WOLFSSL_PUB_PEM_TO_DER */

#endif /* !NO_FILESYSTEM */


#if !defined(NO_RSA) && (defined(WOLFSSL_CERT_GEN) || \
    ((defined(WOLFSSL_KEY_GEN) || defined(OPENSSL_EXTRA)) && !defined(HAVE_USER_RSA)))
/* USER RSA ifdef portions used instead of refactor in consideration for
   possible fips build */
/* Write a public RSA key to output */
static int SetRsaPublicKey(byte* output, RsaKey* key,
                           int outLen, int with_header)
{
#ifdef WOLFSSL_SMALL_STACK
    byte* n = NULL;
    byte* e = NULL;
#else
    byte n[MAX_RSA_INT_SZ];
    byte e[MAX_RSA_E_SZ];
#endif
    byte seq[MAX_SEQ_SZ];
    byte bitString[1 + MAX_LENGTH_SZ + 1];
    int  nSz;
    int  eSz;
    int  seqSz;
    int  bitStringSz;
    int  idx;

    if (output == NULL || key == NULL || outLen < MAX_SEQ_SZ)
        return BAD_FUNC_ARG;

    /* n */
#ifdef WOLFSSL_SMALL_STACK
    n = (byte*)XMALLOC(MAX_RSA_INT_SZ, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (n == NULL)
        return MEMORY_E;
#endif

#ifdef HAVE_USER_RSA
    nSz = SetASNIntRSA(key->n, n);
#else
    nSz = SetASNIntMP(&key->n, MAX_RSA_INT_SZ, n);
#endif
    if (nSz < 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(n, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return nSz;
    }

    /* e */
#ifdef WOLFSSL_SMALL_STACK
    e = (byte*)XMALLOC(MAX_RSA_E_SZ, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (e == NULL) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(n, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return MEMORY_E;
    }
#endif

#ifdef HAVE_USER_RSA
    eSz = SetASNIntRSA(key->e, e);
#else
    eSz = SetASNIntMP(&key->e, MAX_RSA_INT_SZ, e);
#endif
    if (eSz < 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(n, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(e, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return eSz;
    }

    seqSz  = SetSequence(nSz + eSz, seq);

    /* check output size */
    if ( (seqSz + nSz + eSz) > outLen) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(n,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(e,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return BUFFER_E;
    }

    /* headers */
    if (with_header) {
        int  algoSz;
#ifdef WOLFSSL_SMALL_STACK
        byte* algo;

        algo = (byte*)XMALLOC(MAX_ALGO_SZ, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        if (algo == NULL) {
            XFREE(n, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(e, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            return MEMORY_E;
        }
#else
        byte algo[MAX_ALGO_SZ];
#endif
        algoSz = SetAlgoID(RSAk, algo, oidKeyType, 0);
        bitStringSz  = SetBitString(seqSz + nSz + eSz, 0, bitString);

        idx = SetSequence(nSz + eSz + seqSz + bitStringSz + algoSz, output);

        /* check output size */
        if ( (idx + algoSz + bitStringSz + seqSz + nSz + eSz) > outLen) {
            #ifdef WOLFSSL_SMALL_STACK
                XFREE(n,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
                XFREE(e,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
                XFREE(algo, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            #endif

            return BUFFER_E;
        }

        /* algo */
        XMEMCPY(output + idx, algo, algoSz);
        idx += algoSz;
        /* bit string */
        XMEMCPY(output + idx, bitString, bitStringSz);
        idx += bitStringSz;
#ifdef WOLFSSL_SMALL_STACK
        XFREE(algo, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
    }
    else
        idx = 0;

    /* seq */
    XMEMCPY(output + idx, seq, seqSz);
    idx += seqSz;
    /* n */
    XMEMCPY(output + idx, n, nSz);
    idx += nSz;
    /* e */
    XMEMCPY(output + idx, e, eSz);
    idx += eSz;

#ifdef WOLFSSL_SMALL_STACK
    XFREE(n,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(e,    key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return idx;
}

#endif /* !NO_RSA && (WOLFSSL_CERT_GEN || (WOLFSSL_KEY_GEN &&
                                           !HAVE_USER_RSA))) */

#if !defined(NO_RSA) && (defined(WOLFSSL_CERT_GEN) || defined(OPENSSL_EXTRA))
int wc_RsaPublicKeyDerSize(RsaKey* key, int with_header)
{
    int  idx = 0;
    int  nSz, eSz, seqSz, bitStringSz, algoSz;

    if (key == NULL)
        return BAD_FUNC_ARG;

    /* n */
#ifdef HAVE_USER_RSA
    nSz = SetASNIntRSA(key->n, NULL);
#else
    nSz = SetASNIntMP(&key->n, MAX_RSA_INT_SZ, NULL);
#endif
    if (nSz < 0) {
        return nSz;
    }

    /* e */
#ifdef HAVE_USER_RSA
    eSz = SetASNIntRSA(key->e, NULL);
#else
    eSz = SetASNIntMP(&key->e, MAX_RSA_INT_SZ, NULL);
#endif
    if (eSz < 0) {
        return eSz;
    }

    seqSz  = SetSequence(nSz + eSz, NULL);

    /* headers */
    if (with_header) {
        algoSz = SetAlgoID(RSAk, NULL, oidKeyType, 0);
        bitStringSz = SetBitString(seqSz + nSz + eSz, 0, NULL);

        idx += SetSequence(nSz + eSz + seqSz + bitStringSz + algoSz, NULL);

        /* algo */
        idx += algoSz;
        /* bit string */
        idx += bitStringSz;
    }

    /* seq */
    idx += seqSz;
    /* n */
    idx += nSz;
    /* e */
    idx += eSz;

    return idx;
}

#endif /* !NO_RSA && WOLFSSL_CERT_GEN */


#if defined(WOLFSSL_KEY_GEN) && !defined(NO_RSA) && !defined(HAVE_USER_RSA)

static mp_int* GetRsaInt(RsaKey* key, int idx)
{
    if (idx == 0)
        return &key->n;
    if (idx == 1)
        return &key->e;
    if (idx == 2)
        return &key->d;
    if (idx == 3)
        return &key->p;
    if (idx == 4)
        return &key->q;
    if (idx == 5)
        return &key->dP;
    if (idx == 6)
        return &key->dQ;
    if (idx == 7)
        return &key->u;

    return NULL;
}


/* Release Tmp RSA resources */
static WC_INLINE void FreeTmpRsas(byte** tmps, void* heap)
{
    int i;

    (void)heap;

    for (i = 0; i < RSA_INTS; i++)
        XFREE(tmps[i], heap, DYNAMIC_TYPE_RSA);
}


/* Convert RsaKey key to DER format, write to output (inLen), return bytes
   written */
int wc_RsaKeyToDer(RsaKey* key, byte* output, word32 inLen)
{
    word32 seqSz, verSz, rawLen, intTotalLen = 0;
    word32 sizes[RSA_INTS];
    int    i, j, outLen, ret = 0, mpSz;

    byte  seq[MAX_SEQ_SZ];
    byte  ver[MAX_VERSION_SZ];
    byte* tmps[RSA_INTS];

    if (!key)
        return BAD_FUNC_ARG;

    if (key->type != RSA_PRIVATE)
        return BAD_FUNC_ARG;

    for (i = 0; i < RSA_INTS; i++)
        tmps[i] = NULL;

    /* write all big ints from key to DER tmps */
    for (i = 0; i < RSA_INTS; i++) {
        mp_int* keyInt = GetRsaInt(key, i);

        rawLen = mp_unsigned_bin_size(keyInt) + 1;
        tmps[i] = (byte*)XMALLOC(rawLen + MAX_SEQ_SZ, key->heap,
                                 DYNAMIC_TYPE_RSA);
        if (tmps[i] == NULL) {
            ret = MEMORY_E;
            break;
        }

        mpSz = SetASNIntMP(keyInt, MAX_RSA_INT_SZ, tmps[i]);
        if (mpSz < 0) {
            ret = mpSz;
            break;
        }
        intTotalLen += (sizes[i] = mpSz);
    }

    if (ret != 0) {
        FreeTmpRsas(tmps, key->heap);
        return ret;
    }

    /* make headers */
    verSz = SetMyVersion(0, ver, FALSE);
    seqSz = SetSequence(verSz + intTotalLen, seq);

    outLen = seqSz + verSz + intTotalLen;
    if (output) {
        if (outLen > (int)inLen) {
            FreeTmpRsas(tmps, key->heap);
            return BAD_FUNC_ARG;
        }

        /* write to output */
        XMEMCPY(output, seq, seqSz);
        j = seqSz;
        XMEMCPY(output + j, ver, verSz);
        j += verSz;

        for (i = 0; i < RSA_INTS; i++) {
            XMEMCPY(output + j, tmps[i], sizes[i]);
            j += sizes[i];
        }
    }
    FreeTmpRsas(tmps, key->heap);

    return outLen;
}
#endif

#if (defined(WOLFSSL_KEY_GEN) || defined(OPENSSL_EXTRA)) && !defined(NO_RSA) && !defined(HAVE_USER_RSA)
/* Convert Rsa Public key to DER format, write to output (inLen), return bytes
   written */
int wc_RsaKeyToPublicDer(RsaKey* key, byte* output, word32 inLen)
{
    return SetRsaPublicKey(output, key, inLen, 1);
}

#endif /* (WOLFSSL_KEY_GEN || OPENSSL_EXTRA) && !NO_RSA && !HAVE_USER_RSA */


#ifdef WOLFSSL_CERT_GEN

/* Initialize and Set Certificate defaults:
   version    = 3 (0x2)
   serial     = 0
   sigType    = SHA_WITH_RSA
   issuer     = blank
   daysValid  = 500
   selfSigned = 1 (true) use subject as issuer
   subject    = blank
*/
int wc_InitCert(Cert* cert)
{
#ifdef WOLFSSL_MULTI_ATTRIB
    int i = 0;
#endif
    if (cert == NULL) {
        return BAD_FUNC_ARG;
    }

    XMEMSET(cert, 0, sizeof(Cert));

    cert->version    = 2;   /* version 3 is hex 2 */
#ifndef NO_SHA
    cert->sigType    = CTC_SHAwRSA;
#elif !defined(NO_SHA256)
    cert->sigType    = CTC_SHA256wRSA;
#else
    cert->sigType    = 0;
#endif
    cert->daysValid  = 500;
    cert->selfSigned = 1;
    cert->keyType    = RSA_KEY;

    cert->issuer.countryEnc = CTC_PRINTABLE;
    cert->issuer.stateEnc = CTC_UTF8;
    cert->issuer.localityEnc = CTC_UTF8;
    cert->issuer.surEnc = CTC_UTF8;
    cert->issuer.orgEnc = CTC_UTF8;
    cert->issuer.unitEnc = CTC_UTF8;
    cert->issuer.commonNameEnc = CTC_UTF8;

    cert->subject.countryEnc = CTC_PRINTABLE;
    cert->subject.stateEnc = CTC_UTF8;
    cert->subject.localityEnc = CTC_UTF8;
    cert->subject.surEnc = CTC_UTF8;
    cert->subject.orgEnc = CTC_UTF8;
    cert->subject.unitEnc = CTC_UTF8;
    cert->subject.commonNameEnc = CTC_UTF8;

#ifdef WOLFSSL_MULTI_ATTRIB
    for (i = 0; i < CTC_MAX_ATTRIB; i++) {
        cert->issuer.name[i].type   = CTC_UTF8;
        cert->subject.name[i].type  = CTC_UTF8;
    }
#endif /* WOLFSSL_MULTI_ATTRIB */

#ifdef WOLFSSL_HEAP_TEST
    cert->heap = (void*)WOLFSSL_HEAP_TEST;
#endif

    return 0;
}


/* DER encoded x509 Certificate */
typedef struct DerCert {
    byte size[MAX_LENGTH_SZ];          /* length encoded */
    byte version[MAX_VERSION_SZ];      /* version encoded */
    byte serial[(int)CTC_SERIAL_SIZE + (int)MAX_LENGTH_SZ]; /* serial number encoded */
    byte sigAlgo[MAX_ALGO_SZ];         /* signature algo encoded */
    byte issuer[ASN_NAME_MAX];         /* issuer  encoded */
    byte subject[ASN_NAME_MAX];        /* subject encoded */
    byte validity[MAX_DATE_SIZE*2 + MAX_SEQ_SZ*2];  /* before and after dates */
    byte publicKey[MAX_PUBLIC_KEY_SZ]; /* rsa / ntru public key encoded */
    byte ca[MAX_CA_SZ];                /* basic constraint CA true size */
    byte extensions[MAX_EXTENSIONS_SZ]; /* all extensions */
#ifdef WOLFSSL_CERT_EXT
    byte skid[MAX_KID_SZ];             /* Subject Key Identifier extension */
    byte akid[MAX_KID_SZ];             /* Authority Key Identifier extension */
    byte keyUsage[MAX_KEYUSAGE_SZ];    /* Key Usage extension */
    byte extKeyUsage[MAX_EXTKEYUSAGE_SZ]; /* Extended Key Usage extension */
    byte certPolicies[MAX_CERTPOL_NB*MAX_CERTPOL_SZ]; /* Certificate Policies */
#endif
#ifdef WOLFSSL_CERT_REQ
    byte attrib[MAX_ATTRIB_SZ];        /* Cert req attributes encoded */
#endif
#ifdef WOLFSSL_ALT_NAMES
    byte altNames[CTC_MAX_ALT_SIZE];   /* Alternative Names encoded */
#endif
    int  sizeSz;                       /* encoded size length */
    int  versionSz;                    /* encoded version length */
    int  serialSz;                     /* encoded serial length */
    int  sigAlgoSz;                    /* encoded sig algo length */
    int  issuerSz;                     /* encoded issuer length */
    int  subjectSz;                    /* encoded subject length */
    int  validitySz;                   /* encoded validity length */
    int  publicKeySz;                  /* encoded public key length */
    int  caSz;                         /* encoded CA extension length */
#ifdef WOLFSSL_CERT_EXT
    int  skidSz;                       /* encoded SKID extension length */
    int  akidSz;                       /* encoded SKID extension length */
    int  keyUsageSz;                   /* encoded KeyUsage extension length */
    int  extKeyUsageSz;                /* encoded ExtendedKeyUsage extension length */
    int  certPoliciesSz;               /* encoded CertPolicies extension length*/
#endif
#ifdef WOLFSSL_ALT_NAMES
    int  altNamesSz;                   /* encoded AltNames extension length */
#endif
    int  extensionsSz;                 /* encoded extensions total length */
    int  total;                        /* total encoded lengths */
#ifdef WOLFSSL_CERT_REQ
    int  attribSz;
#endif
} DerCert;


#ifdef WOLFSSL_CERT_REQ

/* Write a set header to output */
static word32 SetPrintableString(word32 len, byte* output)
{
    output[0] = ASN_PRINTABLE_STRING;
    return SetLength(len, output + 1) + 1;
}

static word32 SetUTF8String(word32 len, byte* output)
{
    output[0] = ASN_UTF8STRING;
    return SetLength(len, output + 1) + 1;
}

#endif /* WOLFSSL_CERT_REQ */


#ifndef WOLFSSL_CERT_GEN_CACHE
/* wc_SetCert_Free is only public when WOLFSSL_CERT_GEN_CACHE is not defined */
static
#endif
void wc_SetCert_Free(Cert* cert)
{
    if (cert != NULL) {
        cert->der = NULL;
        if (cert->decodedCert) {
            FreeDecodedCert((DecodedCert*)cert->decodedCert);

            XFREE(cert->decodedCert, cert->heap, DYNAMIC_TYPE_DCERT);
            cert->decodedCert = NULL;
        }
    }
}

static int wc_SetCert_LoadDer(Cert* cert, const byte* der, word32 derSz)
{
    int ret;

    if (cert == NULL) {
        ret = BAD_FUNC_ARG;
    }
    else {
        /* Allocate DecodedCert struct and Zero */
        cert->decodedCert = (void*)XMALLOC(sizeof(DecodedCert), cert->heap,
            DYNAMIC_TYPE_DCERT);

        if (cert->decodedCert == NULL) {
            ret = MEMORY_E;
        }
        else {
            XMEMSET(cert->decodedCert, 0, sizeof(DecodedCert));

            InitDecodedCert((DecodedCert*)cert->decodedCert, der, derSz,
                    cert->heap);
            ret = ParseCertRelative((DecodedCert*)cert->decodedCert,
                    CERT_TYPE, 0, NULL);
            if (ret >= 0) {
                cert->der = (byte*)der;
            }
            else {
                wc_SetCert_Free(cert);
            }
        }
    }

    return ret;
}

#endif /* WOLFSSL_CERT_GEN */


#if defined(HAVE_ECC) && defined(HAVE_ECC_KEY_EXPORT)

/* Write a public ECC key to output */
static int SetEccPublicKey(byte* output, ecc_key* key, int with_header)
{
    byte bitString[1 + MAX_LENGTH_SZ + 1];
    int  algoSz;
    int  curveSz;
    int  bitStringSz;
    int  idx;
    word32 pubSz = ECC_BUFSIZE;
#ifdef WOLFSSL_SMALL_STACK
    byte* algo = NULL;
    byte* curve = NULL;
    byte* pub;
#else
    byte algo[MAX_ALGO_SZ];
    byte curve[MAX_ALGO_SZ];
    byte pub[ECC_BUFSIZE];
#endif
    int ret;

#ifdef WOLFSSL_SMALL_STACK
    pub = (byte*)XMALLOC(ECC_BUFSIZE, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (pub == NULL)
        return MEMORY_E;
#endif

#if defined(HAVE_SELFTEST) || defined(HAVE_FIPS)
    /* older version of ecc.c can not handle dp being NULL */
    if (key != NULL && key->dp == NULL) {
        ret = BAD_FUNC_ARG;
    }
    else {
        ret = wc_ecc_export_x963(key, pub, &pubSz);
    }
#else
    ret = wc_ecc_export_x963(key, pub, &pubSz);
#endif
    if (ret != 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(pub, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ret;
    }

    /* headers */
    if (with_header) {
#ifdef WOLFSSL_SMALL_STACK
        curve = (byte*)XMALLOC(MAX_ALGO_SZ, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        if (curve == NULL) {
            XFREE(pub, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            return MEMORY_E;
        }
#endif
        curveSz = SetCurve(key, curve);
        if (curveSz <= 0) {
#ifdef WOLFSSL_SMALL_STACK
            XFREE(curve, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(pub,   key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return curveSz;
        }

#ifdef WOLFSSL_SMALL_STACK
        algo = (byte*)XMALLOC(MAX_ALGO_SZ, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        if (algo == NULL) {
            XFREE(curve, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(pub,   key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            return MEMORY_E;
        }
#endif
        algoSz  = SetAlgoID(ECDSAk, algo, oidKeyType, curveSz);

        bitStringSz = SetBitString(pubSz, 0, bitString);

        idx = SetSequence(pubSz + curveSz + bitStringSz + algoSz, output);
        /* algo */
        if (output)
            XMEMCPY(output + idx, algo, algoSz);
        idx += algoSz;
        /* curve */
        if (output)
            XMEMCPY(output + idx, curve, curveSz);
        idx += curveSz;
        /* bit string */
        if (output)
            XMEMCPY(output + idx, bitString, bitStringSz);
        idx += bitStringSz;
    }
    else
        idx = 0;

    /* pub */
    if (output)
        XMEMCPY(output + idx, pub, pubSz);
    idx += pubSz;

#ifdef WOLFSSL_SMALL_STACK
    if (with_header) {
        XFREE(algo,  key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(curve, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    }
    XFREE(pub,   key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return idx;
}


/* returns the size of buffer used, the public ECC key in DER format is stored
   in output buffer
   with_AlgCurve is a flag for when to include a header that has the Algorithm
   and Curve information */
int wc_EccPublicKeyToDer(ecc_key* key, byte* output, word32 inLen,
                                                              int with_AlgCurve)
{
    word32 infoSz = 0;
    word32 keySz  = 0;
    int ret;

    if (key == NULL) {
        return BAD_FUNC_ARG;
    }

    if (with_AlgCurve) {
        /* buffer space for algorithm/curve */
        infoSz += MAX_SEQ_SZ;
        infoSz += 2 * MAX_ALGO_SZ;

        /* buffer space for public key sequence */
        infoSz += MAX_SEQ_SZ;
        infoSz += TRAILING_ZERO;
    }

#if defined(HAVE_SELFTEST) || defined(HAVE_FIPS)
    /* older version of ecc.c can not handle dp being NULL */
    if (key != NULL && key->dp == NULL) {
        keySz = 1 + 2 * MAX_ECC_BYTES;
        ret = LENGTH_ONLY_E;
    }
    else {
        ret = wc_ecc_export_x963(key, NULL, &keySz);
    }
#else
    ret = wc_ecc_export_x963(key, NULL, &keySz);
#endif
    if (ret != LENGTH_ONLY_E) {
        WOLFSSL_MSG("Error in getting ECC public key size");
        return ret;
    }

    /* if output null then just return size */
    if (output == NULL) {
        return keySz + infoSz;
    }

    if (inLen < keySz + infoSz) {
        return BUFFER_E;
    }

    return SetEccPublicKey(output, key, with_AlgCurve);
}

int wc_EccPublicKeyDerSize(ecc_key* key, int with_AlgCurve)
{
    return wc_EccPublicKeyToDer(key, NULL, 0, with_AlgCurve);
}

#endif /* HAVE_ECC && HAVE_ECC_KEY_EXPORT */

#if defined(HAVE_ED25519) && (defined(WOLFSSL_CERT_GEN) || \
                              defined(WOLFSSL_KEY_GEN))

/* Write a public ECC key to output */
static int SetEd25519PublicKey(byte* output, ed25519_key* key, int with_header)
{
    byte bitString[1 + MAX_LENGTH_SZ + 1];
    int  algoSz;
    int  bitStringSz;
    int  idx;
    word32 pubSz = ED25519_PUB_KEY_SIZE;
#ifdef WOLFSSL_SMALL_STACK
    byte* algo = NULL;
    byte* pub;
#else
    byte algo[MAX_ALGO_SZ];
    byte pub[ED25519_PUB_KEY_SIZE];
#endif

#ifdef WOLFSSL_SMALL_STACK
    pub = (byte*)XMALLOC(ECC_BUFSIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (pub == NULL)
        return MEMORY_E;
#endif

    idx = wc_ed25519_export_public(key, pub, &pubSz);
    if (idx != 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(pub, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return idx;
    }

    /* headers */
    if (with_header) {
#ifdef WOLFSSL_SMALL_STACK
        algo = (byte*)XMALLOC(MAX_ALGO_SZ, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (algo == NULL) {
            XFREE(pub, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            return MEMORY_E;
        }
#endif
        algoSz  = SetAlgoID(ED25519k, algo, oidKeyType, 0);

        bitStringSz = SetBitString(pubSz, 0, bitString);

        idx = SetSequence(pubSz + bitStringSz + algoSz, output);
        /* algo */
        XMEMCPY(output + idx, algo, algoSz);
        idx += algoSz;
        /* bit string */
        XMEMCPY(output + idx, bitString, bitStringSz);
        idx += bitStringSz;
    }
    else
        idx = 0;

    /* pub */
    XMEMCPY(output + idx, pub, pubSz);
    idx += pubSz;

#ifdef WOLFSSL_SMALL_STACK
    if (with_header) {
        XFREE(algo, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
    XFREE(pub, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return idx;
}

int wc_Ed25519PublicKeyToDer(ed25519_key* key, byte* output, word32 inLen,
                                                                    int withAlg)
{
    word32 infoSz = 0;
    word32 keySz  = 0;
    int ret;

    if (output == NULL || key == NULL) {
        return BAD_FUNC_ARG;
    }

    if (withAlg) {
        /* buffer space for algorithm */
        infoSz += MAX_SEQ_SZ;
        infoSz += MAX_ALGO_SZ;

        /* buffer space for public key sequence */
        infoSz += MAX_SEQ_SZ;
        infoSz += TRAILING_ZERO;
    }

    if ((ret = wc_ed25519_export_public(key, output, &keySz)) != BUFFER_E) {
        WOLFSSL_MSG("Error in getting ECC public key size");
        return ret;
    }

    if (inLen < keySz + infoSz) {
        return BUFFER_E;
    }

    return SetEd25519PublicKey(output, key, withAlg);
}
#endif /* HAVE_ED25519 && (WOLFSSL_CERT_GEN || WOLFSSL_KEY_GEN) */
#if defined(HAVE_ED448) && (defined(WOLFSSL_CERT_GEN) || \
                                                       defined(WOLFSSL_KEY_GEN))

/* Write a public ECC key to output */
static int SetEd448PublicKey(byte* output, ed448_key* key, int with_header)
{
    byte bitString[1 + MAX_LENGTH_SZ + 1];
    int  algoSz;
    int  bitStringSz;
    int  idx;
    word32 pubSz = ED448_PUB_KEY_SIZE;
#ifdef WOLFSSL_SMALL_STACK
    byte* algo = NULL;
    byte* pub = NULL;
#else
    byte algo[MAX_ALGO_SZ];
    byte pub[ED448_PUB_KEY_SIZE];
#endif

#ifdef WOLFSSL_SMALL_STACK
    pub = (byte*)XMALLOC(ECC_BUFSIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (pub == NULL)
        return MEMORY_E;
#endif

    idx = wc_ed448_export_public(key, pub, &pubSz);
    if (idx != 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(pub, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return idx;
    }

    /* headers */
    if (with_header) {
#ifdef WOLFSSL_SMALL_STACK
        algo = (byte*)XMALLOC(MAX_ALGO_SZ, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (algo == NULL) {
            XFREE(pub, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            return MEMORY_E;
        }
#endif
        algoSz  = SetAlgoID(ED448k, algo, oidKeyType, 0);

        bitStringSz = SetBitString(pubSz, 0, bitString);

        idx = SetSequence(pubSz + bitStringSz + algoSz, output);
        /* algo */
        XMEMCPY(output + idx, algo, algoSz);
        idx += algoSz;
        /* bit string */
        XMEMCPY(output + idx, bitString, bitStringSz);
        idx += bitStringSz;
    }
    else
        idx = 0;

    /* pub */
    XMEMCPY(output + idx, pub, pubSz);
    idx += pubSz;

#ifdef WOLFSSL_SMALL_STACK
    if (with_header) {
        XFREE(algo, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
    XFREE(pub, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return idx;
}

int wc_Ed448PublicKeyToDer(ed448_key* key, byte* output, word32 inLen,
                                                                    int withAlg)
{
    word32 infoSz = 0;
    word32 keySz  = 0;
    int ret;

    if (output == NULL || key == NULL) {
        return BAD_FUNC_ARG;
    }

    if (withAlg) {
        /* buffer space for algorithm */
        infoSz += MAX_SEQ_SZ;
        infoSz += MAX_ALGO_SZ;

        /* buffer space for public key sequence */
        infoSz += MAX_SEQ_SZ;
        infoSz += TRAILING_ZERO;
    }

    if ((ret = wc_ed448_export_public(key, output, &keySz)) != BUFFER_E) {
        WOLFSSL_MSG("Error in getting ECC public key size");
        return ret;
    }

    if (inLen < keySz + infoSz) {
        return BUFFER_E;
    }

    return SetEd448PublicKey(output, key, withAlg);
}
#endif /* HAVE_ED448 && (WOLFSSL_CERT_GEN || WOLFSSL_KEY_GEN) */


#ifdef WOLFSSL_CERT_GEN

static WC_INLINE byte itob(int number)
{
    return (byte)number + 0x30;
}


/* write time to output, format */
static void SetTime(struct tm* date, byte* output)
{
    int i = 0;

    output[i++] = itob((date->tm_year % 10000) / 1000);
    output[i++] = itob((date->tm_year % 1000)  /  100);
    output[i++] = itob((date->tm_year % 100)   /   10);
    output[i++] = itob( date->tm_year % 10);

    output[i++] = itob(date->tm_mon / 10);
    output[i++] = itob(date->tm_mon % 10);

    output[i++] = itob(date->tm_mday / 10);
    output[i++] = itob(date->tm_mday % 10);

    output[i++] = itob(date->tm_hour / 10);
    output[i++] = itob(date->tm_hour % 10);

    output[i++] = itob(date->tm_min / 10);
    output[i++] = itob(date->tm_min % 10);

    output[i++] = itob(date->tm_sec / 10);
    output[i++] = itob(date->tm_sec % 10);

    output[i] = 'Z';  /* Zulu profile */
}


#ifdef WOLFSSL_ALT_NAMES

/* Copy Dates from cert, return bytes written */
static int CopyValidity(byte* output, Cert* cert)
{
    int seqSz;

    WOLFSSL_ENTER("CopyValidity");

    /* headers and output */
    seqSz = SetSequence(cert->beforeDateSz + cert->afterDateSz, output);
    if (output) {
        XMEMCPY(output + seqSz, cert->beforeDate, cert->beforeDateSz);
        XMEMCPY(output + seqSz + cert->beforeDateSz, cert->afterDate,
                                                     cert->afterDateSz);
    }
    return seqSz + cert->beforeDateSz + cert->afterDateSz;
}

#endif


/* Set Date validity from now until now + daysValid
 * return size in bytes written to output, 0 on error */
static int SetValidity(byte* output, int daysValid)
{
    byte before[MAX_DATE_SIZE];
    byte  after[MAX_DATE_SIZE];

    int beforeSz;
    int afterSz;
    int seqSz;

    time_t now;
    time_t then;
    struct tm* tmpTime;
    struct tm* expandedTime;
    struct tm localTime;

#if defined(NEED_TMP_TIME)
    /* for use with gmtime_r */
    struct tm tmpTimeStorage;
    tmpTime = &tmpTimeStorage;
#else
    tmpTime = NULL;
#endif
    (void)tmpTime;

    now = XTIME(0);

    /* before now */
    before[0] = ASN_GENERALIZED_TIME;
    beforeSz = SetLength(ASN_GEN_TIME_SZ, before + 1) + 1;  /* gen tag */

    /* subtract 1 day of seconds for more compliance */
    then = now - 86400;
    expandedTime = XGMTIME(&then, tmpTime);
    if (expandedTime == NULL) {
        WOLFSSL_MSG("XGMTIME failed");
        return 0;   /* error */
    }
    localTime = *expandedTime;

    /* adjust */
    localTime.tm_year += 1900;
    localTime.tm_mon +=    1;

    SetTime(&localTime, before + beforeSz);
    beforeSz += ASN_GEN_TIME_SZ;

    after[0] = ASN_GENERALIZED_TIME;
    afterSz  = SetLength(ASN_GEN_TIME_SZ, after + 1) + 1;  /* gen tag */

    /* add daysValid of seconds */
    then = now + (daysValid * (time_t)86400);
    expandedTime = XGMTIME(&then, tmpTime);
    if (expandedTime == NULL) {
        WOLFSSL_MSG("XGMTIME failed");
        return 0;   /* error */
    }
    localTime = *expandedTime;

    /* adjust */
    localTime.tm_year += 1900;
    localTime.tm_mon  +=    1;

    SetTime(&localTime, after + afterSz);
    afterSz += ASN_GEN_TIME_SZ;

    /* headers and output */
    seqSz = SetSequence(beforeSz + afterSz, output);
    XMEMCPY(output + seqSz, before, beforeSz);
    XMEMCPY(output + seqSz + beforeSz, after, afterSz);

    return seqSz + beforeSz + afterSz;
}


/* ASN Encoded Name field */
typedef struct EncodedName {
    int  nameLen;                /* actual string value length */
    int  totalLen;               /* total encoded length */
    int  type;                   /* type of name */
    int  used;                   /* are we actually using this one */
    byte encoded[CTC_NAME_SIZE * 2]; /* encoding */
} EncodedName;


/* Get Which Name from index */
const char* GetOneCertName(CertName* name, int idx)
{
    switch (idx) {
    case 0:
       return name->country;

    case 1:
       return name->state;

    case 2:
       return name->locality;

    case 3:
       return name->sur;

    case 4:
       return name->org;

    case 5:
       return name->unit;

    case 6:
       return name->commonName;

    case 7:
       return name->serialDev;

#ifdef WOLFSSL_CERT_EXT
    case 8:
       return name->busCat;

    case 9:
#else
    case 8:
#endif
       return name->email;

    default:
       return 0;
    }
}


/* Get Which Name Encoding from index */
static char GetNameType(CertName* name, int idx)
{
    switch (idx) {
    case 0:
       return name->countryEnc;

    case 1:
       return name->stateEnc;

    case 2:
       return name->localityEnc;

    case 3:
       return name->surEnc;

    case 4:
       return name->orgEnc;

    case 5:
       return name->unitEnc;

    case 6:
       return name->commonNameEnc;

    case 7:
       return name->serialDevEnc;

#ifdef WOLFSSL_CERT_EXT
    case 8:
       return name->busCatEnc;

    case 9:
#else
    case 8:
#endif
        /* FALL THROUGH */
        /* The last index, email name, does not have encoding type.
           The empty case here is to keep track of it for future reference. */
    default:
       return 0;
    }
}


/* Get ASN Name from index */
byte GetCertNameId(int idx)
{
    switch (idx) {
    case 0:
       return ASN_COUNTRY_NAME;

    case 1:
       return ASN_STATE_NAME;

    case 2:
       return ASN_LOCALITY_NAME;

    case 3:
       return ASN_SUR_NAME;

    case 4:
       return ASN_ORG_NAME;

    case 5:
       return ASN_ORGUNIT_NAME;

    case 6:
       return ASN_COMMON_NAME;

    case 7:
       return ASN_SERIAL_NUMBER;

#ifdef WOLFSSL_CERT_EXT
    case 8:
        return ASN_BUS_CAT;

    case 9:
#else
    case 8:
#endif
        return ASN_EMAIL_NAME;

    default:
       return 0;
    }
}


/*
 Extensions ::= SEQUENCE OF Extension

 Extension ::= SEQUENCE {
 extnId     OBJECT IDENTIFIER,
 critical   BOOLEAN DEFAULT FALSE,
 extnValue  OCTET STRING }
 */

/* encode all extensions, return total bytes written */
static int SetExtensions(byte* out, word32 outSz, int *IdxInOut,
                         const byte* ext, int extSz)
{
    if (out == NULL || IdxInOut == NULL || ext == NULL)
        return BAD_FUNC_ARG;

    if (outSz < (word32)(*IdxInOut+extSz))
        return BUFFER_E;

    XMEMCPY(&out[*IdxInOut], ext, extSz);  /* extensions */
    *IdxInOut += extSz;

    return *IdxInOut;
}

/* encode extensions header, return total bytes written */
static int SetExtensionsHeader(byte* out, word32 outSz, int extSz)
{
    byte sequence[MAX_SEQ_SZ];
    byte len[MAX_LENGTH_SZ];
    int seqSz, lenSz, idx = 0;

    if (out == NULL)
        return BAD_FUNC_ARG;

    if (outSz < 3)
        return BUFFER_E;

    seqSz = SetSequence(extSz, sequence);

    /* encode extensions length provided */
    lenSz = SetLength(extSz+seqSz, len);

    if (outSz < (word32)(lenSz+seqSz+1))
        return BUFFER_E;

    out[idx++] = ASN_EXTENSIONS; /* extensions id */
    XMEMCPY(&out[idx], len, lenSz);  /* length */
    idx += lenSz;

    XMEMCPY(&out[idx], sequence, seqSz);  /* sequence */
    idx += seqSz;

    return idx;
}


/* encode CA basic constraint true, return total bytes written */
static int SetCa(byte* out, word32 outSz)
{
    const byte ca[] = { 0x30, 0x0c, 0x06, 0x03, 0x55, 0x1d, 0x13, 0x04,
                               0x05, 0x30, 0x03, 0x01, 0x01, 0xff };

    if (out == NULL)
        return BAD_FUNC_ARG;

    if (outSz < sizeof(ca))
        return BUFFER_E;

    XMEMCPY(out, ca, sizeof(ca));

    return (int)sizeof(ca);
}


#ifdef WOLFSSL_CERT_EXT
/* encode OID and associated value, return total bytes written */
static int SetOidValue(byte* out, word32 outSz, const byte *oid, word32 oidSz,
                       byte *in, word32 inSz)
{
    int idx = 0;

    if (out == NULL || oid == NULL || in == NULL)
        return BAD_FUNC_ARG;

    if (outSz < 3)
        return BUFFER_E;

    /* sequence,  + 1 => byte to put value size */
    idx = SetSequence(inSz + oidSz + 1, out);

    if ((idx + inSz + oidSz + 1) > outSz)
        return BUFFER_E;

    XMEMCPY(out+idx, oid, oidSz);
    idx += oidSz;
    out[idx++] = (byte)inSz;
    XMEMCPY(out+idx, in, inSz);

    return (idx+inSz);
}

/* encode Subject Key Identifier, return total bytes written
 * RFC5280 : non-critical */
static int SetSKID(byte* output, word32 outSz, const byte *input, word32 length)
{
    byte skid_len[1 + MAX_LENGTH_SZ];
    byte skid_enc_len[MAX_LENGTH_SZ];
    int idx = 0, skid_lenSz, skid_enc_lenSz;
    const byte skid_oid[] = { 0x06, 0x03, 0x55, 0x1d, 0x0e, 0x04 };

    if (output == NULL || input == NULL)
        return BAD_FUNC_ARG;

    /* Octet String header */
    skid_lenSz = SetOctetString(length, skid_len);

    /* length of encoded value */
    skid_enc_lenSz = SetLength(length + skid_lenSz, skid_enc_len);

    if (outSz < 3)
        return BUFFER_E;

    idx = SetSequence(length + sizeof(skid_oid) + skid_lenSz + skid_enc_lenSz,
                      output);

    if ((length + sizeof(skid_oid) + skid_lenSz + skid_enc_lenSz) > outSz)
        return BUFFER_E;

    /* put oid */
    XMEMCPY(output+idx, skid_oid, sizeof(skid_oid));
    idx += sizeof(skid_oid);

    /* put encoded len */
    XMEMCPY(output+idx, skid_enc_len, skid_enc_lenSz);
    idx += skid_enc_lenSz;

    /* put octet header */
    XMEMCPY(output+idx, skid_len, skid_lenSz);
    idx += skid_lenSz;

    /* put value */
    XMEMCPY(output+idx, input, length);
    idx += length;

    return idx;
}

/* encode Authority Key Identifier, return total bytes written
 * RFC5280 : non-critical */
static int SetAKID(byte* output, word32 outSz,
                                         byte *input, word32 length, void* heap)
{
    byte    *enc_val;
    int     ret, enc_valSz;
    const byte akid_oid[] = { 0x06, 0x03, 0x55, 0x1d, 0x23, 0x04 };
    const byte akid_cs[] = { 0x80 };

    (void)heap;

    if (output == NULL || input == NULL)
        return BAD_FUNC_ARG;

    enc_valSz = length + 3 + sizeof(akid_cs);
    enc_val = (byte *)XMALLOC(enc_valSz, heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (enc_val == NULL)
        return MEMORY_E;

    /* sequence for ContentSpec & value */
    ret = SetOidValue(enc_val, enc_valSz, akid_cs, sizeof(akid_cs),
                      input, length);
    if (ret > 0) {
        enc_valSz = ret;

        ret = SetOidValue(output, outSz, akid_oid, sizeof(akid_oid),
                          enc_val, enc_valSz);
    }

    XFREE(enc_val, heap, DYNAMIC_TYPE_TMP_BUFFER);
    return ret;
}

/* encode Key Usage, return total bytes written
 * RFC5280 : critical */
static int SetKeyUsage(byte* output, word32 outSz, word16 input)
{
    byte ku[5];
    int  idx;
    const byte keyusage_oid[] = { 0x06, 0x03, 0x55, 0x1d, 0x0f,
                                         0x01, 0x01, 0xff, 0x04};
    if (output == NULL)
        return BAD_FUNC_ARG;

    idx = SetBitString16Bit(input, ku);
    return SetOidValue(output, outSz, keyusage_oid, sizeof(keyusage_oid),
                       ku, idx);
}

static int SetOjectIdValue(byte* output, word32 outSz, int* idx,
    const byte* oid, word32 oidSz)
{
    /* verify room */
    if (*idx + 2 + oidSz >= outSz)
        return ASN_PARSE_E;

    *idx += SetObjectId(oidSz, &output[*idx]);
    XMEMCPY(&output[*idx], oid, oidSz);
    *idx += oidSz;

    return 0;
}

/* encode Extended Key Usage (RFC 5280 4.2.1.12), return total bytes written */
static int SetExtKeyUsage(Cert* cert, byte* output, word32 outSz, byte input)
{
    int idx = 0, oidListSz = 0, totalSz, ret = 0;
    const byte extkeyusage_oid[] = { 0x06, 0x03, 0x55, 0x1d, 0x25 };

    if (output == NULL)
        return BAD_FUNC_ARG;

    /* Skip to OID List */
    totalSz = 2 + sizeof(extkeyusage_oid) + 4;
    idx = totalSz;

    /* Build OID List */
    /* If any set, then just use it */
    if (input & EXTKEYUSE_ANY) {
        ret |= SetOjectIdValue(output, outSz, &idx,
            extExtKeyUsageAnyOid, sizeof(extExtKeyUsageAnyOid));
    }
    else {
        if (input & EXTKEYUSE_SERVER_AUTH)
            ret |= SetOjectIdValue(output, outSz, &idx,
                extExtKeyUsageServerAuthOid, sizeof(extExtKeyUsageServerAuthOid));
        if (input & EXTKEYUSE_CLIENT_AUTH)
            ret |= SetOjectIdValue(output, outSz, &idx,
                extExtKeyUsageClientAuthOid, sizeof(extExtKeyUsageClientAuthOid));
        if (input & EXTKEYUSE_CODESIGN)
            ret |= SetOjectIdValue(output, outSz, &idx,
                extExtKeyUsageCodeSigningOid, sizeof(extExtKeyUsageCodeSigningOid));
        if (input & EXTKEYUSE_EMAILPROT)
            ret |= SetOjectIdValue(output, outSz, &idx,
                extExtKeyUsageEmailProtectOid, sizeof(extExtKeyUsageEmailProtectOid));
        if (input & EXTKEYUSE_TIMESTAMP)
            ret |= SetOjectIdValue(output, outSz, &idx,
                extExtKeyUsageTimestampOid, sizeof(extExtKeyUsageTimestampOid));
        if (input & EXTKEYUSE_OCSP_SIGN)
            ret |= SetOjectIdValue(output, outSz, &idx,
                extExtKeyUsageOcspSignOid, sizeof(extExtKeyUsageOcspSignOid));
    #ifdef WOLFSSL_EKU_OID
        /* iterate through OID values */
        if (input & EXTKEYUSE_USER) {
            int i, sz;
            for (i = 0; i < CTC_MAX_EKU_NB; i++) {
                sz = cert->extKeyUsageOIDSz[i];
                if (sz > 0) {
                    ret |= SetOjectIdValue(output, outSz, &idx,
                        cert->extKeyUsageOID[i], sz);
                }
            }
        }
    #endif /* WOLFSSL_EKU_OID */
    }
    if (ret != 0)
        return ASN_PARSE_E;

    /* Calculate Sizes */
    oidListSz = idx - totalSz;
    totalSz = idx - 2; /* exclude first seq/len (2) */

    /* 1. Seq + Total Len (2) */
    idx = SetSequence(totalSz, output);

    /* 2. Object ID (2) */
    XMEMCPY(&output[idx], extkeyusage_oid, sizeof(extkeyusage_oid));
    idx += sizeof(extkeyusage_oid);

    /* 3. Octet String (2) */
    idx += SetOctetString(totalSz - idx, &output[idx]);

    /* 4. Seq + OidListLen (2) */
    idx += SetSequence(oidListSz, &output[idx]);

    /* 5. Oid List (already set in-place above) */
    idx += oidListSz;

    (void)cert;
    return idx;
}

/* encode Certificate Policies, return total bytes written
 * each input value must be ITU-T X.690 formatted : a.b.c...
 * input must be an array of values with a NULL terminated for the latest
 * RFC5280 : non-critical */
static int SetCertificatePolicies(byte *output,
                                  word32 outputSz,
                                  char input[MAX_CERTPOL_NB][MAX_CERTPOL_SZ],
                                  word16 nb_certpol,
                                  void* heap)
{
    byte    oid[MAX_OID_SZ],
            der_oid[MAX_CERTPOL_NB][MAX_OID_SZ],
            out[MAX_CERTPOL_SZ];
    word32  oidSz;
    word32  outSz, i = 0, der_oidSz[MAX_CERTPOL_NB];
    int     ret;

    const byte certpol_oid[] = { 0x06, 0x03, 0x55, 0x1d, 0x20, 0x04 };
    const byte oid_oid[] = { 0x06 };

    if (output == NULL || input == NULL || nb_certpol > MAX_CERTPOL_NB)
        return BAD_FUNC_ARG;

    for (i = 0; i < nb_certpol; i++) {
        oidSz = sizeof(oid);
        XMEMSET(oid, 0, oidSz);

        ret = EncodePolicyOID(oid, &oidSz, input[i], heap);
        if (ret != 0)
            return ret;

        /* compute sequence value for the oid */
        ret = SetOidValue(der_oid[i], MAX_OID_SZ, oid_oid,
                          sizeof(oid_oid), oid, oidSz);
        if (ret <= 0)
            return ret;
        else
            der_oidSz[i] = (word32)ret;
    }

    /* concatenate oid, keep two byte for sequence/size of the created value */
    for (i = 0, outSz = 2; i < nb_certpol; i++) {
        XMEMCPY(out+outSz, der_oid[i], der_oidSz[i]);
        outSz += der_oidSz[i];
    }

    /* add sequence */
    ret = SetSequence(outSz-2, out);
    if (ret <= 0)
        return ret;

    /* add Policy OID to compute final value */
    return SetOidValue(output, outputSz, certpol_oid, sizeof(certpol_oid),
                      out, outSz);
}
#endif /* WOLFSSL_CERT_EXT */


#ifdef WOLFSSL_ALT_NAMES

/* encode Alternative Names, return total bytes written */
static int SetAltNames(byte *output, word32 outSz,
        const byte *input, word32 length)
{
    byte san_len[1 + MAX_LENGTH_SZ];
    int idx = 0, san_lenSz;
    const byte san_oid[] = { 0x06, 0x03, 0x55, 0x1d, 0x11 };

    if (output == NULL || input == NULL)
        return BAD_FUNC_ARG;

    if (outSz < length)
        return BUFFER_E;

    /* Octet String header */
    san_lenSz = SetOctetString(length, san_len);

    if (outSz < MAX_SEQ_SZ)
        return BUFFER_E;

    idx = SetSequence(length + sizeof(san_oid) + san_lenSz, output);

    if ((length + sizeof(san_oid) + san_lenSz) > outSz)
        return BUFFER_E;

    /* put oid */
    XMEMCPY(output+idx, san_oid, sizeof(san_oid));
    idx += sizeof(san_oid);

    /* put octet header */
    XMEMCPY(output+idx, san_len, san_lenSz);
    idx += san_lenSz;

    /* put value */
    XMEMCPY(output+idx, input, length);
    idx += length;

    return idx;
}


#ifdef WOLFSSL_CERT_GEN

int FlattenAltNames(byte* output, word32 outputSz, const DNS_entry* names)
{
    word32 idx;
    const DNS_entry* curName;
    word32 namesSz = 0;

    if (output == NULL)
        return BAD_FUNC_ARG;

    if (names == NULL)
        return 0;

    curName = names;
    do {
        namesSz += curName->len + 2 +
            ((curName->len < ASN_LONG_LENGTH) ? 0
             : BytePrecision(curName->len));
        curName = curName->next;
    } while (curName != NULL);

    if (outputSz < MAX_SEQ_SZ + namesSz)
        return BUFFER_E;

    idx = SetSequence(namesSz, output);

    curName = names;
    do {
        output[idx++] = ASN_CONTEXT_SPECIFIC | curName->type;
        idx += SetLength(curName->len, output + idx);
        XMEMCPY(output + idx, curName->name, curName->len);
        idx += curName->len;
        curName = curName->next;
    } while (curName != NULL);

    return idx;
}

#endif /* WOLFSSL_CERT_GEN */

#endif /* WOLFSSL_ALT_NAMES */

/* Encodes one attribute of the name (issuer/subject)
 *
 * name     structure to hold result of encoding
 * nameStr  value to be encoded
 * nameType type of encoding i.e CTC_UTF8
 * type     id of attribute i.e ASN_COMMON_NAME
 *
 * returns length on success
 */
static int wc_EncodeName(EncodedName* name, const char* nameStr, char nameType,
        byte type)
{
    word32 idx = 0;

    if (nameStr) {
        /* bottom up */
        byte firstLen[1 + MAX_LENGTH_SZ];
        byte secondLen[MAX_LENGTH_SZ];
        byte sequence[MAX_SEQ_SZ];
        byte set[MAX_SET_SZ];

        int strLen  = (int)XSTRLEN(nameStr);
        int thisLen = strLen;
        int firstSz, secondSz, seqSz, setSz;

        if (strLen == 0) { /* no user data for this item */
            name->used = 0;
            return 0;
        }

        /* Restrict country code size */
        if (ASN_COUNTRY_NAME == type && strLen != CTC_COUNTRY_SIZE) {
            WOLFSSL_MSG("Country code size error");
            return ASN_COUNTRY_SIZE_E;
        }

        secondSz = SetLength(strLen, secondLen);
        thisLen += secondSz;
        switch (type) {
            case ASN_EMAIL_NAME: /* email */
                thisLen += EMAIL_JOINT_LEN;
                firstSz  = EMAIL_JOINT_LEN;
                break;

            case ASN_DOMAIN_COMPONENT:
                thisLen += PILOT_JOINT_LEN;
                firstSz  = PILOT_JOINT_LEN;
                break;

            default:
                thisLen++;                                 /* str type */
                thisLen += JOINT_LEN;
                firstSz  = JOINT_LEN + 1;
        }
        thisLen++; /* id  type */
        firstSz  = SetObjectId(firstSz, firstLen);
        thisLen += firstSz;

        seqSz = SetSequence(thisLen, sequence);
        thisLen += seqSz;
        setSz = SetSet(thisLen, set);
        thisLen += setSz;

        if (thisLen > (int)sizeof(name->encoded)) {
            return BUFFER_E;
        }

        /* store it */
        idx = 0;
        /* set */
        XMEMCPY(name->encoded, set, setSz);
        idx += setSz;
        /* seq */
        XMEMCPY(name->encoded + idx, sequence, seqSz);
        idx += seqSz;
        /* asn object id */
        XMEMCPY(name->encoded + idx, firstLen, firstSz);
        idx += firstSz;
        switch (type) {
            case ASN_EMAIL_NAME:
                {
                    const byte EMAIL_OID[] = { 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d,
                                       0x01, 0x09, 0x01, 0x16 };
                    /* email joint id */
                    XMEMCPY(name->encoded + idx, EMAIL_OID, sizeof(EMAIL_OID));
                    idx += (int)sizeof(EMAIL_OID);
                }
                break;

            case ASN_DOMAIN_COMPONENT:
                {
                    const byte PILOT_OID[] = { 0x09, 0x92, 0x26, 0x89,
                                    0x93, 0xF2, 0x2C, 0x64, 0x01
                    };

                    XMEMCPY(name->encoded + idx, PILOT_OID,
                                                     sizeof(PILOT_OID));
                    idx += (int)sizeof(PILOT_OID);
                    /* id type */
                    name->encoded[idx++] = type;
                    /* str type */
                    name->encoded[idx++] = nameType;
                }
                break;

            default:
                name->encoded[idx++] = 0x55;
                name->encoded[idx++] = 0x04;
                /* id type */
                name->encoded[idx++] = type;
                /* str type */
                name->encoded[idx++] = nameType;
        }
        /* second length */
        XMEMCPY(name->encoded + idx, secondLen, secondSz);
        idx += secondSz;
        /* str value */
        XMEMCPY(name->encoded + idx, nameStr, strLen);
        idx += strLen;

        name->type = type;
        name->totalLen = idx;
        name->used = 1;
    }
    else
        name->used = 0;

    return idx;
}

/* encode CertName into output, return total bytes written */
int SetName(byte* output, word32 outputSz, CertName* name)
{
    int          totalBytes = 0, i, idx;
#ifdef WOLFSSL_SMALL_STACK
    EncodedName* names = NULL;
#else
    EncodedName  names[NAME_ENTRIES];
#endif
#ifdef WOLFSSL_MULTI_ATTRIB
    EncodedName addNames[CTC_MAX_ATTRIB];
    int j, type;
#endif

    if (output == NULL || name == NULL)
        return BAD_FUNC_ARG;

    if (outputSz < 3)
        return BUFFER_E;

#ifdef WOLFSSL_SMALL_STACK
    names = (EncodedName*)XMALLOC(sizeof(EncodedName) * NAME_ENTRIES, NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (names == NULL)
        return MEMORY_E;
#endif

    for (i = 0; i < NAME_ENTRIES; i++) {
        int ret;
        const char* nameStr = GetOneCertName(name, i);

        ret = wc_EncodeName(&names[i], nameStr, GetNameType(name, i),
                          GetCertNameId(i));
        if (ret < 0) {
        #ifdef WOLFSSL_SMALL_STACK
            XFREE(names, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        #endif
            WOLFSSL_MSG("EncodeName failed");
            return BUFFER_E;
        }
        totalBytes += ret;
    }
#ifdef WOLFSSL_MULTI_ATTRIB
    for (i = 0; i < CTC_MAX_ATTRIB; i++) {
        if (name->name[i].sz > 0) {
            int ret;
            ret = wc_EncodeName(&addNames[i], name->name[i].value,
                        name->name[i].type, name->name[i].id);
            if (ret < 0) {
            #ifdef WOLFSSL_SMALL_STACK
                XFREE(names, NULL, DYNAMIC_TYPE_TMP_BUFFER);
            #endif
                WOLFSSL_MSG("EncodeName on multiple attributes failed\n");
                return BUFFER_E;
            }
            totalBytes += ret;
        }
        else {
            addNames[i].used = 0;
        }
    }
#endif /* WOLFSSL_MULTI_ATTRIB */

    /* header */
    idx = SetSequence(totalBytes, output);
    totalBytes += idx;
    if (totalBytes > ASN_NAME_MAX) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(names, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        WOLFSSL_MSG("Total Bytes is greater than ASN_NAME_MAX");
        return BUFFER_E;
    }

    for (i = 0; i < NAME_ENTRIES; i++) {
    #ifdef WOLFSSL_MULTI_ATTRIB
        type = GetCertNameId(i);

        /* list all DC values before OUs */
        if (type == ASN_ORGUNIT_NAME) {
            type = ASN_DOMAIN_COMPONENT;
            for (j = 0; j < CTC_MAX_ATTRIB; j++) {
                if (name->name[j].sz > 0 && type == name->name[j].id) {
                    if (outputSz < (word32)(idx+addNames[j].totalLen)) {
                    #ifdef WOLFSSL_SMALL_STACK
                        XFREE(names, NULL, DYNAMIC_TYPE_TMP_BUFFER);
                    #endif
                        WOLFSSL_MSG("Not enough space left for DC value");
                        return BUFFER_E;
                    }

                    XMEMCPY(output + idx, addNames[j].encoded,
                            addNames[j].totalLen);
                    idx += addNames[j].totalLen;
                }
            }
            type = ASN_ORGUNIT_NAME;
        }

        /* write all similar types to the buffer */
        for (j = 0; j < CTC_MAX_ATTRIB; j++) {
            if (name->name[j].sz > 0 && type == name->name[j].id) {
                if (outputSz < (word32)(idx+addNames[j].totalLen)) {
                #ifdef WOLFSSL_SMALL_STACK
                    XFREE(names, NULL, DYNAMIC_TYPE_TMP_BUFFER);
                #endif
                    return BUFFER_E;
                }

                XMEMCPY(output + idx, addNames[j].encoded,
                        addNames[j].totalLen);
                idx += addNames[j].totalLen;
            }
        }
    #endif /* WOLFSSL_MULTI_ATTRIB */

        if (names[i].used) {
            if (outputSz < (word32)(idx+names[i].totalLen)) {
#ifdef WOLFSSL_SMALL_STACK
                XFREE(names, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return BUFFER_E;
            }

            XMEMCPY(output + idx, names[i].encoded, names[i].totalLen);
            idx += names[i].totalLen;
        }
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(names, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return totalBytes;
}

/* encode info from cert into DER encoded format */
static int EncodeCert(Cert* cert, DerCert* der, RsaKey* rsaKey, ecc_key* eccKey,
                      WC_RNG* rng, const byte* ntruKey, word16 ntruSz,
                      ed25519_key* ed25519Key, ed448_key* ed448Key)
{
    int ret;

    if (cert == NULL || der == NULL || rng == NULL)
        return BAD_FUNC_ARG;

    /* make sure at least one key type is provided */
    if (rsaKey == NULL && eccKey == NULL && ed25519Key == NULL &&
                                          ed448Key == NULL && ntruKey == NULL) {
        return PUBLIC_KEY_E;
    }

    /* init */
    XMEMSET(der, 0, sizeof(DerCert));

    /* version */
    der->versionSz = SetMyVersion(cert->version, der->version, TRUE);

    /* serial number (must be positive) */
    if (cert->serialSz == 0) {
        /* generate random serial */
        cert->serialSz = CTC_GEN_SERIAL_SZ;
        ret = wc_RNG_GenerateBlock(rng, cert->serial, cert->serialSz);
        if (ret != 0)
            return ret;
        /* Clear the top bit to avoid a negative value */
        cert->serial[0] &= 0x7f;
    }
    der->serialSz = SetSerialNumber(cert->serial, cert->serialSz, der->serial,
        sizeof(der->serial), CTC_SERIAL_SIZE);
    if (der->serialSz < 0)
        return der->serialSz;

    /* signature algo */
    der->sigAlgoSz = SetAlgoID(cert->sigType, der->sigAlgo, oidSigType, 0);
    if (der->sigAlgoSz <= 0)
        return ALGO_ID_E;

    /* public key */
#ifndef NO_RSA
    if (cert->keyType == RSA_KEY) {
        if (rsaKey == NULL)
            return PUBLIC_KEY_E;
        der->publicKeySz = SetRsaPublicKey(der->publicKey, rsaKey,
                                           sizeof(der->publicKey), 1);
    }
#endif

#ifdef HAVE_ECC
    if (cert->keyType == ECC_KEY) {
        if (eccKey == NULL)
            return PUBLIC_KEY_E;
        der->publicKeySz = SetEccPublicKey(der->publicKey, eccKey, 1);
    }
#endif

#ifdef HAVE_ED25519
    if (cert->keyType == ED25519_KEY) {
        if (ed25519Key == NULL)
            return PUBLIC_KEY_E;
        der->publicKeySz = SetEd25519PublicKey(der->publicKey, ed25519Key, 1);
    }
#endif

#ifdef HAVE_ED448
    if (cert->keyType == ED448_KEY) {
        if (ed448Key == NULL)
            return PUBLIC_KEY_E;
        der->publicKeySz = SetEd448PublicKey(der->publicKey, ed448Key, 1);
    }
#endif

#ifdef HAVE_NTRU
    if (cert->keyType == NTRU_KEY) {
        word32 rc;
        word16 encodedSz;

        if (ntruKey == NULL)
            return PUBLIC_KEY_E;

        rc  = ntru_crypto_ntru_encrypt_publicKey2SubjectPublicKeyInfo(ntruSz,
                                                   ntruKey, &encodedSz, NULL);
        if (rc != NTRU_OK)
            return PUBLIC_KEY_E;
        if (encodedSz > MAX_PUBLIC_KEY_SZ)
            return PUBLIC_KEY_E;

        rc  = ntru_crypto_ntru_encrypt_publicKey2SubjectPublicKeyInfo(ntruSz,
                                         ntruKey, &encodedSz, der->publicKey);
        if (rc != NTRU_OK)
            return PUBLIC_KEY_E;

        der->publicKeySz = encodedSz;
    }
#else
    (void)ntruSz;
#endif /* HAVE_NTRU */

    if (der->publicKeySz <= 0)
        return PUBLIC_KEY_E;

    der->validitySz = 0;
#ifdef WOLFSSL_ALT_NAMES
    /* date validity copy ? */
    if (cert->beforeDateSz && cert->afterDateSz) {
        der->validitySz = CopyValidity(der->validity, cert);
        if (der->validitySz <= 0)
            return DATE_E;
    }
#endif

    /* date validity */
    if (der->validitySz == 0) {
        der->validitySz = SetValidity(der->validity, cert->daysValid);
        if (der->validitySz <= 0)
            return DATE_E;
    }

    /* subject name */
#ifdef WOLFSSL_CERT_EXT
    if (XSTRLEN((const char*)cert->sbjRaw) > 0) {
        /* Use the raw subject */
        int idx;

        der->subjectSz = min(sizeof(der->subject),
                (word32)XSTRLEN((const char*)cert->sbjRaw));
        /* header */
        idx = SetSequence(der->subjectSz, der->subject);
        if (der->subjectSz + idx > (int)sizeof(der->subject)) {
            return SUBJECT_E;
        }

        XMEMCPY((char*)der->subject + idx, (const char*)cert->sbjRaw,
                der->subjectSz);
        der->subjectSz += idx;
    }
    else
#endif
    {
        /* Use the name structure */
        der->subjectSz = SetName(der->subject, sizeof(der->subject),
                &cert->subject);
    }
    if (der->subjectSz <= 0)
        return SUBJECT_E;

    /* issuer name */
#ifdef WOLFSSL_CERT_EXT
    if (XSTRLEN((const char*)cert->issRaw) > 0) {
        /* Use the raw issuer */
        int idx;

        der->issuerSz = min(sizeof(der->issuer),
                (word32)XSTRLEN((const char*)cert->issRaw));
        /* header */
        idx = SetSequence(der->issuerSz, der->issuer);
        if (der->issuerSz + idx > (int)sizeof(der->issuer)) {
            return ISSUER_E;
        }

        XMEMCPY((char*)der->issuer + idx, (const char*)cert->issRaw,
                der->issuerSz);
        der->issuerSz += idx;
    }
    else
#endif
    {
        /* Use the name structure */
        der->issuerSz = SetName(der->issuer, sizeof(der->issuer),
                cert->selfSigned ? &cert->subject : &cert->issuer);
    }
    if (der->issuerSz <= 0)
        return ISSUER_E;

    /* set the extensions */
    der->extensionsSz = 0;

    /* CA */
    if (cert->isCA) {
        der->caSz = SetCa(der->ca, sizeof(der->ca));
        if (der->caSz <= 0)
            return CA_TRUE_E;

        der->extensionsSz += der->caSz;
    }
    else
        der->caSz = 0;

#ifdef WOLFSSL_ALT_NAMES
    /* Alternative Name */
    if (cert->altNamesSz) {
        der->altNamesSz = SetAltNames(der->altNames, sizeof(der->altNames),
                                      cert->altNames, cert->altNamesSz);
        if (der->altNamesSz <= 0)
            return ALT_NAME_E;

        der->extensionsSz += der->altNamesSz;
    }
    else
        der->altNamesSz = 0;
#endif

#ifdef WOLFSSL_CERT_EXT
    /* SKID */
    if (cert->skidSz) {
        /* check the provided SKID size */
        if (cert->skidSz > (int)min(CTC_MAX_SKID_SIZE, sizeof(der->skid)))
            return SKID_E;

        /* Note: different skid buffers sizes for der (MAX_KID_SZ) and
            cert (CTC_MAX_SKID_SIZE). */
        der->skidSz = SetSKID(der->skid, sizeof(der->skid),
                              cert->skid, cert->skidSz);
        if (der->skidSz <= 0)
            return SKID_E;

        der->extensionsSz += der->skidSz;
    }
    else
        der->skidSz = 0;

    /* AKID */
    if (cert->akidSz) {
        /* check the provided AKID size */
        if (cert->akidSz > (int)min(CTC_MAX_AKID_SIZE, sizeof(der->akid)))
            return AKID_E;

        der->akidSz = SetAKID(der->akid, sizeof(der->akid),
                              cert->akid, cert->akidSz, cert->heap);
        if (der->akidSz <= 0)
            return AKID_E;

        der->extensionsSz += der->akidSz;
    }
    else
        der->akidSz = 0;

    /* Key Usage */
    if (cert->keyUsage != 0){
        der->keyUsageSz = SetKeyUsage(der->keyUsage, sizeof(der->keyUsage),
                                      cert->keyUsage);
        if (der->keyUsageSz <= 0)
            return KEYUSAGE_E;

        der->extensionsSz += der->keyUsageSz;
    }
    else
        der->keyUsageSz = 0;

    /* Extended Key Usage */
    if (cert->extKeyUsage != 0){
        der->extKeyUsageSz = SetExtKeyUsage(cert, der->extKeyUsage,
                                sizeof(der->extKeyUsage), cert->extKeyUsage);
        if (der->extKeyUsageSz <= 0)
            return EXTKEYUSAGE_E;

        der->extensionsSz += der->extKeyUsageSz;
    }
    else
        der->extKeyUsageSz = 0;

    /* Certificate Policies */
    if (cert->certPoliciesNb != 0) {
        der->certPoliciesSz = SetCertificatePolicies(der->certPolicies,
                                                     sizeof(der->certPolicies),
                                                     cert->certPolicies,
                                                     cert->certPoliciesNb,
                                                     cert->heap);
        if (der->certPoliciesSz <= 0)
            return CERTPOLICIES_E;

        der->extensionsSz += der->certPoliciesSz;
    }
    else
        der->certPoliciesSz = 0;
#endif /* WOLFSSL_CERT_EXT */

    /* put extensions */
    if (der->extensionsSz > 0) {

        /* put the start of extensions sequence (ID, Size) */
        der->extensionsSz = SetExtensionsHeader(der->extensions,
                                                sizeof(der->extensions),
                                                der->extensionsSz);
        if (der->extensionsSz <= 0)
            return EXTENSIONS_E;

        /* put CA */
        if (der->caSz) {
            ret = SetExtensions(der->extensions, sizeof(der->extensions),
                                &der->extensionsSz,
                                der->ca, der->caSz);
            if (ret == 0)
                return EXTENSIONS_E;
        }

#ifdef WOLFSSL_ALT_NAMES
        /* put Alternative Names */
        if (der->altNamesSz) {
            ret = SetExtensions(der->extensions, sizeof(der->extensions),
                                &der->extensionsSz,
                                der->altNames, der->altNamesSz);
            if (ret <= 0)
                return EXTENSIONS_E;
        }
#endif

#ifdef WOLFSSL_CERT_EXT
        /* put SKID */
        if (der->skidSz) {
            ret = SetExtensions(der->extensions, sizeof(der->extensions),
                                &der->extensionsSz,
                                der->skid, der->skidSz);
            if (ret <= 0)
                return EXTENSIONS_E;
        }

        /* put AKID */
        if (der->akidSz) {
            ret = SetExtensions(der->extensions, sizeof(der->extensions),
                                &der->extensionsSz,
                                der->akid, der->akidSz);
            if (ret <= 0)
                return EXTENSIONS_E;
        }

        /* put KeyUsage */
        if (der->keyUsageSz) {
            ret = SetExtensions(der->extensions, sizeof(der->extensions),
                                &der->extensionsSz,
                                der->keyUsage, der->keyUsageSz);
            if (ret <= 0)
                return EXTENSIONS_E;
        }

        /* put ExtendedKeyUsage */
        if (der->extKeyUsageSz) {
            ret = SetExtensions(der->extensions, sizeof(der->extensions),
                                &der->extensionsSz,
                                der->extKeyUsage, der->extKeyUsageSz);
            if (ret <= 0)
                return EXTENSIONS_E;
        }

        /* put Certificate Policies */
        if (der->certPoliciesSz) {
            ret = SetExtensions(der->extensions, sizeof(der->extensions),
                                &der->extensionsSz,
                                der->certPolicies, der->certPoliciesSz);
            if (ret <= 0)
                return EXTENSIONS_E;
        }
#endif /* WOLFSSL_CERT_EXT */
    }

    der->total = der->versionSz + der->serialSz + der->sigAlgoSz +
        der->publicKeySz + der->validitySz + der->subjectSz + der->issuerSz +
        der->extensionsSz;

    return 0;
}


/* write DER encoded cert to buffer, size already checked */
static int WriteCertBody(DerCert* der, byte* buf)
{
    int idx;

    /* signed part header */
    idx = SetSequence(der->total, buf);
    /* version */
    XMEMCPY(buf + idx, der->version, der->versionSz);
    idx += der->versionSz;
    /* serial */
    XMEMCPY(buf + idx, der->serial, der->serialSz);
    idx += der->serialSz;
    /* sig algo */
    XMEMCPY(buf + idx, der->sigAlgo, der->sigAlgoSz);
    idx += der->sigAlgoSz;
    /* issuer */
    XMEMCPY(buf + idx, der->issuer, der->issuerSz);
    idx += der->issuerSz;
    /* validity */
    XMEMCPY(buf + idx, der->validity, der->validitySz);
    idx += der->validitySz;
    /* subject */
    XMEMCPY(buf + idx, der->subject, der->subjectSz);
    idx += der->subjectSz;
    /* public key */
    XMEMCPY(buf + idx, der->publicKey, der->publicKeySz);
    idx += der->publicKeySz;
    if (der->extensionsSz) {
        /* extensions */
        XMEMCPY(buf + idx, der->extensions, min(der->extensionsSz,
                                                   (int)sizeof(der->extensions)));
        idx += der->extensionsSz;
    }

    return idx;
}


/* Make RSA signature from buffer (sz), write to sig (sigSz) */
static int MakeSignature(CertSignCtx* certSignCtx, const byte* buf, int sz,
    byte* sig, int sigSz, RsaKey* rsaKey, ecc_key* eccKey,
    ed25519_key* ed25519Key, ed448_key* ed448Key, WC_RNG* rng, int sigAlgoType,
    void* heap)
{
    int digestSz = 0, typeH = 0, ret = 0;

    (void)digestSz;
    (void)typeH;
    (void)buf;
    (void)sz;
    (void)sig;
    (void)sigSz;
    (void)rsaKey;
    (void)eccKey;
    (void)ed25519Key;
    (void)ed448Key;
    (void)rng;
    (void)heap;

    switch (certSignCtx->state) {
    case CERTSIGN_STATE_BEGIN:
    case CERTSIGN_STATE_DIGEST:

        certSignCtx->state = CERTSIGN_STATE_DIGEST;
        certSignCtx->digest = (byte*)XMALLOC(WC_MAX_DIGEST_SIZE, heap,
            DYNAMIC_TYPE_TMP_BUFFER);
        if (certSignCtx->digest == NULL) {
            ret = MEMORY_E; goto exit_ms;
        }

        ret = HashForSignature(buf, sz, sigAlgoType, certSignCtx->digest,
                               &typeH, &digestSz, 0);
        /* set next state, since WC_PENDING_E rentry for these are not "call again" */
        certSignCtx->state = CERTSIGN_STATE_ENCODE;
        if (ret != 0) {
            goto exit_ms;
        }
        FALL_THROUGH;

    case CERTSIGN_STATE_ENCODE:
    #ifndef NO_RSA
        if (rsaKey) {
            certSignCtx->encSig = (byte*)XMALLOC(MAX_DER_DIGEST_SZ, heap,
                DYNAMIC_TYPE_TMP_BUFFER);
            if (certSignCtx->encSig == NULL) {
                ret = MEMORY_E; goto exit_ms;
            }

            /* signature */
            certSignCtx->encSigSz = wc_EncodeSignature(certSignCtx->encSig,
                                          certSignCtx->digest, digestSz, typeH);
        }
    #endif /* !NO_RSA */
        FALL_THROUGH;

    case CERTSIGN_STATE_DO:
        certSignCtx->state = CERTSIGN_STATE_DO;
        ret = ALGO_ID_E; /* default to error */

    #ifndef NO_RSA
        if (rsaKey) {
            /* signature */
            ret = wc_RsaSSL_Sign(certSignCtx->encSig, certSignCtx->encSigSz,
                                 sig, sigSz, rsaKey, rng);
        }
    #endif /* !NO_RSA */

    #ifdef HAVE_ECC
        if (!rsaKey && eccKey) {
            word32 outSz = sigSz;

            ret = wc_ecc_sign_hash(certSignCtx->digest, digestSz,
                                   sig, &outSz, rng, eccKey);
            if (ret == 0)
                ret = outSz;
        }
    #endif /* HAVE_ECC */

    #ifdef HAVE_ED25519
        if (!rsaKey && !eccKey && ed25519Key) {
            word32 outSz = sigSz;

            ret = wc_ed25519_sign_msg(buf, sz, sig, &outSz, ed25519Key);
            if (ret == 0)
                ret = outSz;
        }
    #endif /* HAVE_ECC */

    #ifdef HAVE_ED448
        if (!rsaKey && !eccKey && !ed25519Key && ed448Key) {
            word32 outSz = sigSz;

            ret = wc_ed448_sign_msg(buf, sz, sig, &outSz, ed448Key, NULL, 0);
            if (ret == 0)
                ret = outSz;
        }
    #endif /* HAVE_ECC */
        break;
    }

exit_ms:

#ifdef WOLFSSL_ASYNC_CRYPT
    if (ret == WC_PENDING_E) {
        return ret;
    }
#endif

#ifndef NO_RSA
    if (rsaKey) {
        XFREE(certSignCtx->encSig, heap, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif /* !NO_RSA */

    XFREE(certSignCtx->digest, heap, DYNAMIC_TYPE_TMP_BUFFER);
    certSignCtx->digest = NULL;

    /* reset state */
    certSignCtx->state = CERTSIGN_STATE_BEGIN;

    return ret;
}


/* add signature to end of buffer, size of buffer assumed checked, return
   new length */
static int AddSignature(byte* buf, int bodySz, const byte* sig, int sigSz,
                        int sigAlgoType)
{
    byte seq[MAX_SEQ_SZ];
    int  idx = bodySz, seqSz;

    /* algo */
    idx += SetAlgoID(sigAlgoType, buf ? buf + idx : NULL, oidSigType, 0);
    /* bit string */
    idx += SetBitString(sigSz, 0, buf ? buf + idx : NULL);
    /* signature */
    if (buf)
        XMEMCPY(buf + idx, sig, sigSz);
    idx += sigSz;

    /* make room for overall header */
    seqSz = SetSequence(idx, seq);
    if (buf) {
        XMEMMOVE(buf + seqSz, buf, idx);
        XMEMCPY(buf, seq, seqSz);
    }

    return idx + seqSz;
}


/* Make an x509 Certificate v3 any key type from cert input, write to buffer */
static int MakeAnyCert(Cert* cert, byte* derBuffer, word32 derSz,
                       RsaKey* rsaKey, ecc_key* eccKey, WC_RNG* rng,
                       const byte* ntruKey, word16 ntruSz,
                       ed25519_key* ed25519Key, ed448_key* ed448Key)
{
    int ret;
#ifdef WOLFSSL_SMALL_STACK
    DerCert* der;
#else
    DerCert der[1];
#endif

    if (derBuffer == NULL) {
        return BAD_FUNC_ARG;
    }

    cert->keyType = eccKey ? ECC_KEY : (rsaKey ? RSA_KEY :
            (ed25519Key ? ED25519_KEY : (ed448Key ? ED448_KEY : NTRU_KEY)));

#ifdef WOLFSSL_SMALL_STACK
    der = (DerCert*)XMALLOC(sizeof(DerCert), cert->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (der == NULL)
        return MEMORY_E;
#endif

    ret = EncodeCert(cert, der, rsaKey, eccKey, rng, ntruKey, ntruSz,
                     ed25519Key, ed448Key);
    if (ret == 0) {
        if (der->total + MAX_SEQ_SZ * 2 > (int)derSz)
            ret = BUFFER_E;
        else
            ret = cert->bodySz = WriteCertBody(der, derBuffer);
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(der, cert->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}


/* Make an x509 Certificate v3 RSA or ECC from cert input, write to buffer */
int wc_MakeCert_ex(Cert* cert, byte* derBuffer, word32 derSz, int keyType,
                   void* key, WC_RNG* rng)
{
    RsaKey*      rsaKey = NULL;
    ecc_key*     eccKey = NULL;
    ed25519_key* ed25519Key = NULL;
    ed448_key*   ed448Key = NULL;

    if (keyType == RSA_TYPE)
        rsaKey = (RsaKey*)key;
    else if (keyType == ECC_TYPE)
        eccKey = (ecc_key*)key;
    else if (keyType == ED25519_TYPE)
        ed25519Key = (ed25519_key*)key;
    else if (keyType == ED448_TYPE)
        ed448Key = (ed448_key*)key;

    return MakeAnyCert(cert, derBuffer, derSz, rsaKey, eccKey, rng, NULL, 0,
                       ed25519Key, ed448Key);
}
/* Make an x509 Certificate v3 RSA or ECC from cert input, write to buffer */
int wc_MakeCert(Cert* cert, byte* derBuffer, word32 derSz, RsaKey* rsaKey,
             ecc_key* eccKey, WC_RNG* rng)
{
    return MakeAnyCert(cert, derBuffer, derSz, rsaKey, eccKey, rng, NULL, 0,
                       NULL, NULL);
}


#ifdef HAVE_NTRU

int wc_MakeNtruCert(Cert* cert, byte* derBuffer, word32 derSz,
                  const byte* ntruKey, word16 keySz, WC_RNG* rng)
{
    return MakeAnyCert(cert, derBuffer, derSz, NULL, NULL, rng,
            ntruKey, keySz, NULL, NULL);
}

#endif /* HAVE_NTRU */


#ifdef WOLFSSL_CERT_REQ

static int SetReqAttrib(byte* output, char* pw, int pwPrintableString,
                        int extSz)
{
    const byte cpOid[] =
        { ASN_OBJECT_ID, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01,
                         0x09, 0x07 };
    const byte erOid[] =
        { ASN_OBJECT_ID, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01,
                         0x09, 0x0e };

    int sz      = 0; /* overall size */
    int cpSz    = 0; /* Challenge Password section size */
    int cpSeqSz = 0;
    int cpSetSz = 0;
    int cpStrSz = 0;
    int pwSz    = 0;
    int erSz    = 0; /* Extension Request section size */
    int erSeqSz = 0;
    int erSetSz = 0;
    byte cpSeq[MAX_SEQ_SZ];
    byte cpSet[MAX_SET_SZ];
    byte cpStr[MAX_PRSTR_SZ];
    byte erSeq[MAX_SEQ_SZ];
    byte erSet[MAX_SET_SZ];

    output[0] = 0xa0;
    sz++;

    if (pw && pw[0]) {
        pwSz = (int)XSTRLEN(pw);
        if (pwPrintableString) {
            cpStrSz = SetPrintableString(pwSz, cpStr);
        } else {
            cpStrSz = SetUTF8String(pwSz, cpStr);
        }
        cpSetSz = SetSet(cpStrSz + pwSz, cpSet);
        cpSeqSz = SetSequence(sizeof(cpOid) + cpSetSz + cpStrSz + pwSz, cpSeq);
        cpSz = cpSeqSz + sizeof(cpOid) + cpSetSz + cpStrSz + pwSz;
    }

    if (extSz) {
        erSetSz = SetSet(extSz, erSet);
        erSeqSz = SetSequence(erSetSz + sizeof(erOid) + extSz, erSeq);
        erSz = extSz + erSetSz + erSeqSz + sizeof(erOid);
    }

    /* Put the pieces together. */
    sz += SetLength(cpSz + erSz, &output[sz]);

    if (cpSz) {
        XMEMCPY(&output[sz], cpSeq, cpSeqSz);
        sz += cpSeqSz;
        XMEMCPY(&output[sz], cpOid, sizeof(cpOid));
        sz += sizeof(cpOid);
        XMEMCPY(&output[sz], cpSet, cpSetSz);
        sz += cpSetSz;
        XMEMCPY(&output[sz], cpStr, cpStrSz);
        sz += cpStrSz;
        XMEMCPY(&output[sz], pw, pwSz);
        sz += pwSz;
    }

    if (erSz) {
        XMEMCPY(&output[sz], erSeq, erSeqSz);
        sz += erSeqSz;
        XMEMCPY(&output[sz], erOid, sizeof(erOid));
        sz += sizeof(erOid);
        XMEMCPY(&output[sz], erSet, erSetSz);
        sz += erSetSz;
        /* The actual extension data will be tacked onto the output later. */
    }

    return sz;
}


/* encode info from cert into DER encoded format */
static int EncodeCertReq(Cert* cert, DerCert* der, RsaKey* rsaKey,
                         ecc_key* eccKey, ed25519_key* ed25519Key,
                         ed448_key* ed448Key)
{
    (void)eccKey;
    (void)ed25519Key;
    (void)ed448Key;

    if (cert == NULL || der == NULL)
        return BAD_FUNC_ARG;

    if (rsaKey == NULL && eccKey == NULL && ed25519Key == NULL &&
                                                             ed448Key == NULL) {
            return PUBLIC_KEY_E;
    }

    /* init */
    XMEMSET(der, 0, sizeof(DerCert));

    /* version */
    der->versionSz = SetMyVersion(cert->version, der->version, FALSE);

    /* subject name */
    der->subjectSz = SetName(der->subject, sizeof(der->subject), &cert->subject);
    if (der->subjectSz <= 0)
        return SUBJECT_E;

    /* public key */
#ifndef NO_RSA
    if (cert->keyType == RSA_KEY) {
        if (rsaKey == NULL)
            return PUBLIC_KEY_E;
        der->publicKeySz = SetRsaPublicKey(der->publicKey, rsaKey,
                                           sizeof(der->publicKey), 1);
    }
#endif

#ifdef HAVE_ECC
    if (cert->keyType == ECC_KEY) {
        if (eccKey == NULL)
            return PUBLIC_KEY_E;
        der->publicKeySz = SetEccPublicKey(der->publicKey, eccKey, 1);
    }
#endif

#ifdef HAVE_ED25519
    if (cert->keyType == ED25519_KEY) {
        if (ed25519Key == NULL)
            return PUBLIC_KEY_E;
        der->publicKeySz = SetEd25519PublicKey(der->publicKey, ed25519Key, 1);
    }
#endif

#ifdef HAVE_ED448
    if (cert->keyType == ED448_KEY) {
        if (ed448Key == NULL)
            return PUBLIC_KEY_E;
        der->publicKeySz = SetEd448PublicKey(der->publicKey, ed448Key, 1);
    }
#endif
    if (der->publicKeySz <= 0)
        return PUBLIC_KEY_E;

    /* set the extensions */
    der->extensionsSz = 0;

    /* CA */
    if (cert->isCA) {
        der->caSz = SetCa(der->ca, sizeof(der->ca));
        if (der->caSz <= 0)
            return CA_TRUE_E;

        der->extensionsSz += der->caSz;
    }
    else
        der->caSz = 0;

#ifdef WOLFSSL_CERT_EXT
    /* SKID */
    if (cert->skidSz) {
        /* check the provided SKID size */
        if (cert->skidSz > (int)min(CTC_MAX_SKID_SIZE, sizeof(der->skid)))
            return SKID_E;

        der->skidSz = SetSKID(der->skid, sizeof(der->skid),
                              cert->skid, cert->skidSz);
        if (der->skidSz <= 0)
            return SKID_E;

        der->extensionsSz += der->skidSz;
    }
    else
        der->skidSz = 0;

    /* Key Usage */
    if (cert->keyUsage != 0){
        der->keyUsageSz = SetKeyUsage(der->keyUsage, sizeof(der->keyUsage),
                                      cert->keyUsage);
        if (der->keyUsageSz <= 0)
            return KEYUSAGE_E;

        der->extensionsSz += der->keyUsageSz;
    }
    else
        der->keyUsageSz = 0;

    /* Extended Key Usage */
    if (cert->extKeyUsage != 0){
        der->extKeyUsageSz = SetExtKeyUsage(cert, der->extKeyUsage,
                                sizeof(der->extKeyUsage), cert->extKeyUsage);
        if (der->extKeyUsageSz <= 0)
            return EXTKEYUSAGE_E;

        der->extensionsSz += der->extKeyUsageSz;
    }
    else
        der->extKeyUsageSz = 0;

#endif /* WOLFSSL_CERT_EXT */

    /* put extensions */
    if (der->extensionsSz > 0) {
        int ret;

        /* put the start of sequence (ID, Size) */
        der->extensionsSz = SetSequence(der->extensionsSz, der->extensions);
        if (der->extensionsSz <= 0)
            return EXTENSIONS_E;

        /* put CA */
        if (der->caSz) {
            ret = SetExtensions(der->extensions, sizeof(der->extensions),
                                &der->extensionsSz,
                                der->ca, der->caSz);
            if (ret <= 0)
                return EXTENSIONS_E;
        }

#ifdef WOLFSSL_CERT_EXT
        /* put SKID */
        if (der->skidSz) {
            ret = SetExtensions(der->extensions, sizeof(der->extensions),
                                &der->extensionsSz,
                                der->skid, der->skidSz);
            if (ret <= 0)
                return EXTENSIONS_E;
        }

        /* put AKID */
        if (der->akidSz) {
            ret = SetExtensions(der->extensions, sizeof(der->extensions),
                                &der->extensionsSz,
                                der->akid, der->akidSz);
            if (ret <= 0)
                return EXTENSIONS_E;
        }

        /* put KeyUsage */
        if (der->keyUsageSz) {
            ret = SetExtensions(der->extensions, sizeof(der->extensions),
                                &der->extensionsSz,
                                der->keyUsage, der->keyUsageSz);
            if (ret <= 0)
                return EXTENSIONS_E;
        }

        /* put ExtendedKeyUsage */
        if (der->extKeyUsageSz) {
            ret = SetExtensions(der->extensions, sizeof(der->extensions),
                                &der->extensionsSz,
                                der->extKeyUsage, der->extKeyUsageSz);
            if (ret <= 0)
                return EXTENSIONS_E;
        }

#endif /* WOLFSSL_CERT_EXT */
    }

    der->attribSz = SetReqAttrib(der->attrib, cert->challengePw,
                                 cert->challengePwPrintableString,
                                 der->extensionsSz);
    if (der->attribSz <= 0)
        return REQ_ATTRIBUTE_E;

    der->total = der->versionSz + der->subjectSz + der->publicKeySz +
        der->extensionsSz + der->attribSz;

    return 0;
}


/* write DER encoded cert req to buffer, size already checked */
static int WriteCertReqBody(DerCert* der, byte* buf)
{
    int idx;

    /* signed part header */
    idx = SetSequence(der->total, buf);
    /* version */
    if (buf)
        XMEMCPY(buf + idx, der->version, der->versionSz);
    idx += der->versionSz;
    /* subject */
    if (buf)
        XMEMCPY(buf + idx, der->subject, der->subjectSz);
    idx += der->subjectSz;
    /* public key */
    if (buf)
        XMEMCPY(buf + idx, der->publicKey, der->publicKeySz);
    idx += der->publicKeySz;
    /* attributes */
    if (buf)
        XMEMCPY(buf + idx, der->attrib, der->attribSz);
    idx += der->attribSz;
    /* extensions */
    if (der->extensionsSz) {
        if (buf)
            XMEMCPY(buf + idx, der->extensions, min(der->extensionsSz,
                                               (int)sizeof(der->extensions)));
        idx += der->extensionsSz;
    }

    return idx;
}


static int MakeCertReq(Cert* cert, byte* derBuffer, word32 derSz,
                   RsaKey* rsaKey, ecc_key* eccKey, ed25519_key* ed25519Key,
                   ed448_key* ed448Key)
{
    int ret;
#ifdef WOLFSSL_SMALL_STACK
    DerCert* der;
#else
    DerCert der[1];
#endif

    cert->keyType = eccKey ? ECC_KEY : (ed25519Key ? ED25519_KEY :
                                       (ed448Key ? ED448_KEY: RSA_KEY));

#ifdef WOLFSSL_SMALL_STACK
    der = (DerCert*)XMALLOC(sizeof(DerCert), cert->heap,
                                                    DYNAMIC_TYPE_TMP_BUFFER);
    if (der == NULL)
        return MEMORY_E;
#endif

    ret = EncodeCertReq(cert, der, rsaKey, eccKey, ed25519Key, ed448Key);

    if (ret == 0) {
        if (der->total + MAX_SEQ_SZ * 2 > (int)derSz)
            ret = BUFFER_E;
        else
            ret = cert->bodySz = WriteCertReqBody(der, derBuffer);
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(der, cert->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

int wc_MakeCertReq_ex(Cert* cert, byte* derBuffer, word32 derSz, int keyType,
                      void* key)
{
    RsaKey*      rsaKey = NULL;
    ecc_key*     eccKey = NULL;
    ed25519_key* ed25519Key = NULL;
    ed448_key*   ed448Key = NULL;

    if (keyType == RSA_TYPE)
        rsaKey = (RsaKey*)key;
    else if (keyType == ECC_TYPE)
        eccKey = (ecc_key*)key;
    else if (keyType == ED25519_TYPE)
        ed25519Key = (ed25519_key*)key;
    else if (keyType == ED448_TYPE)
        ed448Key = (ed448_key*)key;

    return MakeCertReq(cert, derBuffer, derSz, rsaKey, eccKey, ed25519Key,
                       ed448Key);
}

int wc_MakeCertReq(Cert* cert, byte* derBuffer, word32 derSz,
                   RsaKey* rsaKey, ecc_key* eccKey)
{
    return MakeCertReq(cert, derBuffer, derSz, rsaKey, eccKey, NULL, NULL);
}
#endif /* WOLFSSL_CERT_REQ */


static int SignCert(int requestSz, int sType, byte* buf, word32 buffSz,
                    RsaKey* rsaKey, ecc_key* eccKey, ed25519_key* ed25519Key,
                    ed448_key* ed448Key, WC_RNG* rng)
{
    int sigSz = 0;
    void* heap = NULL;
    CertSignCtx* certSignCtx;
#ifndef WOLFSSL_ASYNC_CRYPT
    CertSignCtx  certSignCtx_lcl;

    certSignCtx = &certSignCtx_lcl;
    XMEMSET(certSignCtx, 0, sizeof(CertSignCtx));
#else
    certSignCtx = NULL;
#endif

    if (requestSz < 0)
        return requestSz;

    /* locate ctx */
    if (rsaKey) {
    #ifndef NO_RSA
    #ifdef WOLFSSL_ASYNC_CRYPT
        certSignCtx = &rsaKey->certSignCtx;
    #endif
        heap = rsaKey->heap;
    #else
        return NOT_COMPILED_IN;
    #endif /* NO_RSA */
    }
    else if (eccKey) {
    #ifdef HAVE_ECC
    #ifdef WOLFSSL_ASYNC_CRYPT
        certSignCtx = &eccKey->certSignCtx;
    #endif
        heap = eccKey->heap;
    #else
        return NOT_COMPILED_IN;
    #endif /* HAVE_ECC */
    }

#ifdef WOLFSSL_ASYNC_CRYPT
    if (certSignCtx == NULL) {
        return BAD_FUNC_ARG;
    }
#endif

    if (certSignCtx->sig == NULL) {
        certSignCtx->sig = (byte*)XMALLOC(MAX_ENCODED_SIG_SZ, heap,
            DYNAMIC_TYPE_TMP_BUFFER);
        if (certSignCtx->sig == NULL)
            return MEMORY_E;
    }

    sigSz = MakeSignature(certSignCtx, buf, requestSz, certSignCtx->sig,
        MAX_ENCODED_SIG_SZ, rsaKey, eccKey, ed25519Key, ed448Key, rng, sType,
        heap);
#ifdef WOLFSSL_ASYNC_CRYPT
    if (sigSz == WC_PENDING_E) {
        /* Not free'ing certSignCtx->sig here because it could still be in use
         * with async operations. */
        return sigSz;
    }
#endif

    if (sigSz >= 0) {
        if (requestSz + MAX_SEQ_SZ * 2 + sigSz > (int)buffSz)
            sigSz = BUFFER_E;
        else
            sigSz = AddSignature(buf, requestSz, certSignCtx->sig, sigSz,
                                 sType);
    }

    XFREE(certSignCtx->sig, heap, DYNAMIC_TYPE_TMP_BUFFER);
    certSignCtx->sig = NULL;

    return sigSz;
}

int wc_SignCert_ex(int requestSz, int sType, byte* buf, word32 buffSz,
                   int keyType, void* key, WC_RNG* rng)
{
    RsaKey*      rsaKey = NULL;
    ecc_key*     eccKey = NULL;
    ed25519_key* ed25519Key = NULL;
    ed448_key*   ed448Key = NULL;

    if (keyType == RSA_TYPE)
        rsaKey = (RsaKey*)key;
    else if (keyType == ECC_TYPE)
        eccKey = (ecc_key*)key;
    else if (keyType == ED25519_TYPE)
        ed25519Key = (ed25519_key*)key;
    else if (keyType == ED448_TYPE)
        ed448Key = (ed448_key*)key;

    return SignCert(requestSz, sType, buf, buffSz, rsaKey, eccKey, ed25519Key,
                    ed448Key, rng);
}

int wc_SignCert(int requestSz, int sType, byte* buf, word32 buffSz,
                RsaKey* rsaKey, ecc_key* eccKey, WC_RNG* rng)
{
    return SignCert(requestSz, sType, buf, buffSz, rsaKey, eccKey, NULL, NULL,
                    rng);
}

int wc_MakeSelfCert(Cert* cert, byte* buf, word32 buffSz,
                    RsaKey* key, WC_RNG* rng)
{
    int ret;

    ret = wc_MakeCert(cert, buf, buffSz, key, NULL, rng);
    if (ret < 0)
        return ret;

    return wc_SignCert(cert->bodySz, cert->sigType,
                       buf, buffSz, key, NULL, rng);
}


#ifdef WOLFSSL_CERT_EXT

/* Get raw subject from cert, which may contain OIDs not parsed by Decode.
   The raw subject pointer will only be valid while "cert" is valid. */
int wc_GetSubjectRaw(byte **subjectRaw, Cert *cert)
{
    int rc = BAD_FUNC_ARG;
    if ((subjectRaw != NULL) && (cert != NULL)) {
        *subjectRaw = cert->sbjRaw;
        rc = 0;
    }
    return rc;
}

/* Set KID from public key */
static int SetKeyIdFromPublicKey(Cert *cert, RsaKey *rsakey, ecc_key *eckey,
                                 byte *ntruKey, word16 ntruKeySz,
                                 ed25519_key* ed25519Key, ed448_key* ed448Key,
                                 int kid_type)
{
    byte *buf;
    int   bufferSz, ret;

    if (cert == NULL ||
        (rsakey == NULL && eckey == NULL && ntruKey == NULL &&
                                      ed25519Key == NULL && ed448Key == NULL) ||
        (kid_type != SKID_TYPE && kid_type != AKID_TYPE))
        return BAD_FUNC_ARG;

    buf = (byte *)XMALLOC(MAX_PUBLIC_KEY_SZ, cert->heap,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (buf == NULL)
        return MEMORY_E;

    /* Public Key */
    bufferSz = -1;
#ifndef NO_RSA
    /* RSA public key */
    if (rsakey != NULL)
        bufferSz = SetRsaPublicKey(buf, rsakey, MAX_PUBLIC_KEY_SZ, 0);
#endif
#ifdef HAVE_ECC
    /* ECC public key */
    if (eckey != NULL)
        bufferSz = SetEccPublicKey(buf, eckey, 0);
#endif
#ifdef HAVE_NTRU
    /* NTRU public key */
    if (ntruKey != NULL) {
        bufferSz = MAX_PUBLIC_KEY_SZ;
        ret = ntru_crypto_ntru_encrypt_publicKey2SubjectPublicKeyInfo(
                        ntruKeySz, ntruKey, (word16 *)(&bufferSz), buf);
        if (ret != NTRU_OK)
            bufferSz = -1;
    }
#else
    (void)ntruKeySz;
#endif
#ifdef HAVE_ED25519
    /* ED25519 public key */
    if (ed25519Key != NULL)
        bufferSz = SetEd25519PublicKey(buf, ed25519Key, 0);
#endif
#ifdef HAVE_ED448
    /* ED448 public key */
    if (ed448Key != NULL)
        bufferSz = SetEd448PublicKey(buf, ed448Key, 0);
#endif

    if (bufferSz <= 0) {
        XFREE(buf, cert->heap, DYNAMIC_TYPE_TMP_BUFFER);
        return PUBLIC_KEY_E;
    }

    /* Compute SKID by hashing public key */
    if (kid_type == SKID_TYPE) {
        ret = CalcHashId(buf, bufferSz, cert->skid);
        cert->skidSz = KEYID_SIZE;
    }
    else if (kid_type == AKID_TYPE) {
        ret = CalcHashId(buf, bufferSz, cert->akid);
        cert->akidSz = KEYID_SIZE;
    }
    else
        ret = BAD_FUNC_ARG;

    XFREE(buf, cert->heap, DYNAMIC_TYPE_TMP_BUFFER);
    return ret;
}

int wc_SetSubjectKeyIdFromPublicKey_ex(Cert *cert, int keyType, void* key)
{
    RsaKey*      rsaKey = NULL;
    ecc_key*     eccKey = NULL;
    ed25519_key* ed25519Key = NULL;
    ed448_key*   ed448Key = NULL;

    if (keyType == RSA_TYPE)
        rsaKey = (RsaKey*)key;
    else if (keyType == ECC_TYPE)
        eccKey = (ecc_key*)key;
    else if (keyType == ED25519_TYPE)
        ed25519Key = (ed25519_key*)key;
    else if (keyType == ED448_TYPE)
        ed448Key = (ed448_key*)key;

    return SetKeyIdFromPublicKey(cert, rsaKey, eccKey, NULL, 0, ed25519Key,
                                 ed448Key, SKID_TYPE);
}

/* Set SKID from RSA or ECC public key */
int wc_SetSubjectKeyIdFromPublicKey(Cert *cert, RsaKey *rsakey, ecc_key *eckey)
{
    return SetKeyIdFromPublicKey(cert, rsakey, eckey, NULL, 0, NULL, NULL,
                                 SKID_TYPE);
}

#ifdef HAVE_NTRU
/* Set SKID from NTRU public key */
int wc_SetSubjectKeyIdFromNtruPublicKey(Cert *cert,
                                        byte *ntruKey, word16 ntruKeySz)
{
    return SetKeyIdFromPublicKey(cert, NULL,NULL,ntruKey, ntruKeySz, NULL, NULL,
                                 SKID_TYPE);
}
#endif

int wc_SetAuthKeyIdFromPublicKey_ex(Cert *cert, int keyType, void* key)
{
    RsaKey*      rsaKey = NULL;
    ecc_key*     eccKey = NULL;
    ed25519_key* ed25519Key = NULL;
    ed448_key*   ed448Key = NULL;

    if (keyType == RSA_TYPE)
        rsaKey = (RsaKey*)key;
    else if (keyType == ECC_TYPE)
        eccKey = (ecc_key*)key;
    else if (keyType == ED25519_TYPE)
        ed25519Key = (ed25519_key*)key;
    else if (keyType == ED448_TYPE)
        ed448Key = (ed448_key*)key;

    return SetKeyIdFromPublicKey(cert, rsaKey, eccKey, NULL, 0, ed25519Key,
                                 ed448Key, AKID_TYPE);
}

/* Set SKID from RSA or ECC public key */
int wc_SetAuthKeyIdFromPublicKey(Cert *cert, RsaKey *rsakey, ecc_key *eckey)
{
    return SetKeyIdFromPublicKey(cert, rsakey, eckey, NULL, 0, NULL, NULL,
                                 AKID_TYPE);
}


#if !defined(NO_FILESYSTEM) && !defined(NO_ASN_CRYPT)

/* Set SKID from public key file in PEM */
int wc_SetSubjectKeyId(Cert *cert, const char* file)
{
    int     ret, derSz;
    byte*   der;
    word32  idx;
    RsaKey  *rsakey = NULL;
    ecc_key *eckey = NULL;

    if (cert == NULL || file == NULL)
        return BAD_FUNC_ARG;

    der = (byte*)XMALLOC(MAX_PUBLIC_KEY_SZ, cert->heap, DYNAMIC_TYPE_CERT);
    if (der == NULL) {
        WOLFSSL_MSG("wc_SetSubjectKeyId memory Problem");
        return MEMORY_E;
    }
    derSz = MAX_PUBLIC_KEY_SZ;

    XMEMSET(der, 0, derSz);
    derSz = wc_PemPubKeyToDer(file, der, derSz);
    if (derSz <= 0) {
        XFREE(der, cert->heap, DYNAMIC_TYPE_CERT);
        return derSz;
    }

    /* Load PubKey in internal structure */
#ifndef NO_RSA
    rsakey = (RsaKey*) XMALLOC(sizeof(RsaKey), cert->heap, DYNAMIC_TYPE_RSA);
    if (rsakey == NULL) {
        XFREE(der, cert->heap, DYNAMIC_TYPE_CERT);
        return MEMORY_E;
    }

    if (wc_InitRsaKey(rsakey, cert->heap) != 0) {
        WOLFSSL_MSG("wc_InitRsaKey failure");
        XFREE(rsakey, cert->heap, DYNAMIC_TYPE_RSA);
        XFREE(der, cert->heap, DYNAMIC_TYPE_CERT);
        return MEMORY_E;
    }

    idx = 0;
    ret = wc_RsaPublicKeyDecode(der, &idx, rsakey, derSz);
    if (ret != 0)
#endif
    {
#ifndef NO_RSA
        WOLFSSL_MSG("wc_RsaPublicKeyDecode failed");
        wc_FreeRsaKey(rsakey);
        XFREE(rsakey, cert->heap, DYNAMIC_TYPE_RSA);
        rsakey = NULL;
#endif
#ifdef HAVE_ECC
        /* Check to load ecc public key */
        eckey = (ecc_key*) XMALLOC(sizeof(ecc_key), cert->heap,
                                                              DYNAMIC_TYPE_ECC);
        if (eckey == NULL) {
            XFREE(der, cert->heap, DYNAMIC_TYPE_CERT);
            return MEMORY_E;
        }

        if (wc_ecc_init(eckey) != 0) {
            WOLFSSL_MSG("wc_ecc_init failure");
            wc_ecc_free(eckey);
            XFREE(eckey, cert->heap, DYNAMIC_TYPE_ECC);
            XFREE(der, cert->heap, DYNAMIC_TYPE_CERT);
            return MEMORY_E;
        }

        idx = 0;
        ret = wc_EccPublicKeyDecode(der, &idx, eckey, derSz);
        if (ret != 0) {
            WOLFSSL_MSG("wc_EccPublicKeyDecode failed");
            XFREE(der, cert->heap, DYNAMIC_TYPE_CERT);
            wc_ecc_free(eckey);
            XFREE(eckey, cert->heap, DYNAMIC_TYPE_ECC);
            return PUBLIC_KEY_E;
        }
#else
        XFREE(der, cert->heap, DYNAMIC_TYPE_CERT);
        return PUBLIC_KEY_E;
#endif /* HAVE_ECC */
    }

    XFREE(der, cert->heap, DYNAMIC_TYPE_CERT);

    ret = wc_SetSubjectKeyIdFromPublicKey(cert, rsakey, eckey);

#ifndef NO_RSA
    wc_FreeRsaKey(rsakey);
    XFREE(rsakey, cert->heap, DYNAMIC_TYPE_RSA);
#endif
#ifdef HAVE_ECC
    wc_ecc_free(eckey);
    XFREE(eckey, cert->heap, DYNAMIC_TYPE_ECC);
#endif
    return ret;
}

#endif /* !NO_FILESYSTEM && !NO_ASN_CRYPT */

static int SetAuthKeyIdFromDcert(Cert* cert, DecodedCert* decoded)
{
    int ret = 0;

    /* Subject Key Id not found !! */
    if (decoded->extSubjKeyIdSet == 0) {
        ret = ASN_NO_SKID;
    }

    /* SKID invalid size */
    else if (sizeof(cert->akid) < sizeof(decoded->extSubjKeyId)) {
        ret = MEMORY_E;
    }

    else {
        /* Put the SKID of CA to AKID of certificate */
        XMEMCPY(cert->akid, decoded->extSubjKeyId, KEYID_SIZE);
        cert->akidSz = KEYID_SIZE;
    }

    return ret;
}

/* Set AKID from certificate contains in buffer (DER encoded) */
int wc_SetAuthKeyIdFromCert(Cert *cert, const byte *der, int derSz)
{
    int ret = 0;

    if (cert == NULL) {
        ret = BAD_FUNC_ARG;
    }
    else {
        /* Check if decodedCert is cached */
        if (cert->der != der) {
            /* Allocate cache for the decoded cert */
            ret = wc_SetCert_LoadDer(cert, der, derSz);
        }

        if (ret >= 0) {
            ret = SetAuthKeyIdFromDcert(cert, (DecodedCert*)cert->decodedCert);
#ifndef WOLFSSL_CERT_GEN_CACHE
            wc_SetCert_Free(cert);
#endif
        }
    }

    return ret;
}


#ifndef NO_FILESYSTEM

/* Set AKID from certificate file in PEM */
int wc_SetAuthKeyId(Cert *cert, const char* file)
{
    int         ret;
    int         derSz;
    byte*       der;

    if (cert == NULL || file == NULL)
        return BAD_FUNC_ARG;

    der = (byte*)XMALLOC(EIGHTK_BUF, cert->heap, DYNAMIC_TYPE_CERT);
    if (der == NULL) {
        WOLFSSL_MSG("wc_SetAuthKeyId OOF Problem");
        return MEMORY_E;
    }

    derSz = wc_PemCertToDer(file, der, EIGHTK_BUF);
    if (derSz <= 0)
    {
        XFREE(der, cert->heap, DYNAMIC_TYPE_CERT);
        return derSz;
    }

    ret = wc_SetAuthKeyIdFromCert(cert, der, derSz);
    XFREE(der, cert->heap, DYNAMIC_TYPE_CERT);

    return ret;
}

#endif /* !NO_FILESYSTEM */

/* Set KeyUsage from human readable string */
int wc_SetKeyUsage(Cert *cert, const char *value)
{
    int ret = 0;
    char *token, *str, *ptr;
    word32 len;

    if (cert == NULL || value == NULL)
        return BAD_FUNC_ARG;

    cert->keyUsage = 0;

    /* duplicate string (including terminator) */
    len = (word32)XSTRLEN(value);
    str = (char*)XMALLOC(len+1, cert->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (str == NULL)
        return MEMORY_E;
    XMEMCPY(str, value, len+1);

    /* parse value, and set corresponding Key Usage value */
    if ((token = XSTRTOK(str, ",", &ptr)) == NULL) {
        XFREE(str, cert->heap, DYNAMIC_TYPE_TMP_BUFFER);
        return KEYUSAGE_E;
    }
    while (token != NULL)
    {
        len = (word32)XSTRLEN(token);

        if (!XSTRNCASECMP(token, "digitalSignature", len))
            cert->keyUsage |= KEYUSE_DIGITAL_SIG;
        else if (!XSTRNCASECMP(token, "nonRepudiation", len) ||
                 !XSTRNCASECMP(token, "contentCommitment", len))
            cert->keyUsage |= KEYUSE_CONTENT_COMMIT;
        else if (!XSTRNCASECMP(token, "keyEncipherment", len))
            cert->keyUsage |= KEYUSE_KEY_ENCIPHER;
        else if (!XSTRNCASECMP(token, "dataEncipherment", len))
            cert->keyUsage |= KEYUSE_DATA_ENCIPHER;
        else if (!XSTRNCASECMP(token, "keyAgreement", len))
            cert->keyUsage |= KEYUSE_KEY_AGREE;
        else if (!XSTRNCASECMP(token, "keyCertSign", len))
            cert->keyUsage |= KEYUSE_KEY_CERT_SIGN;
        else if (!XSTRNCASECMP(token, "cRLSign", len))
            cert->keyUsage |= KEYUSE_CRL_SIGN;
        else if (!XSTRNCASECMP(token, "encipherOnly", len))
            cert->keyUsage |= KEYUSE_ENCIPHER_ONLY;
        else if (!XSTRNCASECMP(token, "decipherOnly", len))
            cert->keyUsage |= KEYUSE_DECIPHER_ONLY;
        else {
            ret = KEYUSAGE_E;
            break;
        }

        token = XSTRTOK(NULL, ",", &ptr);
    }

    XFREE(str, cert->heap, DYNAMIC_TYPE_TMP_BUFFER);
    return ret;
}

/* Set ExtendedKeyUsage from human readable string */
int wc_SetExtKeyUsage(Cert *cert, const char *value)
{
    int ret = 0;
    char *token, *str, *ptr;
    word32 len;

    if (cert == NULL || value == NULL)
        return BAD_FUNC_ARG;

    cert->extKeyUsage = 0;

    /* duplicate string (including terminator) */
    len = (word32)XSTRLEN(value);
    str = (char*)XMALLOC(len+1, cert->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (str == NULL)
        return MEMORY_E;
    XMEMCPY(str, value, len+1);

    /* parse value, and set corresponding Key Usage value */
    if ((token = XSTRTOK(str, ",", &ptr)) == NULL) {
        XFREE(str, cert->heap, DYNAMIC_TYPE_TMP_BUFFER);
        return EXTKEYUSAGE_E;
    }

    while (token != NULL)
    {
        len = (word32)XSTRLEN(token);

        if (!XSTRNCASECMP(token, "any", len))
            cert->extKeyUsage |= EXTKEYUSE_ANY;
        else if (!XSTRNCASECMP(token, "serverAuth", len))
            cert->extKeyUsage |= EXTKEYUSE_SERVER_AUTH;
        else if (!XSTRNCASECMP(token, "clientAuth", len))
            cert->extKeyUsage |= EXTKEYUSE_CLIENT_AUTH;
        else if (!XSTRNCASECMP(token, "codeSigning", len))
            cert->extKeyUsage |= EXTKEYUSE_CODESIGN;
        else if (!XSTRNCASECMP(token, "emailProtection", len))
            cert->extKeyUsage |= EXTKEYUSE_EMAILPROT;
        else if (!XSTRNCASECMP(token, "timeStamping", len))
            cert->extKeyUsage |= EXTKEYUSE_TIMESTAMP;
        else if (!XSTRNCASECMP(token, "OCSPSigning", len))
            cert->extKeyUsage |= EXTKEYUSE_OCSP_SIGN;
        else {
            ret = EXTKEYUSAGE_E;
            break;
        }

        token = XSTRTOK(NULL, ",", &ptr);
    }

    XFREE(str, cert->heap, DYNAMIC_TYPE_TMP_BUFFER);
    return ret;
}

#ifdef WOLFSSL_EKU_OID
/*
 * cert structure to set EKU oid in
 * oid  the oid in byte representation
 * sz   size of oid buffer
 * idx  index of array to place oid
 *
 * returns 0 on success
 */
int wc_SetExtKeyUsageOID(Cert *cert, const char *in, word32 sz, byte idx,
        void* heap)
{
    byte oid[MAX_OID_SZ];
    word32 oidSz = MAX_OID_SZ;

    if (idx >= CTC_MAX_EKU_NB || sz >= CTC_MAX_EKU_OID_SZ) {
        WOLFSSL_MSG("Either idx or sz was too large");
        return BAD_FUNC_ARG;
    }

    if (EncodePolicyOID(oid, &oidSz, in, heap) != 0) {
        return BUFFER_E;
    }

    XMEMCPY(cert->extKeyUsageOID[idx], oid, oidSz);
    cert->extKeyUsageOIDSz[idx] = oidSz;
    cert->extKeyUsage |= EXTKEYUSE_USER;

    return 0;
}
#endif /* WOLFSSL_EKU_OID */
#endif /* WOLFSSL_CERT_EXT */


#ifdef WOLFSSL_ALT_NAMES

static int SetAltNamesFromDcert(Cert* cert, DecodedCert* decoded)
{
    int ret = 0;
    byte tag;

    if (decoded->extensions) {
        int    length;
        word32 maxExtensionsIdx;

        decoded->srcIdx = decoded->extensionsIdx;
        if (GetASNTag(decoded->source, &decoded->srcIdx, &tag, decoded->maxIdx)
                != 0) {
            return ASN_PARSE_E;
        }

        if (tag != ASN_EXTENSIONS) {
            ret = ASN_PARSE_E;
        }
        else if (GetLength(decoded->source, &decoded->srcIdx, &length,
                                                         decoded->maxIdx) < 0) {
            ret = ASN_PARSE_E;
        }
        else if (GetSequence(decoded->source, &decoded->srcIdx, &length,
                                                         decoded->maxIdx) < 0) {
            ret = ASN_PARSE_E;
        }
        else {
            maxExtensionsIdx = decoded->srcIdx + length;

            while (decoded->srcIdx < maxExtensionsIdx) {
                word32 oid;
                word32 startIdx = decoded->srcIdx;
                word32 tmpIdx;

                if (GetSequence(decoded->source, &decoded->srcIdx, &length,
                            decoded->maxIdx) < 0) {
                    ret = ASN_PARSE_E;
                    break;
                }

                tmpIdx = decoded->srcIdx;
                decoded->srcIdx = startIdx;

                if (GetAlgoId(decoded->source, &decoded->srcIdx, &oid,
                              oidCertExtType, decoded->maxIdx) < 0) {
                    ret = ASN_PARSE_E;
                    break;
                }

                if (oid == ALT_NAMES_OID) {
                    cert->altNamesSz = length + (tmpIdx - startIdx);

                    if (cert->altNamesSz < (int)sizeof(cert->altNames))
                        XMEMCPY(cert->altNames, &decoded->source[startIdx],
                                cert->altNamesSz);
                    else {
                        cert->altNamesSz = 0;
                        WOLFSSL_MSG("AltNames extensions too big");
                        ret = ALT_NAME_E;
                        break;
                    }
                }
                decoded->srcIdx = tmpIdx + length;
            }
        }
    }

    return ret;
}

#ifndef NO_FILESYSTEM

/* Set Alt Names from der cert, return 0 on success */
static int SetAltNamesFromCert(Cert* cert, const byte* der, int derSz)
{
    int ret;
#ifdef WOLFSSL_SMALL_STACK
    DecodedCert* decoded;
#else
    DecodedCert decoded[1];
#endif

    if (derSz < 0)
        return derSz;

#ifdef WOLFSSL_SMALL_STACK
    decoded = (DecodedCert*)XMALLOC(sizeof(DecodedCert), cert->heap,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (decoded == NULL)
        return MEMORY_E;
#endif

    InitDecodedCert(decoded, der, derSz, NULL);
    ret = ParseCertRelative(decoded, CA_TYPE, NO_VERIFY, 0);

    if (ret < 0) {
        WOLFSSL_MSG("ParseCertRelative error");
    }
    else {
        ret = SetAltNamesFromDcert(cert, decoded);
    }

    FreeDecodedCert(decoded);
#ifdef WOLFSSL_SMALL_STACK
    XFREE(decoded, cert->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret < 0 ? ret : 0;
}

#endif

static int SetDatesFromDcert(Cert* cert, DecodedCert* decoded)
{
    int ret = 0;

    if (decoded->beforeDate == NULL || decoded->afterDate == NULL) {
        WOLFSSL_MSG("Couldn't extract dates");
        ret = -1;
    }
    else if (decoded->beforeDateLen > MAX_DATE_SIZE ||
                                        decoded->afterDateLen > MAX_DATE_SIZE) {
        WOLFSSL_MSG("Bad date size");
        ret = -1;
    }
    else {
        XMEMCPY(cert->beforeDate, decoded->beforeDate, decoded->beforeDateLen);
        XMEMCPY(cert->afterDate,  decoded->afterDate,  decoded->afterDateLen);

        cert->beforeDateSz = decoded->beforeDateLen;
        cert->afterDateSz  = decoded->afterDateLen;
    }

    return ret;
}

#endif /* WOLFSSL_ALT_NAMES */

static void SetNameFromDcert(CertName* cn, DecodedCert* decoded)
{
    int sz;

    if (decoded->subjectCN) {
        sz = (decoded->subjectCNLen < CTC_NAME_SIZE) ? decoded->subjectCNLen
                                                     : CTC_NAME_SIZE - 1;
        XSTRNCPY(cn->commonName, decoded->subjectCN, sz);
        cn->commonName[sz] = '\0';
        cn->commonNameEnc = decoded->subjectCNEnc;
    }
    if (decoded->subjectC) {
        sz = (decoded->subjectCLen < CTC_NAME_SIZE) ? decoded->subjectCLen
                                                    : CTC_NAME_SIZE - 1;
        XSTRNCPY(cn->country, decoded->subjectC, sz);
        cn->country[sz] = '\0';
        cn->countryEnc = decoded->subjectCEnc;
    }
    if (decoded->subjectST) {
        sz = (decoded->subjectSTLen < CTC_NAME_SIZE) ? decoded->subjectSTLen
                                                     : CTC_NAME_SIZE - 1;
        XSTRNCPY(cn->state, decoded->subjectST, sz);
        cn->state[sz] = '\0';
        cn->stateEnc = decoded->subjectSTEnc;
    }
    if (decoded->subjectL) {
        sz = (decoded->subjectLLen < CTC_NAME_SIZE) ? decoded->subjectLLen
                                                    : CTC_NAME_SIZE - 1;
        XSTRNCPY(cn->locality, decoded->subjectL, sz);
        cn->locality[sz] = '\0';
        cn->localityEnc = decoded->subjectLEnc;
    }
    if (decoded->subjectO) {
        sz = (decoded->subjectOLen < CTC_NAME_SIZE) ? decoded->subjectOLen
                                                    : CTC_NAME_SIZE - 1;
        XSTRNCPY(cn->org, decoded->subjectO, sz);
        cn->org[sz] = '\0';
        cn->orgEnc = decoded->subjectOEnc;
    }
    if (decoded->subjectOU) {
        sz = (decoded->subjectOULen < CTC_NAME_SIZE) ? decoded->subjectOULen
                                                     : CTC_NAME_SIZE - 1;
        XSTRNCPY(cn->unit, decoded->subjectOU, sz);
        cn->unit[sz] = '\0';
        cn->unitEnc = decoded->subjectOUEnc;
    }
    if (decoded->subjectSN) {
        sz = (decoded->subjectSNLen < CTC_NAME_SIZE) ? decoded->subjectSNLen
                                                     : CTC_NAME_SIZE - 1;
        XSTRNCPY(cn->sur, decoded->subjectSN, sz);
        cn->sur[sz] = '\0';
        cn->surEnc = decoded->subjectSNEnc;
    }
    if (decoded->subjectSND) {
        sz = (decoded->subjectSNDLen < CTC_NAME_SIZE) ? decoded->subjectSNDLen
                                                     : CTC_NAME_SIZE - 1;
        XSTRNCPY(cn->serialDev, decoded->subjectSND, sz);
        cn->serialDev[sz] = '\0';
        cn->serialDevEnc = decoded->subjectSNDEnc;
    }
#ifdef WOLFSSL_CERT_EXT
    if (decoded->subjectBC) {
        sz = (decoded->subjectBCLen < CTC_NAME_SIZE) ? decoded->subjectBCLen
                                                     : CTC_NAME_SIZE - 1;
        XSTRNCPY(cn->busCat, decoded->subjectBC, sz);
        cn->busCat[sz] = '\0';
        cn->busCatEnc = decoded->subjectBCEnc;
    }
    if (decoded->subjectJC) {
        sz = (decoded->subjectJCLen < CTC_NAME_SIZE) ? decoded->subjectJCLen
                                                     : CTC_NAME_SIZE - 1;
        XSTRNCPY(cn->joiC, decoded->subjectJC, sz);
        cn->joiC[sz] = '\0';
        cn->joiCEnc = decoded->subjectJCEnc;
    }
    if (decoded->subjectJS) {
        sz = (decoded->subjectJSLen < CTC_NAME_SIZE) ? decoded->subjectJSLen
                                                     : CTC_NAME_SIZE - 1;
        XSTRNCPY(cn->joiSt, decoded->subjectJS, sz);
        cn->joiSt[sz] = '\0';
        cn->joiStEnc = decoded->subjectJSEnc;
    }
#endif
    if (decoded->subjectEmail) {
        sz = (decoded->subjectEmailLen < CTC_NAME_SIZE)
           ?  decoded->subjectEmailLen : CTC_NAME_SIZE - 1;
        XSTRNCPY(cn->email, decoded->subjectEmail, sz);
        cn->email[sz] = '\0';
    }
}

#ifndef NO_FILESYSTEM

/* Set cn name from der buffer, return 0 on success */
static int SetNameFromCert(CertName* cn, const byte* der, int derSz)
{
    int ret;
#ifdef WOLFSSL_SMALL_STACK
    DecodedCert* decoded;
#else
    DecodedCert decoded[1];
#endif

    if (derSz < 0)
        return derSz;

#ifdef WOLFSSL_SMALL_STACK
    decoded = (DecodedCert*)XMALLOC(sizeof(DecodedCert), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (decoded == NULL)
        return MEMORY_E;
#endif

    InitDecodedCert(decoded, der, derSz, NULL);
    ret = ParseCertRelative(decoded, CA_TYPE, NO_VERIFY, 0);

    if (ret < 0) {
        WOLFSSL_MSG("ParseCertRelative error");
    }
    else {
        SetNameFromDcert(cn, decoded);
    }

    FreeDecodedCert(decoded);

#ifdef WOLFSSL_SMALL_STACK
    XFREE(decoded, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret < 0 ? ret : 0;
}

/* Set cert issuer from issuerFile in PEM */
int wc_SetIssuer(Cert* cert, const char* issuerFile)
{
    int         ret;
    int         derSz;
    byte*       der;

    if (cert == NULL) {
        return BAD_FUNC_ARG;
    }

    der = (byte*)XMALLOC(EIGHTK_BUF, cert->heap, DYNAMIC_TYPE_CERT);
    if (der == NULL) {
        WOLFSSL_MSG("wc_SetIssuer OOF Problem");
        return MEMORY_E;
    }
    derSz = wc_PemCertToDer(issuerFile, der, EIGHTK_BUF);
    cert->selfSigned = 0;
    ret = SetNameFromCert(&cert->issuer, der, derSz);
    XFREE(der, cert->heap, DYNAMIC_TYPE_CERT);

    return ret;
}


/* Set cert subject from subjectFile in PEM */
int wc_SetSubject(Cert* cert, const char* subjectFile)
{
    int         ret;
    int         derSz;
    byte*       der;

    if (cert == NULL) {
        return BAD_FUNC_ARG;
    }

    der = (byte*)XMALLOC(EIGHTK_BUF, cert->heap, DYNAMIC_TYPE_CERT);
    if (der == NULL) {
        WOLFSSL_MSG("wc_SetSubject OOF Problem");
        return MEMORY_E;
    }

    derSz = wc_PemCertToDer(subjectFile, der, EIGHTK_BUF);
    ret = SetNameFromCert(&cert->subject, der, derSz);
    XFREE(der, cert->heap, DYNAMIC_TYPE_CERT);

    return ret;
}

#ifdef WOLFSSL_ALT_NAMES

/* Set alt names from file in PEM */
int wc_SetAltNames(Cert* cert, const char* file)
{
    int         ret;
    int         derSz;
    byte*       der;

    if (cert == NULL) {
        return BAD_FUNC_ARG;
    }

    der = (byte*)XMALLOC(EIGHTK_BUF, cert->heap, DYNAMIC_TYPE_CERT);
    if (der == NULL) {
        WOLFSSL_MSG("wc_SetAltNames OOF Problem");
        return MEMORY_E;
    }
    derSz = wc_PemCertToDer(file, der, EIGHTK_BUF);
    ret = SetAltNamesFromCert(cert, der, derSz);
    XFREE(der, cert->heap, DYNAMIC_TYPE_CERT);

    return ret;
}

#endif /* WOLFSSL_ALT_NAMES */

#endif /* !NO_FILESYSTEM */

/* Set cert issuer from DER buffer */
int wc_SetIssuerBuffer(Cert* cert, const byte* der, int derSz)
{
    int ret = 0;

    if (cert == NULL) {
        ret = BAD_FUNC_ARG;
    }
    else {
        cert->selfSigned = 0;

        /* Check if decodedCert is cached */
        if (cert->der != der) {
            /* Allocate cache for the decoded cert */
            ret = wc_SetCert_LoadDer(cert, der, derSz);
        }

        if (ret >= 0) {
            SetNameFromDcert(&cert->issuer, (DecodedCert*)cert->decodedCert);
#ifndef WOLFSSL_CERT_GEN_CACHE
            wc_SetCert_Free(cert);
#endif
        }
    }

    return ret;
}

/* Set cert subject from DER buffer */
int wc_SetSubjectBuffer(Cert* cert, const byte* der, int derSz)
{
    int ret = 0;

    if (cert == NULL) {
        ret = BAD_FUNC_ARG;
    }
    else {
        /* Check if decodedCert is cached */
        if (cert->der != der) {
            /* Allocate cache for the decoded cert */
            ret = wc_SetCert_LoadDer(cert, der, derSz);
        }

        if (ret >= 0) {
            SetNameFromDcert(&cert->subject, (DecodedCert*)cert->decodedCert);
#ifndef WOLFSSL_CERT_GEN_CACHE
            wc_SetCert_Free(cert);
#endif
        }
    }

    return ret;
}
#ifdef WOLFSSL_CERT_EXT
/* Set cert raw subject from DER buffer */
int wc_SetSubjectRaw(Cert* cert, const byte* der, int derSz)
{
    int ret = 0;

    if (cert == NULL) {
        ret = BAD_FUNC_ARG;
    }
    else {
        /* Check if decodedCert is cached */
        if (cert->der != der) {
            /* Allocate cache for the decoded cert */
            ret = wc_SetCert_LoadDer(cert, der, derSz);
        }

        if (ret >= 0) {
            if ((((DecodedCert*)cert->decodedCert)->subjectRaw) &&
                (((DecodedCert*)cert->decodedCert)->subjectRawLen <=
                        (int)sizeof(CertName))) {
                XMEMCPY(cert->sbjRaw,
                        ((DecodedCert*)cert->decodedCert)->subjectRaw,
                        ((DecodedCert*)cert->decodedCert)->subjectRawLen);
            }
#ifndef WOLFSSL_CERT_GEN_CACHE
            wc_SetCert_Free(cert);
#endif
        }
    }

    return ret;
}

/* Set cert raw issuer from DER buffer */
int wc_SetIssuerRaw(Cert* cert, const byte* der, int derSz)
{
    int ret = 0;

    if (cert == NULL) {
        ret = BAD_FUNC_ARG;
    }
    else {
        /* Check if decodedCert is cached */
        if (cert->der != der) {
            /* Allocate cache for the decoded cert */
            ret = wc_SetCert_LoadDer(cert, der, derSz);
        }

        if (ret >= 0) {
            if ((((DecodedCert*)cert->decodedCert)->issuerRaw) &&
                (((DecodedCert*)cert->decodedCert)->issuerRawLen <=
                        (int)sizeof(CertName))) {
                XMEMCPY(cert->issRaw,
                        ((DecodedCert*)cert->decodedCert)->issuerRaw,
                        ((DecodedCert*)cert->decodedCert)->issuerRawLen);
            }
#ifndef WOLFSSL_CERT_GEN_CACHE
            wc_SetCert_Free(cert);
#endif
        }
    }
    return ret;
}
#endif

#ifdef WOLFSSL_ALT_NAMES

/* Set cert alt names from DER buffer */
int wc_SetAltNamesBuffer(Cert* cert, const byte* der, int derSz)
{
    int ret = 0;

    if (cert == NULL) {
     ret = BAD_FUNC_ARG;
    }
    else {
        /* Check if decodedCert is cached */
        if (cert->der != der) {
            /* Allocate cache for the decoded cert */
            ret = wc_SetCert_LoadDer(cert, der, derSz);
        }

        if (ret >= 0) {
            ret = SetAltNamesFromDcert(cert, (DecodedCert*)cert->decodedCert);
#ifndef WOLFSSL_CERT_GEN_CACHE
            wc_SetCert_Free(cert);
#endif
       }
    }

    return(ret);
}

/* Set cert dates from DER buffer */
int wc_SetDatesBuffer(Cert* cert, const byte* der, int derSz)
{
    int ret = 0;

    if (cert == NULL) {
     ret = BAD_FUNC_ARG;
    }
    else {
        /* Check if decodedCert is cached */
        if (cert->der != der) {
            /* Allocate cache for the decoded cert */
            ret = wc_SetCert_LoadDer(cert, der, derSz);
        }

        if (ret >= 0) {
            ret = SetDatesFromDcert(cert, (DecodedCert*)cert->decodedCert);
#ifndef WOLFSSL_CERT_GEN_CACHE
            wc_SetCert_Free(cert);
#endif
        }
    }

    return(ret);
}

#endif /* WOLFSSL_ALT_NAMES */

#endif /* WOLFSSL_CERT_GEN */

#if (defined(WOLFSSL_CERT_GEN) && defined(WOLFSSL_CERT_EXT)) \
        || defined(OPENSSL_EXTRA)
/* Encode OID string representation to ITU-T X.690 format */
int EncodePolicyOID(byte *out, word32 *outSz, const char *in, void* heap)
{
    word32 val, idx = 0, nb_val;
    char *token, *str, *ptr;
    word32 len;

    (void)heap;

    if (out == NULL || outSz == NULL || *outSz < 2 || in == NULL)
        return BAD_FUNC_ARG;

    /* duplicate string (including terminator) */
    len = (word32)XSTRLEN(in);
    str = (char *)XMALLOC(len+1, heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (str == NULL)
        return MEMORY_E;
    XMEMCPY(str, in, len+1);

    nb_val = 0;

    /* parse value, and set corresponding Policy OID value */
    token = XSTRTOK(str, ".", &ptr);
    while (token != NULL)
    {
        val = (word32)XATOI(token);

        if (nb_val == 0) {
            if (val > 2) {
                XFREE(str, heap, DYNAMIC_TYPE_TMP_BUFFER);
                return ASN_OBJECT_ID_E;
            }

            out[idx] = (byte)(40 * val);
        }
        else if (nb_val == 1) {
            if (val > 127) {
                XFREE(str, heap, DYNAMIC_TYPE_TMP_BUFFER);
                return ASN_OBJECT_ID_E;
            }

            if (idx > *outSz) {
                XFREE(str, heap, DYNAMIC_TYPE_TMP_BUFFER);
                return BUFFER_E;
            }

            out[idx++] += (byte)val;
        }
        else {
            word32  tb = 0, x;
            int     i = 0;
            byte    oid[MAX_OID_SZ];

            while (val >= 128) {
                x = val % 128;
                val /= 128;
                oid[i++] = (byte) (((tb++) ? 0x80 : 0) | x);
            }

            if ((idx+(word32)i) > *outSz) {
                XFREE(str, heap, DYNAMIC_TYPE_TMP_BUFFER);
                return BUFFER_E;
            }

            oid[i] = (byte) (((tb++) ? 0x80 : 0) | val);

            /* push value in the right order */
            while (i >= 0)
                out[idx++] = oid[i--];
        }

        token = XSTRTOK(NULL, ".", &ptr);
        nb_val++;
    }

    *outSz = idx;

    XFREE(str, heap, DYNAMIC_TYPE_TMP_BUFFER);
    return 0;
}
#endif /* WOLFSSL_CERT_EXT || OPENSSL_EXTRA */

#endif /* !NO_CERTS */

#if !defined(NO_DH) && (defined(WOLFSSL_QT) || defined(OPENSSL_ALL))
/* Helper function for wolfSSL_i2d_DHparams */
int StoreDHparams(byte* out, word32* outLen, mp_int* p, mp_int* g)
{
    word32 idx = 0;
    int pSz;
    int gSz;
    unsigned int tmp;
    word32 headerSz = 4; /* 2*ASN_TAG + 2*LEN(ENUM) */

    /* If the leading bit on the INTEGER is a 1, add a leading zero */
    int pLeadingZero = mp_leading_bit(p);
    int gLeadingZero = mp_leading_bit(g);
    int pLen = mp_unsigned_bin_size(p);
    int gLen = mp_unsigned_bin_size(g);

    WOLFSSL_ENTER("StoreDHparams");
    if (out == NULL) {
        WOLFSSL_MSG("Null buffer error");
        return BUFFER_E;
    }

    tmp = pLeadingZero + gLeadingZero + pLen + gLen;
    if (*outLen < (tmp + headerSz)) {
        return BUFFER_E;
    }

    /* Set sequence */
    idx = SetSequence(tmp + headerSz + 2, out);

    /* Encode p */
    pSz = SetASNIntMP(p, -1, &out[idx]);
    if (pSz < 0) {
        WOLFSSL_MSG("SetASNIntMP failed");
        return pSz;
    }
    idx += pSz;

    /* Encode g */
    gSz = SetASNIntMP(g, -1, &out[idx]);
    if (gSz < 0) {
        WOLFSSL_MSG("SetASNIntMP failed");
        return gSz;
    }
    idx += gSz;

    *outLen = idx;

    return 0;
}
#endif /* !NO_DH && (WOLFSSL_QT || OPENSSL_ALL) */

#ifdef HAVE_ECC

/* Der Encode r & s ints into out, outLen is (in/out) size */
int StoreECC_DSA_Sig(byte* out, word32* outLen, mp_int* r, mp_int* s)
{
    word32 idx = 0;
    int    rSz;                           /* encoding size */
    int    sSz;
    word32 headerSz = 4;   /* 2*ASN_TAG + 2*LEN(ENUM) */

    /* If the leading bit on the INTEGER is a 1, add a leading zero */
    int rLeadingZero = mp_leading_bit(r);
    int sLeadingZero = mp_leading_bit(s);
    int rLen = mp_unsigned_bin_size(r);   /* big int size */
    int sLen = mp_unsigned_bin_size(s);

    if (*outLen < (rLen + rLeadingZero + sLen + sLeadingZero +
                   headerSz + 2))  /* SEQ_TAG + LEN(ENUM) */
        return BUFFER_E;

    idx = SetSequence(rLen + rLeadingZero + sLen+sLeadingZero + headerSz, out);

    /* store r */
    rSz = SetASNIntMP(r, -1, &out[idx]);
    if (rSz < 0)
        return rSz;
    idx += rSz;

    /* store s */
    sSz = SetASNIntMP(s, -1, &out[idx]);
    if (sSz < 0)
        return sSz;
    idx += sSz;

    *outLen = idx;

    return 0;
}


/* Der Decode ECC-DSA Signature, r & s stored as big ints */
int DecodeECC_DSA_Sig(const byte* sig, word32 sigLen, mp_int* r, mp_int* s)
{
    word32 idx = 0;
    int    len = 0;

    if (GetSequence(sig, &idx, &len, sigLen) < 0) {
        return ASN_ECC_KEY_E;
    }

#ifndef NO_STRICT_ECDSA_LEN
    /* enable strict length checking for signature */
    if (sigLen != idx + (word32)len) {
        return ASN_ECC_KEY_E;
    }
#else
    /* allow extra signature bytes at end */
    if ((word32)len > (sigLen - idx)) {
        return ASN_ECC_KEY_E;
    }
#endif

    if (GetInt(r, sig, &idx, sigLen) < 0) {
        return ASN_ECC_KEY_E;
    }

    if (GetInt(s, sig, &idx, sigLen) < 0) {
        mp_clear(r);
        return ASN_ECC_KEY_E;
    }

    return 0;
}


int wc_EccPrivateKeyDecode(const byte* input, word32* inOutIdx, ecc_key* key,
                        word32 inSz)
{
    word32 oidSum;
    int    version, length;
    int    privSz, pubSz = 0;
    byte   b;
    int    ret = 0;
    int    curve_id = ECC_CURVE_DEF;
#ifdef WOLFSSL_SMALL_STACK
    byte* priv;
    byte* pub;
#else
    byte priv[ECC_MAXSIZE+1];
    byte pub[2*(ECC_MAXSIZE+1)]; /* public key has two parts plus header */
#endif
    byte* pubData = NULL;

    if (input == NULL || inOutIdx == NULL || key == NULL || inSz == 0)
        return BAD_FUNC_ARG;

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

    if (GetMyVersion(input, inOutIdx, &version, inSz) < 0)
        return ASN_PARSE_E;

    if (*inOutIdx >= inSz)
        return ASN_PARSE_E;

    b = input[*inOutIdx];
    *inOutIdx += 1;

    /* priv type */
    if (b != 4 && b != 6 && b != 7)
        return ASN_PARSE_E;

    if (GetLength(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

    if (length > ECC_MAXSIZE)
        return BUFFER_E;

#ifdef WOLFSSL_SMALL_STACK
    priv = (byte*)XMALLOC(ECC_MAXSIZE+1, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (priv == NULL)
        return MEMORY_E;

    pub = (byte*)XMALLOC(2*(ECC_MAXSIZE+1), key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (pub == NULL) {
        XFREE(priv, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
#endif

    /* priv key */
    privSz = length;
    XMEMCPY(priv, &input[*inOutIdx], privSz);
    *inOutIdx += length;

    if ((*inOutIdx + 1) < inSz) {
        /* prefix 0, may have */
        b = input[*inOutIdx];
        if (b == ECC_PREFIX_0) {
            *inOutIdx += 1;

            if (GetLength(input, inOutIdx, &length, inSz) <= 0)
                ret = ASN_PARSE_E;
            else {
                ret = GetObjectId(input, inOutIdx, &oidSum, oidIgnoreType,
                                  inSz);
                if (ret == 0) {
                    if ((ret = CheckCurve(oidSum)) < 0)
                        ret = ECC_CURVE_OID_E;
                    else {
                        curve_id = ret;
                        ret = 0;
                    }
                }
            }
        }
    }

    if (ret == 0 && (*inOutIdx + 1) < inSz) {
        /* prefix 1 */
        b = input[*inOutIdx];
        *inOutIdx += 1;

        if (b != ECC_PREFIX_1) {
            ret = ASN_ECC_KEY_E;
        }
        else if (GetLength(input, inOutIdx, &length, inSz) <= 0) {
            ret = ASN_PARSE_E;
        }
        else {
            /* key header */
            ret = CheckBitString(input, inOutIdx, &length, inSz, 0, NULL);
            if (ret == 0) {
                /* pub key */
                pubSz = length;
                if (pubSz < 2*(ECC_MAXSIZE+1)) {
                    XMEMCPY(pub, &input[*inOutIdx], pubSz);
                    *inOutIdx += length;
                    pubData = pub;
                }
                else
                    ret = BUFFER_E;
            }
        }
    }

    if (ret == 0) {
        ret = wc_ecc_import_private_key_ex(priv, privSz, pubData, pubSz, key,
                                                                      curve_id);
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(priv, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(pub,  key->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}


#ifdef WOLFSSL_CUSTOM_CURVES
static void ByteToHex(byte n, char* str)
{
    const char hexChar[] = { '0', '1', '2', '3', '4', '5', '6', '7',
                                    '8', '9', 'a', 'b', 'c', 'd', 'e', 'f' };

    str[0] = hexChar[n >> 4];
    str[1] = hexChar[n & 0xf];
}

/* returns 0 on success */
static int ASNToHexString(const byte* input, word32* inOutIdx, char** out,
                          word32 inSz, void* heap, int heapType)
{
    int len;
    int i;
    char* str;
    word32 localIdx;
    byte   tag;

    if (*inOutIdx >= inSz) {
        return BUFFER_E;
    }

    localIdx = *inOutIdx;
    if (GetASNTag(input, &localIdx, &tag, inSz) == 0 && tag == ASN_INTEGER) {
        if (GetASNInt(input, inOutIdx, &len, inSz) < 0)
            return ASN_PARSE_E;
    }
    else {
        if (GetOctetString(input, inOutIdx, &len, inSz) < 0)
            return ASN_PARSE_E;
    }

    str = (char*)XMALLOC(len * 2 + 1, heap, heapType);
    for (i=0; i<len; i++)
        ByteToHex(input[*inOutIdx + i], str + i*2);
    str[len*2] = '\0';

    *inOutIdx += len;
    *out = str;

    (void)heap;
    (void)heapType;

    return 0;
}
#endif /* WOLFSSL_CUSTOM_CURVES */

#ifdef WOLFSSL_CUSTOM_CURVES
static int EccKeyParamCopy(char** dst, char* src)
{
    int ret = 0;
#ifdef WOLFSSL_ECC_CURVE_STATIC
    word32 length;
#endif

    if (dst == NULL || src == NULL)
        return BAD_FUNC_ARG;

#ifndef WOLFSSL_ECC_CURVE_STATIC
    *dst = src;
#else
    length = (int)XSTRLEN(src) + 1;
    if (length > MAX_ECC_STRING) {
        WOLFSSL_MSG("ECC Param too large for buffer");
        ret = BUFFER_E;
    }
    else {
        XSTRNCPY(*dst, src, length);
    }
    XFREE(src, key->heap, DYNAMIC_TYPE_ECC_BUFFER);
#endif

    return ret;
}
#endif /* WOLFSSL_CUSTOM_CURVES */

int wc_EccPublicKeyDecode(const byte* input, word32* inOutIdx,
                          ecc_key* key, word32 inSz)
{
    int    ret;
    int    version, length;
    int    curve_id = ECC_CURVE_DEF;
    word32 oidSum, localIdx;
    byte   tag, isPrivFormat = 0;

    if (input == NULL || inOutIdx == NULL || key == NULL || inSz == 0)
        return BAD_FUNC_ARG;

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

    /* Check if ECC private key is being used and skip private portion */
    if (GetMyVersion(input, inOutIdx, &version, inSz) >= 0) {
        isPrivFormat = 1;

        /* Type private key */
        if (*inOutIdx >= inSz)
            return ASN_PARSE_E;
        tag = input[*inOutIdx];
        *inOutIdx += 1;
        if (tag != 4 && tag != 6 && tag != 7)
            return ASN_PARSE_E;

        /* Skip Private Key */
        if (GetLength(input, inOutIdx, &length, inSz) < 0)
            return ASN_PARSE_E;
        if (length > ECC_MAXSIZE)
            return BUFFER_E;
        *inOutIdx += length;

        /* Private Curve Header */
        if (*inOutIdx >= inSz)
            return ASN_PARSE_E;
        tag = input[*inOutIdx];
        *inOutIdx += 1;
        if (tag != ECC_PREFIX_0)
            return ASN_ECC_KEY_E;
        if (GetLength(input, inOutIdx, &length, inSz) <= 0)
            return ASN_PARSE_E;
    }
    /* Standard ECC public key */
    else {
        if (GetSequence(input, inOutIdx, &length, inSz) < 0)
            return ASN_PARSE_E;

        ret = SkipObjectId(input, inOutIdx, inSz);
        if (ret != 0)
            return ret;
    }

    if (*inOutIdx >= inSz) {
        return BUFFER_E;
    }

    localIdx = *inOutIdx;
    if (GetASNTag(input, &localIdx, &tag, inSz) == 0 &&
            tag == (ASN_SEQUENCE | ASN_CONSTRUCTED)) {
#ifdef WOLFSSL_CUSTOM_CURVES
        ecc_set_type* curve;
        int len;
        char* point = NULL;

        ret = 0;

        curve = (ecc_set_type*)XMALLOC(sizeof(*curve), key->heap,
                                                       DYNAMIC_TYPE_ECC_BUFFER);
        if (curve == NULL)
            ret = MEMORY_E;

        if (ret == 0) {
            static const char customName[] = "Custom";
            XMEMSET(curve, 0, sizeof(*curve));
        #ifndef WOLFSSL_ECC_CURVE_STATIC
            curve->name = customName;
        #else
            XMEMCPY((void*)curve->name, customName, sizeof(customName));
        #endif
            curve->id = ECC_CURVE_CUSTOM;

            if (GetSequence(input, inOutIdx, &length, inSz) < 0)
                ret = ASN_PARSE_E;
        }

        if (ret == 0) {
            GetInteger7Bit(input, inOutIdx, inSz);
            if (GetSequence(input, inOutIdx, &length, inSz) < 0)
                ret = ASN_PARSE_E;
        }
        if (ret == 0) {
            char* p = NULL;
            SkipObjectId(input, inOutIdx, inSz);
            ret = ASNToHexString(input, inOutIdx, &p, inSz,
                                            key->heap, DYNAMIC_TYPE_ECC_BUFFER);
            if (ret == 0)
                ret = EccKeyParamCopy((char**)&curve->prime, p);
        }
        if (ret == 0) {
            curve->size = (int)XSTRLEN(curve->prime) / 2;

            if (GetSequence(input, inOutIdx, &length, inSz) < 0)
                ret = ASN_PARSE_E;
        }
        if (ret == 0) {
            char* af = NULL;
            ret = ASNToHexString(input, inOutIdx, &af, inSz,
                                            key->heap, DYNAMIC_TYPE_ECC_BUFFER);
            if (ret == 0)
                ret = EccKeyParamCopy((char**)&curve->Af, af);
        }
        if (ret == 0) {
            char* bf = NULL;
            ret = ASNToHexString(input, inOutIdx, &bf, inSz,
                                            key->heap, DYNAMIC_TYPE_ECC_BUFFER);
            if (ret == 0)
                ret = EccKeyParamCopy((char**)&curve->Bf, bf);
        }
        if (ret == 0) {
            localIdx = *inOutIdx;
            if (*inOutIdx < inSz && GetASNTag(input, &localIdx, &tag, inSz)
                    == 0 && tag == ASN_BIT_STRING) {
                len = 0;
                ret = GetASNHeader(input, ASN_BIT_STRING, inOutIdx, &len, inSz);
                *inOutIdx += len;
            }
        }
        if (ret == 0) {
            ret = ASNToHexString(input, inOutIdx, (char**)&point, inSz,
                                            key->heap, DYNAMIC_TYPE_ECC_BUFFER);

            /* sanity check that point buffer is not smaller than the expected
             * size to hold ( 0 4 || Gx || Gy )
             * where Gx and Gy are each the size of curve->size * 2 */
            if (ret == 0 && (int)XSTRLEN(point) < (curve->size * 4) + 2) {
                XFREE(point, key->heap, DYNAMIC_TYPE_ECC_BUFFER);
                ret = BUFFER_E;
            }
        }
        if (ret == 0) {
        #ifndef WOLFSSL_ECC_CURVE_STATIC
            curve->Gx = (const char*)XMALLOC(curve->size * 2 + 2, key->heap,
                                                       DYNAMIC_TYPE_ECC_BUFFER);
            curve->Gy = (const char*)XMALLOC(curve->size * 2 + 2, key->heap,
                                                       DYNAMIC_TYPE_ECC_BUFFER);
            if (curve->Gx == NULL || curve->Gy == NULL) {
                XFREE(point, key->heap, DYNAMIC_TYPE_ECC_BUFFER);
                ret = MEMORY_E;
            }
        #else
            if (curve->size * 2 + 2 > MAX_ECC_STRING) {
                WOLFSSL_MSG("curve size is too large to fit in buffer");
                ret = BUFFER_E;
            }
        #endif
        }
        if (ret == 0) {
            char* o = NULL;

            XMEMCPY((char*)curve->Gx, point + 2, curve->size * 2);
            XMEMCPY((char*)curve->Gy, point + curve->size * 2 + 2,
                                                               curve->size * 2);
            ((char*)curve->Gx)[curve->size * 2] = '\0';
            ((char*)curve->Gy)[curve->size * 2] = '\0';
            XFREE(point, key->heap, DYNAMIC_TYPE_ECC_BUFFER);
            ret = ASNToHexString(input, inOutIdx, &o, inSz,
                                            key->heap, DYNAMIC_TYPE_ECC_BUFFER);
            if (ret == 0)
                ret = EccKeyParamCopy((char**)&curve->order, o);
        }
        if (ret == 0) {
            curve->cofactor = GetInteger7Bit(input, inOutIdx, inSz);

        #ifndef WOLFSSL_ECC_CURVE_STATIC
            curve->oid = NULL;
        #else
            XMEMSET((void*)curve->oid, 0, sizeof(curve->oid));
        #endif
            curve->oidSz = 0;
            curve->oidSum = 0;

            if (wc_ecc_set_custom_curve(key, curve) < 0) {
                ret = ASN_PARSE_E;
            }
        #ifdef WOLFSSL_CUSTOM_CURVES
            key->deallocSet = 1;
        #endif
            curve = NULL;
        }
        if (curve != NULL)
            wc_ecc_free_curve(curve, key->heap);

        if (ret < 0)
            return ret;
#else
        return ASN_PARSE_E;
#endif /* WOLFSSL_CUSTOM_CURVES */
    }
    else {
        /* ecc params information */
        ret = GetObjectId(input, inOutIdx, &oidSum, oidIgnoreType, inSz);
        if (ret != 0)
            return ret;

        /* get curve id */
        if ((ret = CheckCurve(oidSum)) < 0)
            return ECC_CURVE_OID_E;
        else {
            curve_id = ret;
        }
    }

    if (isPrivFormat) {
        /* Public Curve Header - skip */
        if (*inOutIdx >= inSz)
            return ASN_PARSE_E;
        tag = input[*inOutIdx];
        *inOutIdx += 1;
        if (tag != ECC_PREFIX_1)
            return ASN_ECC_KEY_E;
        if (GetLength(input, inOutIdx, &length, inSz) <= 0)
            return ASN_PARSE_E;
    }

    /* key header */
    ret = CheckBitString(input, inOutIdx, &length, inSz, 1, NULL);
    if (ret != 0)
        return ret;

    /* This is the raw point data compressed or uncompressed. */
    if (wc_ecc_import_x963_ex(input + *inOutIdx, length, key,
                                                            curve_id) != 0) {
        return ASN_ECC_KEY_E;
    }

    *inOutIdx += length;

    return 0;
}

#if defined(HAVE_ECC_KEY_EXPORT) && !defined(NO_ASN_CRYPT)
/* build DER formatted ECC key, include optional public key if requested,
 * return length on success, negative on error */
static int wc_BuildEccKeyDer(ecc_key* key, byte* output, word32 inLen,
                             int pubIn)
{
    byte   curve[MAX_ALGO_SZ+2];
    byte   ver[MAX_VERSION_SZ];
    byte   seq[MAX_SEQ_SZ];
    byte   *prv = NULL, *pub = NULL;
    int    ret, totalSz, curveSz, verSz;
    int    privHdrSz  = ASN_ECC_HEADER_SZ;
    int    pubHdrSz   = ASN_ECC_CONTEXT_SZ + ASN_ECC_HEADER_SZ;

    word32 idx = 0, prvidx = 0, pubidx = 0, curveidx = 0;
    word32 seqSz, privSz, pubSz = ECC_BUFSIZE;

    if (key == NULL || output == NULL || inLen == 0)
        return BAD_FUNC_ARG;

    /* curve */
    curve[curveidx++] = ECC_PREFIX_0;
    curveidx++ /* to put the size after computation */;
    curveSz = SetCurve(key, curve+curveidx);
    if (curveSz < 0)
        return curveSz;
    /* set computed size */
    curve[1] = (byte)curveSz;
    curveidx += curveSz;

    /* private */
    privSz = key->dp->size;
    prv = (byte*)XMALLOC(privSz + privHdrSz + MAX_SEQ_SZ,
                         key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (prv == NULL) {
        return MEMORY_E;
    }
    prvidx += SetOctetString8Bit(key->dp->size, &prv[prvidx]);
    ret = wc_ecc_export_private_only(key, prv + prvidx, &privSz);
    if (ret < 0) {
        XFREE(prv, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        return ret;
    }
    prvidx += privSz;

    /* pubIn */
    if (pubIn) {
        ret = wc_ecc_export_x963(key, NULL, &pubSz);
        if (ret != LENGTH_ONLY_E) {
            XFREE(prv, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            return ret;
        }

        pub = (byte*)XMALLOC(pubSz + pubHdrSz + MAX_SEQ_SZ,
                             key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        if (pub == NULL) {
            XFREE(prv, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            return MEMORY_E;
        }

        pub[pubidx++] = ECC_PREFIX_1;
        if (pubSz > 128) /* leading zero + extra size byte */
            pubidx += SetLength(pubSz + ASN_ECC_CONTEXT_SZ + 2, pub+pubidx);
        else /* leading zero */
            pubidx += SetLength(pubSz + ASN_ECC_CONTEXT_SZ + 1, pub+pubidx);

        /* SetBitString adds leading zero */
        pubidx += SetBitString(pubSz, 0, pub + pubidx);
        ret = wc_ecc_export_x963(key, pub + pubidx, &pubSz);
        if (ret != 0) {
            XFREE(prv, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(pub, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
            return ret;
        }
        pubidx += pubSz;
    }

    /* make headers */
    verSz = SetMyVersion(1, ver, FALSE);
    seqSz = SetSequence(verSz + prvidx + pubidx + curveidx, seq);

    totalSz = prvidx + pubidx + curveidx + verSz + seqSz;
    if (totalSz > (int)inLen) {
        XFREE(prv, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        if (pubIn) {
            XFREE(pub, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        }
        return BAD_FUNC_ARG;
    }

    /* write out */
    /* seq */
    XMEMCPY(output + idx, seq, seqSz);
    idx = seqSz;

    /* ver */
    XMEMCPY(output + idx, ver, verSz);
    idx += verSz;

    /* private */
    XMEMCPY(output + idx, prv, prvidx);
    idx += prvidx;
    XFREE(prv, key->heap, DYNAMIC_TYPE_TMP_BUFFER);

    /* curve */
    XMEMCPY(output + idx, curve, curveidx);
    idx += curveidx;

    /* pubIn */
    if (pubIn) {
        XMEMCPY(output + idx, pub, pubidx);
        /* idx += pubidx;  not used after write, if more data remove comment */
        XFREE(pub, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    }

    return totalSz;
}

/* Write a Private ecc key, including public to DER format,
 * length on success else < 0 */
int wc_EccKeyToDer(ecc_key* key, byte* output, word32 inLen)
{
    return wc_BuildEccKeyDer(key, output, inLen, 1);
}


/* Write only private ecc key to DER format,
 * length on success else < 0 */
int wc_EccPrivateKeyToDer(ecc_key* key, byte* output, word32 inLen)
{
    return wc_BuildEccKeyDer(key, output, inLen, 0);
}

#ifdef HAVE_PKCS8
/* Write only private ecc key to unencrypted PKCS#8 format.
 *
 * If output is NULL, places required PKCS#8 buffer size in outLen and
 * returns LENGTH_ONLY_E.
 *
 * return length on success else < 0 */
int wc_EccPrivateKeyToPKCS8(ecc_key* key, byte* output, word32* outLen)
{
    int ret, tmpDerSz;
    int algoID = 0;
    word32 oidSz = 0;
    word32 pkcs8Sz = 0;
    const byte* curveOID = NULL;
    byte* tmpDer = NULL;

    if (key == NULL || outLen == NULL)
        return BAD_FUNC_ARG;

    /* set algoID, get curve OID */
    algoID = ECDSAk;
    ret = wc_ecc_get_oid(key->dp->oidSum, &curveOID, &oidSz);
    if (ret < 0)
        return ret;

    /* temp buffer for plain DER key */
    tmpDer = (byte*)XMALLOC(ECC_BUFSIZE, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (tmpDer == NULL)
        return MEMORY_E;

    XMEMSET(tmpDer, 0, ECC_BUFSIZE);

    tmpDerSz = wc_BuildEccKeyDer(key, tmpDer, ECC_BUFSIZE, 0);
    if (tmpDerSz < 0) {
        XFREE(tmpDer, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        return tmpDerSz;
    }

    /* get pkcs8 expected output size */
    ret = wc_CreatePKCS8Key(NULL, &pkcs8Sz, tmpDer, tmpDerSz, algoID,
                            curveOID, oidSz);
    if (ret != LENGTH_ONLY_E) {
        XFREE(tmpDer, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        return ret;
    }

    if (output == NULL) {
        XFREE(tmpDer, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        *outLen = pkcs8Sz;
        return LENGTH_ONLY_E;

    } else if (*outLen < pkcs8Sz) {
        XFREE(tmpDer, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        WOLFSSL_MSG("Input buffer too small for ECC PKCS#8 key");
        return BUFFER_E;
    }

    ret = wc_CreatePKCS8Key(output, &pkcs8Sz, tmpDer, tmpDerSz,
                            algoID, curveOID, oidSz);
    if (ret < 0) {
        XFREE(tmpDer, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
        return ret;
    }

    XFREE(tmpDer, key->heap, DYNAMIC_TYPE_TMP_BUFFER);

    *outLen = ret;
    return ret;
}
#endif /* HAVE_PKCS8 */
#endif /* HAVE_ECC_KEY_EXPORT && !NO_ASN_CRYPT */
#endif /* HAVE_ECC */


#ifdef HAVE_ED25519

int wc_Ed25519PrivateKeyDecode(const byte* input, word32* inOutIdx,
                               ed25519_key* key, word32 inSz)
{
    word32      oid;
    int         ret, version, length, endKeyIdx, privSz, pubSz;
    const byte* priv;
    const byte* pub;

    if (input == NULL || inOutIdx == NULL || key == NULL || inSz == 0)
        return BAD_FUNC_ARG;

    if (GetSequence(input, inOutIdx, &length, inSz) >= 0) {
        endKeyIdx = *inOutIdx + length;

        if (GetMyVersion(input, inOutIdx, &version, inSz) < 0)
            return ASN_PARSE_E;
        if (version != 0) {
            WOLFSSL_MSG("Unrecognized version of ED25519 private key");
            return ASN_PARSE_E;
        }

        if (GetAlgoId(input, inOutIdx, &oid, oidKeyType, inSz) < 0)
            return ASN_PARSE_E;
        if (oid != ED25519k)
            return ASN_PARSE_E;

        if (GetOctetString(input, inOutIdx, &length, inSz) < 0)
            return ASN_PARSE_E;

        if (GetOctetString(input, inOutIdx, &privSz, inSz) < 0)
            return ASN_PARSE_E;

        priv = input + *inOutIdx;
        *inOutIdx += privSz;
    }
    else {
        if (GetOctetString(input, inOutIdx, &privSz, inSz) < 0)
            return ASN_PARSE_E;

        if (privSz != 32)
            return ASN_PARSE_E;

        priv = input + *inOutIdx;
        *inOutIdx += privSz;
        endKeyIdx = *inOutIdx;
    }

    if (endKeyIdx == (int)*inOutIdx) {
        ret = wc_ed25519_import_private_only(priv, privSz, key);
    }
    else {
        if (GetASNHeader(input, ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | 1,
                         inOutIdx, &length, inSz) < 0) {
            return ASN_PARSE_E;
        }
        if (GetOctetString(input, inOutIdx, &pubSz, inSz) < 0)
            return ASN_PARSE_E;
        pub = input + *inOutIdx;
        *inOutIdx += pubSz;

        ret = wc_ed25519_import_private_key(priv, privSz, pub, pubSz, key);
    }
    if (ret == 0 && endKeyIdx != (int)*inOutIdx)
        return ASN_PARSE_E;

    return ret;
}


int wc_Ed25519PublicKeyDecode(const byte* input, word32* inOutIdx,
                              ed25519_key* key, word32 inSz)
{
    int    length;
    int    ret;

    if (input == NULL || inOutIdx == NULL || key == NULL || inSz == 0)
        return BAD_FUNC_ARG;

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

    ret = SkipObjectId(input, inOutIdx, inSz);
    if (ret != 0)
        return ret;

    /* key header */
    ret = CheckBitString(input, inOutIdx, NULL, inSz, 1, NULL);
    if (ret != 0)
        return ret;

    /* This is the raw point data compressed or uncompressed. */
    if (wc_ed25519_import_public(input + *inOutIdx, inSz - *inOutIdx, key) != 0)
        return ASN_ECC_KEY_E;

    return 0;
}


#ifdef WOLFSSL_KEY_GEN

/* build DER formatted ED25519 key,
 * return length on success, negative on error */
static int wc_BuildEd25519KeyDer(ed25519_key* key, byte* output, word32 inLen,
                                 int pubOut)
{
    byte   algoArray[MAX_ALGO_SZ];
    byte   ver[MAX_VERSION_SZ];
    byte   seq[MAX_SEQ_SZ];
    int    ret;
    word32 idx = 0, seqSz, verSz, algoSz, privSz, pubSz = 0;

    if (key == NULL || output == NULL || inLen == 0)
        return BAD_FUNC_ARG;

    if (pubOut)
        pubSz = 2 + 2 + ED25519_PUB_KEY_SIZE;
    privSz = 2 + 2 + ED25519_KEY_SIZE;
    algoSz = SetAlgoID(ED25519k, algoArray, oidKeyType, 0);
    verSz  = SetMyVersion(0, ver, FALSE);
    seqSz  = SetSequence(verSz + algoSz + privSz + pubSz, seq);

    if (seqSz + verSz + algoSz + privSz + pubSz > inLen)
        return BAD_FUNC_ARG;

    /* write out */
    /* seq */
    XMEMCPY(output + idx, seq, seqSz);
    idx = seqSz;
    /* ver */
    XMEMCPY(output + idx, ver, verSz);
    idx += verSz;
    /* algo */
    XMEMCPY(output + idx, algoArray, algoSz);
    idx += algoSz;
    /* privKey */
    idx += SetOctetString(2 + ED25519_KEY_SIZE, output + idx);
    idx += SetOctetString(ED25519_KEY_SIZE, output + idx);
    ret = wc_ed25519_export_private_only(key, output + idx, &privSz);
    if (ret != 0)
        return ret;
    idx += privSz;
    /* pubKey */
    if (pubOut) {
        idx += SetExplicit(1, 2 + ED25519_PUB_KEY_SIZE, output + idx);
        idx += SetOctetString(ED25519_KEY_SIZE, output + idx);
        ret = wc_ed25519_export_public(key, output + idx, &pubSz);
        if (ret != 0)
            return ret;
        idx += pubSz;
    }

    return idx;
}

/* Write a Private ecc key, including public to DER format,
 * length on success else < 0 */
int wc_Ed25519KeyToDer(ed25519_key* key, byte* output, word32 inLen)
{
    return wc_BuildEd25519KeyDer(key, output, inLen, 1);
}



/* Write only private ecc key to DER format,
 * length on success else < 0 */
int wc_Ed25519PrivateKeyToDer(ed25519_key* key, byte* output, word32 inLen)
{
    return wc_BuildEd25519KeyDer(key, output, inLen, 0);
}

#endif /* WOLFSSL_KEY_GEN */

#endif /* HAVE_ED25519 */

#ifdef HAVE_ED448

int wc_Ed448PrivateKeyDecode(const byte* input, word32* inOutIdx,
                             ed448_key* key, word32 inSz)
{
    word32      oid;
    int         ret, version, length, endKeyIdx, privSz, pubSz;
    const byte* priv;
    const byte* pub;

    if (input == NULL || inOutIdx == NULL || key == NULL || inSz == 0)
        return BAD_FUNC_ARG;

    if (GetSequence(input, inOutIdx, &length, inSz) >= 0) {
        endKeyIdx = *inOutIdx + length;

        if (GetMyVersion(input, inOutIdx, &version, inSz) < 0)
            return ASN_PARSE_E;
        if (version != 0) {
            WOLFSSL_MSG("Unrecognized version of ED448 private key");
            return ASN_PARSE_E;
        }

        if (GetAlgoId(input, inOutIdx, &oid, oidKeyType, inSz) < 0)
            return ASN_PARSE_E;
        if (oid != ED448k)
            return ASN_PARSE_E;

        if (GetOctetString(input, inOutIdx, &length, inSz) < 0)
            return ASN_PARSE_E;

        if (GetOctetString(input, inOutIdx, &privSz, inSz) < 0)
            return ASN_PARSE_E;

        priv = input + *inOutIdx;
        *inOutIdx += privSz;
    }
    else {
        if (GetOctetString(input, inOutIdx, &privSz, inSz) < 0)
            return ASN_PARSE_E;

        if (privSz != 57)
            return ASN_PARSE_E;

        priv = input + *inOutIdx;
        *inOutIdx += privSz;
        endKeyIdx = *inOutIdx;
    }

    if (endKeyIdx == (int)*inOutIdx) {
        ret = wc_ed448_import_private_only(priv, privSz, key);
    }
    else {
        if (GetASNHeader(input, ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | 1,
                         inOutIdx, &length, inSz) < 0) {
            return ASN_PARSE_E;
        }
        if (GetOctetString(input, inOutIdx, &pubSz, inSz) < 0)
            return ASN_PARSE_E;
        pub = input + *inOutIdx;
        *inOutIdx += pubSz;

        ret = wc_ed448_import_private_key(priv, privSz, pub, pubSz, key);
    }
    if (ret == 0 && endKeyIdx != (int)*inOutIdx)
        return ASN_PARSE_E;

    return ret;
}


int wc_Ed448PublicKeyDecode(const byte* input, word32* inOutIdx,
                            ed448_key* key, word32 inSz)
{
    int    length;
    int    ret;

    if (input == NULL || inOutIdx == NULL || key == NULL || inSz == 0)
        return BAD_FUNC_ARG;

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

    ret = SkipObjectId(input, inOutIdx, inSz);
    if (ret != 0)
        return ret;

    /* key header */
    ret = CheckBitString(input, inOutIdx, NULL, inSz, 1, NULL);
    if (ret != 0)
        return ret;

    /* This is the raw point data compressed or uncompressed. */
    if (wc_ed448_import_public(input + *inOutIdx, inSz - *inOutIdx, key) != 0)
        return ASN_ECC_KEY_E;

    return 0;
}


#ifdef WOLFSSL_KEY_GEN

/* build DER formatted ED448 key,
 * return length on success, negative on error */
static int wc_BuildEd448KeyDer(ed448_key* key, byte* output, word32 inLen,
                               int pubOut)
{
    byte   algoArray[MAX_ALGO_SZ];
    byte   ver[MAX_VERSION_SZ];
    byte   seq[MAX_SEQ_SZ];
    int    ret;
    word32 idx = 0, seqSz, verSz, algoSz, privSz, pubSz = 0;

    if (key == NULL || output == NULL || inLen == 0)
        return BAD_FUNC_ARG;

    if (pubOut) {
        pubSz = 2 + 2 + ED448_PUB_KEY_SIZE;
    }
    privSz = 2 + 2 + ED448_KEY_SIZE;
    algoSz = SetAlgoID(ED448k, algoArray, oidKeyType, 0);
    verSz  = SetMyVersion(0, ver, FALSE);
    seqSz  = SetSequence(verSz + algoSz + privSz + pubSz, seq);

    if (seqSz + verSz + algoSz + privSz + pubSz > inLen)
        return BAD_FUNC_ARG;

    /* write out */
    /* seq */
    XMEMCPY(output + idx, seq, seqSz);
    idx = seqSz;
    /* ver */
    XMEMCPY(output + idx, ver, verSz);
    idx += verSz;
    /* algo */
    XMEMCPY(output + idx, algoArray, algoSz);
    idx += algoSz;
    /* privKey */
    idx += SetOctetString(2 + ED448_KEY_SIZE, output + idx);
    idx += SetOctetString(ED448_KEY_SIZE, output + idx);
    ret = wc_ed448_export_private_only(key, output + idx, &privSz);
    if (ret != 0)
        return ret;
    idx += privSz;
    /* pubKey */
    if (pubOut) {
        idx += SetExplicit(1, 2 + ED448_PUB_KEY_SIZE, output + idx);
        idx += SetOctetString(ED448_KEY_SIZE, output + idx);
        ret = wc_ed448_export_public(key, output + idx, &pubSz);
        if (ret != 0)
            return ret;
        idx += pubSz;
    }

    return idx;
}

/* Write a Private ecc key, including public to DER format,
 * length on success else < 0 */
int wc_Ed448KeyToDer(ed448_key* key, byte* output, word32 inLen)
{
    return wc_BuildEd448KeyDer(key, output, inLen, 1);
}



/* Write only private ecc key to DER format,
 * length on success else < 0 */
int wc_Ed448PrivateKeyToDer(ed448_key* key, byte* output, word32 inLen)
{
    return wc_BuildEd448KeyDer(key, output, inLen, 0);
}

#endif /* WOLFSSL_KEY_GEN */

#endif /* HAVE_ED448 */

#if defined(HAVE_OCSP) || defined(HAVE_CRL)

/* Get raw Date only, no processing, 0 on success */
static int GetBasicDate(const byte* source, word32* idx, byte* date,
                        byte* format, int maxIdx)
{
    int    ret, length;
    const byte *datePtr = NULL;

    WOLFSSL_ENTER("GetBasicDate");

    ret = GetDateInfo(source, idx, &datePtr, format, &length, maxIdx);
    if (ret < 0)
        return ret;

    XMEMCPY(date, datePtr, length);

    return 0;
}

#endif /* HAVE_OCSP || HAVE_CRL */


#ifdef HAVE_OCSP

static int GetEnumerated(const byte* input, word32* inOutIdx, int *value,
        int sz)
{
    word32 idx = *inOutIdx;
    word32 len;
    byte   tag;

    WOLFSSL_ENTER("GetEnumerated");

    *value = 0;

    if (GetASNTag(input, &idx, &tag, sz) < 0)
        return ASN_PARSE_E;

    if (tag != ASN_ENUMERATED)
        return ASN_PARSE_E;

    if ((int)idx >= sz)
        return BUFFER_E;

    len = input[idx++];
    if (len > 4 || (int)(len + idx) > sz)
        return ASN_PARSE_E;

    while (len--) {
        *value  = *value << 8 | input[idx++];
    }

    *inOutIdx = idx;

    return *value;
}


static int DecodeSingleResponse(byte* source,
                            word32* ioIndex, OcspResponse* resp, word32 size)
{
    word32 idx = *ioIndex, prevIndex, oid, localIdx;
    int length, wrapperSz;
    CertStatus* cs = resp->status;
    int ret;
    byte tag;

    WOLFSSL_ENTER("DecodeSingleResponse");

    /* Outer wrapper of the SEQUENCE OF Single Responses. */
    if (GetSequence(source, &idx, &wrapperSz, size) < 0)
        return ASN_PARSE_E;

    prevIndex = idx;

    /* When making a request, we only request one status on one certificate
     * at a time. There should only be one SingleResponse */

    /* Wrapper around the Single Response */
    if (GetSequence(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;

    /* Wrapper around the CertID */
    if (GetSequence(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;
    /* Skip the hash algorithm */
    if (GetAlgoId(source, &idx, &oid, oidIgnoreType, size) < 0)
        return ASN_PARSE_E;
    /* Save reference to the hash of CN */
    ret = GetOctetString(source, &idx, &length, size);
    if (ret < 0)
        return ret;
    resp->issuerHash = source + idx;
    idx += length;
    /* Save reference to the hash of the issuer public key */
    ret = GetOctetString(source, &idx, &length, size);
    if (ret < 0)
        return ret;
    resp->issuerKeyHash = source + idx;
    idx += length;

    /* Get serial number */
    if (GetSerialNumber(source, &idx, cs->serial, &cs->serialSz, size) < 0)
        return ASN_PARSE_E;

    if ( idx >= size )
        return BUFFER_E;

    /* CertStatus */
    switch (source[idx++])
    {
        case (ASN_CONTEXT_SPECIFIC | CERT_GOOD):
            cs->status = CERT_GOOD;
            idx++;
            break;
        case (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | CERT_REVOKED):
            cs->status = CERT_REVOKED;
            if (GetLength(source, &idx, &length, size) < 0)
                return ASN_PARSE_E;
            idx += length;
            break;
        case (ASN_CONTEXT_SPECIFIC | CERT_UNKNOWN):
            cs->status = CERT_UNKNOWN;
            idx++;
            break;
        default:
            return ASN_PARSE_E;
    }

#if defined(OPENSSL_ALL) || defined(WOLFSSL_NGINX) || defined(WOLFSSL_HAPROXY)
    cs->thisDateAsn = source + idx;
    localIdx = 0;
    if (GetDateInfo(cs->thisDateAsn, &localIdx, NULL,
                    (byte*)&cs->thisDateParsed.type,
                    &cs->thisDateParsed.length, size) < 0)
        return ASN_PARSE_E;
    XMEMCPY(cs->thisDateParsed.data,
            cs->thisDateAsn + localIdx - cs->thisDateParsed.length,
            cs->thisDateParsed.length);
#endif
    if (GetBasicDate(source, &idx, cs->thisDate,
                                                &cs->thisDateFormat, size) < 0)
        return ASN_PARSE_E;

#ifndef NO_ASN_TIME
#ifndef WOLFSSL_NO_OCSP_DATE_CHECK
    if (!XVALIDATE_DATE(cs->thisDate, cs->thisDateFormat, BEFORE))
        return ASN_BEFORE_DATE_E;
#endif
#endif

    /* The following items are optional. Only check for them if there is more
     * unprocessed data in the singleResponse wrapper. */

    localIdx = idx;
    if (((int)(idx - prevIndex) < wrapperSz) &&
        GetASNTag(source, &localIdx, &tag, size) == 0 &&
        tag == (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 0))
    {
        idx++;
        if (GetLength(source, &idx, &length, size) < 0)
            return ASN_PARSE_E;
#if defined(OPENSSL_ALL) || defined(WOLFSSL_NGINX) || defined(WOLFSSL_HAPROXY)
        cs->nextDateAsn = source + idx;
        localIdx = 0;
        if (GetDateInfo(cs->nextDateAsn, &localIdx, NULL,
                        (byte*)&cs->nextDateParsed.type,
                        &cs->nextDateParsed.length, size) < 0)
            return ASN_PARSE_E;
        XMEMCPY(cs->nextDateParsed.data,
                cs->nextDateAsn + localIdx - cs->nextDateParsed.length,
                cs->nextDateParsed.length);
#endif
        if (GetBasicDate(source, &idx, cs->nextDate,
                                                &cs->nextDateFormat, size) < 0)
            return ASN_PARSE_E;

#ifndef NO_ASN_TIME
#ifndef WOLFSSL_NO_OCSP_DATE_CHECK
        if (!XVALIDATE_DATE(cs->nextDate, cs->nextDateFormat, AFTER))
            return ASN_AFTER_DATE_E;
#endif
#endif
    }

    localIdx = idx;
    if (((int)(idx - prevIndex) < wrapperSz) &&
        GetASNTag(source, &localIdx, &tag, size) == 0 &&
        tag == (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 1))
    {
        idx++;
        if (GetLength(source, &idx, &length, size) < 0)
            return ASN_PARSE_E;
        idx += length;
    }

    *ioIndex = idx;

    return 0;
}

static int DecodeOcspRespExtensions(byte* source,
                            word32* ioIndex, OcspResponse* resp, word32 sz)
{
    word32 idx = *ioIndex;
    int length;
    int ext_bound; /* boundary index for the sequence of extensions */
    word32 oid;
    int ret;
    byte tag;

    WOLFSSL_ENTER("DecodeOcspRespExtensions");

    if ((idx + 1) > sz)
        return BUFFER_E;

    if (GetASNTag(source, &idx, &tag, sz) < 0)
        return ASN_PARSE_E;

    if (tag != (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 1))
        return ASN_PARSE_E;

    if (GetLength(source, &idx, &length, sz) < 0)
        return ASN_PARSE_E;

    if (GetSequence(source, &idx, &length, sz) < 0)
        return ASN_PARSE_E;

    ext_bound = idx + length;

    while (idx < (word32)ext_bound) {
        word32 localIdx;

        if (GetSequence(source, &idx, &length, sz) < 0) {
            WOLFSSL_MSG("\tfail: should be a SEQUENCE");
            return ASN_PARSE_E;
        }

        oid = 0;
        if (GetObjectId(source, &idx, &oid, oidOcspType, sz) < 0) {
            WOLFSSL_MSG("\tfail: OBJECT ID");
            return ASN_PARSE_E;
        }

        /* check for critical flag */
        if ((idx + 1) > (word32)sz) {
            WOLFSSL_MSG("\tfail: malformed buffer");
            return BUFFER_E;
        }

        localIdx = idx;
        if (GetASNTag(source, &localIdx, &tag, sz) == 0 && tag == ASN_BOOLEAN) {
            WOLFSSL_MSG("\tfound optional critical flag, moving past");
            ret = GetBoolean(source, &idx, sz);
            if (ret < 0)
                return ret;
        }

        ret = GetOctetString(source, &idx, &length, sz);
        if (ret < 0)
            return ret;

        if (oid == OCSP_NONCE_OID) {
            /* get data inside extra OCTET_STRING */
            ret = GetOctetString(source, &idx, &length, sz);
            if (ret < 0)
                return ret;

            resp->nonce = source + idx;
            resp->nonceSz = length;
        }

        idx += length;
    }

    *ioIndex = idx;
    return 0;
}


static int DecodeResponseData(byte* source,
                            word32* ioIndex, OcspResponse* resp, word32 size)
{
    word32 idx = *ioIndex, prev_idx, localIdx;
    int length;
    int version;
    int ret;
    byte tag;

    WOLFSSL_ENTER("DecodeResponseData");

    resp->response = source + idx;
    prev_idx = idx;
    if (GetSequence(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;
    resp->responseSz = length + idx - prev_idx;

    /* Get version. It is an EXPLICIT[0] DEFAULT(0) value. If this
     * item isn't an EXPLICIT[0], then set version to zero and move
     * onto the next item.
     */
    localIdx = idx;
    if (GetASNTag(source, &localIdx, &tag, size) == 0 &&
            tag == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED))
    {
        idx += 2; /* Eat the value and length */
        if (GetMyVersion(source, &idx, &version, size) < 0)
            return ASN_PARSE_E;
    } else
        version = 0;

    localIdx = idx;
    if (GetASNTag(source, &localIdx, &tag, size) == 0 &&
        ( tag == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | 1) ||
          tag == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | 2) ))
    {
        idx++; /* advance past ASN tag */
        if (GetLength(source, &idx, &length, size) < 0)
            return ASN_PARSE_E;
        idx += length;
    }
    else
        return ASN_PARSE_E;

    /* save pointer to the producedAt time */
    if (GetBasicDate(source, &idx, resp->producedDate,
                                        &resp->producedDateFormat, size) < 0)
        return ASN_PARSE_E;

    if ((ret = DecodeSingleResponse(source, &idx, resp, size)) < 0)
        return ret; /* ASN_PARSE_E, ASN_BEFORE_DATE_E, ASN_AFTER_DATE_E */

    /*
     * Check the length of the ResponseData against the current index to
     * see if there are extensions, they are optional.
     */
    if (idx - prev_idx < resp->responseSz)
        if (DecodeOcspRespExtensions(source, &idx, resp, size) < 0)
            return ASN_PARSE_E;

    *ioIndex = idx;
    return 0;
}


#ifndef WOLFSSL_NO_OCSP_OPTIONAL_CERTS

static int DecodeCerts(byte* source,
                            word32* ioIndex, OcspResponse* resp, word32 size)
{
    word32 idx = *ioIndex;
    byte tag;

    WOLFSSL_ENTER("DecodeCerts");

    if (GetASNTag(source, &idx, &tag, size) < 0)
        return ASN_PARSE_E;

    if (tag == (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC))
    {
        int length;

        if (GetLength(source, &idx, &length, size) < 0)
            return ASN_PARSE_E;

        if (GetSequence(source, &idx, &length, size) < 0)
            return ASN_PARSE_E;

        resp->cert = source + idx;
        resp->certSz = length;

        idx += length;
    }
    *ioIndex = idx;
    return 0;
}

#endif /* WOLFSSL_NO_OCSP_OPTIONAL_CERTS */


static int DecodeBasicOcspResponse(byte* source, word32* ioIndex,
            OcspResponse* resp, word32 size, void* cm, void* heap, int noVerify)
{
    int    length;
    word32 idx = *ioIndex;
    word32 end_index;
    int    ret;
    int    sigLength;

    WOLFSSL_ENTER("DecodeBasicOcspResponse");
    (void)heap;

    if (GetSequence(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;

    if (idx + length > size)
        return ASN_INPUT_E;
    end_index = idx + length;

    if ((ret = DecodeResponseData(source, &idx, resp, size)) < 0)
        return ret; /* ASN_PARSE_E, ASN_BEFORE_DATE_E, ASN_AFTER_DATE_E */

    /* Get the signature algorithm */
    if (GetAlgoId(source, &idx, &resp->sigOID, oidSigType, size) < 0)
        return ASN_PARSE_E;

    ret = CheckBitString(source, &idx, &sigLength, size, 1, NULL);
    if (ret != 0)
        return ret;

    resp->sigSz = sigLength;
    resp->sig = source + idx;
    idx += sigLength;

    /*
     * Check the length of the BasicOcspResponse against the current index to
     * see if there are certificates, they are optional.
     */
#ifndef WOLFSSL_NO_OCSP_OPTIONAL_CERTS
    if (idx < end_index)
    {
        DecodedCert cert;

        if (DecodeCerts(source, &idx, resp, size) < 0)
            return ASN_PARSE_E;

        InitDecodedCert(&cert, resp->cert, resp->certSz, heap);

        /* Don't verify if we don't have access to Cert Manager. */
        ret = ParseCertRelative(&cert, CERT_TYPE,
                                noVerify ? NO_VERIFY : VERIFY_OCSP, cm);
        if (ret < 0) {
            WOLFSSL_MSG("\tOCSP Responder certificate parsing failed");
            FreeDecodedCert(&cert);
            return ret;
        }

#ifndef WOLFSSL_NO_OCSP_ISSUER_CHECK
        if ((cert.extExtKeyUsage & EXTKEYUSE_OCSP_SIGN) == 0) {
            if (XMEMCMP(cert.subjectHash,
                        resp->issuerHash, KEYID_SIZE) == 0) {
                WOLFSSL_MSG("\tOCSP Response signed by issuer");
            }
            else {
                WOLFSSL_MSG("\tOCSP Responder key usage check failed");
    #ifdef OPENSSL_EXTRA
                resp->verifyError = OCSP_BAD_ISSUER;
    #else
                FreeDecodedCert(&cert);
                return BAD_OCSP_RESPONDER;
    #endif
            }
        }
#endif

        /* ConfirmSignature is blocking here */
        ret = ConfirmSignature(&cert.sigCtx,
            resp->response, resp->responseSz,
            cert.publicKey, cert.pubKeySize, cert.keyOID,
            resp->sig, resp->sigSz, resp->sigOID, NULL);

        FreeDecodedCert(&cert);

        if (ret != 0) {
            WOLFSSL_MSG("\tOCSP Confirm signature failed");
            return ASN_OCSP_CONFIRM_E;
        }
    }
    else
#endif /* WOLFSSL_NO_OCSP_OPTIONAL_CERTS */
    {
        Signer* ca;
        int sigValid = -1;

        #ifndef NO_SKID
            ca = GetCA(cm, resp->issuerKeyHash);
        #else
            ca = GetCA(cm, resp->issuerHash);
        #endif

        if (ca) {
            SignatureCtx sigCtx;
            InitSignatureCtx(&sigCtx, heap, INVALID_DEVID);

            /* ConfirmSignature is blocking here */
            sigValid = ConfirmSignature(&sigCtx, resp->response,
                resp->responseSz, ca->publicKey, ca->pubKeySize, ca->keyOID,
                                resp->sig, resp->sigSz, resp->sigOID, NULL);
        }
        if (ca == NULL || sigValid != 0) {
            WOLFSSL_MSG("\tOCSP Confirm signature failed");
            return ASN_OCSP_CONFIRM_E;
        }

        (void)noVerify;
    }

    *ioIndex = idx;
    return 0;
}


void InitOcspResponse(OcspResponse* resp, CertStatus* status,
                                                    byte* source, word32 inSz)
{
    WOLFSSL_ENTER("InitOcspResponse");

    XMEMSET(status, 0, sizeof(CertStatus));
    XMEMSET(resp,   0, sizeof(OcspResponse));

    resp->responseStatus = -1;
    resp->status         = status;
    resp->source         = source;
    resp->maxIdx         = inSz;
}


int OcspResponseDecode(OcspResponse* resp, void* cm, void* heap, int noVerify)
{
    int ret;
    int length = 0;
    word32 idx = 0;
    byte* source = resp->source;
    word32 size = resp->maxIdx;
    word32 oid;
    byte   tag;

    WOLFSSL_ENTER("OcspResponseDecode");

    /* peel the outer SEQUENCE wrapper */
    if (GetSequence(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;

    /* First get the responseStatus, an ENUMERATED */
    if (GetEnumerated(source, &idx, &resp->responseStatus, size) < 0)
        return ASN_PARSE_E;

    if (resp->responseStatus != OCSP_SUCCESSFUL)
        return 0;

    /* Next is an EXPLICIT record called ResponseBytes, OPTIONAL */
    if (idx >= size)
        return ASN_INPUT_E;
    if (GetASNTag(source, &idx, &tag, size) < 0)
        return ASN_PARSE_E;
    if (tag != (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC))
        return ASN_PARSE_E;
    if (GetLength(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;

    /* Get the responseBytes SEQUENCE */
    if (GetSequence(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;

    /* Check ObjectID for the resposeBytes */
    if (GetObjectId(source, &idx, &oid, oidOcspType, size) < 0)
        return ASN_PARSE_E;
    if (oid != OCSP_BASIC_OID)
        return ASN_PARSE_E;
    ret = GetOctetString(source, &idx, &length, size);
    if (ret < 0)
        return ret;

    ret = DecodeBasicOcspResponse(source, &idx, resp, size, cm, heap, noVerify);
    if (ret < 0)
        return ret;

    return 0;
}


word32 EncodeOcspRequestExtensions(OcspRequest* req, byte* output, word32 size)
{
    const byte NonceObjId[] = { 0x2b, 0x06, 0x01, 0x05, 0x05, 0x07,
                                       0x30, 0x01, 0x02 };
    byte seqArray[5][MAX_SEQ_SZ];
    word32 seqSz[5], totalSz = (word32)sizeof(NonceObjId);

    WOLFSSL_ENTER("SetOcspReqExtensions");

    if (!req || !output || !req->nonceSz)
        return 0;

    totalSz += req->nonceSz;
    totalSz += seqSz[0] = SetOctetString(req->nonceSz, seqArray[0]);
    totalSz += seqSz[1] = SetOctetString(req->nonceSz + seqSz[0], seqArray[1]);
    totalSz += seqSz[2] = SetObjectId(sizeof(NonceObjId), seqArray[2]);
    totalSz += seqSz[3] = SetSequence(totalSz, seqArray[3]);
    totalSz += seqSz[4] = SetSequence(totalSz, seqArray[4]);

    if (totalSz > size)
        return 0;

    totalSz = 0;

    XMEMCPY(output + totalSz, seqArray[4], seqSz[4]);
    totalSz += seqSz[4];

    XMEMCPY(output + totalSz, seqArray[3], seqSz[3]);
    totalSz += seqSz[3];

    XMEMCPY(output + totalSz, seqArray[2], seqSz[2]);
    totalSz += seqSz[2];

    XMEMCPY(output + totalSz, NonceObjId, sizeof(NonceObjId));
    totalSz += (word32)sizeof(NonceObjId);

    XMEMCPY(output + totalSz, seqArray[1], seqSz[1]);
    totalSz += seqSz[1];

    XMEMCPY(output + totalSz, seqArray[0], seqSz[0]);
    totalSz += seqSz[0];

    XMEMCPY(output + totalSz, req->nonce, req->nonceSz);
    totalSz += req->nonceSz;

    return totalSz;
}


int EncodeOcspRequest(OcspRequest* req, byte* output, word32 size)
{
    byte seqArray[5][MAX_SEQ_SZ];
    /* The ASN.1 of the OCSP Request is an onion of sequences */
    byte algoArray[MAX_ALGO_SZ];
    byte issuerArray[MAX_ENCODED_DIG_SZ];
    byte issuerKeyArray[MAX_ENCODED_DIG_SZ];
    byte snArray[MAX_SN_SZ];
    byte extArray[MAX_OCSP_EXT_SZ];
    word32 seqSz[5], algoSz, issuerSz, issuerKeySz, extSz, totalSz;
    int i, snSz;

    WOLFSSL_ENTER("EncodeOcspRequest");

#ifdef NO_SHA
    algoSz = SetAlgoID(SHA256h, algoArray, oidHashType, 0);
#else
    algoSz = SetAlgoID(SHAh, algoArray, oidHashType, 0);
#endif

    issuerSz    = SetDigest(req->issuerHash,    KEYID_SIZE,    issuerArray);
    issuerKeySz = SetDigest(req->issuerKeyHash, KEYID_SIZE,    issuerKeyArray);
    snSz        = SetSerialNumber(req->serial,  req->serialSz, snArray,
                                                          MAX_SN_SZ, MAX_SN_SZ);
    extSz       = 0;

    if (snSz < 0)
        return snSz;

    if (req->nonceSz) {
        /* TLS Extensions use this function too - put extensions after
         * ASN.1: Context Specific [2].
         */
        extSz = EncodeOcspRequestExtensions(req, extArray + 2,
                                            OCSP_NONCE_EXT_SZ);
        extSz += SetExplicit(2, extSz, extArray);
    }

    totalSz = algoSz + issuerSz + issuerKeySz + snSz;
    for (i = 4; i >= 0; i--) {
        seqSz[i] = SetSequence(totalSz, seqArray[i]);
        totalSz += seqSz[i];
        if (i == 2) totalSz += extSz;
    }

    if (output == NULL)
        return totalSz;
    if (totalSz > size)
        return BUFFER_E;

    totalSz = 0;
    for (i = 0; i < 5; i++) {
        XMEMCPY(output + totalSz, seqArray[i], seqSz[i]);
        totalSz += seqSz[i];
    }

    XMEMCPY(output + totalSz, algoArray, algoSz);
    totalSz += algoSz;

    XMEMCPY(output + totalSz, issuerArray, issuerSz);
    totalSz += issuerSz;

    XMEMCPY(output + totalSz, issuerKeyArray, issuerKeySz);
    totalSz += issuerKeySz;

    XMEMCPY(output + totalSz, snArray, snSz);
    totalSz += snSz;

    if (extSz != 0) {
        XMEMCPY(output + totalSz, extArray, extSz);
        totalSz += extSz;
    }

    return totalSz;
}


int InitOcspRequest(OcspRequest* req, DecodedCert* cert, byte useNonce,
                                                                     void* heap)
{
    int ret;

    WOLFSSL_ENTER("InitOcspRequest");

    if (req == NULL)
        return BAD_FUNC_ARG;

    ForceZero(req, sizeof(OcspRequest));
    req->heap = heap;

    if (cert) {
        XMEMCPY(req->issuerHash,    cert->issuerHash,    KEYID_SIZE);
        XMEMCPY(req->issuerKeyHash, cert->issuerKeyHash, KEYID_SIZE);

        req->serial = (byte*)XMALLOC(cert->serialSz, req->heap,
                                                     DYNAMIC_TYPE_OCSP_REQUEST);
        if (req->serial == NULL)
            return MEMORY_E;

        XMEMCPY(req->serial, cert->serial, cert->serialSz);
        req->serialSz = cert->serialSz;

        if (cert->extAuthInfoSz != 0 && cert->extAuthInfo != NULL) {
            req->url = (byte*)XMALLOC(cert->extAuthInfoSz + 1, req->heap,
                                                     DYNAMIC_TYPE_OCSP_REQUEST);
            if (req->url == NULL) {
                XFREE(req->serial, req->heap, DYNAMIC_TYPE_OCSP);
                return MEMORY_E;
            }

            XMEMCPY(req->url, cert->extAuthInfo, cert->extAuthInfoSz);
            req->urlSz = cert->extAuthInfoSz;
            req->url[req->urlSz] = 0;
        }
    }

    if (useNonce) {
        WC_RNG rng;

    #ifndef HAVE_FIPS
        ret = wc_InitRng_ex(&rng, req->heap, INVALID_DEVID);
    #else
        ret = wc_InitRng(&rng);
    #endif
        if (ret != 0) {
            WOLFSSL_MSG("\tCannot initialize RNG. Skipping the OSCP Nonce.");
        } else {
            if (wc_RNG_GenerateBlock(&rng, req->nonce, MAX_OCSP_NONCE_SZ) != 0)
                WOLFSSL_MSG("\tCannot run RNG. Skipping the OSCP Nonce.");
            else
                req->nonceSz = MAX_OCSP_NONCE_SZ;

            wc_FreeRng(&rng);
        }
    }

    return 0;
}

void FreeOcspRequest(OcspRequest* req)
{
    WOLFSSL_ENTER("FreeOcspRequest");

    if (req) {
        if (req->serial)
            XFREE(req->serial, req->heap, DYNAMIC_TYPE_OCSP_REQUEST);
        req->serial = NULL;

#ifdef OPENSSL_EXTRA
        if (req->serialInt) {
            if (req->serialInt->isDynamic) {
                XFREE(req->serialInt->data, NULL, DYNAMIC_TYPE_OPENSSL);
            }
            XFREE(req->serialInt, NULL, DYNAMIC_TYPE_OPENSSL);
        }
        req->serialInt = NULL;
#endif

        if (req->url)
            XFREE(req->url, req->heap, DYNAMIC_TYPE_OCSP_REQUEST);
        req->url = NULL;
    }
}


int CompareOcspReqResp(OcspRequest* req, OcspResponse* resp)
{
    int cmp;

    WOLFSSL_ENTER("CompareOcspReqResp");

    if (req == NULL) {
        WOLFSSL_MSG("\tReq missing");
        return -1;
    }
    if (resp == NULL || resp->issuerHash == NULL || 
            resp->issuerKeyHash == NULL || resp->status == NULL) {
        WOLFSSL_MSG("\tResp missing");
        return 1;
    }

    /* Nonces are not critical. The responder may not necessarily add
     * the nonce to the response. */
    if (req->nonceSz && resp->nonce != NULL
#ifndef WOLFSSL_FORCE_OCSP_NONCE_CHECK
            && resp->nonceSz != 0
#endif
    ) {
        cmp = req->nonceSz - resp->nonceSz;
        if (cmp != 0) {
            WOLFSSL_MSG("\tnonceSz mismatch");
            return cmp;
        }

        cmp = XMEMCMP(req->nonce, resp->nonce, req->nonceSz);
        if (cmp != 0) {
            WOLFSSL_MSG("\tnonce mismatch");
            return cmp;
        }
    }

    cmp = XMEMCMP(req->issuerHash, resp->issuerHash, KEYID_SIZE);
    if (cmp != 0) {
        WOLFSSL_MSG("\tissuerHash mismatch");
        return cmp;
    }

    cmp = XMEMCMP(req->issuerKeyHash, resp->issuerKeyHash, KEYID_SIZE);
    if (cmp != 0) {
        WOLFSSL_MSG("\tissuerKeyHash mismatch");
        return cmp;
    }

    cmp = req->serialSz - resp->status->serialSz;
    if (cmp != 0) {
        WOLFSSL_MSG("\tserialSz mismatch");
        return cmp;
    }

    cmp = XMEMCMP(req->serial, resp->status->serial, req->serialSz);
    if (cmp != 0) {
        WOLFSSL_MSG("\tserial mismatch");
        return cmp;
    }

    return 0;
}

#endif /* HAVE_OCSP */


/* store WC_SHA hash of NAME */
int GetNameHash(const byte* source, word32* idx, byte* hash,
                             int maxIdx)
{
    int    length;  /* length of all distinguished names */
    int    ret;
    word32 dummy;
    byte   tag;

    WOLFSSL_ENTER("GetNameHash");

    dummy = *idx;
    if (GetASNTag(source, &dummy, &tag, maxIdx) == 0 && tag == ASN_OBJECT_ID) {
        WOLFSSL_MSG("Trying optional prefix...");

        if (GetLength(source, idx, &length, maxIdx) < 0)
            return ASN_PARSE_E;

        *idx += length;
        WOLFSSL_MSG("Got optional prefix");
    }

    /* For OCSP, RFC2560 section 4.1.1 states the issuer hash should be
     * calculated over the entire DER encoding of the Name field, including
     * the tag and length. */
    dummy = *idx;
    if (GetSequence(source, idx, &length, maxIdx) < 0)
        return ASN_PARSE_E;

    ret = CalcHashId(source + dummy, length + *idx - dummy, hash);

    *idx += length;

    return ret;
}


#ifdef HAVE_CRL

/* initialize decoded CRL */
void InitDecodedCRL(DecodedCRL* dcrl, void* heap)
{
    WOLFSSL_MSG("InitDecodedCRL");

    XMEMSET(dcrl, 0, sizeof(DecodedCRL));
    dcrl->heap = heap;
    #ifdef WOLFSSL_HEAP_TEST
        dcrl->heap = (void*)WOLFSSL_HEAP_TEST;
    #endif
}


/* free decoded CRL resources */
void FreeDecodedCRL(DecodedCRL* dcrl)
{
    RevokedCert* tmp = dcrl->certs;

    WOLFSSL_MSG("FreeDecodedCRL");

    while(tmp) {
        RevokedCert* next = tmp->next;
        XFREE(tmp, dcrl->heap, DYNAMIC_TYPE_REVOKED);
        tmp = next;
    }
}


/* Get Revoked Cert list, 0 on success */
static int GetRevoked(const byte* buff, word32* idx, DecodedCRL* dcrl,
                      int maxIdx)
{
    int    ret, len;
    word32 end;
    byte   b;
    RevokedCert* rc;

    WOLFSSL_ENTER("GetRevoked");

    if (GetSequence(buff, idx, &len, maxIdx) < 0)
        return ASN_PARSE_E;

    end = *idx + len;

    rc = (RevokedCert*)XMALLOC(sizeof(RevokedCert), dcrl->heap,
                                                          DYNAMIC_TYPE_REVOKED);
    if (rc == NULL) {
        WOLFSSL_MSG("Alloc Revoked Cert failed");
        return MEMORY_E;
    }

    if (GetSerialNumber(buff, idx, rc->serialNumber, &rc->serialSz,
                                                                maxIdx) < 0) {
        XFREE(rc, dcrl->heap, DYNAMIC_TYPE_REVOKED);
        return ASN_PARSE_E;
    }

    /* add to list */
    rc->next = dcrl->certs;
    dcrl->certs = rc;
    dcrl->totalCerts++;

    /* get date */
    ret = GetDateInfo(buff, idx, NULL, &b, NULL, maxIdx);
    if (ret < 0) {
        WOLFSSL_MSG("Expecting Date");
        return ret;
    }

    /* skip extensions */
    *idx = end;

    return 0;
}


/* Get CRL Signature, 0 on success */
static int GetCRL_Signature(const byte* source, word32* idx, DecodedCRL* dcrl,
                            int maxIdx)
{
    int    length;
    int    ret;

    WOLFSSL_ENTER("GetCRL_Signature");

    ret = CheckBitString(source, idx, &length, maxIdx, 1, NULL);
    if (ret != 0)
        return ret;
    dcrl->sigLength = length;

    dcrl->signature = (byte*)&source[*idx];
    *idx += dcrl->sigLength;

    return 0;
}

int VerifyCRL_Signature(SignatureCtx* sigCtx, const byte* toBeSigned,
                        word32 tbsSz, const byte* signature, word32 sigSz,
                        word32 signatureOID, Signer *ca, void* heap)
{
    /* try to confirm/verify signature */
#ifndef IGNORE_KEY_EXTENSIONS
    if ((ca->keyUsage & KEYUSE_CRL_SIGN) == 0) {
        WOLFSSL_MSG("CA cannot sign CRLs");
        return ASN_CRL_NO_SIGNER_E;
    }
#endif /* IGNORE_KEY_EXTENSIONS */

    InitSignatureCtx(sigCtx, heap, INVALID_DEVID);
    if (ConfirmSignature(sigCtx, toBeSigned, tbsSz, ca->publicKey,
                         ca->pubKeySize, ca->keyOID, signature, sigSz,
                         signatureOID, NULL) != 0) {
        WOLFSSL_MSG("CRL Confirm signature failed");
        return ASN_CRL_CONFIRM_E;
    }

    return 0;
}


static int ParseCRL_CertList(DecodedCRL* dcrl, const byte* buf,
        word32* inOutIdx, int sz)
{
    word32 oid, dateIdx, idx, checkIdx;
    int version, doNextDate = 1;
    byte tag;

    if (dcrl == NULL || inOutIdx == NULL || buf == NULL) {
        return BAD_FUNC_ARG;
    }

    /* may have version */
    idx = *inOutIdx;

    checkIdx = idx;
    if (GetASNTag(buf, &checkIdx, &tag, sz) == 0 && tag == ASN_INTEGER) {
        if (GetMyVersion(buf, &idx, &version, sz) < 0)
            return ASN_PARSE_E;
    }

    if (GetAlgoId(buf, &idx, &oid, oidIgnoreType, sz) < 0)
        return ASN_PARSE_E;

    if (GetNameHash(buf, &idx, dcrl->issuerHash, sz) < 0)
        return ASN_PARSE_E;

    if (GetBasicDate(buf, &idx, dcrl->lastDate, &dcrl->lastDateFormat, sz) < 0)
        return ASN_PARSE_E;

    dateIdx = idx;

    if (GetBasicDate(buf, &idx, dcrl->nextDate, &dcrl->nextDateFormat, sz) < 0)
    {
#ifndef WOLFSSL_NO_CRL_NEXT_DATE
        (void)dateIdx;
        return ASN_PARSE_E;
#else
        dcrl->nextDateFormat = ASN_OTHER_TYPE;  /* skip flag */
        doNextDate = 0;
        idx = dateIdx;
#endif
    }

    if (doNextDate) {
#ifndef NO_ASN_TIME
        if (!XVALIDATE_DATE(dcrl->nextDate, dcrl->nextDateFormat, AFTER)) {
            WOLFSSL_MSG("CRL after date is no longer valid");
            return ASN_AFTER_DATE_E;
        }
#endif
    }

    checkIdx = idx;
    if (idx != dcrl->sigIndex &&
           GetASNTag(buf, &checkIdx, &tag, sz) == 0 && tag != CRL_EXTENSIONS) {

        int len;

        if (GetSequence(buf, &idx, &len, sz) < 0)
            return ASN_PARSE_E;
        len += idx;

        while (idx < (word32)len) {
            if (GetRevoked(buf, &idx, dcrl, len) < 0)
                return ASN_PARSE_E;
        }
    }

    *inOutIdx = idx;

    return 0;
}


#ifndef NO_SKID
static int ParseCRL_AuthKeyIdExt(const byte* input, int sz, DecodedCRL* dcrl)
{
    word32 idx = 0;
    int length = 0, ret = 0;
    byte tag;

    WOLFSSL_ENTER("ParseCRL_AuthKeyIdExt");

    if (GetSequence(input, &idx, &length, sz) < 0) {
        WOLFSSL_MSG("\tfail: should be a SEQUENCE\n");
        return ASN_PARSE_E;
    }

    if (GetASNTag(input, &idx, &tag, sz) < 0) {
        return ASN_PARSE_E;
    }

    if (tag != (ASN_CONTEXT_SPECIFIC | 0)) {
        WOLFSSL_MSG("\tinfo: OPTIONAL item 0, not available\n");
        return 0;
    }

    if (GetLength(input, &idx, &length, sz) <= 0) {
        WOLFSSL_MSG("\tfail: extension data length");
        return ASN_PARSE_E;
    }

    dcrl->extAuthKeyIdSet = 1;
    if (length == KEYID_SIZE) {
        XMEMCPY(dcrl->extAuthKeyId, input + idx, length);
    }
    else {
        ret = CalcHashId(input + idx, length, dcrl->extAuthKeyId);
    }

    return ret;
}
#endif


static int ParseCRL_Extensions(DecodedCRL* dcrl, const byte* buf,
        word32* inOutIdx, word32 sz)
{
    int length;
    word32 idx;
    word32 ext_bound; /* boundary index for the sequence of extensions */
    word32 oid;
    byte tag;

    WOLFSSL_ENTER("ParseCRL_Extensions");
    (void)dcrl;

    if (inOutIdx == NULL)
        return BAD_FUNC_ARG;

    idx = *inOutIdx;

    /* CRL Extensions are optional */
    if ((idx + 1) > sz)
        return 0;

    /* CRL Extensions are optional */
    if (GetASNTag(buf, &idx, &tag, sz) < 0)
        return 0;

    /* CRL Extensions are optional */
    if (tag != (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 0))
        return 0;

    if (GetLength(buf, &idx, &length, sz) < 0)
        return ASN_PARSE_E;

    if (GetSequence(buf, &idx, &length, sz) < 0)
        return ASN_PARSE_E;

    ext_bound = idx + length;

    while (idx < (word32)ext_bound) {
        word32 localIdx;
        int ret;

        if (GetSequence(buf, &idx, &length, sz) < 0) {
            WOLFSSL_MSG("\tfail: should be a SEQUENCE");
            return ASN_PARSE_E;
        }

        oid = 0;
        if (GetObjectId(buf, &idx, &oid, oidCrlExtType, sz) < 0) {
            WOLFSSL_MSG("\tfail: OBJECT ID");
            return ASN_PARSE_E;
        }

        /* check for critical flag */
        if ((idx + 1) > (word32)sz) {
            WOLFSSL_MSG("\tfail: malformed buffer");
            return BUFFER_E;
        }

        localIdx = idx;
        if (GetASNTag(buf, &localIdx, &tag, sz) == 0 && tag == ASN_BOOLEAN) {
            WOLFSSL_MSG("\tfound optional critical flag, moving past");
            ret = GetBoolean(buf, &idx, sz);
            if (ret < 0)
                return ret;
        }

        ret = GetOctetString(buf, &idx, &length, sz);
        if (ret < 0)
            return ret;

        if (oid == AUTH_KEY_OID) {
        #ifndef NO_SKID
            ret = ParseCRL_AuthKeyIdExt(buf + idx, length, dcrl);
            if (ret < 0) {
                WOLFSSL_MSG("\tcouldn't parse AuthKeyId extension");
                return ret;
            }
        #endif
        }

        idx += length;
    }

    *inOutIdx = idx;

    return 0;
}


/* parse crl buffer into decoded state, 0 on success */
int ParseCRL(DecodedCRL* dcrl, const byte* buff, word32 sz, void* cm)
{
    int          len;
    word32       idx = 0;
    Signer*      ca = NULL;
    SignatureCtx sigCtx;

    WOLFSSL_MSG("ParseCRL");

    /* raw crl hash */
    /* hash here if needed for optimized comparisons
     * wc_Sha sha;
     * wc_InitSha(&sha);
     * wc_ShaUpdate(&sha, buff, sz);
     * wc_ShaFinal(&sha, dcrl->crlHash); */

    if (GetSequence(buff, &idx, &len, sz) < 0)
        return ASN_PARSE_E;

    dcrl->certBegin = idx;
    /* Normalize sz for the length inside the outer sequence. */
    sz = len + idx;

    if (GetSequence(buff, &idx, &len, sz) < 0)
        return ASN_PARSE_E;
    dcrl->sigIndex = len + idx;

    if (ParseCRL_CertList(dcrl, buff, &idx, dcrl->sigIndex) < 0)
        return ASN_PARSE_E;

    if (ParseCRL_Extensions(dcrl, buff, &idx, dcrl->sigIndex) < 0)
        return ASN_PARSE_E;

    idx = dcrl->sigIndex;

    if (GetAlgoId(buff, &idx, &dcrl->signatureOID, oidSigType, sz) < 0)
        return ASN_PARSE_E;

    if (GetCRL_Signature(buff, &idx, dcrl, sz) < 0)
        return ASN_PARSE_E;

    /* openssl doesn't add skid by default for CRLs cause firefox chokes
       if experiencing issues uncomment NO_SKID define in CRL section of
       wolfssl/wolfcrypt/settings.h */
#ifndef NO_SKID
    if (dcrl->extAuthKeyIdSet) {
        ca = GetCA(cm, dcrl->extAuthKeyId); /* more unique than issuerHash */
    }
    if (ca != NULL && XMEMCMP(dcrl->issuerHash, ca->subjectNameHash,
                KEYID_SIZE) != 0) {
        ca = NULL;
    }
    if (ca == NULL) {
        ca = GetCAByName(cm, dcrl->issuerHash); /* last resort */
        /* If AKID is available then this CA doesn't have the public
         * key required */
        if (ca && dcrl->extAuthKeyIdSet) {
            WOLFSSL_MSG("CA SKID doesn't match AKID");
            ca = NULL;
        }
    }
#else
    ca = GetCA(cm, dcrl->issuerHash);
#endif /* !NO_SKID */
    WOLFSSL_MSG("About to verify CRL signature");

    if (ca == NULL) {
        WOLFSSL_MSG("Did NOT find CRL issuer CA");
        return ASN_CRL_NO_SIGNER_E;
    }

    WOLFSSL_MSG("Found CRL issuer CA");
    return VerifyCRL_Signature(&sigCtx, buff + dcrl->certBegin,
           dcrl->sigIndex - dcrl->certBegin, dcrl->signature, dcrl->sigLength,
           dcrl->signatureOID, ca, dcrl->heap);
}

#endif /* HAVE_CRL */



#ifdef WOLFSSL_CERT_PIV

int wc_ParseCertPIV(wc_CertPIV* piv, const byte* buf, word32 totalSz)
{
    int length = 0;
    word32 idx = 0;

    WOLFSSL_ENTER("wc_ParseCertPIV");

    if (piv == NULL || buf == NULL || totalSz == 0)
        return BAD_FUNC_ARG;

    XMEMSET(piv, 0, sizeof(wc_CertPIV));

    /* Detect Identiv PIV (with 0x0A, 0x0B and 0x0C sections) */
    /* Certificate (0A 82 05FA) */
    if (GetASNHeader(buf, ASN_PIV_CERT, &idx, &length, totalSz) >= 0) {
        /* Identiv Type PIV card */
        piv->isIdentiv = 1;

        piv->cert =   &buf[idx];
        piv->certSz = length;
        idx += length;

        /* Nonce (0B 14) */
        if (GetASNHeader(buf, ASN_PIV_NONCE, &idx, &length, totalSz) >= 0) {
            piv->nonce =   &buf[idx];
            piv->nonceSz = length;
            idx += length;
        }

        /* Signed Nonce (0C 82 0100) */
        if (GetASNHeader(buf, ASN_PIV_SIGNED_NONCE, &idx, &length, totalSz) >= 0) {
            piv->signedNonce =   &buf[idx];
            piv->signedNonceSz = length;
        }

        idx = 0;
        buf = piv->cert;
        totalSz = piv->certSz;
    }

    /* Certificate Buffer Total Size (53 82 05F6) */
    if (GetASNHeader(buf, ASN_APPLICATION | ASN_PRINTABLE_STRING, &idx,
                                                   &length, totalSz) < 0) {
        return ASN_PARSE_E;
    }
    /* PIV Certificate (70 82 05ED) */
    if (GetASNHeader(buf, ASN_PIV_TAG_CERT, &idx, &length,
                                                         totalSz) < 0) {
        return ASN_PARSE_E;
    }

    /* Capture certificate buffer pointer and length */
    piv->cert =   &buf[idx];
    piv->certSz = length;
    idx += length;

    /* PIV Certificate Info (71 01 00) */
    if (GetASNHeader(buf, ASN_PIV_TAG_CERT_INFO, &idx, &length,
                                                        totalSz) >= 0) {
        if (length >= 1) {
            piv->compression = (buf[idx] & ASN_PIV_CERT_INFO_COMPRESSED);
            piv->isX509 =      (buf[idx] & ASN_PIV_CERT_INFO_ISX509);
        }
        idx += length;
    }

    /* PIV Error Detection (FE 00) */
    if (GetASNHeader(buf, ASN_PIV_TAG_ERR_DET, &idx, &length,
                                                        totalSz) >= 0) {
        piv->certErrDet =   &buf[idx];
        piv->certErrDetSz = length;
        idx += length;
    }

    return 0;
}

#endif /* WOLFSSL_CERT_PIV */


#undef ERROR_OUT

#endif /* !NO_ASN */

#ifdef WOLFSSL_SEP


#endif /* WOLFSSL_SEP */
