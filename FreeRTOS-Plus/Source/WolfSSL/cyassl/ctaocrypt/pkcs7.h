/* pkcs7.h
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
 * * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */


#ifdef HAVE_PKCS7

#ifndef CTAO_CRYPT_PKCS7_H
#define CTAO_CRYPT_PKCS7_H

#include <cyassl/ctaocrypt/types.h>
#include <cyassl/ctaocrypt/asn.h>
#include <cyassl/ctaocrypt/asn_public.h>
#include <cyassl/ctaocrypt/random.h>
#include <cyassl/ctaocrypt/des3.h>

#ifdef __cplusplus
    extern "C" {
#endif

/* PKCS#7 content types, ref RFC 2315 (Section 14) */
enum PKCS7_TYPES {
    PKCS7_MSG                 = 650,   /* 1.2.840.113549.1.7   */
    DATA                      = 651,   /* 1.2.840.113549.1.7.1 */
    SIGNED_DATA               = 652,   /* 1.2.840.113549.1.7.2 */
    ENVELOPED_DATA            = 653,   /* 1.2.840.113549.1.7.3 */
    SIGNED_AND_ENVELOPED_DATA = 654,   /* 1.2.840.113549.1.7.4 */
    DIGESTED_DATA             = 655,   /* 1.2.840.113549.1.7.5 */
    ENCRYPTED_DATA            = 656    /* 1.2.840.113549.1.7.6 */
};

enum Pkcs7_Misc {
    PKCS7_NONCE_SZ       = 16,
    MAX_ENCRYPTED_KEY_SZ = 512,           /* max enc. key size, RSA <= 4096 */
    MAX_CONTENT_KEY_LEN  = DES3_KEYLEN,   /* highest current cipher is 3DES */
    MAX_RECIP_SZ         = MAX_VERSION_SZ +
                           MAX_SEQ_SZ + ASN_NAME_MAX + MAX_SN_SZ +
                           MAX_SEQ_SZ + MAX_ALGO_SZ + 1 + MAX_ENCRYPTED_KEY_SZ
};


typedef struct PKCS7Attrib {
    byte* oid;
    word32 oidSz;
    byte* value;
    word32 valueSz;
} PKCS7Attrib;


typedef struct PKCS7 {
    byte* content;                /* inner content, not owner             */
    word32 contentSz;             /* content size                         */
    int contentOID;               /* PKCS#7 content type OID sum          */

    RNG* rng;

    int hashOID;
    int encryptOID;               /* key encryption algorithm OID         */

    byte*  singleCert;            /* recipient cert, DER, not owner       */
    word32 singleCertSz;          /* size of recipient cert buffer, bytes */
    byte issuerHash[SHA_SIZE];    /* hash of all alt Names                */
    byte*  issuer;                /* issuer name of singleCert            */
    word32 issuerSz;              /* length of issuer name                */
    byte issuerSn[MAX_SN_SZ];     /* singleCert's serial number           */
    word32 issuerSnSz;            /* length of serial number              */
    byte publicKey[512];
    word32 publicKeySz;
    byte*  privateKey;            /* private key, DER, not owner          */
    word32 privateKeySz;          /* size of private key buffer, bytes    */
    
    PKCS7Attrib* signedAttribs;
    word32 signedAttribsSz;
} PKCS7;


CYASSL_LOCAL int SetContentType(int pkcs7TypeOID, byte* output);
CYASSL_LOCAL int GetContentType(const byte* input, word32* inOutIdx,
                                word32* oid, word32 maxIdx);
CYASSL_LOCAL int CreateRecipientInfo(const byte* cert, word32 certSz,
                                     int keyEncAlgo, int blockKeySz,
                                     RNG* rng, byte* contentKeyPlain,
                                     byte* contentKeyEnc,
                                     int* keyEncSz, byte* out, word32 outSz);

CYASSL_API int  PKCS7_InitWithCert(PKCS7* pkcs7, byte* cert, word32 certSz);
CYASSL_API void PKCS7_Free(PKCS7* pkcs7);
CYASSL_API int  PKCS7_EncodeData(PKCS7* pkcs7, byte* output, word32 outputSz);
CYASSL_API int  PKCS7_EncodeSignedData(PKCS7* pkcs7,
                                       byte* output, word32 outputSz);
CYASSL_API int  PKCS7_VerifySignedData(PKCS7* pkcs7,
                                       byte* pkiMsg, word32 pkiMsgSz);
CYASSL_API int  PKCS7_EncodeEnvelopedData(PKCS7* pkcs7,
                                          byte* output, word32 outputSz);
CYASSL_API int  PKCS7_DecodeEnvelopedData(PKCS7* pkcs7, byte* pkiMsg,
                                          word32 pkiMsgSz, byte* output,
                                          word32 outputSz);

#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* CTAO_CRYPT_PKCS7_H */

#endif /* HAVE_PKCS7 */

