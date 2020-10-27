/* asn_public.h
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

/*!
    \file wolfssl/wolfcrypt/asn_public.h
*/

/*
DESCRIPTION
This library defines the interface APIs for X509 certificates.

*/
#ifndef WOLF_CRYPT_ASN_PUBLIC_H
#define WOLF_CRYPT_ASN_PUBLIC_H

#include <wolfssl/wolfcrypt/types.h>

#ifdef __cplusplus
    extern "C" {
#endif

/* guard on redeclaration */
#ifndef WC_ECCKEY_TYPE_DEFINED
    typedef struct ecc_key ecc_key;
    #define WC_ECCKEY_TYPE_DEFINED
#endif
#ifndef WC_ED25519KEY_TYPE_DEFINED
    typedef struct ed25519_key ed25519_key;
    #define WC_ED25519KEY_TYPE_DEFINED
#endif
#ifndef WC_ED448KEY_TYPE_DEFINED
    typedef struct ed448_key ed448_key;
    #define WC_ED448KEY_TYPE_DEFINED
#endif
#ifndef WC_RSAKEY_TYPE_DEFINED
    typedef struct RsaKey RsaKey;
    #define WC_RSAKEY_TYPE_DEFINED
#endif
#ifndef WC_RNG_TYPE_DEFINED
    typedef struct WC_RNG WC_RNG;
    #define WC_RNG_TYPE_DEFINED
#endif

enum Ecc_Sum {
    ECC_SECP112R1_OID = 182,
    ECC_SECP112R2_OID = 183,
    ECC_SECP128R1_OID = 204,
    ECC_SECP128R2_OID = 205,
    ECC_SECP160R1_OID = 184,
    ECC_SECP160R2_OID = 206,
    ECC_SECP160K1_OID = 185,
    ECC_BRAINPOOLP160R1_OID = 98,
    ECC_SECP192R1_OID = 520,
    ECC_PRIME192V2_OID = 521,
    ECC_PRIME192V3_OID = 522,
    ECC_SECP192K1_OID = 207,
    ECC_BRAINPOOLP192R1_OID = 100,
    ECC_SECP224R1_OID = 209,
    ECC_SECP224K1_OID = 208,
    ECC_BRAINPOOLP224R1_OID = 102,
    ECC_PRIME239V1_OID = 523,
    ECC_PRIME239V2_OID = 524,
    ECC_PRIME239V3_OID = 525,
    ECC_SECP256R1_OID = 526,
    ECC_SECP256K1_OID = 186,
    ECC_BRAINPOOLP256R1_OID = 104,
    ECC_X25519_OID = 365,
    ECC_ED25519_OID = 256,
    ECC_BRAINPOOLP320R1_OID = 106,
    ECC_X448_OID = 362,
    ECC_ED448_OID = 257,
    ECC_SECP384R1_OID = 210,
    ECC_BRAINPOOLP384R1_OID = 108,
    ECC_BRAINPOOLP512R1_OID = 110,
    ECC_SECP521R1_OID = 211,
};


/* Certificate file Type */
enum CertType {
    CERT_TYPE       = 0,
    PRIVATEKEY_TYPE,
    DH_PARAM_TYPE,
    DSA_PARAM_TYPE,
    CRL_TYPE,
    CA_TYPE,
    ECC_PRIVATEKEY_TYPE,
    DSA_PRIVATEKEY_TYPE,
    CERTREQ_TYPE,
    DSA_TYPE,
    ECC_TYPE,
    RSA_TYPE,
    PUBLICKEY_TYPE,
    RSA_PUBLICKEY_TYPE,
    ECC_PUBLICKEY_TYPE,
    TRUSTED_PEER_TYPE,
    EDDSA_PRIVATEKEY_TYPE,
    ED25519_TYPE,
    ED448_TYPE,
    PKCS12_TYPE,
    PKCS8_PRIVATEKEY_TYPE,
    PKCS8_ENC_PRIVATEKEY_TYPE,
    DETECT_CERT_TYPE,
    DH_PRIVATEKEY_TYPE,
};


/* Signature type, by OID sum */
enum Ctc_SigType {
    CTC_SHAwDSA      = 517,
    CTC_MD2wRSA      = 646,
    CTC_MD5wRSA      = 648,
    CTC_SHAwRSA      = 649,
    CTC_SHAwECDSA    = 520,
    CTC_SHA224wRSA   = 658,
    CTC_SHA224wECDSA = 523,
    CTC_SHA256wRSA   = 655,
    CTC_SHA256wECDSA = 524,
    CTC_SHA384wRSA   = 656,
    CTC_SHA384wECDSA = 525,
    CTC_SHA512wRSA   = 657,
    CTC_SHA512wECDSA = 526,
    CTC_ED25519      = 256,
    CTC_ED448        = 257
};

enum Ctc_Encoding {
    CTC_UTF8       = 0x0c, /* utf8      */
    CTC_PRINTABLE  = 0x13  /* printable */
};

#ifndef WC_CTC_NAME_SIZE
    #define WC_CTC_NAME_SIZE 64
#endif
#ifndef WC_CTC_MAX_ALT_SIZE
    #define WC_CTC_MAX_ALT_SIZE 16384
#endif

enum Ctc_Misc {
    CTC_COUNTRY_SIZE  =     2,
    CTC_NAME_SIZE     = WC_CTC_NAME_SIZE,
    CTC_DATE_SIZE     =    32,
    CTC_MAX_ALT_SIZE  = WC_CTC_MAX_ALT_SIZE, /* may be huge, default: 16384 */
    CTC_SERIAL_SIZE   =    20,
    CTC_GEN_SERIAL_SZ =    16,
#ifdef WOLFSSL_CERT_EXT
    /* AKID could contains: hash + (Option) AuthCertIssuer,AuthCertSerialNum
     * We support only hash */
    CTC_MAX_SKID_SIZE = 32, /* SHA256_DIGEST_SIZE */
    CTC_MAX_AKID_SIZE = 32, /* SHA256_DIGEST_SIZE */
    CTC_MAX_CERTPOL_SZ = 64,
    CTC_MAX_CERTPOL_NB = 2 /* Max number of Certificate Policy */
#endif /* WOLFSSL_CERT_EXT */
};

/* DER buffer */
typedef struct DerBuffer {
    byte*  buffer;
    void*  heap;
    word32 length;
    int    type;    /* enum CertType */
    int    dynType; /* DYNAMIC_TYPE_* */
} DerBuffer;

typedef struct WOLFSSL_ASN1_TIME {
    unsigned char data[CTC_DATE_SIZE]; /* date bytes */
    int length;
    int type;
} WOLFSSL_ASN1_TIME;

enum {
    IV_SZ   = 32,                   /* max iv sz */
    NAME_SZ = 80,                   /* max one line */

    PEM_PASS_READ  = 0,
    PEM_PASS_WRITE = 1,
};


typedef int (pem_password_cb)(char* passwd, int sz, int rw, void* userdata);

typedef struct EncryptedInfo {
    pem_password_cb* passwd_cb;
    void*            passwd_userdata;

    long     consumed;         /* tracks PEM bytes consumed */

    int      cipherType;
    word32   keySz;
    word32   ivSz;             /* salt or encrypted IV size */

    char     name[NAME_SZ];    /* cipher name, such as "DES-CBC" */
    byte     iv[IV_SZ];        /* salt or encrypted IV */

    word16   set:1;            /* if encryption set */
} EncryptedInfo;


#define WOLFSSL_ASN1_INTEGER_MAX 20
typedef struct WOLFSSL_ASN1_INTEGER {
    /* size can be increased set at 20 for tag, length then to hold at least 16
     * byte type */
    unsigned char  intData[WOLFSSL_ASN1_INTEGER_MAX];
    /* ASN_INTEGER | LENGTH | hex of number */
    unsigned char  negative;   /* negative number flag */

    unsigned char* data;
    unsigned int   dataMax;   /* max size of data buffer */
    unsigned int   isDynamic:1; /* flag for if data pointer dynamic (1 is yes 0 is no) */

    int length;
    int type;
} WOLFSSL_ASN1_INTEGER;


#if defined(WOLFSSL_CERT_GEN) || defined(WOLFSSL_CERT_EXT)
#ifdef WOLFSSL_EKU_OID
    #ifndef CTC_MAX_EKU_NB
        #define CTC_MAX_EKU_NB 1
    #endif
    #ifndef CTC_MAX_EKU_OID_SZ
        #define CTC_MAX_EKU_OID_SZ 30
    #endif
#else
    #undef CTC_MAX_EKU_OID_SZ
    #define CTC_MAX_EKU_OID_SZ 0
#endif
#endif /* WOLFSSL_CERT_GEN || WOLFSSL_CERT_EXT */

#ifdef WOLFSSL_CERT_GEN

#ifdef WOLFSSL_MULTI_ATTRIB
#ifndef CTC_MAX_ATTRIB
    #define CTC_MAX_ATTRIB 4
#endif

/* ASN Encoded Name field */
typedef struct NameAttrib {
    int  sz;                     /* actual string value length */
    int  id;                     /* id of name */
    int  type;                   /* enc of name */
    char value[CTC_NAME_SIZE];   /* name */
} NameAttrib;
#endif /* WOLFSSL_MULTI_ATTRIB */


typedef struct CertName {
    char country[CTC_NAME_SIZE];
    char countryEnc;
    char state[CTC_NAME_SIZE];
    char stateEnc;
    char locality[CTC_NAME_SIZE];
    char localityEnc;
    char sur[CTC_NAME_SIZE];
    char surEnc;
    char org[CTC_NAME_SIZE];
    char orgEnc;
    char unit[CTC_NAME_SIZE];
    char unitEnc;
    char commonName[CTC_NAME_SIZE];
    char commonNameEnc;
    char serialDev[CTC_NAME_SIZE];
    char serialDevEnc;
#ifdef WOLFSSL_CERT_EXT
    char busCat[CTC_NAME_SIZE];
    char busCatEnc;
    char joiC[CTC_NAME_SIZE];
    char joiCEnc;
    char joiSt[CTC_NAME_SIZE];
    char joiStEnc;
#endif
    char email[CTC_NAME_SIZE];  /* !!!! email has to be last !!!! */
#ifdef WOLFSSL_MULTI_ATTRIB
    NameAttrib name[CTC_MAX_ATTRIB];
#endif
} CertName;


/* for user to fill for certificate generation */
typedef struct Cert {
    int      version;                   /* x509 version  */
    byte     serial[CTC_SERIAL_SIZE];   /* serial number */
    int      serialSz;                  /* serial size */
    int      sigType;                   /* signature algo type */
    CertName issuer;                    /* issuer info */
    int      daysValid;                 /* validity days */
    int      selfSigned;                /* self signed flag */
    CertName subject;                   /* subject info */
    int      isCA;                      /* is this going to be a CA */
    /* internal use only */
    int      bodySz;                    /* pre sign total size */
    int      keyType;                   /* public key type of subject */
#ifdef WOLFSSL_ALT_NAMES
    byte     altNames[CTC_MAX_ALT_SIZE]; /* altNames copy */
    int      altNamesSz;                 /* altNames size in bytes */
    byte     beforeDate[CTC_DATE_SIZE];  /* before date copy */
    int      beforeDateSz;               /* size of copy */
    byte     afterDate[CTC_DATE_SIZE];   /* after date copy */
    int      afterDateSz;                /* size of copy */
#endif
#ifdef WOLFSSL_CERT_EXT
    byte    skid[CTC_MAX_SKID_SIZE];     /* Subject Key Identifier */
    int     skidSz;                      /* SKID size in bytes */
    byte    akid[CTC_MAX_AKID_SIZE];     /* Authority Key Identifier */
    int     akidSz;                      /* AKID size in bytes */
    word16  keyUsage;                    /* Key Usage */
    byte    extKeyUsage;                 /* Extended Key Usage */
#ifdef WOLFSSL_EKU_OID
    /* Extended Key Usage OIDs */
    byte    extKeyUsageOID[CTC_MAX_EKU_NB][CTC_MAX_EKU_OID_SZ];
    byte    extKeyUsageOIDSz[CTC_MAX_EKU_NB];
#endif
    char    certPolicies[CTC_MAX_CERTPOL_NB][CTC_MAX_CERTPOL_SZ];
    word16  certPoliciesNb;              /* Number of Cert Policy */
    byte     issRaw[sizeof(CertName)];   /* raw issuer info */
    byte     sbjRaw[sizeof(CertName)];   /* raw subject info */
#endif
#ifdef WOLFSSL_CERT_REQ
    char     challengePw[CTC_NAME_SIZE];
    int      challengePwPrintableString; /* encode as PrintableString */
#endif
    void*   decodedCert;    /* internal DecodedCert allocated from heap */
    byte*   der;            /* Pointer to buffer of current DecodedCert cache */
    void*   heap;           /* heap hint */
} Cert;


/* Initialize and Set Certificate defaults:
   version    = 3 (0x2)
   serial     = 0 (Will be randomly generated)
   sigType    = SHA_WITH_RSA
   issuer     = blank
   daysValid  = 500
   selfSigned = 1 (true) use subject as issuer
   subject    = blank
   isCA       = 0 (false)
   keyType    = RSA_KEY (default)
*/
WOLFSSL_API int wc_InitCert(Cert*);
WOLFSSL_API int wc_MakeCert_ex(Cert* cert, byte* derBuffer, word32 derSz,
                                int keyType, void* key, WC_RNG* rng);
WOLFSSL_API int wc_MakeCert(Cert*, byte* derBuffer, word32 derSz, RsaKey*,
                             ecc_key*, WC_RNG*);
#ifdef WOLFSSL_CERT_REQ
    WOLFSSL_API int wc_MakeCertReq_ex(Cert*, byte* derBuffer, word32 derSz,
                                       int, void*);
    WOLFSSL_API int wc_MakeCertReq(Cert*, byte* derBuffer, word32 derSz,
                                    RsaKey*, ecc_key*);
#endif
WOLFSSL_API int wc_SignCert_ex(int requestSz, int sType, byte* buffer,
                                word32 buffSz, int keyType, void* key,
                                WC_RNG* rng);
WOLFSSL_API int wc_SignCert(int requestSz, int sigType, byte* derBuffer,
                             word32 derSz, RsaKey*, ecc_key*, WC_RNG*);
WOLFSSL_API int wc_MakeSelfCert(Cert*, byte* derBuffer, word32 derSz, RsaKey*,
                             WC_RNG*);
WOLFSSL_API int wc_SetIssuer(Cert*, const char*);
WOLFSSL_API int wc_SetSubject(Cert*, const char*);
#ifdef WOLFSSL_ALT_NAMES
    WOLFSSL_API int wc_SetAltNames(Cert*, const char*);
#endif

#ifdef WOLFSSL_CERT_GEN_CACHE
WOLFSSL_API void wc_SetCert_Free(Cert* cert);
#endif

WOLFSSL_API int wc_SetIssuerBuffer(Cert*, const byte*, int);
WOLFSSL_API int wc_SetSubjectBuffer(Cert*, const byte*, int);
WOLFSSL_API int wc_SetAltNamesBuffer(Cert*, const byte*, int);
WOLFSSL_API int wc_SetDatesBuffer(Cert*, const byte*, int);

#ifndef NO_ASN_TIME
WOLFSSL_API int wc_GetCertDates(Cert* cert, struct tm* before,
    struct tm* after);
#endif

#ifdef WOLFSSL_CERT_EXT
WOLFSSL_API int wc_SetAuthKeyIdFromPublicKey_ex(Cert *cert, int keyType,
                                                void* key);
WOLFSSL_API int wc_SetAuthKeyIdFromPublicKey(Cert *cert, RsaKey *rsakey,
                                             ecc_key *eckey);
WOLFSSL_API int wc_SetAuthKeyIdFromCert(Cert *cert, const byte *der, int derSz);
WOLFSSL_API int wc_SetAuthKeyId(Cert *cert, const char* file);
WOLFSSL_API int wc_SetSubjectKeyIdFromPublicKey_ex(Cert *cert, int keyType,
                                                   void* key);
WOLFSSL_API int wc_SetSubjectKeyIdFromPublicKey(Cert *cert, RsaKey *rsakey,
                                                ecc_key *eckey);
WOLFSSL_API int wc_SetSubjectKeyId(Cert *cert, const char* file);
WOLFSSL_API int wc_GetSubjectRaw(byte **subjectRaw, Cert *cert);
WOLFSSL_API int wc_SetSubjectRaw(Cert* cert, const byte* der, int derSz);
WOLFSSL_API int wc_SetIssuerRaw(Cert* cert, const byte* der, int derSz);

#ifdef HAVE_NTRU
WOLFSSL_API int wc_SetSubjectKeyIdFromNtruPublicKey(Cert *cert, byte *ntruKey,
                                                    word16 ntruKeySz);
#endif

/* Set the KeyUsage.
 * Value is a string separated tokens with ','. Accepted tokens are :
 * digitalSignature,nonRepudiation,contentCommitment,keyCertSign,cRLSign,
 * dataEncipherment,keyAgreement,keyEncipherment,encipherOnly and decipherOnly.
 *
 * nonRepudiation and contentCommitment are for the same usage.
 */
WOLFSSL_API int wc_SetKeyUsage(Cert *cert, const char *value);

/* Set ExtendedKeyUsage
 * Value is a string separated tokens with ','. Accepted tokens are :
 * any,serverAuth,clientAuth,codeSigning,emailProtection,timeStamping,OCSPSigning
 */
WOLFSSL_API int wc_SetExtKeyUsage(Cert *cert, const char *value);


#ifdef WOLFSSL_EKU_OID
/* Set ExtendedKeyUsage with unique OID
 * oid is expected to be in byte representation
 */
WOLFSSL_API int wc_SetExtKeyUsageOID(Cert *cert, const char *oid, word32 sz,
                                     byte idx, void* heap);
#endif /* WOLFSSL_EKU_OID */
#endif /* WOLFSSL_CERT_EXT */

    #ifdef HAVE_NTRU
        WOLFSSL_API int wc_MakeNtruCert(Cert*, byte* derBuffer, word32 derSz,
                                     const byte* ntruKey, word16 keySz,
                                     WC_RNG*);
    #endif

#endif /* WOLFSSL_CERT_GEN */

WOLFSSL_API int wc_GetDateInfo(const byte* certDate, int certDateSz,
    const byte** date, byte* format, int* length);
#ifndef NO_ASN_TIME
WOLFSSL_API int wc_GetDateAsCalendarTime(const byte* date, int length,
    byte format, struct tm* time);
#endif

#if defined(WOLFSSL_PEM_TO_DER) || defined(WOLFSSL_DER_TO_PEM)

    WOLFSSL_API int wc_PemGetHeaderFooter(int type, const char** header,
        const char** footer);

#endif

WOLFSSL_API  int wc_AllocDer(DerBuffer** pDer, word32 length, int type, void* heap);
WOLFSSL_API void wc_FreeDer(DerBuffer** pDer);

#ifdef WOLFSSL_PEM_TO_DER
    WOLFSSL_API int wc_PemToDer(const unsigned char* buff, long longSz, int type,
              DerBuffer** pDer, void* heap, EncryptedInfo* info, int* eccKey);

    WOLFSSL_API int wc_KeyPemToDer(const unsigned char*, int,
                                   unsigned char*, int, const char*);
    WOLFSSL_API int wc_CertPemToDer(const unsigned char*, int,
                                    unsigned char*, int, int);
#endif /* WOLFSSL_PEM_TO_DER */

#if defined(WOLFSSL_CERT_EXT) || defined(WOLFSSL_PUB_PEM_TO_DER)
    #ifndef NO_FILESYSTEM
        WOLFSSL_API int wc_PemPubKeyToDer(const char* fileName,
                                          unsigned char* derBuf, int derSz);
    #endif

    WOLFSSL_API int wc_PubKeyPemToDer(const unsigned char*, int,
                                      unsigned char*, int);
#endif /* WOLFSSL_CERT_EXT || WOLFSSL_PUB_PEM_TO_DER */

#ifdef WOLFSSL_CERT_GEN
    #ifndef NO_FILESYSTEM
        WOLFSSL_API int wc_PemCertToDer(const char* fileName,
                                        unsigned char* derBuf, int derSz);
    #endif
#endif /* WOLFSSL_CERT_GEN */

#ifdef WOLFSSL_DER_TO_PEM
    WOLFSSL_API int wc_DerToPem(const byte* der, word32 derSz, byte* output,
                                word32 outputSz, int type);
    WOLFSSL_API int wc_DerToPemEx(const byte* der, word32 derSz, byte* output,
                                word32 outputSz, byte *cipherIno, int type);
#endif

#ifndef NO_RSA
    #if !defined(HAVE_USER_RSA)
    WOLFSSL_API int wc_RsaPublicKeyDecode_ex(const byte* input, word32* inOutIdx,
        word32 inSz, const byte** n, word32* nSz, const byte** e, word32* eSz);
    #endif
    WOLFSSL_API int wc_RsaPublicKeyDerSize(RsaKey* key, int with_header);
#endif

#ifdef HAVE_ECC
    /* private key helpers */
    WOLFSSL_API int wc_EccPrivateKeyDecode(const byte*, word32*,
                                           ecc_key*, word32);
    WOLFSSL_API int wc_EccKeyToDer(ecc_key*, byte* output, word32 inLen);
    WOLFSSL_API int wc_EccPrivateKeyToDer(ecc_key* key, byte* output,
                                          word32 inLen);
    WOLFSSL_API int wc_EccPrivateKeyToPKCS8(ecc_key* key, byte* output,
                                            word32* outLen);

    /* public key helper */
    WOLFSSL_API int wc_EccPublicKeyDecode(const byte*, word32*,
                                              ecc_key*, word32);
    WOLFSSL_API int wc_EccPublicKeyToDer(ecc_key*, byte* output,
                                         word32 inLen, int with_AlgCurve);
    WOLFSSL_API int wc_EccPublicKeyDerSize(ecc_key*, int with_AlgCurve);
#endif

#ifdef HAVE_ED25519
    /* private key helpers */
    WOLFSSL_API int wc_Ed25519PrivateKeyDecode(const byte*, word32*,
                                               ed25519_key*, word32);
    WOLFSSL_API int wc_Ed25519KeyToDer(ed25519_key* key, byte* output,
                                       word32 inLen);
    WOLFSSL_API int wc_Ed25519PrivateKeyToDer(ed25519_key* key, byte* output,
                                              word32 inLen);

    /* public key helper */
    WOLFSSL_API int wc_Ed25519PublicKeyDecode(const byte*, word32*,
                                              ed25519_key*, word32);
    #if (defined(WOLFSSL_CERT_GEN) || defined(WOLFSSL_KEY_GEN))
        WOLFSSL_API int wc_Ed25519PublicKeyToDer(ed25519_key*, byte* output,
                                               word32 inLen, int with_AlgCurve);
    #endif
#endif

#ifdef HAVE_ED448
    /* private key helpers */
    WOLFSSL_API int wc_Ed448PrivateKeyDecode(const byte*, word32*,
                                             ed448_key*, word32);
    WOLFSSL_API int wc_Ed448KeyToDer(ed448_key* key, byte* output,
                                     word32 inLen);
    WOLFSSL_API int wc_Ed448PrivateKeyToDer(ed448_key* key, byte* output,
                                            word32 inLen);

    /* public key helper */
    WOLFSSL_API int wc_Ed448PublicKeyDecode(const byte*, word32*,
                                            ed448_key*, word32);
    #if (defined(WOLFSSL_CERT_GEN) || defined(WOLFSSL_KEY_GEN))
        WOLFSSL_API int wc_Ed448PublicKeyToDer(ed448_key*, byte* output,
                                               word32 inLen, int with_AlgCurve);
    #endif
#endif

/* DER encode signature */
WOLFSSL_API word32 wc_EncodeSignature(byte* out, const byte* digest,
                                      word32 digSz, int hashOID);
WOLFSSL_API int wc_GetCTC_HashOID(int type);

WOLFSSL_API int wc_GetPkcs8TraditionalOffset(byte* input,
                                             word32* inOutIdx, word32 sz);
WOLFSSL_API int wc_CreatePKCS8Key(byte* out, word32* outSz,
       byte* key, word32 keySz, int algoID, const byte* curveOID, word32 oidSz);

#ifndef NO_ASN_TIME
/* Time */
/* Returns seconds (Epoch/UTC)
 * timePtr: is "time_t", which is typically "long"
 * Example:
    long lTime;
    rc = wc_GetTime(&lTime, (word32)sizeof(lTime));
*/
WOLFSSL_API int wc_GetTime(void* timePtr, word32 timeSize);
#endif

#ifdef WOLFSSL_ENCRYPTED_KEYS
    WOLFSSL_API int wc_EncryptedInfoGet(EncryptedInfo* info,
        const char* cipherInfo);
#endif


#ifdef WOLFSSL_CERT_PIV

typedef struct _wc_CertPIV {
    const byte*  cert;
    word32       certSz;
    const byte*  certErrDet;
    word32       certErrDetSz;
    const byte*  nonce;         /* Identiv Only */
    word32       nonceSz;       /* Identiv Only */
    const byte*  signedNonce;   /* Identiv Only */
    word32       signedNonceSz; /* Identiv Only */

    /* flags */
    word16       compression:2;
    word16       isX509:1;
    word16       isIdentiv:1;
} wc_CertPIV;

WOLFSSL_API int wc_ParseCertPIV(wc_CertPIV* cert, const byte* buf, word32 totalSz);
#endif /* WOLFSSL_CERT_PIV */


#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* WOLF_CRYPT_ASN_PUBLIC_H */
