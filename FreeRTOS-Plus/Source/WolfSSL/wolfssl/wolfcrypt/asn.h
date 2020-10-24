/* asn.h
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
    \file wolfssl/wolfcrypt/asn.h
*/

/*

DESCRIPTION
This library provides the interface to Abstract Syntax Notation One (ASN.1) objects.
ASN.1 is a standard interface description language for defining data structures
that can be serialized and deserialized in a cross-platform way.

*/
#ifndef WOLF_CRYPT_ASN_H
#define WOLF_CRYPT_ASN_H

#include <wolfssl/wolfcrypt/types.h>

#ifndef NO_ASN


#if !defined(NO_ASN_TIME) && defined(NO_TIME_H)
    #define NO_ASN_TIME /* backwards compatibility with NO_TIME_H */
#endif

#include <wolfssl/wolfcrypt/integer.h>

/* fips declare of RsaPrivateKeyDecode @wc_fips */
#if defined(HAVE_FIPS) && !defined(NO_RSA) && \
	(!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION < 2))
    #include <cyassl/ctaocrypt/rsa.h>
#endif

#ifndef NO_DH
    #include <wolfssl/wolfcrypt/dh.h>
#endif
#ifndef NO_DSA
    #include <wolfssl/wolfcrypt/dsa.h>
#endif
#ifndef NO_SHA
    #include <wolfssl/wolfcrypt/sha.h>
#endif
#ifndef NO_MD5
    #include <wolfssl/wolfcrypt/md5.h>
#endif
#include <wolfssl/wolfcrypt/sha256.h>
#include <wolfssl/wolfcrypt/asn_public.h>   /* public interface */

#if defined(NO_SHA) && defined(NO_SHA256)
    #define WC_SHA256_DIGEST_SIZE 32
#endif

#ifdef __cplusplus
    extern "C" {
#endif

#ifndef EXTERNAL_SERIAL_SIZE
    #define EXTERNAL_SERIAL_SIZE 32
#endif

enum {
    ISSUER  = 0,
    SUBJECT = 1,

    BEFORE  = 0,
    AFTER   = 1
};

/* ASN Tags   */
enum ASN_Tags {
    ASN_EOC               = 0x00,
    ASN_BOOLEAN           = 0x01,
    ASN_INTEGER           = 0x02,
    ASN_BIT_STRING        = 0x03,
    ASN_OCTET_STRING      = 0x04,
    ASN_TAG_NULL          = 0x05,
    ASN_OBJECT_ID         = 0x06,
    ASN_ENUMERATED        = 0x0a,
    ASN_UTF8STRING        = 0x0c,
    ASN_SEQUENCE          = 0x10,
    ASN_SET               = 0x11,
    ASN_PRINTABLE_STRING  = 0x13,
    ASN_UTC_TIME          = 0x17,
    ASN_OTHER_TYPE        = 0x00,
    ASN_RFC822_TYPE       = 0x01,
    ASN_DNS_TYPE          = 0x02,
    ASN_DIR_TYPE          = 0x04,
    ASN_URI_TYPE          = 0x06, /* the value 6 is from GeneralName OID */
    ASN_IP_TYPE           = 0x07, /* the value 7 is from GeneralName OID */
    ASN_GENERALIZED_TIME  = 0x18,
    CRL_EXTENSIONS        = 0xa0,
    ASN_EXTENSIONS        = 0xa3,
    ASN_LONG_LENGTH       = 0x80,
    ASN_INDEF_LENGTH      = 0x80,

    /* ASN_Flags - Bitmask */
    ASN_CONSTRUCTED       = 0x20,
    ASN_APPLICATION       = 0x40,
    ASN_CONTEXT_SPECIFIC  = 0x80,
};

#define ASN_UTC_TIME_SIZE 14
#define ASN_GENERALIZED_TIME_SIZE 16
#define ASN_GENERALIZED_TIME_MAX 68

enum DN_Tags {
    ASN_DN_NULL       = 0x00,
    ASN_COMMON_NAME   = 0x03,   /* CN */
    ASN_SUR_NAME      = 0x04,   /* SN */
    ASN_SERIAL_NUMBER = 0x05,   /* serialNumber */
    ASN_COUNTRY_NAME  = 0x06,   /* C  */
    ASN_LOCALITY_NAME = 0x07,   /* L  */
    ASN_STATE_NAME    = 0x08,   /* ST */
    ASN_ORG_NAME      = 0x0a,   /* O  */
    ASN_ORGUNIT_NAME  = 0x0b,   /* OU */
    ASN_BUS_CAT       = 0x0f,   /* businessCategory */
    ASN_EMAIL_NAME    = 0x98,   /* not oid number there is 97 in 2.5.4.0-97 */

    /* pilot attribute types
     * OID values of 0.9.2342.19200300.100.1.* */
    ASN_USER_ID          = 0x01, /* UID */
    ASN_DOMAIN_COMPONENT = 0x19  /* DC */
};

#if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
typedef struct WOLFSSL_ObjectInfo {
    int nid;
    int id;
    word32 type;
    const char* sName;
    const char* lName;
} WOLFSSL_ObjectInfo;
extern const size_t wolfssl_object_info_sz;
extern const WOLFSSL_ObjectInfo wolfssl_object_info[];
#endif /* defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL) */

/* DN Tag Strings */
#define WOLFSSL_COMMON_NAME      "/CN="
#define WOLFSSL_LN_COMMON_NAME   "/commonName="
#define WOLFSSL_SUR_NAME         "/SN="
#define WOLFSSL_SERIAL_NUMBER    "/serialNumber="
#define WOLFSSL_COUNTRY_NAME     "/C="
#define WOLFSSL_LN_COUNTRY_NAME  "/countryName="
#define WOLFSSL_LOCALITY_NAME    "/L="
#define WOLFSSL_LN_LOCALITY_NAME "/localityName="
#define WOLFSSL_STATE_NAME       "/ST="
#define WOLFSSL_LN_STATE_NAME    "/stateOrProvinceName="
#define WOLFSSL_ORG_NAME         "/O="
#define WOLFSSL_LN_ORG_NAME      "/organizationName="
#define WOLFSSL_ORGUNIT_NAME     "/OU="
#define WOLFSSL_LN_ORGUNIT_NAME  "/organizationalUnitName="
#define WOLFSSL_DOMAIN_COMPONENT "/DC="
#define WOLFSSL_LN_DOMAIN_COMPONENT "/domainComponent="
#define WOLFSSL_BUS_CAT          "/businessCategory="
#define WOLFSSL_JOI_C            "/jurisdictionC="
#define WOLFSSL_JOI_ST           "/jurisdictionST="
#define WOLFSSL_EMAIL_ADDR       "/emailAddress="

#define WOLFSSL_USER_ID          "/UID="
#define WOLFSSL_DOMAIN_COMPONENT "/DC="

#if defined(WOLFSSL_APACHE_HTTPD)
    /* otherName strings */
    #define WOLFSSL_SN_MS_UPN       "msUPN"
    #define WOLFSSL_LN_MS_UPN       "Microsoft User Principal Name"
    #define WOLFSSL_MS_UPN_SUM 265
    #define WOLFSSL_SN_DNS_SRV      "id-on-dnsSRV"
    #define WOLFSSL_LN_DNS_SRV      "SRVName"
    /* TLS features extension strings */
    #define WOLFSSL_SN_TLS_FEATURE  "tlsfeature"
    #define WOLFSSL_LN_TLS_FEATURE  "TLS Feature"
    #define WOLFSSL_TLS_FEATURE_SUM 92
#endif

/* NIDs */
enum
{
    NID_undef = 0,
    NID_netscape_cert_type = NID_undef,
    NID_des = 66,
    NID_des3 = 67,
    NID_sha256 = 672,
    NID_sha384 = 673,
    NID_sha512 = 674,
    NID_hw_name_oid = 73,
    NID_id_pkix_OCSP_basic = 74,
    NID_any_policy = 75,
    NID_anyExtendedKeyUsage = 76,
    NID_givenName = 99,
    NID_initials = 101,
    NID_title = 106,
    NID_description = 107,
    NID_basic_constraints = 133,
    NID_key_usage = 129,     /* 2.5.29.15 */
    NID_ext_key_usage = 151, /* 2.5.29.37 */
    NID_subject_key_identifier = 128,
    NID_authority_key_identifier = 149,
    NID_private_key_usage_period = 130, /* 2.5.29.16 */
    NID_subject_alt_name = 131,
    NID_issuer_alt_name = 132,
    NID_info_access = 69,
    NID_sinfo_access = 79,      /* id-pe 11 */
    NID_name_constraints = 144, /* 2.5.29.30 */
    NID_crl_distribution_points = 145, /* 2.5.29.31 */
    NID_certificate_policies = 146,
    NID_policy_mappings = 147,
    NID_policy_constraints = 150,
    NID_inhibit_any_policy = 168,      /* 2.5.29.54 */
    NID_tlsfeature = 1020,             /* id-pe 24 */
    NID_commonName = 0x03,             /* matches ASN_COMMON_NAME in asn.h */


    NID_surname = 0x04,                /* SN */
    NID_serialNumber = 0x05,           /* serialNumber */
    NID_countryName = 0x06,            /* C  */
    NID_localityName = 0x07,           /* L  */
    NID_stateOrProvinceName = 0x08,    /* ST */
    NID_organizationName = 0x0a,       /* O  */
    NID_organizationalUnitName = 0x0b, /* OU */
    NID_jurisdictionCountryName = 0xc,
    NID_jurisdictionStateOrProvinceName = 0xd,
    NID_businessCategory = ASN_BUS_CAT,
    NID_domainComponent = ASN_DOMAIN_COMPONENT,
    NID_userId = 458,
    NID_emailAddress = 0x30,           /* emailAddress */
    NID_id_on_dnsSRV = 82,             /* 1.3.6.1.5.5.7.8.7 */
    NID_ms_upn = 265,                  /* 1.3.6.1.4.1.311.20.2.3 */

    NID_X9_62_prime_field = 406        /* 1.2.840.10045.1.1 */
};

enum ECC_TYPES
{
    ECC_PREFIX_0 = 160,
    ECC_PREFIX_1 = 161
};

#ifdef WOLFSSL_CERT_PIV
    enum PIV_Tags {
        ASN_PIV_CERT          = 0x0A,
        ASN_PIV_NONCE         = 0x0B,
        ASN_PIV_SIGNED_NONCE  = 0x0C,

        ASN_PIV_TAG_CERT      = 0x70,
        ASN_PIV_TAG_CERT_INFO = 0x71,
        ASN_PIV_TAG_MSCUID    = 0x72,
        ASN_PIV_TAG_ERR_DET   = 0xFE,

        /* certificate info masks */
        ASN_PIV_CERT_INFO_COMPRESSED = 0x03,
        ASN_PIV_CERT_INFO_ISX509     = 0x04,
    };
#endif /* WOLFSSL_CERT_PIV */


#define ASN_JOI_PREFIX_SZ       10
#define ASN_JOI_PREFIX          "\x2b\x06\x01\x04\x01\x82\x37\x3c\x02\x01"
#define ASN_JOI_C               0x3
#define ASN_JOI_ST              0x2

#ifndef WC_ASN_NAME_MAX
    #ifdef OPENSSL_EXTRA
        #define WC_ASN_NAME_MAX 300
    #else
        #define WC_ASN_NAME_MAX 256
    #endif
#endif
#define ASN_NAME_MAX WC_ASN_NAME_MAX

enum Misc_ASN {
    MAX_SALT_SIZE       =  64,     /* MAX PKCS Salt length */
    MAX_IV_SIZE         =  64,     /* MAX PKCS Iv length */
    ASN_BOOL_SIZE       =   2,     /* including type */
    ASN_ECC_HEADER_SZ   =   2,     /* String type + 1 byte len */
    ASN_ECC_CONTEXT_SZ  =   2,     /* Content specific type + 1 byte len */
#ifdef NO_SHA
    KEYID_SIZE          = WC_SHA256_DIGEST_SIZE,
#else
    KEYID_SIZE          = WC_SHA_DIGEST_SIZE,
#endif
    RSA_INTS            =   8,     /* RSA ints in private key */
    DSA_INTS            =   5,     /* DSA ints in private key */
    MIN_DATE_SIZE       =  13,
    MAX_DATE_SIZE       =  32,
    ASN_GEN_TIME_SZ     =  15,     /* 7 numbers * 2 + Zulu tag */
#ifndef NO_RSA
    MAX_ENCODED_SIG_SZ  = 512,
#elif defined(HAVE_ECC)
    MAX_ENCODED_SIG_SZ  = 140,
#elif defined(HAVE_CURVE448)
    MAX_ENCODED_SIG_SZ  = 114,
#else
    MAX_ENCODED_SIG_SZ  =  64,
#endif
    MAX_SIG_SZ          = 256,
    MAX_ALGO_SZ         =  20,
    MAX_SHORT_SZ        =   6,     /* asn int + byte len + 4 byte length */
    MAX_SEQ_SZ          =   5,     /* enum(seq | con) + length(4) */
    MAX_SET_SZ          =   5,     /* enum(set | con) + length(4) */
    MAX_OCTET_STR_SZ    =   5,     /* enum(set | con) + length(4) */
    MAX_EXP_SZ          =   5,     /* enum(contextspec|con|exp) + length(4) */
    MAX_PRSTR_SZ        =   5,     /* enum(prstr) + length(4) */
    MAX_VERSION_SZ      =   5,     /* enum + id + version(byte) + (header(2))*/
    MAX_ENCODED_DIG_ASN_SZ= 9,     /* enum(bit or octet) + length(4) */
    MAX_ENCODED_DIG_SZ  =  64 + MAX_ENCODED_DIG_ASN_SZ, /* asn header + sha512 */
    MAX_RSA_INT_SZ      = 517,     /* RSA raw sz 4096 for bits + tag + len(4) */
    MAX_DSA_INT_SZ      = 261,     /* DSA raw sz 2048 for bits + tag + len(4) */
    MAX_NTRU_KEY_SZ     = 610,     /* NTRU 112 bit public key */
    MAX_NTRU_ENC_SZ     = 628,     /* NTRU 112 bit DER public encoding */
    MAX_LENGTH_SZ       =   4,     /* Max length size for DER encoding */
    MAX_RSA_E_SZ        =  16,     /* Max RSA public e size */
    MAX_CA_SZ           =  32,     /* Max encoded CA basic constraint length */
    MAX_SN_SZ           =  35,     /* Max encoded serial number (INT) length */
    MAX_DER_DIGEST_SZ     = MAX_ENCODED_DIG_SZ + MAX_ALGO_SZ + MAX_SEQ_SZ,
                            /* Maximum DER digest size */
    MAX_DER_DIGEST_ASN_SZ = MAX_ENCODED_DIG_ASN_SZ + MAX_ALGO_SZ + MAX_SEQ_SZ,
                            /* Maximum DER digest ASN header size */
                            /* Max X509 header length indicates the max length + 2 ('\n', '\0') */
    MAX_X509_HEADER_SZ  = (37 + 2), /* Maximum PEM Header/Footer Size */
#ifdef WOLFSSL_CERT_GEN
    #ifdef WOLFSSL_CERT_REQ
                          /* Max encoded cert req attributes length */
        MAX_ATTRIB_SZ   = MAX_SEQ_SZ * 3 + (11 + MAX_SEQ_SZ) * 2 +
                          MAX_PRSTR_SZ + CTC_NAME_SIZE, /* 11 is the OID size */
    #endif
    #if defined(WOLFSSL_ALT_NAMES) || defined(WOLFSSL_CERT_EXT)
        MAX_EXTENSIONS_SZ   = 1 + MAX_LENGTH_SZ + CTC_MAX_ALT_SIZE,
    #else
        MAX_EXTENSIONS_SZ   = 1 + MAX_LENGTH_SZ + MAX_CA_SZ,
    #endif
                                   /* Max total extensions, id + len + others */
#endif
#if defined(WOLFSSL_CERT_EXT) || defined(OPENSSL_EXTRA) || \
        defined(HAVE_PKCS7) || defined(OPENSSL_EXTRA_X509_SMALL)
    MAX_OID_SZ          = 32,      /* Max DER length of OID*/
    MAX_OID_STRING_SZ   = 64,      /* Max string length representation of OID*/
#endif
#ifdef WOLFSSL_CERT_EXT
    MAX_KID_SZ          = 45,      /* Max encoded KID length (SHA-256 case) */
    MAX_KEYUSAGE_SZ     = 18,      /* Max encoded Key Usage length */
    MAX_EXTKEYUSAGE_SZ  = 12 + (6 * (8 + 2)) +
                          CTC_MAX_EKU_OID_SZ, /* Max encoded ExtKeyUsage
                          (SEQ/LEN + OBJID + OCTSTR/LEN + SEQ +
                          (6 * (SEQ + OID))) */
    MAX_CERTPOL_NB      = CTC_MAX_CERTPOL_NB,/* Max number of Cert Policy */
    MAX_CERTPOL_SZ      = CTC_MAX_CERTPOL_SZ,
#endif
    MAX_AIA_SZ          = 2,       /* Max Authority Info Access extension size*/
    MAX_NAME_ENTRIES    = 13,      /* entries added to x509 name struct */
    OCSP_NONCE_EXT_SZ   = 35,      /* OCSP Nonce Extension size */
    MAX_OCSP_EXT_SZ     = 58,      /* Max OCSP Extension length */
    MAX_OCSP_NONCE_SZ   = 16,      /* OCSP Nonce size           */
    EIGHTK_BUF          = 8192,    /* Tmp buffer size           */
    MAX_PUBLIC_KEY_SZ   = MAX_NTRU_ENC_SZ + MAX_ALGO_SZ + MAX_SEQ_SZ * 2,
                                   /* use bigger NTRU size */
#ifdef WOLFSSL_ENCRYPTED_KEYS
    HEADER_ENCRYPTED_KEY_SIZE = 88,/* Extra header size for encrypted key */
#else
    HEADER_ENCRYPTED_KEY_SIZE = 0,
#endif
    TRAILING_ZERO       = 1,       /* Used for size of zero pad */
    ASN_TAG_SZ          = 1,       /* single byte ASN.1 tag */
    MIN_VERSION_SZ      = 3,       /* Min bytes needed for GetMyVersion */
    MAX_X509_VERSION    = 3,       /* Max X509 version allowed */
    MIN_X509_VERSION    = 0,       /* Min X509 version allowed */
#if defined(OPENSSL_ALL)  || defined(WOLFSSL_MYSQL_COMPATIBLE) || \
    defined(WOLFSSL_NGINX) || defined(WOLFSSL_HAPROXY) || \
    defined(OPENSSL_EXTRA) || defined(HAVE_PKCS7)
    MAX_TIME_STRING_SZ  = 25,      /* Max length of formatted time string */
#endif

    PKCS5_SALT_SZ       = 8,

    PEM_LINE_SZ        = 64,               /* Length of Base64 encoded line, not including new line */
    PEM_LINE_LEN       = PEM_LINE_SZ + 12, /* PEM line max + fudge */
};


enum Oid_Types {
    oidHashType         = 0,
    oidSigType          = 1,
    oidKeyType          = 2,
    oidCurveType        = 3,
    oidBlkType          = 4,
    oidOcspType         = 5,
    oidCertExtType      = 6,
    oidCertAuthInfoType = 7,
    oidCertPolicyType   = 8,
    oidCertAltNameType  = 9,
    oidCertKeyUseType   = 10,
    oidKdfType          = 11,
    oidKeyWrapType      = 12,
    oidCmsKeyAgreeType  = 13,
    oidPBEType          = 14,
    oidHmacType         = 15,
    oidCompressType     = 16,
    oidCertNameType     = 17,
    oidTlsExtType       = 18,
    oidCrlExtType       = 19,
    oidIgnoreType
};


enum Hash_Sum  {
    MD2h      = 646,
    MD5h      = 649,
    SHAh      =  88,
    SHA224h   = 417,
    SHA256h   = 414,
    SHA384h   = 415,
    SHA512h   = 416,
    SHA3_224h = 420,
    SHA3_256h = 421,
    SHA3_384h = 422,
    SHA3_512h = 423
};


#if !defined(NO_DES3) || !defined(NO_AES)
enum Block_Sum {
#ifdef WOLFSSL_AES_128
    AES128CBCb = 414,
    AES128GCMb = 418,
    AES128CCMb = 419,
#endif
#ifdef WOLFSSL_AES_192
    AES192CBCb = 434,
    AES192GCMb = 438,
    AES192CCMb = 439,
#endif
#ifdef WOLFSSL_AES_256
    AES256CBCb = 454,
    AES256GCMb = 458,
    AES256CCMb = 459,
#endif
#ifndef NO_DES3
    DESb       = 69,
    DES3b      = 652
#endif
};
#endif /* !NO_DES3 || !NO_AES */


enum Key_Sum {
    DSAk     = 515,
    RSAk     = 645,
    NTRUk    = 274,
    ECDSAk   = 518,
    ED25519k = 256,
    ED448k   = 257,
    DHk      = 647, /* dhKeyAgreement OID: 1.2.840.113549.1.3.1 */
};

#if !defined(NO_AES) || defined(HAVE_PKCS7)
enum KeyWrap_Sum {
#ifdef WOLFSSL_AES_128
    AES128_WRAP  = 417,
#endif
#ifdef WOLFSSL_AES_192
    AES192_WRAP  = 437,
#endif
#ifdef WOLFSSL_AES_256
    AES256_WRAP  = 457,
#endif
#ifdef HAVE_PKCS7
    PWRI_KEK_WRAP = 680  /*id-alg-PWRI-KEK, 1.2.840.113549.1.9.16.3.9 */
#endif
};
#endif /* !NO_AES || PKCS7 */

enum Key_Agree {
    dhSinglePass_stdDH_sha1kdf_scheme   = 464,
    dhSinglePass_stdDH_sha224kdf_scheme = 188,
    dhSinglePass_stdDH_sha256kdf_scheme = 189,
    dhSinglePass_stdDH_sha384kdf_scheme = 190,
    dhSinglePass_stdDH_sha512kdf_scheme = 191,
};



enum KDF_Sum {
    PBKDF2_OID = 660
};


enum HMAC_Sum {
    HMAC_SHA224_OID   = 652,
    HMAC_SHA256_OID   = 653,
    HMAC_SHA384_OID   = 654,
    HMAC_SHA512_OID   = 655,
    HMAC_SHA3_224_OID = 426,
    HMAC_SHA3_256_OID = 427,
    HMAC_SHA3_384_OID = 428,
    HMAC_SHA3_512_OID = 429
};


enum Extensions_Sum {
    BASIC_CA_OID    = 133,
    ALT_NAMES_OID   = 131,
    CRL_DIST_OID    = 145,
    AUTH_INFO_OID   = 69, /* id-pe 1 */
    AUTH_KEY_OID    = 149,
    SUBJ_KEY_OID    = 128,
    CERT_POLICY_OID = 146,
    KEY_USAGE_OID   = 129,  /* 2.5.29.15 */
    INHIBIT_ANY_OID = 168,  /* 2.5.29.54 */
    EXT_KEY_USAGE_OID         = 151, /* 2.5.29.37 */
    NAME_CONS_OID             = 144, /* 2.5.29.30 */
    PRIV_KEY_USAGE_PERIOD_OID = 130, /* 2.5.29.16 */
    SUBJECT_INFO_ACCESS       = 79,  /* id-pe 11 */
    POLICY_MAP_OID            = 147,
    POLICY_CONST_OID          = 150,
    ISSUE_ALT_NAMES_OID       = 132,
    TLS_FEATURE_OID           = 92,  /* id-pe 24 */
    NETSCAPE_CT_OID           = 753  /* 2.16.840.1.113730.1.1 */
};

enum CertificatePolicy_Sum {
    CP_ANY_OID      = 146  /* id-ce 32 0 */
};

enum SepHardwareName_Sum {
    HW_NAME_OID     = 79   /* 1.3.6.1.5.5.7.8.4 from RFC 4108*/
};

enum AuthInfo_Sum {
    AIA_OCSP_OID      = 116, /* 1.3.6.1.5.5.7.48.1 */
    AIA_CA_ISSUER_OID = 117  /* 1.3.6.1.5.5.7.48.2 */
};

enum ExtKeyUsage_Sum { /* From RFC 5280 */
    EKU_ANY_OID         = 151, /* 2.5.29.37.0, anyExtendedKeyUsage         */
    EKU_SERVER_AUTH_OID = 71,  /* 1.3.6.1.5.5.7.3.1, id-kp-serverAuth      */
    EKU_CLIENT_AUTH_OID = 72,  /* 1.3.6.1.5.5.7.3.2, id-kp-clientAuth      */
    EKU_CODESIGNING_OID = 73,  /* 1.3.6.1.5.5.7.3.3, id-kp-codeSigning     */
    EKU_EMAILPROTECT_OID = 74, /* 1.3.6.1.5.5.7.3.4, id-kp-emailProtection */
    EKU_TIMESTAMP_OID   = 78,  /* 1.3.6.1.5.5.7.3.8, id-kp-timeStamping    */
    EKU_OCSP_SIGN_OID   = 79   /* 1.3.6.1.5.5.7.3.9, id-kp-OCSPSigning     */
};

#ifdef HAVE_LIBZ
enum CompressAlg_Sum {
    ZLIBc = 679  /* 1.2.840.113549.1.9.16.3.8, id-alg-zlibCompress */
};
#endif

enum VerifyType {
    NO_VERIFY   = 0,
    VERIFY      = 1,
    VERIFY_CRL  = 2,
    VERIFY_OCSP = 3,
    VERIFY_NAME = 4,
    VERIFY_SKIP_DATE = 5,
};

#ifdef WOLFSSL_CERT_EXT
enum KeyIdType {
    SKID_TYPE = 0,
    AKID_TYPE = 1
};
#endif

/* Key usage extension bits (based on RFC 5280) */
#define KEYUSE_DIGITAL_SIG    0x0080
#define KEYUSE_CONTENT_COMMIT 0x0040
#define KEYUSE_KEY_ENCIPHER   0x0020
#define KEYUSE_DATA_ENCIPHER  0x0010
#define KEYUSE_KEY_AGREE      0x0008
#define KEYUSE_KEY_CERT_SIGN  0x0004
#define KEYUSE_CRL_SIGN       0x0002
#define KEYUSE_ENCIPHER_ONLY  0x0001
#define KEYUSE_DECIPHER_ONLY  0x8000

/* Extended Key Usage bits (internal mapping only) */
#define EXTKEYUSE_USER        0x80
#define EXTKEYUSE_OCSP_SIGN   0x40
#define EXTKEYUSE_TIMESTAMP   0x20
#define EXTKEYUSE_EMAILPROT   0x10
#define EXTKEYUSE_CODESIGN    0x08
#define EXTKEYUSE_CLIENT_AUTH 0x04
#define EXTKEYUSE_SERVER_AUTH 0x02
#define EXTKEYUSE_ANY         0x01

typedef struct DNS_entry   DNS_entry;

struct DNS_entry {
    DNS_entry* next;   /* next on DNS list */
    int        type;   /* i.e. ASN_DNS_TYPE */
    int        len;    /* actual DNS len */
    char*      name;   /* actual DNS name */
};


typedef struct Base_entry  Base_entry;

struct Base_entry {
    Base_entry* next;   /* next on name base list */
    char*       name;   /* actual name base */
    int         nameSz; /* name length */
    byte        type;   /* Name base type (DNS or RFC822) */
};


enum SignatureState {
    SIG_STATE_BEGIN,
    SIG_STATE_HASH,
    SIG_STATE_KEY,
    SIG_STATE_DO,
    SIG_STATE_CHECK,
};


#ifdef HAVE_PK_CALLBACKS
#ifdef HAVE_ECC
    typedef int (*wc_CallbackEccVerify)(
           const unsigned char* sig, unsigned int sigSz,
           const unsigned char* hash, unsigned int hashSz,
           const unsigned char* keyDer, unsigned int keySz,
           int* result, void* ctx);
#endif
#ifndef NO_RSA
    typedef int (*wc_CallbackRsaVerify)(
           unsigned char* sig, unsigned int sigSz,
           unsigned char** out,
           const unsigned char* keyDer, unsigned int keySz,
           void* ctx);
#endif
#endif /* HAVE_PK_CALLBACKS */

struct SignatureCtx {
    void* heap;
    byte* digest;
#ifndef NO_RSA
    byte* out;
    byte* plain;
#endif
#if defined(HAVE_ECC) || defined(HAVE_ED25519) || defined(HAVE_ED448)
    int verify;
#endif
    union {
    #ifndef NO_RSA
        struct RsaKey*      rsa;
    #endif
    #ifdef HAVE_ECC
        struct ecc_key*     ecc;
    #endif
    #ifdef HAVE_ED25519
        struct ed25519_key* ed25519;
    #endif
    #ifdef HAVE_ED448
        struct ed448_key* ed448;
    #endif
        void* ptr;
    } key;
    int devId;
    int state;
    int typeH;
    int digestSz;
    word32 keyOID;
#ifdef WOLFSSL_ASYNC_CRYPT
    WC_ASYNC_DEV* asyncDev;
    void* asyncCtx;
#endif

#ifdef HAVE_PK_CALLBACKS
#ifdef HAVE_ECC
    wc_CallbackEccVerify pkCbEcc;
    void* pkCtxEcc;
#endif
#ifndef NO_RSA
    wc_CallbackRsaVerify pkCbRsa;
    void* pkCtxRsa;
#endif
#endif /* HAVE_PK_CALLBACKS */
#ifndef NO_RSA
#ifdef WOLFSSL_RENESAS_TSIP_TLS
    byte verifyByTSIP;
    word32 certBegin;
    word32 pubkey_n_start;
    word32 pubkey_n_len;
    word32 pubkey_e_start;
    word32 pubkey_e_len;
#endif
#endif
};

enum CertSignState {
    CERTSIGN_STATE_BEGIN,
    CERTSIGN_STATE_DIGEST,
    CERTSIGN_STATE_ENCODE,
    CERTSIGN_STATE_DO,
};

struct CertSignCtx {
    byte* sig;
    byte* digest;
    #ifndef NO_RSA
        byte* encSig;
        int encSigSz;
    #endif
    int state; /* enum CertSignState */
};

#ifndef WOLFSSL_MAX_PATH_LEN
    /* RFC 5280 Section 6.1.2. "Initialization" - item (k) defines
     *     (k)  max_path_length:  this integer is initialized to "n", is
     *     decremented for each non-self-issued certificate in the path,
     *     and may be reduced to the value in the path length constraint
     *     field within the basic constraints extension of a CA
     *     certificate.
     *
     * wolfSSL has arbitrarily selected the value 127 for "n" in the above
     * description. Users can modify the maximum path length by setting
     * WOLFSSL_MAX_PATH_LEN to a preferred value at build time
     */
    #define WOLFSSL_MAX_PATH_LEN 127
#endif

typedef struct DecodedCert DecodedCert;
typedef struct Signer      Signer;
#ifdef WOLFSSL_TRUST_PEER_CERT
typedef struct TrustedPeerCert TrustedPeerCert;
#endif /* WOLFSSL_TRUST_PEER_CERT */
typedef struct SignatureCtx SignatureCtx;
typedef struct CertSignCtx  CertSignCtx;


struct DecodedCert {
    const byte* publicKey;
    word32  pubKeySize;
    int     pubKeyStored;
    word32  certBegin;               /* offset to start of cert          */
    word32  sigIndex;                /* offset to start of signature     */
    word32  sigLength;               /* length of signature              */
    word32  signatureOID;            /* sum of algorithm object id       */
    word32  keyOID;                  /* sum of key algo  object id       */
    int     version;                 /* cert version, 1 or 3             */
    DNS_entry* altNames;             /* alt names list of dns entries    */
#ifndef IGNORE_NAME_CONSTRAINTS
    DNS_entry* altEmailNames;        /* alt names list of RFC822 entries */
    Base_entry* permittedNames;      /* Permitted name bases             */
    Base_entry* excludedNames;       /* Excluded name bases              */
#endif /* IGNORE_NAME_CONSTRAINTS */
    byte    subjectHash[KEYID_SIZE]; /* hash of all Names                */
    byte    issuerHash[KEYID_SIZE];  /* hash of all Names                */
#ifdef HAVE_OCSP
    byte    subjectKeyHash[KEYID_SIZE]; /* hash of the public Key         */
    byte    issuerKeyHash[KEYID_SIZE]; /* hash of the public Key         */
#endif /* HAVE_OCSP */
    const byte* signature;           /* not owned, points into raw cert  */
    char*   subjectCN;               /* CommonName                       */
    int     subjectCNLen;            /* CommonName Length                */
    char    subjectCNEnc;            /* CommonName Encoding              */
    char    issuer[ASN_NAME_MAX];    /* full name including common name  */
    char    subject[ASN_NAME_MAX];   /* full name including common name  */
    int     verify;                  /* Default to yes, but could be off */
    const byte* source;              /* byte buffer holder cert, NOT owner */
    word32  srcIdx;                  /* current offset into buffer       */
    word32  maxIdx;                  /* max offset based on init size    */
    void*   heap;                    /* for user memory overrides        */
    byte    serial[EXTERNAL_SERIAL_SIZE];  /* raw serial number          */
    int     serialSz;                /* raw serial bytes stored */
    const byte* extensions;          /* not owned, points into raw cert  */
    int     extensionsSz;            /* length of cert extensions */
    word32  extensionsIdx;           /* if want to go back and parse later */
    const byte* extAuthInfo;         /* Authority Information Access URI */
    int     extAuthInfoSz;           /* length of the URI                */
#if defined(OPENSSL_ALL) || defined(WOLFSSL_QT)
    const byte* extAuthInfoCaIssuer; /* Authority Info Access caIssuer URI */
    int     extAuthInfoCaIssuerSz;   /* length of the caIssuer URI         */
#endif
    const byte* extCrlInfo;          /* CRL Distribution Points          */
    int     extCrlInfoSz;            /* length of the URI                */
    byte    extSubjKeyId[KEYID_SIZE]; /* Subject Key ID                  */
    byte    extAuthKeyId[KEYID_SIZE]; /* Authority Key ID                */
    byte    pathLength;              /* CA basic constraint path length  */
    byte    maxPathLen;              /* max_path_len see RFC 5280 section
                                      * 6.1.2 "Initialization" - (k) for
                                      * description of max_path_len */
    word16  extKeyUsage;             /* Key usage bitfield               */
    byte    extExtKeyUsage;          /* Extended Key usage bitfield      */

#if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
    const byte* extExtKeyUsageSrc;
    word32  extExtKeyUsageSz;
    word32  extExtKeyUsageCount;
    const byte* extAuthKeyIdSrc;
    word32  extAuthKeyIdSz;
    const byte* extSubjKeyIdSrc;
    word32  extSubjKeyIdSz;
#endif

#if defined(HAVE_ECC) || defined(HAVE_ED25519) || defined(HAVE_ED448)
    word32  pkCurveOID;           /* Public Key's curve OID */
#endif /* HAVE_ECC */
    const byte* beforeDate;
    int     beforeDateLen;
    const byte* afterDate;
    int     afterDateLen;
#if defined(HAVE_PKCS7) || defined(WOLFSSL_CERT_EXT)
    const byte* issuerRaw;           /* pointer to issuer inside source */
    int     issuerRawLen;
#endif
#if !defined(IGNORE_NAME_CONSTRAINTS) || defined(WOLFSSL_CERT_EXT)
    const byte* subjectRaw;          /* pointer to subject inside source */
    int     subjectRawLen;
#endif
#if defined(WOLFSSL_CERT_GEN) || defined(WOLFSSL_CERT_EXT)
    /* easy access to subject info for other sign */
    char*   subjectSN;
    int     subjectSNLen;
    char    subjectSNEnc;
    char*   subjectC;
    int     subjectCLen;
    char    subjectCEnc;
    char*   subjectL;
    int     subjectLLen;
    char    subjectLEnc;
    char*   subjectST;
    int     subjectSTLen;
    char    subjectSTEnc;
    char*   subjectO;
    int     subjectOLen;
    char    subjectOEnc;
    char*   subjectOU;
    int     subjectOULen;
    char    subjectOUEnc;
    char*   subjectSND;
    int     subjectSNDLen;
    char    subjectSNDEnc;
#ifdef WOLFSSL_CERT_EXT
    char*   subjectBC;
    int     subjectBCLen;
    char    subjectBCEnc;
    char*   subjectJC;
    int     subjectJCLen;
    char    subjectJCEnc;
    char*   subjectJS;
    int     subjectJSLen;
    char    subjectJSEnc;
#endif
    char*   subjectEmail;
    int     subjectEmailLen;
#endif /* WOLFSSL_CERT_GEN */
#if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
    /* WOLFSSL_X509_NAME structures (used void* to avoid including ssl.h) */
    void* issuerName;
    void* subjectName;
#endif /* OPENSSL_EXTRA */
#ifdef WOLFSSL_SEP
    int     deviceTypeSz;
    byte*   deviceType;
    int     hwTypeSz;
    byte*   hwType;
    int     hwSerialNumSz;
    byte*   hwSerialNum;
#endif /* WOLFSSL_SEP */
#ifdef WOLFSSL_CERT_EXT
    char    extCertPolicies[MAX_CERTPOL_NB][MAX_CERTPOL_SZ];
    int     extCertPoliciesNb;
#endif /* defined(WOLFSSL_CERT_GEN) || defined(WOLFSSL_CERT_EXT) */

    Signer* ca;
#ifndef NO_CERTS
    SignatureCtx sigCtx;
#endif
#ifdef WOLFSSL_RENESAS_TSIP
    byte*  tsip_encRsaKeyIdx;
#endif

    int badDate;
    int criticalExt;

    /* Option Bits */
    byte subjectCNStored : 1;      /* have we saved a copy we own */
    byte extSubjKeyIdSet : 1;      /* Set when the SKID was read from cert */
    byte extAuthKeyIdSet : 1;      /* Set when the AKID was read from cert */
#ifndef IGNORE_NAME_CONSTRAINTS
    byte extNameConstraintSet : 1;
#endif
    byte isCA : 1;                 /* CA basic constraint true */
    byte pathLengthSet : 1;        /* CA basic const path length set */
    byte weOwnAltNames : 1;        /* altNames haven't been given to copy */
    byte extKeyUsageSet : 1;
    byte extExtKeyUsageSet : 1;    /* Extended Key Usage set */
    byte extCRLdistSet : 1;
    byte extAuthInfoSet : 1;
    byte extBasicConstSet : 1;
    byte extSubjAltNameSet : 1;
    byte inhibitAnyOidSet : 1;
    byte selfSigned : 1;           /* Indicates subject and issuer are same */
#if defined(WOLFSSL_SEP) || defined(WOLFSSL_QT)
    byte extCertPolicySet : 1;
#endif
#if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
    byte extCRLdistCrit : 1;
    byte extAuthInfoCrit : 1;
    byte extBasicConstCrit : 1;
    byte extSubjAltNameCrit : 1;
    byte extAuthKeyIdCrit : 1;
    #ifndef IGNORE_NAME_CONSTRAINTS
        byte extNameConstraintCrit : 1;
    #endif
    byte extSubjKeyIdCrit : 1;
    byte extKeyUsageCrit : 1;
    byte extExtKeyUsageCrit : 1;
#endif /* OPENSSL_EXTRA */
#if defined(WOLFSSL_SEP) || defined(WOLFSSL_QT)
    byte extCertPolicyCrit : 1;
#endif

};


#ifdef NO_SHA
    #define SIGNER_DIGEST_SIZE WC_SHA256_DIGEST_SIZE
#else
    #define SIGNER_DIGEST_SIZE WC_SHA_DIGEST_SIZE
#endif

/* CA Signers */
/* if change layout change PERSIST_CERT_CACHE functions too */
struct Signer {
    word32  pubKeySize;
    word32  keyOID;                  /* key type */
    word16  keyUsage;
    byte    maxPathLen;
    byte    pathLength;
    byte    pathLengthSet : 1;
    byte    selfSigned : 1;
    const byte* publicKey;
    int     nameLen;
    char*   name;                    /* common name */
#ifndef IGNORE_NAME_CONSTRAINTS
        Base_entry* permittedNames;
        Base_entry* excludedNames;
#endif /* IGNORE_NAME_CONSTRAINTS */
    byte    subjectNameHash[SIGNER_DIGEST_SIZE];
                                     /* sha hash of names in certificate */
    #ifndef NO_SKID
        byte    subjectKeyIdHash[SIGNER_DIGEST_SIZE];
                                     /* sha hash of names in certificate */
    #endif
    #ifdef HAVE_OCSP
        byte subjectKeyHash[KEYID_SIZE];
    #endif
#ifdef WOLFSSL_SIGNER_DER_CERT
    DerBuffer* derCert;
#endif
#ifdef WOLFSSL_RENESAS_TSIP_TLS
    word32 cm_idx;
#endif
    Signer* next;
};


#ifdef WOLFSSL_TRUST_PEER_CERT
/* used for having trusted peer certs rather then CA */
struct TrustedPeerCert {
    int     nameLen;
    char*   name;                    /* common name */
    #ifndef IGNORE_NAME_CONSTRAINTS
        Base_entry* permittedNames;
        Base_entry* excludedNames;
    #endif /* IGNORE_NAME_CONSTRAINTS */
    byte    subjectNameHash[SIGNER_DIGEST_SIZE];
                                     /* sha hash of names in certificate */
    #ifndef NO_SKID
        byte    subjectKeyIdHash[SIGNER_DIGEST_SIZE];
                                     /* sha hash of names in certificate */
    #endif
    word32 sigLen;
    byte*  sig;
    struct TrustedPeerCert* next;
};
#endif /* WOLFSSL_TRUST_PEER_CERT */


/* for testing or custom openssl wrappers */
#if defined(WOLFSSL_TEST_CERT) || defined(OPENSSL_EXTRA) || \
    defined(OPENSSL_EXTRA_X509_SMALL)
    #define WOLFSSL_ASN_API WOLFSSL_API
#else
    #define WOLFSSL_ASN_API WOLFSSL_LOCAL
#endif

WOLFSSL_LOCAL int CalcHashId(const byte* data, word32 len, byte* hash);
WOLFSSL_LOCAL int GetName(DecodedCert* cert, int nameType, int maxIdx);

WOLFSSL_ASN_API int wc_BerToDer(const byte* ber, word32 berSz, byte* der,
                                word32* derSz);

WOLFSSL_ASN_API void FreeAltNames(DNS_entry*, void*);
#ifndef IGNORE_NAME_CONSTRAINTS
    WOLFSSL_ASN_API void FreeNameSubtrees(Base_entry*, void*);
#endif /* IGNORE_NAME_CONSTRAINTS */
WOLFSSL_ASN_API void InitDecodedCert(DecodedCert*, const byte*, word32, void*);
WOLFSSL_ASN_API void FreeDecodedCert(DecodedCert*);
WOLFSSL_ASN_API int  ParseCert(DecodedCert*, int type, int verify, void* cm);

WOLFSSL_LOCAL int DecodePolicyOID(char *o, word32 oSz,
                                  const byte *in, word32 inSz);
WOLFSSL_LOCAL int EncodePolicyOID(byte *out, word32 *outSz,
                                  const char *in, void* heap);
WOLFSSL_API int CheckCertSignature(const byte*,word32,void*,void* cm);
WOLFSSL_LOCAL int CheckCertSignaturePubKey(const byte* cert, word32 certSz,
        void* heap, const byte* pubKey, word32 pubKeySz, int pubKeyOID);
WOLFSSL_LOCAL int ParseCertRelative(DecodedCert*,int type,int verify,void* cm);
WOLFSSL_LOCAL int DecodeToKey(DecodedCert*, int verify);
WOLFSSL_LOCAL int wc_GetPubX509(DecodedCert* cert, int verify, int* badDate);

WOLFSSL_LOCAL const byte* OidFromId(word32 id, word32 type, word32* oidSz);
WOLFSSL_LOCAL Signer* MakeSigner(void*);
WOLFSSL_LOCAL void    FreeSigner(Signer*, void*);
WOLFSSL_LOCAL void    FreeSignerTable(Signer**, int, void*);
#ifdef WOLFSSL_TRUST_PEER_CERT
WOLFSSL_LOCAL void    FreeTrustedPeer(TrustedPeerCert*, void*);
WOLFSSL_LOCAL void    FreeTrustedPeerTable(TrustedPeerCert**, int, void*);
#endif /* WOLFSSL_TRUST_PEER_CERT */

WOLFSSL_ASN_API int ToTraditional(byte* buffer, word32 length);
WOLFSSL_ASN_API int ToTraditional_ex(byte* buffer, word32 length,
                                     word32* algId);
WOLFSSL_LOCAL int ToTraditionalInline(const byte* input, word32* inOutIdx,
                                      word32 length);
WOLFSSL_LOCAL int ToTraditionalInline_ex(const byte* input, word32* inOutIdx,
                                         word32 length, word32* algId);
WOLFSSL_LOCAL int ToTraditionalEnc(byte* buffer, word32 length,const char*,int,
                                   word32* algId);
WOLFSSL_ASN_API int UnTraditionalEnc(byte* key, word32 keySz, byte* out,
        word32* outSz, const char* password, int passwordSz, int vPKCS,
        int vAlgo, byte* salt, word32 saltSz, int itt, WC_RNG* rng, void* heap);
WOLFSSL_ASN_API int TraditionalEnc(byte* key, word32 keySz, byte* out,
        word32* outSz, const char* password, int passwordSz, int vPKCS,
        int vAlgo, int encAlgId, byte* salt, word32 saltSz, int itt,
        WC_RNG* rng, void* heap);
WOLFSSL_LOCAL int DecryptContent(byte* input, word32 sz,const char* psw,int pswSz);
WOLFSSL_LOCAL int EncryptContent(byte* input, word32 sz, byte* out, word32* outSz,
        const char* password,int passwordSz, int vPKCS, int vAlgo,
        byte* salt, word32 saltSz, int itt, WC_RNG* rng, void* heap);
WOLFSSL_LOCAL int wc_GetKeyOID(byte* key, word32 keySz, const byte** curveOID,
        word32* oidSz, int* algoID, void* heap);

typedef struct tm wolfssl_tm;
#if defined(OPENSSL_ALL) || defined(WOLFSSL_MYSQL_COMPATIBLE) || defined(OPENSSL_EXTRA) || \
    defined(WOLFSSL_NGINX) || defined(WOLFSSL_HAPROXY)
WOLFSSL_LOCAL int GetTimeString(byte* date, int format, char* buf, int len);
#endif
#if !defined(NO_ASN_TIME) && defined(HAVE_PKCS7)
WOLFSSL_LOCAL int GetAsnTimeString(void* currTime, byte* buf, word32 len);
#endif
WOLFSSL_LOCAL int ExtractDate(const unsigned char* date, unsigned char format,
                                                 wolfssl_tm* certTime, int* idx);
WOLFSSL_LOCAL int DateGreaterThan(const struct tm* a, const struct tm* b);
WOLFSSL_LOCAL int wc_ValidateDate(const byte* date, byte format, int dateType);
WOLFSSL_LOCAL int wc_OBJ_sn2nid(const char *sn);

/* ASN.1 helper functions */
#ifdef WOLFSSL_CERT_GEN
WOLFSSL_ASN_API int SetName(byte* output, word32 outputSz, CertName* name);
WOLFSSL_LOCAL const char* GetOneCertName(CertName* name, int idx);
WOLFSSL_LOCAL byte GetCertNameId(int idx);
#endif
WOLFSSL_LOCAL int GetShortInt(const byte* input, word32* inOutIdx, int* number,
                              word32 maxIdx);
WOLFSSL_LOCAL int SetShortInt(byte* input, word32* inOutIdx, word32 number,
                              word32 maxIdx);

WOLFSSL_LOCAL const char* GetSigName(int oid);
WOLFSSL_LOCAL int GetLength(const byte* input, word32* inOutIdx, int* len,
                           word32 maxIdx);
WOLFSSL_LOCAL int GetLength_ex(const byte* input, word32* inOutIdx, int* len,
                           word32 maxIdx, int check);
WOLFSSL_LOCAL int GetSequence(const byte* input, word32* inOutIdx, int* len,
                             word32 maxIdx);
WOLFSSL_LOCAL int GetSequence_ex(const byte* input, word32* inOutIdx, int* len,
                           word32 maxIdx, int check);
WOLFSSL_LOCAL int GetOctetString(const byte* input, word32* inOutIdx, int* len,
                         word32 maxIdx);
WOLFSSL_LOCAL int GetSet(const byte* input, word32* inOutIdx, int* len,
                        word32 maxIdx);
WOLFSSL_LOCAL int GetSet_ex(const byte* input, word32* inOutIdx, int* len,
                        word32 maxIdx, int check);
WOLFSSL_LOCAL int GetMyVersion(const byte* input, word32* inOutIdx,
                              int* version, word32 maxIdx);
WOLFSSL_LOCAL int GetInt(mp_int* mpi, const byte* input, word32* inOutIdx,
                        word32 maxIdx);
#ifdef HAVE_OID_ENCODING
    WOLFSSL_LOCAL int EncodeObjectId(const word16* in, word32 inSz,
        byte* out, word32* outSz);
#endif
#ifdef HAVE_OID_DECODING
    WOLFSSL_LOCAL int DecodeObjectId(const byte* in, word32 inSz,
        word16* out, word32* outSz);
#endif
WOLFSSL_LOCAL int GetASNObjectId(const byte* input, word32* inOutIdx, int* len,
                                 word32 maxIdx);
WOLFSSL_LOCAL int SetObjectId(int len, byte* output);
WOLFSSL_LOCAL int GetObjectId(const byte* input, word32* inOutIdx, word32* oid,
                              word32 oidType, word32 maxIdx);
WOLFSSL_LOCAL int GetAlgoId(const byte* input, word32* inOutIdx, word32* oid,
                           word32 oidType, word32 maxIdx);
WOLFSSL_LOCAL int GetASNTag(const byte* input, word32* idx, byte* tag,
                            word32 inputSz);
WOLFSSL_LOCAL word32 SetLength(word32 length, byte* output);
WOLFSSL_LOCAL word32 SetSequence(word32 len, byte* output);
WOLFSSL_LOCAL word32 SetOctetString(word32 len, byte* output);
#if (defined(WOLFSSL_QT) || defined(OPENSSL_ALL)) && !defined(NO_DH) \
    || defined(WOLFSSL_OPENSSH)
WOLFSSL_LOCAL int wc_DhParamsToDer(DhKey* key, byte* out, word32* outSz);
WOLFSSL_LOCAL int wc_DhPubKeyToDer(DhKey* key, byte* out, word32* outSz);
WOLFSSL_LOCAL int wc_DhPrivKeyToDer(DhKey* key, byte* out, word32* outSz);
#endif
WOLFSSL_LOCAL word32 SetBitString(word32 len, byte unusedBits, byte* output);
WOLFSSL_LOCAL word32 SetImplicit(byte tag,byte number,word32 len,byte* output);
WOLFSSL_LOCAL word32 SetExplicit(byte number, word32 len, byte* output);
WOLFSSL_LOCAL word32 SetSet(word32 len, byte* output);
WOLFSSL_LOCAL word32 SetAlgoID(int algoOID,byte* output,int type,int curveSz);
WOLFSSL_LOCAL int SetMyVersion(word32 version, byte* output, int header);
WOLFSSL_LOCAL int SetSerialNumber(const byte* sn, word32 snSz, byte* output,
    word32 outputSz, int maxSnSz);
WOLFSSL_LOCAL int GetSerialNumber(const byte* input, word32* inOutIdx,
    byte* serial, int* serialSz, word32 maxIdx);
WOLFSSL_LOCAL int GetNameHash(const byte* source, word32* idx, byte* hash,
                             int maxIdx);
WOLFSSL_LOCAL int wc_CheckPrivateKey(byte* key, word32 keySz, DecodedCert* der);
WOLFSSL_LOCAL int StoreDHparams(byte* out, word32* outLen, mp_int* p, mp_int* g);
WOLFSSL_LOCAL int FlattenAltNames( byte*, word32, const DNS_entry*);

#ifdef HAVE_ECC
    /* ASN sig helpers */
    WOLFSSL_LOCAL int StoreECC_DSA_Sig(byte* out, word32* outLen, mp_int* r,
                                      mp_int* s);
    WOLFSSL_LOCAL int DecodeECC_DSA_Sig(const byte* sig, word32 sigLen,
                                       mp_int* r, mp_int* s);
#endif
#if defined HAVE_ECC && (defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL))
WOLFSSL_API int EccEnumToNID(int n);
#endif

WOLFSSL_LOCAL void InitSignatureCtx(SignatureCtx* sigCtx, void* heap, int devId);
WOLFSSL_LOCAL void FreeSignatureCtx(SignatureCtx* sigCtx);

#ifndef NO_CERTS

WOLFSSL_LOCAL int wc_EncryptedInfoParse(EncryptedInfo* info, char** pBuffer,
                                        size_t bufSz);

WOLFSSL_LOCAL int PemToDer(const unsigned char* buff, long sz, int type,
                          DerBuffer** pDer, void* heap, EncryptedInfo* info,
                          int* eccKey);
WOLFSSL_LOCAL int AllocDer(DerBuffer** der, word32 length, int type, void* heap);
WOLFSSL_LOCAL void FreeDer(DerBuffer** der);

#endif /* !NO_CERTS */

#ifdef WOLFSSL_CERT_GEN

enum cert_enums {
#ifdef WOLFSSL_CERT_EXT
    NAME_ENTRIES    =  10,
#else
    NAME_ENTRIES    =  9,
#endif
    JOINT_LEN       =  2,
    EMAIL_JOINT_LEN =  9,
    PILOT_JOINT_LEN =  10,
    RSA_KEY         = 10,
    NTRU_KEY        = 11,
    ECC_KEY         = 12,
    ED25519_KEY     = 13,
    ED448_KEY       = 14
};

#endif /* WOLFSSL_CERT_GEN */



/* for pointer use */
typedef struct CertStatus CertStatus;

#ifdef HAVE_OCSP

enum Ocsp_Response_Status {
    OCSP_SUCCESSFUL        = 0, /* Response has valid confirmations */
    OCSP_MALFORMED_REQUEST = 1, /* Illegal confirmation request */
    OCSP_INTERNAL_ERROR    = 2, /* Internal error in issuer */
    OCSP_TRY_LATER         = 3, /* Try again later */
    OCSP_SIG_REQUIRED      = 5, /* Must sign the request (4 is skipped) */
    OCSP_UNAUTHROIZED      = 6  /* Request unauthorized */
};


enum Ocsp_Cert_Status {
    CERT_GOOD    = 0,
    CERT_REVOKED = 1,
    CERT_UNKNOWN = 2
};


enum Ocsp_Sums {
    OCSP_BASIC_OID = 117,
    OCSP_NONCE_OID = 118
};

#ifdef OPENSSL_EXTRA
enum Ocsp_Verify_Error {
    OCSP_VERIFY_ERROR_NONE = 0,
    OCSP_BAD_ISSUER = 1
};
#endif


typedef struct OcspRequest  OcspRequest;
typedef struct OcspResponse OcspResponse;


struct CertStatus {
    CertStatus* next;

    byte serial[EXTERNAL_SERIAL_SIZE];
    int serialSz;

    int status;

    byte thisDate[MAX_DATE_SIZE];
    byte nextDate[MAX_DATE_SIZE];
    byte thisDateFormat;
    byte nextDateFormat;
#if defined(OPENSSL_ALL) || defined(WOLFSSL_NGINX) || defined(WOLFSSL_HAPROXY)
    WOLFSSL_ASN1_TIME thisDateParsed;
    WOLFSSL_ASN1_TIME nextDateParsed;
    byte* thisDateAsn;
    byte* nextDateAsn;
#endif

    byte*  rawOcspResponse;
    word32 rawOcspResponseSz;
};


struct OcspResponse {
    int     responseStatus;  /* return code from Responder */

    byte*   response;        /* Pointer to beginning of OCSP Response */
    word32  responseSz;      /* length of the OCSP Response */

    byte    producedDate[MAX_DATE_SIZE];
                             /* Date at which this response was signed */
    byte    producedDateFormat; /* format of the producedDate */
    byte*   issuerHash;
    byte*   issuerKeyHash;

    byte*   cert;
    word32  certSz;

    byte*   sig;             /* Pointer to sig in source */
    word32  sigSz;           /* Length in octets for the sig */
    word32  sigOID;          /* OID for hash used for sig */

    CertStatus* status;      /* certificate status to fill out */

    byte*   nonce;           /* pointer to nonce inside ASN.1 response */
    int     nonceSz;         /* length of the nonce string */

    byte*   source;          /* pointer to source buffer, not owned */
    word32  maxIdx;          /* max offset based on init size */

#ifdef OPENSSL_EXTRA
    int     verifyError;
#endif
};


struct OcspRequest {
    byte   issuerHash[KEYID_SIZE];
    byte   issuerKeyHash[KEYID_SIZE];
    byte*  serial;   /* copy of the serial number in source cert */
    int    serialSz;
#ifdef OPENSSL_EXTRA
    WOLFSSL_ASN1_INTEGER* serialInt;
#endif
    byte*  url;      /* copy of the extAuthInfo in source cert */
    int    urlSz;

    byte   nonce[MAX_OCSP_NONCE_SZ];
    int    nonceSz;
    void*  heap;
    void*  ssl;
};

typedef struct OcspEntry OcspEntry;

#ifdef NO_SHA
#define OCSP_DIGEST_SIZE WC_SHA256_DIGEST_SIZE
#else
#define OCSP_DIGEST_SIZE WC_SHA_DIGEST_SIZE
#endif

struct OcspEntry
{
    OcspEntry *next;                      /* next entry             */
    byte issuerHash[OCSP_DIGEST_SIZE];    /* issuer hash            */
    byte issuerKeyHash[OCSP_DIGEST_SIZE]; /* issuer public key hash */
    CertStatus *status;                   /* OCSP response list     */
    int totalStatus;                      /* number on list         */
};

WOLFSSL_LOCAL void InitOcspResponse(OcspResponse*, CertStatus*, byte*, word32);
WOLFSSL_LOCAL int  OcspResponseDecode(OcspResponse*, void*, void* heap, int);

WOLFSSL_LOCAL int    InitOcspRequest(OcspRequest*, DecodedCert*, byte, void*);
WOLFSSL_LOCAL void   FreeOcspRequest(OcspRequest*);
WOLFSSL_LOCAL int    EncodeOcspRequest(OcspRequest*, byte*, word32);
WOLFSSL_LOCAL word32 EncodeOcspRequestExtensions(OcspRequest*, byte*, word32);


WOLFSSL_LOCAL int  CompareOcspReqResp(OcspRequest*, OcspResponse*);


#endif /* HAVE_OCSP */


/* for pointer use */
typedef struct RevokedCert RevokedCert;

#ifdef HAVE_CRL

struct RevokedCert {
    byte         serialNumber[EXTERNAL_SERIAL_SIZE];
    int          serialSz;
    RevokedCert* next;
};

typedef struct DecodedCRL DecodedCRL;

struct DecodedCRL {
    word32  certBegin;               /* offset to start of cert          */
    word32  sigIndex;                /* offset to start of signature     */
    word32  sigLength;               /* length of signature              */
    word32  signatureOID;            /* sum of algorithm object id       */
    byte*   signature;               /* pointer into raw source, not owned */
    byte    issuerHash[SIGNER_DIGEST_SIZE]; /* issuer name hash          */
    byte    crlHash[SIGNER_DIGEST_SIZE]; /* raw crl data hash            */
    byte    lastDate[MAX_DATE_SIZE]; /* last date updated  */
    byte    nextDate[MAX_DATE_SIZE]; /* next update date   */
    byte    lastDateFormat;          /* format of last date */
    byte    nextDateFormat;          /* format of next date */
    RevokedCert* certs;              /* revoked cert list  */
    int          totalCerts;         /* number on list     */
    void*   heap;
#ifndef NO_SKID
    byte    extAuthKeyIdSet;
    byte    extAuthKeyId[SIGNER_DIGEST_SIZE]; /* Authority Key ID        */
#endif
};

WOLFSSL_LOCAL void InitDecodedCRL(DecodedCRL*, void* heap);
WOLFSSL_LOCAL int VerifyCRL_Signature(SignatureCtx* sigCtx,
                                      const byte* toBeSigned, word32 tbsSz,
                                      const byte* signature, word32 sigSz,
                                      word32 signatureOID, Signer *ca,
                                      void* heap);
WOLFSSL_LOCAL int  ParseCRL(DecodedCRL*, const byte* buff, word32 sz, void* cm);
WOLFSSL_LOCAL void FreeDecodedCRL(DecodedCRL*);


#endif /* HAVE_CRL */


#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* !NO_ASN */


#if !defined(NO_ASN) || !defined(NO_PWDBASED)

#ifndef MAX_KEY_SIZE
    #define MAX_KEY_SIZE    64  /* MAX PKCS Key length */
#endif
#ifndef MAX_UNICODE_SZ
    #define MAX_UNICODE_SZ  256
#endif

enum PBESTypes {
    PBE_MD5_DES      = 0,
    PBE_SHA1_RC4_128 = 1,
    PBE_SHA1_DES     = 2,
    PBE_SHA1_DES3    = 3,
    PBE_AES256_CBC   = 4,
    PBE_AES128_CBC   = 5,

    PBE_SHA1_RC4_128_SUM = 657,
    PBE_SHA1_DES3_SUM    = 659,
    PBES2            = 13       /* algo ID */
};

enum PKCSTypes {
    PKCS5v2             =   6,     /* PKCS #5 v2.0 */
    PKCS12v1            =  12,     /* PKCS #12 */
    PKCS5               =   5,     /* PKCS oid tag */
    PKCS8v0             =   0,     /* default PKCS#8 version */
};

#endif /* !NO_ASN || !NO_PWDBASED */

#endif /* WOLF_CRYPT_ASN_H */
