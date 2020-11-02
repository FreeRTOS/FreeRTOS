/* pkcs12.c
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


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#if !defined(NO_ASN) && !defined(NO_PWDBASED) && defined(HAVE_PKCS12)

#include <wolfssl/wolfcrypt/asn.h>
#include <wolfssl/wolfcrypt/asn_public.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/hmac.h>
#include <wolfssl/wolfcrypt/logging.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif
#include <wolfssl/wolfcrypt/pkcs12.h>
#include <wolfssl/wolfcrypt/pwdbased.h>
#include <wolfssl/wolfcrypt/hash.h>


#define ERROR_OUT(err, eLabel) { ret = (err); goto eLabel; }

enum {
    WC_PKCS12_KeyBag = 667,
    WC_PKCS12_ShroudedKeyBag = 668,
    WC_PKCS12_CertBag = 669,
    WC_PKCS12_CertBag_Type1 = 675,
    WC_PKCS12_CrlBag = 670,
    WC_PKCS12_SecretBag = 671,
    WC_PKCS12_SafeContentsBag = 672,
    WC_PKCS12_DATA = 651,
    WC_PKCS12_ENCRYPTED_DATA = 656,

    WC_PKCS12_DATA_OBJ_SZ = 11,
};

static const byte WC_PKCS12_ENCRYPTED_OID[] =
                         {0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x07, 0x06};
static const byte WC_PKCS12_DATA_OID[] =
                         {0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x07, 0x01};
static const byte WC_PKCS12_CertBag_Type1_OID[] =
                   {0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x09, 0x16, 0x01};
static const byte WC_PKCS12_CertBag_OID[] =
             {0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x0c, 0x0a, 0x01, 0x03};
static const byte WC_PKCS12_KeyBag_OID[] =
             {0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x0c, 0x0a, 0x01, 0x01};
static const byte WC_PKCS12_ShroudedKeyBag_OID[] =
             {0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x0c, 0x0a, 0x01, 0x02};


typedef struct ContentInfo {
    byte* data;
    struct ContentInfo* next;
    word32 encC;  /* encryptedContent */
    word32 dataSz;
    int type; /* DATA / encrypted / enveloped */
} ContentInfo;


typedef struct AuthenticatedSafe {
    ContentInfo* CI;
    byte* data; /* T contents.... */
    word32 oid; /* encrypted or not */
    word32 numCI; /* number of Content Info structs */
    word32 dataSz;
} AuthenticatedSafe;


typedef struct MacData {
    byte* digest;
    byte* salt;
    word32 oid;
    word32 digestSz;
    word32 saltSz;
    int itt; /* number of iterations when creating HMAC key */
} MacData;


struct WC_PKCS12 {
    void* heap;
    AuthenticatedSafe* safe;
    MacData* signData;
    word32 oid; /* DATA / Enveloped DATA ... */
};


/* for friendlyName, localKeyId .... */
typedef struct WC_PKCS12_ATTRIBUTE {
    byte* data;
    word32 oid;
    word32 dataSz;
} WC_PKCS12_ATTRIBUTE;


WC_PKCS12* wc_PKCS12_new(void)
{
    WC_PKCS12* pkcs12 = (WC_PKCS12*)XMALLOC(sizeof(WC_PKCS12),
                                                      NULL, DYNAMIC_TYPE_PKCS);
    if (pkcs12 == NULL) {
        WOLFSSL_MSG("Memory issue when creating WC_PKCS12 struct");
        return NULL;
    }

    XMEMSET(pkcs12, 0, sizeof(WC_PKCS12));

    return pkcs12;
}


static void freeSafe(AuthenticatedSafe* safe, void* heap)
{
    int i;

    if (safe == NULL) {
        return;
    }

    /* free content info structs */
    for (i = safe->numCI; i > 0; i--) {
        ContentInfo* ci = safe->CI;
        safe->CI = ci->next;
        XFREE(ci, heap, DYNAMIC_TYPE_PKCS);
    }
    if (safe->data != NULL) {
        XFREE(safe->data, heap, DYNAMIC_TYPE_PKCS);
    }
    XFREE(safe, heap, DYNAMIC_TYPE_PKCS);

    (void)heap;
}


void wc_PKCS12_free(WC_PKCS12* pkcs12)
{
    void* heap;

    /* if null pointer is passed in do nothing */
    if (pkcs12 == NULL) {
        WOLFSSL_MSG("Trying to free null WC_PKCS12 object");
        return;
    }

    heap = pkcs12->heap;
    if (pkcs12->safe != NULL) {
    	freeSafe(pkcs12->safe, heap);
    }

    /* free mac data */
    if (pkcs12->signData != NULL) {
        if (pkcs12->signData->digest != NULL) {
            XFREE(pkcs12->signData->digest, heap, DYNAMIC_TYPE_DIGEST);
            pkcs12->signData->digest = NULL;
        }
        if (pkcs12->signData->salt != NULL) {
            XFREE(pkcs12->signData->salt, heap, DYNAMIC_TYPE_SALT);
            pkcs12->signData->salt = NULL;
        }
        XFREE(pkcs12->signData, heap, DYNAMIC_TYPE_PKCS);
        pkcs12->signData = NULL;
    }

    XFREE(pkcs12, NULL, DYNAMIC_TYPE_PKCS);
    pkcs12 = NULL;
}


/* return 0 on success */
static int GetSafeContent(WC_PKCS12* pkcs12, const byte* input,
                          word32* idx, int maxIdx)
{
    AuthenticatedSafe* safe;
    word32 oid;
    word32 localIdx = *idx;
    int ret;
    int size = 0;
    byte tag;

    safe = (AuthenticatedSafe*)XMALLOC(sizeof(AuthenticatedSafe), pkcs12->heap,
                                       DYNAMIC_TYPE_PKCS);
    if (safe == NULL) {
        return MEMORY_E;
    }
    XMEMSET(safe, 0, sizeof(AuthenticatedSafe));

    ret = GetObjectId(input, &localIdx, &oid, oidIgnoreType, maxIdx);
    if (ret < 0) {
        WOLFSSL_LEAVE("Get object id failed", ret);
        freeSafe(safe, pkcs12->heap);
        return ASN_PARSE_E;
    }

    safe->oid = oid;
    /* check tag, length */
    if (GetASNTag(input, &localIdx, &tag, maxIdx) < 0) {
        freeSafe(safe, pkcs12->heap);
        return ASN_PARSE_E;
    }

    if (tag != (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC)) {
        WOLFSSL_MSG("Unexpected tag in PKCS12 DER");
        freeSafe(safe, pkcs12->heap);
        return ASN_PARSE_E;
    }
    if ((ret = GetLength(input, &localIdx, &size, maxIdx)) <= 0) {
        freeSafe(safe, pkcs12->heap);
        return ASN_PARSE_E;
    }

    switch (oid) {
        case WC_PKCS12_ENCRYPTED_DATA:
            WOLFSSL_MSG("Found PKCS12 OBJECT: ENCRYPTED DATA\n");
            break;

        case WC_PKCS12_DATA:
            WOLFSSL_MSG("Found PKCS12 OBJECT: DATA");
            /* get octets holding contents */
            if (GetASNTag(input, &localIdx, &tag, maxIdx) < 0) {
                freeSafe(safe, pkcs12->heap);
                return ASN_PARSE_E;
            }

            if (tag != ASN_OCTET_STRING) {
                WOLFSSL_MSG("Wrong tag with content PKCS12 type DATA");
                freeSafe(safe, pkcs12->heap);
                return ASN_PARSE_E;
            }
            if ((ret = GetLength(input, &localIdx, &size, maxIdx)) <= 0) {
                freeSafe(safe, pkcs12->heap);
                return ASN_PARSE_E;
            }

            break;
    }

    safe->dataSz = size;
    safe->data = (byte*)XMALLOC(size, pkcs12->heap, DYNAMIC_TYPE_PKCS);
    if (safe->data == NULL) {
        freeSafe(safe, pkcs12->heap);
        return MEMORY_E;
    }
    XMEMCPY(safe->data, input + localIdx, size);
    *idx = localIdx;

    /* an instance of AuthenticatedSafe is created from
     * ContentInfo's strung together in a SEQUENCE. Here we iterate
     * through the ContentInfo's and add them to our
     * AuthenticatedSafe struct */
    localIdx = 0;
    input = safe->data;
    {
        int CISz;
        ret = GetSequence(input, &localIdx, &CISz, safe->dataSz);
        if (ret < 0) {
            freeSafe(safe, pkcs12->heap);
            return ASN_PARSE_E;
        }
        CISz += localIdx;
        while ((int)localIdx < CISz) {
            int curSz = 0;
            word32 curIdx;
            ContentInfo* ci = NULL;

        #ifdef WOLFSSL_DEBUG_PKCS12
            printf("\t\tlooking for Content Info.... ");
        #endif

            if ((ret = GetSequence(input, &localIdx, &curSz, safe->dataSz))
                                                                          < 0) {
                freeSafe(safe, pkcs12->heap);
                return ret;
            }

            if (curSz > CISz) {
                /* subset should not be larger than universe */
                freeSafe(safe, pkcs12->heap);
                return ASN_PARSE_E;
            }

            curIdx = localIdx;
            if ((ret = GetObjectId(input, &localIdx, &oid, oidIgnoreType,
                                                           safe->dataSz)) < 0) {
                WOLFSSL_LEAVE("Get object id failed", ret);
                freeSafe(safe, pkcs12->heap);
                return ret;
            }

            /* create new content info struct ... possible OID sanity check? */
            ci = (ContentInfo*)XMALLOC(sizeof(ContentInfo), pkcs12->heap,
                                       DYNAMIC_TYPE_PKCS);
            if (ci == NULL) {
                freeSafe(safe, pkcs12->heap);
                return MEMORY_E;
            }

            ci->type   = oid;
            ci->dataSz = curSz - (localIdx-curIdx);
            ci->data   = (byte*)input + localIdx;
            localIdx  += ci->dataSz;

        #ifdef WOLFSSL_DEBUG_PKCS12
            switch (oid) {
                case WC_PKCS12_ENCRYPTED_DATA:
                    printf("CONTENT INFO: ENCRYPTED DATA, size = %d\n", ci->dataSz);
                    break;

                case WC_PKCS12_DATA:
                    printf("CONTENT INFO: DATA, size = %d\n", ci->dataSz);
                    break;
                default:
                    printf("CONTENT INFO: UNKNOWN, size = %d\n", ci->dataSz);
            }
        #endif

            /* insert to head of list */
            ci->next = safe->CI;
            safe->CI = ci;
            safe->numCI += 1;
        }
    }

    pkcs12->safe = safe;
    *idx += localIdx;

    return ret;
}


/* parse optional mac data
 * return 0 on success */
static int GetSignData(WC_PKCS12* pkcs12, const byte* mem, word32* idx,
                       word32 totalSz)
{
    MacData* mac;
    word32 curIdx = *idx;
    word32 oid = 0;
    int size, ret;
    byte tag;

    /* Digest Info : Sequence
     *      DigestAlgorithmIdentifier
     *      Digest
     */
    if ((ret = GetSequence(mem, &curIdx, &size, totalSz)) <= 0) {
        WOLFSSL_MSG("Failed to get PKCS12 sequence");
        return ASN_PARSE_E;
    }

#ifdef WOLFSSL_DEBUG_PKCS12
    printf("\t\tSEQUENCE: DigestInfo size = %d\n", size);
#endif

    mac = (MacData*)XMALLOC(sizeof(MacData), pkcs12->heap, DYNAMIC_TYPE_PKCS);
    if (mac == NULL) {
        return MEMORY_E;
    }
    XMEMSET(mac, 0, sizeof(MacData));

    /* DigestAlgorithmIdentifier */
    if ((ret = GetAlgoId(mem, &curIdx, &oid, oidIgnoreType, totalSz)) < 0) {
        WOLFSSL_MSG("Failed to get PKCS12 sequence");
        XFREE(mac, pkcs12->heap, DYNAMIC_TYPE_PKCS);
        return ret;
    }
    mac->oid = oid;

#ifdef WOLFSSL_DEBUG_PKCS12
    printf("\t\tALGO ID = %d\n", oid);
#endif

    /* Digest: should be octet type holding digest */
    if (GetASNTag(mem, &curIdx, &tag, totalSz) < 0) {
        XFREE(mac, pkcs12->heap, DYNAMIC_TYPE_PKCS);
        return ASN_PARSE_E;
    }

    if (tag != ASN_OCTET_STRING) {
        WOLFSSL_MSG("Failed to get digest");
        XFREE(mac, pkcs12->heap, DYNAMIC_TYPE_PKCS);
        return ASN_PARSE_E;
    }

    if ((ret = GetLength(mem, &curIdx, &size, totalSz)) <= 0) {
        XFREE(mac, pkcs12->heap, DYNAMIC_TYPE_PKCS);
        return ASN_PARSE_E;
    }
    mac->digestSz = size;
    mac->digest = (byte*)XMALLOC(mac->digestSz, pkcs12->heap,
                                 DYNAMIC_TYPE_DIGEST);
    if (mac->digest == NULL || mac->digestSz + curIdx > totalSz) {
        ERROR_OUT(MEMORY_E, exit_gsd);
    }
    XMEMCPY(mac->digest, mem + curIdx, mac->digestSz);

#ifdef WOLFSSL_DEBUG_PKCS12
    {
        byte* p;
        for (printf("\t\tDigest = "), p = (byte*)mem+curIdx;
             p < (byte*)mem + curIdx + mac->digestSz;
             printf("%02X", *p), p++);
        printf(" : size = %d\n", mac->digestSz);
    }
#endif

    curIdx += mac->digestSz;

    /* get salt, should be octet string */
    if (GetASNTag(mem, &curIdx, &tag, totalSz) < 0) {
        ERROR_OUT(ASN_PARSE_E, exit_gsd);
    }

    if (tag != ASN_OCTET_STRING) {
        WOLFSSL_MSG("Failed to get salt");
        ERROR_OUT(ASN_PARSE_E, exit_gsd);
    }

    if ((ret = GetLength(mem, &curIdx, &size, totalSz)) < 0) {
        goto exit_gsd;
    }
    mac->saltSz = size;
    mac->salt = (byte*)XMALLOC(mac->saltSz, pkcs12->heap, DYNAMIC_TYPE_SALT);
    if (mac->salt == NULL || mac->saltSz + curIdx > totalSz) {
        ERROR_OUT(MEMORY_E, exit_gsd);
    }
    XMEMCPY(mac->salt, mem + curIdx, mac->saltSz);

#ifdef WOLFSSL_DEBUG_PKCS12
    {
        byte* p;
        for (printf("\t\tSalt = "), p = (byte*)mem + curIdx;
             p < (byte*)mem + curIdx + mac->saltSz;
             printf("%02X", *p), p++);
        printf(" : size = %d\n", mac->saltSz);
    }
#endif

    curIdx += mac->saltSz;

    /* check for MAC iterations, default to 1 */
    mac->itt = WC_PKCS12_MAC_DEFAULT;
    if (curIdx < totalSz) {
        int number = 0;
        if ((ret = GetShortInt(mem, &curIdx, &number, totalSz)) >= 0) {
            /* found a iteration value */
            mac->itt = number;
        }
    }

#ifdef WOLFSSL_DEBUG_PKCS12
    printf("\t\tITERATIONS : %d\n", mac->itt);
#endif

    *idx = curIdx;
    pkcs12->signData = mac;
    ret = 0; /* success */

exit_gsd:

    /* failure cleanup */
    if (ret != 0) {
        if (mac) {
            if (mac->digest)
                XFREE(mac->digest, pkcs12->heap, DYNAMIC_TYPE_DIGEST);
            XFREE(mac, pkcs12->heap, DYNAMIC_TYPE_PKCS);
        }
    }

    return ret;
}


/* expects PKCS12 signData to be set up with OID
 *
 * returns the size of mac created on success. A negative value will be returned
 *         in the case that an error happened.
 */
static int wc_PKCS12_create_mac(WC_PKCS12* pkcs12, byte* data, word32 dataSz,
                         const byte* psw, word32 pswSz, byte* out, word32 outSz)
{
    Hmac     hmac;
    MacData* mac;
    int ret, kLen;
    enum wc_HashType hashT;
    int idx = 0;
    int id  = 3; /* value from RFC 7292 indicating key is used for MAC */
    word32 i;
    byte unicodePasswd[MAX_UNICODE_SZ];
    byte key[MAX_KEY_SIZE];

    if (pkcs12 == NULL || pkcs12->signData == NULL || data == NULL ||
            out == NULL) {
        return BAD_FUNC_ARG;
    }

    mac = pkcs12->signData;

    /* unicode set up from asn.c */
    if ((pswSz * 2 + 2) > (int)sizeof(unicodePasswd)) {
        WOLFSSL_MSG("PKCS12 max unicode size too small");
        return UNICODE_SIZE_E;
    }

    for (i = 0; i < pswSz; i++) {
        unicodePasswd[idx++] = 0x00;
        unicodePasswd[idx++] = (byte)psw[i];
    }
    /* add trailing NULL */
    unicodePasswd[idx++] = 0x00;
    unicodePasswd[idx++] = 0x00;

    /* get hash type used and resulting size of HMAC key */
    hashT = wc_OidGetHash(mac->oid);
    if (hashT == WC_HASH_TYPE_NONE) {
        WOLFSSL_MSG("Unsupported hash used");
        return BAD_FUNC_ARG;
    }
    kLen = wc_HashGetDigestSize(hashT);

    /* check out buffer is large enough */
    if (kLen < 0 || outSz < (word32)kLen) {
        return BAD_FUNC_ARG;
    }

    /* idx contains size of unicodePasswd */
    if ((ret = wc_PKCS12_PBKDF_ex(key, unicodePasswd, idx, mac->salt,
              mac->saltSz, mac->itt, kLen, (int)hashT, id, pkcs12->heap)) < 0) {
        return ret;
    }

    /* now that key has been created use it to get HMAC hash on data */
    if ((ret = wc_HmacInit(&hmac, pkcs12->heap, INVALID_DEVID)) != 0) {
        return ret;
    }
    ret = wc_HmacSetKey(&hmac, (int)hashT, key, kLen);
    if (ret == 0)
        ret = wc_HmacUpdate(&hmac, data, dataSz);
    if (ret == 0)
        ret = wc_HmacFinal(&hmac, out);
    wc_HmacFree(&hmac);

    if (ret != 0)
        return ret;

    return kLen; /* same as digest size */
}


/* check mac on pkcs12, pkcs12->mac has been sanity checked before entering *
 * returns the result of comparison, success is 0 */
static int wc_PKCS12_verify(WC_PKCS12* pkcs12, byte* data, word32 dataSz,
                            const byte* psw, word32 pswSz)
{
    MacData* mac;
    int ret;
    byte digest[WC_MAX_DIGEST_SIZE];

    if (pkcs12 == NULL || pkcs12->signData == NULL || data == NULL) {
        return BAD_FUNC_ARG;
    }

    mac = pkcs12->signData;

#ifdef WOLFSSL_DEBUG_PKCS12
    printf("Verifying MAC with OID = %d\n", mac->oid);
#endif

    /* check if this builds digest size is too small */
    if (mac->digestSz > WC_MAX_DIGEST_SIZE) {
        WOLFSSL_MSG("PKCS12 max digest size too small");
        return BAD_FUNC_ARG;
    }

    if ((ret = wc_PKCS12_create_mac(pkcs12, data, dataSz, psw, pswSz,
            digest, WC_MAX_DIGEST_SIZE)) < 0) {
        return ret;
    }

#ifdef WOLFSSL_DEBUG_PKCS12
    {
        byte* p;
        for (printf("\t\tHash = "), p = (byte*)digest;
             p < (byte*)digest + mac->digestSz;
             printf("%02X", *p), p++);
        printf(" : size = %d\n", mac->digestSz);
    }
#endif

    return XMEMCMP(digest, mac->digest, mac->digestSz);
}


/* Convert DER format stored in der buffer to WC_PKCS12 struct
 * Puts the raw contents of Content Info into structure without completely
 * parsing or decoding.
 * der    : pointer to der buffer holding PKCS12
 * derSz  : size of der buffer
 * pkcs12 : non-null pkcs12 pointer
 * return 0 on success and negative on failure.
 */
int wc_d2i_PKCS12(const byte* der, word32 derSz, WC_PKCS12* pkcs12)
{
    word32 idx  = 0;
    word32 totalSz = 0;
    int ret;
    int size    = 0;
    int version = 0;

    WOLFSSL_ENTER("wolfSSL_d2i_PKCS12_bio");

    if (der == NULL || pkcs12 == NULL) {
        return BAD_FUNC_ARG;
    }

    totalSz = derSz;
    if ((ret = GetSequence(der, &idx, &size, totalSz)) <= 0) {
        WOLFSSL_MSG("Failed to get PKCS12 sequence");
        return ASN_PARSE_E;
    }

    /* get version */
    if ((ret = GetMyVersion(der, &idx, &version, totalSz)) < 0) {
        return ret;
    }

#ifdef WOLFSSL_DEBUG_PKCS12
    printf("\nBEGIN: PKCS12 size = %d\n", totalSz);
    printf("version = %d\n", version);
#endif

    if (version != WC_PKCS12_VERSION_DEFAULT) {
        WOLFSSL_MSG("PKCS12 unsupported version!");
        return ASN_VERSION_E;
    }

    if ((ret = GetSequence(der, &idx, &size, totalSz)) < 0) {
        return ret;
    }

#ifdef WOLFSSL_DEBUG_PKCS12
    printf("\tSEQUENCE: AuthenticatedSafe size = %d\n", size);
#endif

    if ((ret = GetSafeContent(pkcs12, der, &idx, size + idx)) < 0) {
        WOLFSSL_MSG("GetSafeContent error");
        return ret;
    }

    /* if more buffer left check for MAC data */
    if (idx < totalSz) {
        if ((ret = GetSequence(der, &idx, &size, totalSz)) < 0) {
            WOLFSSL_MSG("Ignoring unknown data at end of PKCS12 DER buffer");
        }
        else {
        #ifdef WOLFSSL_DEBUG_PKCS12
            printf("\tSEQUENCE: Signature size = %d\n", size);
        #endif

            if ((ret = GetSignData(pkcs12, der, &idx, totalSz)) < 0) {
                return ASN_PARSE_E;
            }
        }
    }

#ifdef WOLFSSL_DEBUG_PKCS12
    printf("END: PKCS12\n");
#endif

    return ret;
}

/* Convert WC_PKCS12 struct to allocated DER buffer.
 * pkcs12 : non-null pkcs12 pointer
 * der    : pointer-pointer to der buffer. If NULL space will be
 *          allocated for der, which must be freed by application.
 * derSz  : size of buffer passed in when der is not NULL. NULL arg disables
 *          sanity checks on buffer read/writes. Max size gets set to derSz when
 *          the "der" buffer passed in is NULL and LENGTH_ONLY_E is returned.
 * return size of DER on success and negative on failure.
 */
int wc_i2d_PKCS12(WC_PKCS12* pkcs12, byte** der, int* derSz)
{
    int ret = 0;
    word32 seqSz = 0, verSz = 0, totalSz = 0, idx = 0, sdBufSz = 0;
    byte *buf = NULL;
    byte ver[MAX_VERSION_SZ];
    byte seq[MAX_SEQ_SZ];
    byte *sdBuf = NULL;

    if ((pkcs12 == NULL) || (pkcs12->safe == NULL) ||
            (der == NULL && derSz == NULL)) {
        return BAD_FUNC_ARG;
    }

    /* Create the MAC portion */
    if (pkcs12->signData != NULL) {
        MacData *mac = (MacData*)pkcs12->signData;
        word32 innerSz = 0;
        word32 outerSz = 0;

        /* get exact size */
        {
            byte ASNLENGTH[MAX_LENGTH_SZ];
            byte ASNSHORT[MAX_SHORT_SZ];
            byte ASNALGO[MAX_ALGO_SZ];
            word32 tmpIdx = 0;

            /* algo id */
            innerSz += SetAlgoID(mac->oid, ASNALGO, oidHashType, 0);

            /* Octet string holding digest */
            innerSz += ASN_TAG_SZ;
            innerSz += SetLength(mac->digestSz, ASNLENGTH);
            innerSz += mac->digestSz;

            /* salt */
            outerSz += ASN_TAG_SZ;
            outerSz += SetLength(mac->saltSz, ASNLENGTH);
            outerSz += mac->saltSz;

            /* MAC iterations */
            outerSz += SetShortInt(ASNSHORT, &tmpIdx, mac->itt, MAX_SHORT_SZ);

            /* sequence of inner data */
            outerSz += SetSequence(innerSz, seq);
            outerSz += innerSz;
        }
        sdBufSz = outerSz + SetSequence(outerSz, seq);
        sdBuf = (byte*)XMALLOC(sdBufSz, pkcs12->heap, DYNAMIC_TYPE_PKCS);
        if (sdBuf == NULL) {
            ret = MEMORY_E;
        }

        if (ret == 0) {
            idx += SetSequence(outerSz, sdBuf);
            idx += SetSequence(innerSz, &sdBuf[idx]);

            /* Set Algorithm Identifier */
            {
                word32 algoIdSz;

                algoIdSz = SetAlgoID(mac->oid, &sdBuf[idx], oidHashType, 0);
                if (algoIdSz == 0) {
                    ret = ALGO_ID_E;
                }
                else {
                    idx += algoIdSz;
                }
            }
        }

        if (ret == 0) {


            /* Octet string holding digest */
            idx += SetOctetString(mac->digestSz, &sdBuf[idx]);
            XMEMCPY(&sdBuf[idx], mac->digest, mac->digestSz);
            idx += mac->digestSz;

            /* Set salt */
            idx += SetOctetString(mac->saltSz, &sdBuf[idx]);
            XMEMCPY(&sdBuf[idx], mac->salt, mac->saltSz);
            idx += mac->saltSz;

            /* MAC iterations */
            {
                int tmpSz;
                word32 tmpIdx = 0;
                byte ar[MAX_SHORT_SZ];
                tmpSz = SetShortInt(ar, &tmpIdx, mac->itt, MAX_SHORT_SZ);
                if (tmpSz < 0) {
                    ret = tmpSz;
                }
                else {
                    XMEMCPY(&sdBuf[idx], ar, tmpSz);
                }
            }
            totalSz += sdBufSz;
        }
    }

    /* Calculate size of der */
    if (ret == 0) {
        totalSz += pkcs12->safe->dataSz;

        totalSz += 4; /* Octet string */

        totalSz += 4; /* Element */

        totalSz += 2 + sizeof(WC_PKCS12_DATA_OID);

        totalSz += 4; /* Seq */

        ret = SetMyVersion(WC_PKCS12_VERSION_DEFAULT, ver, FALSE);
        if (ret > 0) {
            verSz = (word32)ret;
            ret   = 0; /* value larger than 0 is success */
            totalSz += verSz;

            seqSz = SetSequence(totalSz, seq);
            totalSz += seqSz;

            /* check if getting length only */
            if (der == NULL && derSz != NULL) {
                *derSz = totalSz;
                XFREE(sdBuf, pkcs12->heap, DYNAMIC_TYPE_PKCS);
                return LENGTH_ONLY_E;
            }

            if (*der == NULL) {
                /* Allocate if requested */
                buf = (byte*)XMALLOC(totalSz, NULL, DYNAMIC_TYPE_PKCS);
            }
            else {
                buf = *der;

                /* sanity check on buffer size if passed in */
                if (derSz != NULL) {
                    if (*derSz < (int)totalSz) {
                        WOLFSSL_MSG("Buffer passed in is too small");
                        ret = BUFFER_E;
                    }
                }
            }
        }
    }

    if (buf == NULL) {
        ret = MEMORY_E;
    }

    if (ret == 0) {
        idx = 0;

        /* Copy parts to buf */
        XMEMCPY(&buf[idx], seq, seqSz);
        idx += seqSz;

        XMEMCPY(&buf[idx], ver, verSz);
        idx += verSz;

        seqSz = SetSequence(totalSz - sdBufSz - idx - 4, seq);
        XMEMCPY(&buf[idx], seq, seqSz);
        idx += seqSz;

        /* OID */
        idx += SetObjectId(sizeof(WC_PKCS12_DATA_OID), &buf[idx]);
        XMEMCPY(&buf[idx], WC_PKCS12_DATA_OID, sizeof(WC_PKCS12_DATA_OID));
        idx += sizeof(WC_PKCS12_DATA_OID);

        /* Element */
        buf[idx++] = ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC;
        idx += SetLength(totalSz - sdBufSz - idx - 3, &buf[idx]);

        /* Octet string */
        idx += SetOctetString(totalSz - sdBufSz - idx - 4, &buf[idx]);

        XMEMCPY(&buf[idx], pkcs12->safe->data, pkcs12->safe->dataSz);
        idx += pkcs12->safe->dataSz;

        if (pkcs12->signData != NULL) {
            XMEMCPY(&buf[idx], sdBuf, sdBufSz);
        }

        if (*der == NULL) {
            /* Point to start of data allocated for DER */
            *der = buf;
        }
        else {
            /* Increment pointer to byte past DER */
            *der = &buf[totalSz];
        }

        /* Return size of der */
        ret = totalSz;
    }

    XFREE(sdBuf, pkcs12->heap, DYNAMIC_TYPE_PKCS);
    /* Allocation of buf was the last time ret could be a failure,
     * so no need to free here */

    return ret;
}


/* helper function to free WC_DerCertList */
void wc_FreeCertList(WC_DerCertList* list, void* heap)
{
    WC_DerCertList* current = list;
    WC_DerCertList* next;

    if (list == NULL) {
        return;
    }

    while (current != NULL) {
        next = current->next;
        if (current->buffer != NULL) {
            XFREE(current->buffer, heap, DYNAMIC_TYPE_PKCS);
        }
        XFREE(current, heap, DYNAMIC_TYPE_PKCS);
        current = next;
    }

    (void)heap;
}

static void freeDecCertList(WC_DerCertList** list, byte** pkey, word32* pkeySz,
    byte** cert, word32* certSz, void* heap)
{
    WC_DerCertList* current  = *list;
    WC_DerCertList* previous = NULL;
    DecodedCert DeCert;

    while (current != NULL) {

        InitDecodedCert(&DeCert, current->buffer, current->bufferSz, heap);
        if (ParseCertRelative(&DeCert, CERT_TYPE, NO_VERIFY, NULL) == 0) {
            if (wc_CheckPrivateKey(*pkey, *pkeySz, &DeCert) == 1) {
                WOLFSSL_MSG("Key Pair found");
                *cert = current->buffer;
                *certSz = current->bufferSz;

                if (previous == NULL) {
                    *list = current->next;
                }
                else {
                    previous->next = current->next;
                }
                FreeDecodedCert(&DeCert);
                XFREE(current, heap, DYNAMIC_TYPE_PKCS);
                break;
            }
        }
        FreeDecodedCert(&DeCert);

        previous = current;
        current  = current->next;
    }
}


/* return 0 on success and negative on failure.
 * By side effect returns private key, cert, and optionally ca.
 * Parses and decodes the parts of PKCS12
 *
 * NOTE: can parse with USER RSA enabled but may return cert that is not the
 *       pair for the key when using RSA key pairs.
 *
 * pkcs12 : non-null WC_PKCS12 struct
 * psw    : password to use for PKCS12 decode
 * pkey   : Private key returned
 * cert   : x509 cert returned
 * ca     : optional ca returned
 */
int wc_PKCS12_parse(WC_PKCS12* pkcs12, const char* psw,
        byte** pkey, word32* pkeySz, byte** cert, word32* certSz,
        WC_DerCertList** ca)
{
    ContentInfo* ci       = NULL;
    WC_DerCertList* certList = NULL;
    WC_DerCertList* tailList = NULL;
    byte* buf             = NULL;
    word32 i, oid;
    int ret, pswSz;
    word32 algId;

    WOLFSSL_ENTER("wc_PKCS12_parse");

    if (pkcs12 == NULL || psw == NULL || cert == NULL || certSz == NULL ||
        pkey == NULL   || pkeySz == NULL) {
        return BAD_FUNC_ARG;
    }

    pswSz = (int)XSTRLEN(psw);
    *cert = NULL;
    *pkey = NULL;
    if (ca != NULL)
        *ca = NULL;

    /* if there is sign data then verify the MAC */
    if (pkcs12->signData != NULL ) {
        if ((ret = wc_PKCS12_verify(pkcs12, pkcs12->safe->data,
                               pkcs12->safe->dataSz, (byte*)psw, pswSz)) != 0) {
            WOLFSSL_MSG("PKCS12 Bad MAC on verify");
            WOLFSSL_LEAVE("wc_PKCS12_parse verify ", ret);
            return MAC_CMP_FAILED_E;
        }
    }

    if (pkcs12->safe == NULL) {
        WOLFSSL_MSG("No PKCS12 safes to parse");
        return BAD_FUNC_ARG;
    }

    /* Decode content infos */
    ci = pkcs12->safe->CI;
    for (i = 0; i < pkcs12->safe->numCI; i++) {
        byte*  data;
        word32 idx = 0;
        int    size, totalSz;
        byte   tag;

        if (ci->type == WC_PKCS12_ENCRYPTED_DATA) {
            int number;

            WOLFSSL_MSG("Decrypting PKCS12 Content Info Container");
            data = ci->data;
            if (GetASNTag(data, &idx, &tag, ci->dataSz) < 0) {
                ERROR_OUT(ASN_PARSE_E, exit_pk12par);
            }

            if (tag != (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC)) {
                ERROR_OUT(ASN_PARSE_E, exit_pk12par);
            }
            if ((ret = GetLength(data, &idx, &size, ci->dataSz)) < 0) {
                goto exit_pk12par;
            }

            if ((ret = GetSequence(data, &idx, &size, ci->dataSz)) < 0) {
                goto exit_pk12par;
            }

            if ((ret = GetShortInt(data, &idx, &number, ci->dataSz)) < 0) {
                goto exit_pk12par;
            }

            if (number != 0) {
                WOLFSSL_MSG("Expecting 0 for Integer with Encrypted PKCS12");
            }

            if ((ret = GetSequence(data, &idx, &size, ci->dataSz)) < 0) {
                goto exit_pk12par;
            }

            ret = GetObjectId(data, &idx, &oid, oidIgnoreType, ci->dataSz);
            if (ret < 0 || oid != WC_PKCS12_DATA) {
                WOLFSSL_MSG("Not PKCS12 DATA object or get object parse error");
                ERROR_OUT(ASN_PARSE_E, exit_pk12par);
            }

            /* decrypted content overwrites input buffer */
            size = ci->dataSz - idx;
            buf = (byte*)XMALLOC(size, pkcs12->heap, DYNAMIC_TYPE_PKCS);
            if (buf == NULL) {
                ERROR_OUT(MEMORY_E, exit_pk12par);
            }
            XMEMCPY(buf, data + idx, size);

            if ((ret = DecryptContent(buf, size, psw, pswSz)) < 0) {
                WOLFSSL_MSG("Decryption failed, algorithm not compiled in?");
                goto exit_pk12par;
            }

            data = buf;
            idx = 0;

        #ifdef WOLFSSL_DEBUG_PKCS12
            {
                byte* p;
                for (printf("\tData = "), p = (byte*)buf;
                    p < (byte*)buf + size;
                    printf("%02X", *p), p++);
                printf("\n");
            }
        #endif
        }
        else { /* type DATA */
            WOLFSSL_MSG("Parsing PKCS12 DATA Content Info Container");
            data = ci->data;
            if (GetASNTag(data, &idx, &tag, ci->dataSz) < 0) {
                ERROR_OUT(ASN_PARSE_E, exit_pk12par);
            }

            if (tag != (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC)) {
                ERROR_OUT(ASN_PARSE_E, exit_pk12par);
            }
            if ((ret = GetLength(data, &idx, &size, ci->dataSz)) <= 0) {
                ERROR_OUT(ASN_PARSE_E, exit_pk12par);
            }

            if (GetASNTag(data, &idx, &tag, ci->dataSz) < 0) {
                ERROR_OUT(ASN_PARSE_E, exit_pk12par);
            }
            if (tag != ASN_OCTET_STRING) {
                ERROR_OUT(ASN_PARSE_E, exit_pk12par);
            }
            if ((ret = GetLength(data, &idx, &size, ci->dataSz)) < 0) {
                goto exit_pk12par;
            }

        }

        /* parse through bags in ContentInfo */
        if ((ret = GetSequence(data, &idx, &totalSz, ci->dataSz)) < 0) {
            goto exit_pk12par;
        }
        totalSz += idx;

        while ((int)idx < totalSz) {
            int bagSz;
            if ((ret = GetSequence(data, &idx, &bagSz, ci->dataSz)) < 0) {
                goto exit_pk12par;
            }
            bagSz += idx;

            if ((ret = GetObjectId(data, &idx, &oid, oidIgnoreType,
                                                             ci->dataSz)) < 0) {
                goto exit_pk12par;
            }

            switch (oid) {
                case WC_PKCS12_KeyBag: /* 667 */
                    WOLFSSL_MSG("PKCS12 Key Bag found");
                    if (GetASNTag(data, &idx, &tag, ci->dataSz) < 0) {
                        ERROR_OUT(ASN_PARSE_E, exit_pk12par);
                    }
                    if (tag != (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC)) {
                        ERROR_OUT(ASN_PARSE_E, exit_pk12par);
                    }
                    if ((ret = GetLength(data, &idx, &size, ci->dataSz)) <= 0) {
                        if (ret == 0)
                            ret = ASN_PARSE_E;
                        goto exit_pk12par;
                    }
                    if (*pkey == NULL) {
                        *pkey = (byte*)XMALLOC(size, pkcs12->heap,
                                                       DYNAMIC_TYPE_PUBLIC_KEY);
                        if (*pkey == NULL) {
                            ERROR_OUT(MEMORY_E, exit_pk12par);
                        }
                        XMEMCPY(*pkey, data + idx, size);
                        *pkeySz =  ToTraditional_ex(*pkey, size, &algId);
                    }

                #ifdef WOLFSSL_DEBUG_PKCS12
                    {
                        byte* p;
                        for (printf("\tKey = "), p = (byte*)*pkey;
                            p < (byte*)*pkey + size;
                            printf("%02X", *p), p++);
                        printf("\n");
                    }
                #endif
                    idx += size;
                    break;

                case WC_PKCS12_ShroudedKeyBag: /* 668 */
                    {
                        byte* k;

                        WOLFSSL_MSG("PKCS12 Shrouded Key Bag found");
                        if (GetASNTag(data, &idx, &tag, ci->dataSz) < 0) {
                            ERROR_OUT(ASN_PARSE_E, exit_pk12par);
                        }
                        if (tag != (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC)) {
                            ERROR_OUT(ASN_PARSE_E, exit_pk12par);
                        }
                        if ((ret = GetLength(data, &idx, &size,
                                                             ci->dataSz)) < 0) {
                            goto exit_pk12par;
                        }

                        k = (byte*)XMALLOC(size, pkcs12->heap,
                                                       DYNAMIC_TYPE_PUBLIC_KEY);
                        if (k == NULL) {
                            ERROR_OUT(MEMORY_E, exit_pk12par);
                        }
                        XMEMCPY(k, data + idx, size);

                        /* overwrites input, be warned */
                        if ((ret = ToTraditionalEnc(k, size, psw, pswSz,
                                                                 &algId)) < 0) {
                            XFREE(k, pkcs12->heap, DYNAMIC_TYPE_PUBLIC_KEY);
                            goto exit_pk12par;
                        }

                        if (ret < size) {
                            /* shrink key buffer */
                            byte* tmp = (byte*)XMALLOC(ret, pkcs12->heap,
                                                 DYNAMIC_TYPE_PUBLIC_KEY);
                            if (tmp == NULL) {
                                XFREE(k, pkcs12->heap, DYNAMIC_TYPE_PUBLIC_KEY);
                                ERROR_OUT(MEMORY_E, exit_pk12par);
                            }
                            XMEMCPY(tmp, k, ret);
                            XFREE(k, pkcs12->heap, DYNAMIC_TYPE_PUBLIC_KEY);
                            k = tmp;
                        }
                        size = ret;

                        if (*pkey == NULL) {
                            *pkey = k;
                            *pkeySz = size;
                        }
                        else { /* only expecting one key */
                            XFREE(k, pkcs12->heap, DYNAMIC_TYPE_PUBLIC_KEY);
                        }
                        idx += size;

                    #ifdef WOLFSSL_DEBUG_PKCS12
                        {
                            byte* p;
                            for (printf("\tKey = "), p = (byte*)k;
                                p < (byte*)k + ret;
                                printf("%02X", *p), p++);
                            printf("\n");
                        }
                    #endif
                    }
                    break;

                case WC_PKCS12_CertBag: /* 669 */
                {
                    WC_DerCertList* node;
                    WOLFSSL_MSG("PKCS12 Cert Bag found");
                    if (GetASNTag(data, &idx, &tag, ci->dataSz) < 0) {
                        ERROR_OUT(ASN_PARSE_E, exit_pk12par);
                    }
                    if (tag != (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC)) {
                        ERROR_OUT(ASN_PARSE_E, exit_pk12par);
                    }
                    if ((ret = GetLength(data, &idx, &size, ci->dataSz)) < 0) {
                        goto exit_pk12par;
                    }

                    /* get cert bag type */
                    if ((ret = GetSequence(data, &idx, &size, ci->dataSz)) <0) {
                        goto exit_pk12par;
                    }

                    if ((ret = GetObjectId(data, &idx, &oid, oidIgnoreType,
                                                             ci->dataSz)) < 0) {
                        goto exit_pk12par;
                    }

                    switch (oid) {
                        case WC_PKCS12_CertBag_Type1:  /* 675 */
                            /* type 1 */
                            WOLFSSL_MSG("PKCS12 cert bag type 1");
                            if (GetASNTag(data, &idx, &tag, ci->dataSz) < 0) {
                                ERROR_OUT(ASN_PARSE_E, exit_pk12par);
                            }
                            if (tag != (ASN_CONSTRUCTED |
                                        ASN_CONTEXT_SPECIFIC)) {
                                ERROR_OUT(ASN_PARSE_E, exit_pk12par);
                            }
                            if ((ret = GetLength(data, &idx, &size, ci->dataSz))
                                                                         <= 0) {
                                if (ret == 0)
                                    ret = ASN_PARSE_E;
                                goto exit_pk12par;
                            }
                            if (GetASNTag(data, &idx, &tag, ci->dataSz) < 0) {
                                ERROR_OUT(ASN_PARSE_E, exit_pk12par);
                            }
                            if (tag != ASN_OCTET_STRING) {
                                ERROR_OUT(ASN_PARSE_E, exit_pk12par);

                            }
                            if ((ret = GetLength(data, &idx, &size, ci->dataSz))
                                                                          < 0) {
                                goto exit_pk12par;
                            }
                            break;
                       default:
                            WOLFSSL_MSG("Unknown PKCS12 cert bag type");
                    }

                    if (size + idx > (word32)bagSz) {
                        ERROR_OUT(ASN_PARSE_E, exit_pk12par);
                    }

                    /* list to hold all certs found */
                    node = (WC_DerCertList*)XMALLOC(sizeof(WC_DerCertList),
                                               pkcs12->heap, DYNAMIC_TYPE_PKCS);
                    if (node == NULL) {
                        ERROR_OUT(MEMORY_E, exit_pk12par);
                    }
                    XMEMSET(node, 0, sizeof(WC_DerCertList));

                    node->buffer = (byte*)XMALLOC(size, pkcs12->heap,
                                                             DYNAMIC_TYPE_PKCS);
                    if (node->buffer == NULL) {
                        XFREE(node, pkcs12->heap, DYNAMIC_TYPE_PKCS);
                        ERROR_OUT(MEMORY_E, exit_pk12par);
                    }
                    XMEMCPY(node->buffer, data + idx, size);
                    node->bufferSz = size;

                    /* put the new node into the list */
                    if (certList != NULL) {
                        WOLFSSL_MSG("Pushing new cert onto queue");
                        tailList->next = node;
                        tailList = node;
                    }
                    else {
                        certList = node;
                        tailList = node;
                    }

                    /* on to next */
                    idx += size;
                }
                    break;

                case WC_PKCS12_CrlBag: /* 670 */
                    WOLFSSL_MSG("PKCS12 CRL BAG not yet supported");
                    break;

                case WC_PKCS12_SecretBag: /* 671 */
                    WOLFSSL_MSG("PKCS12 Secret BAG not yet supported");
                    break;

                case WC_PKCS12_SafeContentsBag: /* 672 */
                    WOLFSSL_MSG("PKCS12 Safe Contents BAG not yet supported");
                    break;

                default:
                    WOLFSSL_MSG("Unknown PKCS12 BAG type found");
            }

            /* Attribute, unknown bag or unsupported */
            if ((int)idx < bagSz) {
                idx = bagSz; /* skip for now */
            }
        }

        /* free temporary buffer */
        if (buf != NULL) {
            XFREE(buf, pkcs12->heap, DYNAMIC_TYPE_PKCS);
            buf = NULL;
        }

        ci = ci->next;
        WOLFSSL_MSG("Done Parsing PKCS12 Content Info Container");
    }

    /* check if key pair, remove from list */
    if (*pkey != NULL) {
        freeDecCertList(&certList, pkey, pkeySz, cert, certSz, pkcs12->heap);
    }

    /* if ca arg provided return certList, otherwise free it */
    if (ca != NULL) {
        *ca = certList;
    }
    else {
        /* free list, not wanted */
        wc_FreeCertList(certList, pkcs12->heap);
    }
    (void)tailList; /* not used */

    ret = 0; /* success */

exit_pk12par:

    if (ret != 0) {
        /* failure cleanup */
        if (*pkey) {
            XFREE(*pkey, pkcs12->heap, DYNAMIC_TYPE_PUBLIC_KEY);
            *pkey = NULL;
        }
        if (buf) {
            XFREE(buf, pkcs12->heap, DYNAMIC_TYPE_PKCS);
            buf = NULL;
        }

        wc_FreeCertList(certList, pkcs12->heap);
    }

    return ret;
}


/* Helper function to shroud keys.
 *
 * pkcs12 structure to use with shrouding key
 * rng    random number generator used
 * out    buffer to hold results
 * outSz  size of out buffer
 * key    key that is going to be shrouded
 * keySz  size of key buffer
 * vAlgo  algorithm version
 * pass   password to use
 * passSz size of pass buffer
 * itt    number of iterations
 *
 * returns the size of the shrouded key on success
 */
static int wc_PKCS12_shroud_key(WC_PKCS12* pkcs12, WC_RNG* rng,
        byte* out, word32* outSz, byte* key, word32 keySz, int vAlgo,
        const char* pass, int passSz, int itt)
{
    void* heap;
    word32 tmpIdx = 0;
    int vPKCS     = 1; /* PKCS#12 default set to 1 */
    word32 sz;
    word32 totalSz = 0;
    int ret;


    if (outSz == NULL || pkcs12 == NULL || rng == NULL || key == NULL ||
            pass == NULL) {
        return BAD_FUNC_ARG;
    }

    heap = wc_PKCS12_GetHeap(pkcs12);

    /* check if trying to get size */
    if (out != NULL) {
        tmpIdx += MAX_LENGTH_SZ + 1; /* save room for length and tag (+1) */
        sz = *outSz - tmpIdx;
    }

    /* case of no encryption */
    if (vAlgo < 0) {
        const byte* curveOID = NULL;
        word32 oidSz = 0;
        int algoID;

        WOLFSSL_MSG("creating PKCS12 Key Bag");

        /* check key type and get OID if ECC */
        if ((ret = wc_GetKeyOID(key, keySz, &curveOID, &oidSz, &algoID, heap))
                < 0) {
            return ret;
        }

        /* PKCS#8 wrapping around key */
        ret = wc_CreatePKCS8Key(out + tmpIdx, &sz, key, keySz, algoID,
                curveOID, oidSz);
    }
    else {
        WOLFSSL_MSG("creating PKCS12 Shrouded Key Bag");

        if (vAlgo == PBE_SHA1_DES) {
            vPKCS = PKCS5;
            vAlgo = 10;
        }

        ret = UnTraditionalEnc(key, keySz, out + tmpIdx, &sz, pass, passSz,
                vPKCS, vAlgo, NULL, 0, itt, rng, heap);
    }
    if (ret == LENGTH_ONLY_E) {
        *outSz =  sz + MAX_LENGTH_SZ + 1;
        return LENGTH_ONLY_E;
    }
    if (ret < 0) {
        return ret;
    }

    totalSz += ret;

    /* out should not be null at this point but check before writing */
    if (out == NULL) {
        return BAD_FUNC_ARG;
    }

    /* rewind index and set tag and length */
    tmpIdx -= MAX_LENGTH_SZ + 1;
    sz = SetExplicit(0, ret, out + tmpIdx);
    tmpIdx += sz; totalSz += sz;
    XMEMMOVE(out + tmpIdx, out + MAX_LENGTH_SZ + 1, ret);

    return totalSz;
}


/* Helper function to create key bag.
 *
 * pkcs12 structure to use with key bag
 * rng    random number generator used
 * out    buffer to hold results
 * outSz  size of out buffer
 * key    key that is going into key bag
 * keySz  size of key buffer
 * algo   algorithm version
 * iter   number of iterations
 * pass   password to use
 * passSz size of pass buffer
 *
 * returns the size of the key bag on success
 */
static int wc_PKCS12_create_key_bag(WC_PKCS12* pkcs12, WC_RNG* rng,
        byte* out, word32* outSz, byte* key, word32 keySz, int algo, int iter,
        char* pass, int passSz)
{
    void* heap;
    byte* tmp;
    word32 length  = 0;
    word32 idx     = 0;
    word32 totalSz = 0;
    word32 sz;
    word32 i;
    word32 tmpSz;
    int ret;

    /* get max size for shrouded key */
    ret =  wc_PKCS12_shroud_key(pkcs12, rng, NULL, &length, key, keySz,
            algo, pass, passSz, iter);
    if (ret != LENGTH_ONLY_E && ret < 0) {
        return ret;
    }

    if (out == NULL) {
        *outSz = MAX_SEQ_SZ + WC_PKCS12_DATA_OBJ_SZ + 1 + MAX_LENGTH_SZ +
            length;
        return LENGTH_ONLY_E;
    }

    heap = wc_PKCS12_GetHeap(pkcs12);

    /* leave room for sequence */
    idx += MAX_SEQ_SZ;

    if (algo < 0) { /* not encrypted */
        out[idx++] = ASN_OBJECT_ID; totalSz++;
        sz = SetLength(sizeof(WC_PKCS12_KeyBag_OID), out + idx);
        idx += sz; totalSz += sz;
        for (i = 0; i < sizeof(WC_PKCS12_KeyBag_OID); i++) {
            out[idx++] = WC_PKCS12_KeyBag_OID[i]; totalSz++;
        }
    }
    else { /* encrypted */
        out[idx++] = ASN_OBJECT_ID; totalSz++;
        sz = SetLength(sizeof(WC_PKCS12_ShroudedKeyBag_OID), out + idx);
        idx += sz; totalSz += sz;
        for (i = 0; i < sizeof(WC_PKCS12_ShroudedKeyBag_OID); i++) {
            out[idx++] = WC_PKCS12_ShroudedKeyBag_OID[i]; totalSz++;
        }
    }

    /* shroud key */
    tmp = (byte*)XMALLOC(length, heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (tmp == NULL) {
        return MEMORY_E;
    }

    ret =  wc_PKCS12_shroud_key(pkcs12, rng, tmp, &length, key, keySz,
            algo, pass, passSz, iter);
    if (ret < 0) {
        XFREE(tmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
        return ret;
    }
    length = ret;
    XMEMCPY(out + idx, tmp, length);
    XFREE(tmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
    totalSz += length;

    /* set beginning sequence */
    tmpSz = SetSequence(totalSz, out);
    XMEMMOVE(out + tmpSz, out + MAX_SEQ_SZ, totalSz);

    (void)heap;
    return totalSz + tmpSz;
}


/* Helper function to create cert bag.
 *
 * pkcs12 structure to use with cert bag
 * out    buffer to hold results
 * outSz  size of out buffer
 * cert   cert that is going into cert bag
 * certSz size of cert buffer
 *
 * returns the size of the cert bag on success
 */
static int wc_PKCS12_create_cert_bag(WC_PKCS12* pkcs12,
        byte* out, word32* outSz, byte* cert, word32 certSz)
{
    word32 length = 0;
    word32 idx = 0;
    word32 totalSz = 0;
    word32 sz;
    int WC_CERTBAG_OBJECT_ID  = 13;
    int WC_CERTBAG1_OBJECT_ID = 12;
    word32 i;
    word32 tmpSz;

    if (out == NULL) {
        *outSz = MAX_SEQ_SZ + WC_CERTBAG_OBJECT_ID + 1 + MAX_LENGTH_SZ +
            MAX_SEQ_SZ + WC_CERTBAG1_OBJECT_ID + 1 + MAX_LENGTH_SZ + 1 +
            MAX_LENGTH_SZ + certSz;
        return LENGTH_ONLY_E;
    }

    /* check buffer size able to handle max size */
    if (*outSz < (MAX_SEQ_SZ + WC_CERTBAG_OBJECT_ID + 1 + MAX_LENGTH_SZ +
            MAX_SEQ_SZ + WC_CERTBAG1_OBJECT_ID + 1 + MAX_LENGTH_SZ + 1 +
            MAX_LENGTH_SZ + certSz)) {
        return BUFFER_E;
    }

    /* save room for sequence */
    idx += MAX_SEQ_SZ;

    /* objectId WC_PKCS12_CertBag */
    out[idx++] = ASN_OBJECT_ID; totalSz++;
    sz = SetLength(sizeof(WC_PKCS12_CertBag_OID), out + idx);
    idx += sz; totalSz += sz;
    for (i = 0; i < sizeof(WC_PKCS12_CertBag_OID); i++) {
        out[idx++] = WC_PKCS12_CertBag_OID[i]; totalSz++;
    }

    /**** Cert Bag type 1 ****/
    out[idx++] = (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC); totalSz++;

    /* save room for length and sequence */
    idx += MAX_LENGTH_SZ;
    idx += MAX_SEQ_SZ;

    /* object id WC_PKCS12_CertBag_Type1 */
    out[idx++] = ASN_OBJECT_ID; length++;
    sz = SetLength(sizeof(WC_PKCS12_CertBag_Type1_OID), out + idx);
    idx += sz; length += sz;
    for (i = 0; i < sizeof(WC_PKCS12_CertBag_Type1_OID); i++) {
        out[idx++] = WC_PKCS12_CertBag_Type1_OID[i]; length++;
    }

    out[idx++] = (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC); length++;
    sz = 0;
    idx += MAX_LENGTH_SZ; /* save room for length */

    /* place the cert in the buffer */
    out[idx++] = ASN_OCTET_STRING; sz++;
    tmpSz = SetLength(certSz, out + idx);
    idx += tmpSz; sz += tmpSz;
    XMEMCPY(out + idx, cert, certSz);
    idx += certSz; sz += certSz;

    /* rewind idx and place length */
    idx -= (sz + MAX_LENGTH_SZ);
    tmpSz = SetLength(sz, out + idx);
    XMEMMOVE(out + idx + tmpSz, out + idx + MAX_LENGTH_SZ, sz);
    idx += tmpSz + sz; length += tmpSz + sz;

    /* rewind idx and set sequence */
    idx -= (length + MAX_SEQ_SZ);
    tmpSz = SetSequence(length, out + idx);
    XMEMMOVE(out + idx + tmpSz, out + idx + MAX_SEQ_SZ, length);
    length += tmpSz;

    /* place final length */
    idx -= MAX_LENGTH_SZ;
    tmpSz = SetLength(length, out + idx);
    XMEMMOVE(out + idx + tmpSz, out + idx + MAX_LENGTH_SZ, length);
    length += tmpSz;

    /* place final sequence */
    totalSz += length;
    tmpSz = SetSequence(totalSz, out);
    XMEMMOVE(out + tmpSz, out + MAX_SEQ_SZ, totalSz);

    (void)pkcs12;

    return totalSz + tmpSz;
}


/* Helper function to encrypt content.
 *
 * pkcs12    structure to use with key bag
 * rng       random number generator used
 * out       buffer to hold results
 * outSz     size of out buffer
 * content   content to encrypt
 * contentSz size of content buffer
 * vAlgo     algorithm version
 * pass      password to use
 * passSz    size of pass buffer
 * iter      number of iterations
 * type      content type i.e WC_PKCS12_ENCRYPTED_DATA or WC_PKCS12_DATA
 *
 * returns the size of result on success
 */
static int wc_PKCS12_encrypt_content(WC_PKCS12* pkcs12, WC_RNG* rng,
        byte* out, word32* outSz, byte* content, word32 contentSz, int vAlgo,
        const char* pass, int passSz, int iter, int type)
{
    void* heap;
    int vPKCS     = 1; /* PKCS#12 is always set to 1 */
    int ret;
    byte*  tmp;
    word32 idx = 0;
    word32 totalSz = 0;
    word32 length = 0;
    word32 tmpSz;
    word32 encSz;

    byte seq[MAX_SEQ_SZ];

    WOLFSSL_MSG("encrypting PKCS12 content");

    heap = wc_PKCS12_GetHeap(pkcs12);

    /* ENCRYPTED DATA
     * ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC
     * length
     * sequence
     * short int
     * sequence
     * get object id */
    if (type == WC_PKCS12_ENCRYPTED_DATA) {
        word32 outerSz = 0;

        encSz = contentSz;
        if ((ret = EncryptContent(NULL, contentSz, NULL, &encSz,
                   pass, passSz, vPKCS, vAlgo, NULL, 0, iter, rng, heap)) < 0) {
            if (ret != LENGTH_ONLY_E) {
                return ret;
            }
        }

        /* calculate size */
        totalSz  = SetObjectId(sizeof(WC_PKCS12_ENCRYPTED_OID), seq);
        totalSz += sizeof(WC_PKCS12_ENCRYPTED_OID);
        totalSz += ASN_TAG_SZ;

        length  = SetMyVersion(0, seq, 0);
        tmpSz   = SetObjectId(sizeof(WC_PKCS12_DATA_OID), seq);
        tmpSz  += sizeof(WC_PKCS12_DATA_OID);
        tmpSz  += encSz;
        length += SetSequence(tmpSz, seq) + tmpSz;
        outerSz = SetSequence(length, seq) + length;

        totalSz += SetLength(outerSz, seq) + outerSz;
        if (out == NULL) {
            *outSz = totalSz + SetSequence(totalSz, seq);
            return LENGTH_ONLY_E;
        }

        if (*outSz < totalSz + SetSequence(totalSz, seq)) {
            return BUFFER_E;
        }

        idx = 0;
        idx += SetSequence(totalSz, out + idx);
        idx += SetObjectId(sizeof(WC_PKCS12_ENCRYPTED_OID), out + idx);
        if (idx + sizeof(WC_PKCS12_ENCRYPTED_OID) > *outSz){
            return BUFFER_E;
        }
        XMEMCPY(out + idx, WC_PKCS12_ENCRYPTED_OID,
                sizeof(WC_PKCS12_ENCRYPTED_OID));
        idx += sizeof(WC_PKCS12_ENCRYPTED_OID);

        if (idx + 1 > *outSz){
            return BUFFER_E;
        }
        out[idx++] = (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC);
        idx += SetLength(outerSz, out + idx);

        idx += SetSequence(length, out + idx);
        idx += SetMyVersion(0, out + idx, 0);
        tmp = (byte*)XMALLOC(encSz, heap, DYNAMIC_TYPE_TMP_BUFFER);
        if (tmp == NULL) {
            return MEMORY_E;
        }

        if ((ret = EncryptContent(content, contentSz, tmp, &encSz,
                   pass, passSz, vPKCS, vAlgo, NULL, 0, iter, rng, heap)) < 0) {
            XFREE(tmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
            return ret;
        }
        encSz = ret;

        #ifdef WOLFSSL_DEBUG_PKCS12
        {
            byte* p;
            for (printf("(size %u) Encrypted Content = ", encSz),
                    p = (byte*)tmp;
                p < (byte*)tmp + encSz;
                printf("%02X", *p), p++);
            printf("\n");
        }
        #endif

        idx += SetSequence(WC_PKCS12_DATA_OBJ_SZ + encSz, out + idx);
        idx += SetObjectId(sizeof(WC_PKCS12_DATA_OID), out + idx);
        if (idx + sizeof(WC_PKCS12_DATA_OID) > *outSz){
            WOLFSSL_MSG("Buffer not large enough for DATA OID");
            return BUFFER_E;
        }
        XMEMCPY(out + idx, WC_PKCS12_DATA_OID, sizeof(WC_PKCS12_DATA_OID));
        idx += sizeof(WC_PKCS12_DATA_OID);

        /* copy over encrypted data */
        if (idx + encSz > *outSz){
            return BUFFER_E;
        }
        XMEMCPY(out + idx, tmp, encSz);
        XFREE(tmp, heap, DYNAMIC_TYPE_TMP_BUFFER);
        idx += encSz;
        return idx;
    }

    /* DATA
     * ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC
     * length
     * ASN_OCTET_STRING
     * length
     * sequence containing all bags */
    if (type == WC_PKCS12_DATA) {
        /* calculate size */
        totalSz = SetObjectId(sizeof(WC_PKCS12_DATA_OID), seq);
        totalSz += sizeof(WC_PKCS12_DATA_OID);
        totalSz += ASN_TAG_SZ;

        length   = SetOctetString(contentSz, seq);
        length  += contentSz;
        totalSz += SetLength(length, seq);
        totalSz += length;

        if (out == NULL) {
            *outSz = totalSz + SetSequence(totalSz, seq);
            return LENGTH_ONLY_E;
        }

        if (*outSz < (totalSz + SetSequence(totalSz, seq))) {
            return BUFFER_E;
        }

        /* place data in output buffer */
        idx  = 0;
        idx += SetSequence(totalSz, out);
        idx += SetObjectId(sizeof(WC_PKCS12_DATA_OID), out + idx);
        if (idx + sizeof(WC_PKCS12_DATA_OID) > *outSz){
            WOLFSSL_MSG("Buffer not large enough for DATA OID");
            return BUFFER_E;
        }
        XMEMCPY(out + idx, WC_PKCS12_DATA_OID, sizeof(WC_PKCS12_DATA_OID));
        idx += sizeof(WC_PKCS12_DATA_OID);

        if (idx + 1 > *outSz){
            return BUFFER_E;
        }
        out[idx++] = (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC);
        idx += SetLength(length, out + idx);
        idx += SetOctetString(contentSz, out + idx);

        if (idx + contentSz > *outSz){
            return BUFFER_E;
        }
        XMEMCPY(out + idx, content, contentSz);
        idx += contentSz;

        return idx;
    }

    WOLFSSL_MSG("Unknown/Unsupported content type");
    return BAD_FUNC_ARG;
}


/* helper function to create the PKCS12 key content
 * keyCiSz is output buffer size
 * returns a pointer to be free'd by caller on success and NULL on failure */
static byte* PKCS12_create_key_content(WC_PKCS12* pkcs12, int nidKey,
        word32* keyCiSz, WC_RNG* rng, char* pass, word32 passSz,
        byte* key, word32 keySz, int iter)
{
    byte*  keyBuf;
    word32 keyBufSz = 0;
    byte* keyCi = NULL;
    word32 tmpSz;
    int ret;
    int algo;
    void* heap;

    heap = wc_PKCS12_GetHeap(pkcs12);
    *keyCiSz = 0;
    switch (nidKey) {
        case PBE_SHA1_RC4_128:
            algo = 1;
            break;

        case PBE_SHA1_DES:
            algo = 2;
            break;

        case PBE_SHA1_DES3:
            algo = 3;
            break;

        /* no encryption */
        case -1:
            algo = -1;
            break;

        default:
            WOLFSSL_MSG("Unknown/Unsupported key encryption");
            return NULL;
    }

    /* get max size for key bag */
    ret = wc_PKCS12_create_key_bag(pkcs12, rng, NULL, &keyBufSz, key, keySz,
            algo, iter, pass, passSz);
    if (ret != LENGTH_ONLY_E && ret < 0) {
        WOLFSSL_MSG("Error getting key bag size");
        return NULL;
    }

    /* account for sequence around bag */
    keyBufSz += MAX_SEQ_SZ;
    keyBuf = (byte*)XMALLOC(keyBufSz, heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (keyBuf == NULL) {
        WOLFSSL_MSG("Memory error creating keyBuf buffer");
        return NULL;
    }

    ret = wc_PKCS12_create_key_bag(pkcs12, rng, keyBuf + MAX_SEQ_SZ, &keyBufSz,
            key, keySz, algo, iter, pass, passSz);
    if (ret < 0) {
        XFREE(keyBuf, heap, DYNAMIC_TYPE_TMP_BUFFER);
        WOLFSSL_MSG("Error creating key bag");
        return NULL;
    }
    keyBufSz = ret;

    tmpSz = SetSequence(keyBufSz, keyBuf);
    XMEMMOVE(keyBuf + tmpSz, keyBuf + MAX_SEQ_SZ, keyBufSz);
    keyBufSz += tmpSz;

    #ifdef WOLFSSL_DEBUG_PKCS12
    {
        word32 i;
        printf("(size %u) Key Bag = ", keyBufSz);
        for (i = 0; i < keyBufSz; i++)
            printf("%02X", keyBuf[i]);
        printf("\n");
    }
    #endif
    ret = wc_PKCS12_encrypt_content(pkcs12, rng, NULL, keyCiSz,
            NULL, keyBufSz, algo, pass, passSz, iter, WC_PKCS12_DATA);
    if (ret != LENGTH_ONLY_E) {
        XFREE(keyBuf, heap, DYNAMIC_TYPE_TMP_BUFFER);
        WOLFSSL_MSG("Error getting key encrypt content size");
        return NULL;
    }
    keyCi = (byte*)XMALLOC(*keyCiSz, heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (keyCi == NULL) {
        XFREE(keyBuf, heap, DYNAMIC_TYPE_TMP_BUFFER);
        return NULL;
    }

    ret = wc_PKCS12_encrypt_content(pkcs12, rng, keyCi, keyCiSz,
            keyBuf, keyBufSz, algo, pass, passSz, iter, WC_PKCS12_DATA);
    XFREE(keyBuf, heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (ret < 0 ) {
        XFREE(keyCi, heap, DYNAMIC_TYPE_TMP_BUFFER);
        WOLFSSL_MSG("Error creating key encrypt content");
        return NULL;
    }
    *keyCiSz = ret;

    #ifdef WOLFSSL_DEBUG_PKCS12
    {
        word32 i;
        printf("(size %u) Key Content Info = ", *keyCiSz);
        for (i = 0; i < *keyCiSz; i++)
            printf("%02X", keyCi[i]);
        printf("\n");
    }
    #endif

    (void)heap;
    return keyCi;
}


/* helper function to create the PKCS12 certificate content
 * certCiSz is output buffer size
 * returns a pointer to be free'd by caller on success and NULL on failure */
static byte* PKCS12_create_cert_content(WC_PKCS12* pkcs12, int nidCert,
        WC_DerCertList* ca, byte* cert, word32 certSz, word32* certCiSz,
        WC_RNG* rng, char* pass, word32 passSz, int iter)
{
    int algo;
    int ret;
    int type;

    byte*  certBuf = NULL;
    word32 certBufSz;
    word32 idx;
    word32 sz;
    word32 tmpSz;

    byte* certCi;
    void* heap;

    heap = wc_PKCS12_GetHeap(pkcs12);
    switch (nidCert) {
        case PBE_SHA1_RC4_128:
            type = WC_PKCS12_ENCRYPTED_DATA;
            algo = 1;
            break;

        case PBE_SHA1_DES:
            type = WC_PKCS12_ENCRYPTED_DATA;
            algo = 2;
            break;

        case PBE_SHA1_DES3:
            type = WC_PKCS12_ENCRYPTED_DATA;
            algo = 3;
            break;

        case -1:
            type = WC_PKCS12_DATA;
            algo = -1;
            break;

        default:
            WOLFSSL_MSG("Unknown/Unsupported certificate encryption");
            return NULL;
    }

    /* get max size of buffer needed */
    ret = wc_PKCS12_create_cert_bag(pkcs12, NULL, &certBufSz, cert, certSz);
    if (ret != LENGTH_ONLY_E) {
        return NULL;
    }

    if (ca != NULL) {
        WC_DerCertList* current = ca;
        word32 curBufSz = 0;

        /* get max buffer size */
        while (current != NULL) {
            ret = wc_PKCS12_create_cert_bag(pkcs12, NULL, &curBufSz,
                    current->buffer, current->bufferSz);
            if (ret != LENGTH_ONLY_E) {
                return NULL;
            }
            certBufSz += curBufSz;
            current    = current->next;
        }
    }

    /* account for Sequence that holds all certificate bags */
    certBufSz += MAX_SEQ_SZ;

    /* completed getting max size, now create buffer and start adding bags */
    certBuf = (byte*)XMALLOC(certBufSz, heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (certBuf == NULL) {
        WOLFSSL_MSG("Memory error creating certificate bags");
        return NULL;
    }

    idx = 0;
    idx += MAX_SEQ_SZ;

    sz = certBufSz - idx;
    if ((ret = wc_PKCS12_create_cert_bag(pkcs12, certBuf + idx, &sz,
            cert, certSz)) < 0) {
        XFREE(certBuf, heap, DYNAMIC_TYPE_TMP_BUFFER);
        return NULL;
    }
    idx += ret;

    if (ca != NULL) {
        WC_DerCertList* current = ca;

        while (current != NULL) {
            sz = certBufSz - idx;
            if ((ret = wc_PKCS12_create_cert_bag(pkcs12, certBuf + idx, &sz,
               current->buffer, current->bufferSz)) < 0) {
                XFREE(certBuf, heap, DYNAMIC_TYPE_TMP_BUFFER);
                return NULL;
            }
            idx    += ret;
            current = current->next;
        }
    }

    /* set sequence and create encrypted content with all certificate bags */
    tmpSz = SetSequence(idx - MAX_SEQ_SZ, certBuf);
    XMEMMOVE(certBuf + tmpSz, certBuf + MAX_SEQ_SZ, idx - MAX_SEQ_SZ);
    certBufSz = tmpSz + (idx - MAX_SEQ_SZ);

    /* get buffer size needed for content info */
    ret = wc_PKCS12_encrypt_content(pkcs12, rng, NULL, certCiSz,
            NULL, certBufSz, algo, pass, passSz, iter, type);
    if (ret != LENGTH_ONLY_E) {
        XFREE(certBuf, heap, DYNAMIC_TYPE_TMP_BUFFER);
        WOLFSSL_LEAVE("wc_PKCS12_create()", ret);
        return NULL;
    }
    certCi = (byte*)XMALLOC(*certCiSz, heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (certCi == NULL) {
        XFREE(certBuf, heap, DYNAMIC_TYPE_TMP_BUFFER);
        return NULL;
    }

    ret = wc_PKCS12_encrypt_content(pkcs12, rng, certCi, certCiSz,
            certBuf, certBufSz, algo, pass, passSz, iter, type);
    XFREE(certBuf, heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (ret < 0) {
        WOLFSSL_LEAVE("wc_PKCS12_create()", ret);
        XFREE(certCi, heap, DYNAMIC_TYPE_TMP_BUFFER);
        return NULL;
    }
    *certCiSz = ret;

    #ifdef WOLFSSL_DEBUG_PKCS12
    {
        word32 i;
        printf("(size %u) Encrypted Certificate Content Info = ", *certCiSz);
        for (i = 0; i < *certCiSz; i++)
            printf("%02X", certCi[i]);
        printf("\n");
    }
    #endif

    (void)heap;
    return certCi;
}


/* helper function to create the PKCS12 safe
 * returns 0 on success */
static int PKCS12_create_safe(WC_PKCS12* pkcs12, byte* certCi, word32 certCiSz,
        byte* keyCi, word32 keyCiSz, WC_RNG* rng, char* pass, word32 passSz,
        int iter)
{
    int length;
    int ret;
    byte seq[MAX_SEQ_SZ];
    word32 safeDataSz;
    word32 innerDataSz;
    byte *innerData = NULL;
    byte *safeData  = NULL;
    word32 idx;

    innerDataSz = certCiSz + keyCiSz+SetSequence(certCiSz + keyCiSz, seq);

    /* add Content Info structs to safe, key first then cert */
    ret = wc_PKCS12_encrypt_content(pkcs12, rng, NULL, &safeDataSz,
            NULL, innerDataSz, 0, NULL, 0, 0, WC_PKCS12_DATA);
    if (ret != LENGTH_ONLY_E) {
        return ret;
    }

    safeData = (byte*)XMALLOC(safeDataSz, pkcs12->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (safeData == NULL) {
        WOLFSSL_MSG("Error malloc'ing safe data buffer");
        return MEMORY_E;
    }

    /* create sequence of inner data */
    innerData = (byte*)XMALLOC(innerDataSz, pkcs12->heap, DYNAMIC_TYPE_PKCS);
    if (innerData == NULL) {
        WOLFSSL_MSG("Error malloc'ing inner data buffer");
        XFREE(safeData, pkcs12->heap, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
    idx  = 0;
    idx += SetSequence(certCiSz + keyCiSz, innerData);
    XMEMCPY(innerData + idx, certCi, certCiSz);
    XMEMCPY(innerData + idx + certCiSz, keyCi, keyCiSz);

    ret = wc_PKCS12_encrypt_content(pkcs12, rng, safeData, &safeDataSz,
            innerData, innerDataSz, 0, pass, passSz, iter, WC_PKCS12_DATA);
    XFREE(innerData, pkcs12->heap, DYNAMIC_TYPE_PKCS);
    if (ret < 0 ) {
        WOLFSSL_MSG("Error setting data type for safe contents");
        XFREE(safeData, pkcs12->heap, DYNAMIC_TYPE_TMP_BUFFER);
        return ret;
    }
    idx = 0;

    ret = GetSequence(safeData, &idx, &length, safeDataSz);
    if (ret < 0) {
        WOLFSSL_MSG("Error getting first sequence of safe");
        XFREE(safeData, pkcs12->heap, DYNAMIC_TYPE_TMP_BUFFER);
        return ret;
    }

    ret = GetSafeContent(pkcs12, safeData, &idx, safeDataSz);
    XFREE(safeData, pkcs12->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (ret < 0) {
        WOLFSSL_MSG("Unable to create safe contents");
        return ret;
    }
    return 0;
}


/*
 * pass : password to use with encryption
 * passSz : size of the password buffer
 * name : friendlyName to use
 * key  : DER format of key
 * keySz : size of key buffer
 * cert : DER format of certificate
 * certSz : size of the certificate buffer
 * ca   : a list of extra certificates
 * nidKey  : type of encryption to use on the key (-1 means no encryption)
 * nidCert : type of encryption to use on the certificate
 *           (-1 means no encryption)
 * iter    : number of iterations with encryption
 * macIter : number of iterations when creating MAC
 * keyType : flag for signature and/or encryption key
 * heap : pointer to allocate from memory
 *
 * returns a pointer to a new WC_PKCS12 structure on success and NULL if failed
 */
WC_PKCS12* wc_PKCS12_create(char* pass, word32 passSz, char* name,
        byte* key, word32 keySz, byte* cert, word32 certSz, WC_DerCertList* ca,
        int nidKey, int nidCert, int iter, int macIter, int keyType, void* heap)
{
    WC_PKCS12* pkcs12;
    WC_RNG     rng;
    int ret;

    byte*  certCi = NULL;
    byte*  keyCi  = NULL;
    word32 certCiSz;
    word32 keyCiSz;

    WOLFSSL_ENTER("wc_PKCS12_create()");

    if ((ret = wc_InitRng_ex(&rng, heap, INVALID_DEVID)) != 0) {
        return NULL;
    }

    if ((pkcs12 = wc_PKCS12_new()) == NULL) {
        wc_FreeRng(&rng);
        WOLFSSL_LEAVE("wc_PKCS12_create", MEMORY_E);
        return NULL;
    }

    if ((ret = wc_PKCS12_SetHeap(pkcs12, heap)) != 0) {
        wc_PKCS12_free(pkcs12);
        wc_FreeRng(&rng);
        WOLFSSL_LEAVE("wc_PKCS12_create", ret);
        return NULL;
    }

    if (iter <= 0) {
        iter = WC_PKCS12_ITT_DEFAULT;
    }

    /**** add private key bag ****/
    keyCi = PKCS12_create_key_content(pkcs12, nidKey, &keyCiSz, &rng,
            pass, passSz, key, keySz, iter);
    if (keyCi == NULL) {
        wc_PKCS12_free(pkcs12);
        wc_FreeRng(&rng);
        return NULL;
    }

    /**** add main certificate bag and extras ****/
    certCi = PKCS12_create_cert_content(pkcs12, nidCert, ca, cert, certSz,
            &certCiSz, &rng, pass, passSz, iter);
    if (certCi == NULL) {
        XFREE(keyCi, heap, DYNAMIC_TYPE_TMP_BUFFER);
        wc_PKCS12_free(pkcs12);
        wc_FreeRng(&rng);
        return NULL;
    }

    /**** create safe and Content Info ****/
    ret = PKCS12_create_safe(pkcs12, certCi, certCiSz, keyCi, keyCiSz, &rng,
            pass, passSz, iter);
    XFREE(keyCi,  heap, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(certCi, heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (ret != 0) {
        WOLFSSL_MSG("Unable to create PKCS12 safe");
        wc_PKCS12_free(pkcs12);
        wc_FreeRng(&rng);
        return NULL;
    }

    /* create MAC */
    if (macIter > 0) {
        MacData* mac;
        byte digest[WC_MAX_DIGEST_SIZE]; /* for MAC */

        mac = (MacData*)XMALLOC(sizeof(MacData), heap, DYNAMIC_TYPE_PKCS);
        if (mac == NULL) {
            wc_PKCS12_free(pkcs12);
            wc_FreeRng(&rng);
            WOLFSSL_MSG("Error malloc'ing mac data buffer");
            return NULL;
        }
        XMEMSET(mac, 0, sizeof(MacData));
        pkcs12->signData = mac; /* now wc_PKCS12_free will free all mac too */

        #ifndef NO_SHA256
            mac->oid = SHA256h;
        #elif !defined(NO_SHA)
            mac->oid = SHA;
        #elif defined(WOLFSSL_SHA384)
            mac->oid = SHA384;
        #elif defined(WOLFSSL_SHA512)
            mac->oid = SHA512;
        #else
            WOLFSSL_MSG("No supported hash algorithm compiled in!");
            wc_PKCS12_free(pkcs12);
            wc_FreeRng(&rng);
            return NULL;
        #endif

        /* store number of iterations */
        mac->itt = macIter;

        /* set mac salt */
        mac->saltSz = 8;
        mac->salt = (byte*)XMALLOC(mac->saltSz, heap, DYNAMIC_TYPE_PKCS);
        if (mac->salt == NULL) {
            wc_PKCS12_free(pkcs12);
            wc_FreeRng(&rng);
            WOLFSSL_MSG("Error malloc'ing salt data buffer");
            return NULL;
        }

        if ((ret = wc_RNG_GenerateBlock(&rng, mac->salt, mac->saltSz)) != 0) {
            WOLFSSL_MSG("Error generating random salt");
            wc_PKCS12_free(pkcs12);
            wc_FreeRng(&rng);
            return NULL;
        }
        ret = wc_PKCS12_create_mac(pkcs12, pkcs12->safe->data,
                pkcs12->safe->dataSz, (const byte*)pass, passSz, digest,
                WC_MAX_DIGEST_SIZE);
        if (ret < 0) {
            wc_PKCS12_free(pkcs12);
            wc_FreeRng(&rng);
            WOLFSSL_MSG("Error creating mac");
            WOLFSSL_LEAVE("wc_PKCS12_create", ret);
            return NULL;
        }

        mac->digestSz = ret;
        mac->digest = (byte*)XMALLOC(ret, heap, DYNAMIC_TYPE_PKCS);
        if (mac->digest == NULL) {
            WOLFSSL_MSG("Error malloc'ing mac digest buffer");
            wc_PKCS12_free(pkcs12);
            wc_FreeRng(&rng);
            return NULL;
        }
        XMEMCPY(mac->digest, digest, mac->digestSz);
    }
    else {
        pkcs12->signData = NULL;
    }

    wc_FreeRng(&rng);
    (void)name;
    (void)keyType;

    return pkcs12;
}


/* if using a specific memory heap */
int wc_PKCS12_SetHeap(WC_PKCS12* pkcs12, void* heap)
{
    if (pkcs12 == NULL) {
        return BAD_FUNC_ARG;
    }
    pkcs12->heap = heap;

    return 0;
}


/* getter for heap */
void* wc_PKCS12_GetHeap(WC_PKCS12* pkcs12)
{
    if (pkcs12 == NULL) {
        return NULL;
    }

    return pkcs12->heap;
}

#undef ERROR_OUT

#endif /* !NO_ASN && !NO_PWDBASED && HAVE_PKCS12 */
