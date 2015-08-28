/* pkcs7.c
 *
 * Copyright (C) 2006-2015 wolfSSL Inc.
 *
 * This file is part of wolfSSL. (formerly known as CyaSSL)
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifdef HAVE_PKCS7

#include <wolfssl/wolfcrypt/pkcs7.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/logging.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #include <wolfcrypt/src/misc.c>
#endif

#ifndef WOLFSSL_HAVE_MIN
#define WOLFSSL_HAVE_MIN

    static INLINE word32 min(word32 a, word32 b)
    {
        return a > b ? b : a;
    }

#endif /* WOLFSSL_HAVE_MIN */


/* placed ASN.1 contentType OID into *output, return idx on success,
 * 0 upon failure */
WOLFSSL_LOCAL int wc_SetContentType(int pkcs7TypeOID, byte* output)
{
    /* PKCS#7 content types, RFC 2315, section 14 */
    static const byte pkcs7[]              = { 0x2A, 0x86, 0x48, 0x86, 0xF7,
                                               0x0D, 0x01, 0x07 };
    static const byte data[]               = { 0x2A, 0x86, 0x48, 0x86, 0xF7,
                                               0x0D, 0x01, 0x07, 0x01 };
    static const byte signedData[]         = { 0x2A, 0x86, 0x48, 0x86, 0xF7,
                                               0x0D, 0x01, 0x07, 0x02};
    static const byte envelopedData[]      = { 0x2A, 0x86, 0x48, 0x86, 0xF7,
                                               0x0D, 0x01, 0x07, 0x03 };
    static const byte signedAndEnveloped[] = { 0x2A, 0x86, 0x48, 0x86, 0xF7,
                                               0x0D, 0x01, 0x07, 0x04 };
    static const byte digestedData[]       = { 0x2A, 0x86, 0x48, 0x86, 0xF7,
                                               0x0D, 0x01, 0x07, 0x05 };
    static const byte encryptedData[]      = { 0x2A, 0x86, 0x48, 0x86, 0xF7,
                                               0x0D, 0x01, 0x07, 0x06 };

    int idSz;
    int typeSz = 0, idx = 0;
    const byte* typeName = 0;
    byte ID_Length[MAX_LENGTH_SZ];

    switch (pkcs7TypeOID) {
        case PKCS7_MSG:
            typeSz = sizeof(pkcs7);
            typeName = pkcs7;
            break;

        case DATA:
            typeSz = sizeof(data);
            typeName = data;
            break;

        case SIGNED_DATA:
            typeSz = sizeof(signedData);
            typeName = signedData;
            break;
        
        case ENVELOPED_DATA:
            typeSz = sizeof(envelopedData);
            typeName = envelopedData;
            break;

        case SIGNED_AND_ENVELOPED_DATA:
            typeSz = sizeof(signedAndEnveloped);
            typeName = signedAndEnveloped;
            break;

        case DIGESTED_DATA:
            typeSz = sizeof(digestedData);
            typeName = digestedData;
            break;

        case ENCRYPTED_DATA:
            typeSz = sizeof(encryptedData);
            typeName = encryptedData;
            break;

        default:
            WOLFSSL_MSG("Unknown PKCS#7 Type");
            return 0;
    };

    idSz  = SetLength(typeSz, ID_Length);
    output[idx++] = ASN_OBJECT_ID;
    XMEMCPY(output + idx, ID_Length, idSz);
    idx += idSz;
    XMEMCPY(output + idx, typeName, typeSz);
    idx += typeSz;

    return idx;

}


/* get ASN.1 contentType OID sum, return 0 on success, <0 on failure */
int wc_GetContentType(const byte* input, word32* inOutIdx, word32* oid,
                   word32 maxIdx)
{
    int length;
    word32 i = *inOutIdx;
    byte b;
    *oid = 0;

    WOLFSSL_ENTER("wc_GetContentType");

    b = input[i++];
    if (b != ASN_OBJECT_ID)
        return ASN_OBJECT_ID_E;

    if (GetLength(input, &i, &length, maxIdx) < 0)
        return ASN_PARSE_E;

    while(length--) {
        *oid += input[i];
        i++;
    }

    *inOutIdx = i;

    return 0;
}


/* init PKCS7 struct with recipient cert, decode into DecodedCert */
int wc_PKCS7_InitWithCert(PKCS7* pkcs7, byte* cert, word32 certSz)
{
    int ret = 0;

    XMEMSET(pkcs7, 0, sizeof(PKCS7));
    if (cert != NULL && certSz > 0) {
#ifdef WOLFSSL_SMALL_STACK
        DecodedCert* dCert;

        dCert = (DecodedCert*)XMALLOC(sizeof(DecodedCert), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
        if (dCert == NULL)
            return MEMORY_E;
#else
        DecodedCert stack_dCert;
        DecodedCert* dCert = &stack_dCert;
#endif

        pkcs7->singleCert = cert;
        pkcs7->singleCertSz = certSz;
        InitDecodedCert(dCert, cert, certSz, 0);

        ret = ParseCert(dCert, CA_TYPE, NO_VERIFY, 0);
        if (ret < 0) {
            FreeDecodedCert(dCert);
#ifdef WOLFSSL_SMALL_STACK
            XFREE(dCert, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return ret;
        }

        XMEMCPY(pkcs7->publicKey, dCert->publicKey, dCert->pubKeySize);
        pkcs7->publicKeySz = dCert->pubKeySize;
        XMEMCPY(pkcs7->issuerHash, dCert->issuerHash, KEYID_SIZE);
        pkcs7->issuer = dCert->issuerRaw;
        pkcs7->issuerSz = dCert->issuerRawLen;
        XMEMCPY(pkcs7->issuerSn, dCert->serial, dCert->serialSz);
        pkcs7->issuerSnSz = dCert->serialSz;
        FreeDecodedCert(dCert);

#ifdef WOLFSSL_SMALL_STACK
        XFREE(dCert, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
    }

    return ret;
}


/* releases any memory allocated by a PKCS7 initializer */
void wc_PKCS7_Free(PKCS7* pkcs7)
{
    (void)pkcs7;
}


/* build PKCS#7 data content type */
int wc_PKCS7_EncodeData(PKCS7* pkcs7, byte* output, word32 outputSz)
{
    static const byte oid[] =
        { ASN_OBJECT_ID, 0x09, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01,
                         0x07, 0x01 };
    byte seq[MAX_SEQ_SZ];
    byte octetStr[MAX_OCTET_STR_SZ];
    word32 seqSz;
    word32 octetStrSz;
    word32 oidSz = (word32)sizeof(oid);
    int idx = 0;

    octetStrSz = SetOctetString(pkcs7->contentSz, octetStr);
    seqSz = SetSequence(pkcs7->contentSz + octetStrSz + oidSz, seq);

    if (outputSz < pkcs7->contentSz + octetStrSz + oidSz + seqSz)
        return BUFFER_E;

    XMEMCPY(output, seq, seqSz);
    idx += seqSz;
    XMEMCPY(output + idx, oid, oidSz);
    idx += oidSz;
    XMEMCPY(output + idx, octetStr, octetStrSz);
    idx += octetStrSz;
    XMEMCPY(output + idx, pkcs7->content, pkcs7->contentSz);
    idx += pkcs7->contentSz;

    return idx;
}


typedef struct EncodedAttrib {
    byte valueSeq[MAX_SEQ_SZ];
        const byte* oid;
        byte valueSet[MAX_SET_SZ];
        const byte* value;
    word32 valueSeqSz, oidSz, idSz, valueSetSz, valueSz, totalSz;
} EncodedAttrib;


typedef struct ESD {
    Sha sha;
    byte contentDigest[SHA_DIGEST_SIZE + 2]; /* content only + ASN.1 heading */
    byte contentAttribsDigest[SHA_DIGEST_SIZE];
    byte encContentDigest[512];

    byte outerSeq[MAX_SEQ_SZ];
        byte outerContent[MAX_EXP_SZ];
            byte innerSeq[MAX_SEQ_SZ];
                byte version[MAX_VERSION_SZ];
                byte digAlgoIdSet[MAX_SET_SZ];
                    byte singleDigAlgoId[MAX_ALGO_SZ];

                byte contentInfoSeq[MAX_SEQ_SZ];
                    byte innerContSeq[MAX_EXP_SZ];
                        byte innerOctets[MAX_OCTET_STR_SZ];

                byte certsSet[MAX_SET_SZ];

                byte signerInfoSet[MAX_SET_SZ];
                    byte signerInfoSeq[MAX_SEQ_SZ];
                        byte signerVersion[MAX_VERSION_SZ];
                        byte issuerSnSeq[MAX_SEQ_SZ];
                            byte issuerName[MAX_SEQ_SZ];
                            byte issuerSn[MAX_SN_SZ];
                        byte signerDigAlgoId[MAX_ALGO_SZ];
                        byte digEncAlgoId[MAX_ALGO_SZ];
                        byte signedAttribSet[MAX_SET_SZ];
                            EncodedAttrib signedAttribs[6];
                        byte signerDigest[MAX_OCTET_STR_SZ];
    word32 innerOctetsSz, innerContSeqSz, contentInfoSeqSz;
    word32 outerSeqSz, outerContentSz, innerSeqSz, versionSz, digAlgoIdSetSz,
           singleDigAlgoIdSz, certsSetSz;
    word32 signerInfoSetSz, signerInfoSeqSz, signerVersionSz,
           issuerSnSeqSz, issuerNameSz, issuerSnSz,
           signerDigAlgoIdSz, digEncAlgoIdSz, signerDigestSz;
    word32 encContentDigestSz, signedAttribsSz, signedAttribsCount,
           signedAttribSetSz;
} ESD;


static int EncodeAttributes(EncodedAttrib* ea, int eaSz,
                                            PKCS7Attrib* attribs, int attribsSz)
{
    int i;
    int maxSz = min(eaSz, attribsSz);
    int allAttribsSz = 0;

    for (i = 0; i < maxSz; i++)
    {
        int attribSz = 0;

        ea[i].value = attribs[i].value;
        ea[i].valueSz = attribs[i].valueSz;
        attribSz += ea[i].valueSz;
        ea[i].valueSetSz = SetSet(attribSz, ea[i].valueSet);
        attribSz += ea[i].valueSetSz;
        ea[i].oid = attribs[i].oid;
        ea[i].oidSz = attribs[i].oidSz;
        attribSz += ea[i].oidSz;
        ea[i].valueSeqSz = SetSequence(attribSz, ea[i].valueSeq);
        attribSz += ea[i].valueSeqSz;
        ea[i].totalSz = attribSz;

        allAttribsSz += attribSz;
    }
    return allAttribsSz;
}


static int FlattenAttributes(byte* output, EncodedAttrib* ea, int eaSz)
{
    int i, idx;

    idx = 0;
    for (i = 0; i < eaSz; i++) {
        XMEMCPY(output + idx, ea[i].valueSeq, ea[i].valueSeqSz);
        idx += ea[i].valueSeqSz;
        XMEMCPY(output + idx, ea[i].oid, ea[i].oidSz);
        idx += ea[i].oidSz;
        XMEMCPY(output + idx, ea[i].valueSet, ea[i].valueSetSz);
        idx += ea[i].valueSetSz;
        XMEMCPY(output + idx, ea[i].value, ea[i].valueSz);
        idx += ea[i].valueSz;
    }
    return 0;
}


/* build PKCS#7 signedData content type */
int wc_PKCS7_EncodeSignedData(PKCS7* pkcs7, byte* output, word32 outputSz)
{
    static const byte outerOid[] =
        { ASN_OBJECT_ID, 0x09, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01,
                         0x07, 0x02 };
    static const byte innerOid[] =
        { ASN_OBJECT_ID, 0x09, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01,
                         0x07, 0x01 };

#ifdef WOLFSSL_SMALL_STACK
    ESD* esd = NULL;
#else
    ESD stack_esd;
    ESD* esd = &stack_esd;
#endif

    word32 signerInfoSz = 0;
    word32 totalSz = 0;
    int idx = 0, ret = 0;
    byte* flatSignedAttribs = NULL;
    word32 flatSignedAttribsSz = 0;
    word32 innerOidSz = sizeof(innerOid);
    word32 outerOidSz = sizeof(outerOid);

    if (pkcs7 == NULL || pkcs7->content == NULL || pkcs7->contentSz == 0 ||
        pkcs7->encryptOID == 0 || pkcs7->hashOID == 0 || pkcs7->rng == 0 ||
        pkcs7->singleCert == NULL || pkcs7->singleCertSz == 0 ||
        pkcs7->privateKey == NULL || pkcs7->privateKeySz == 0 ||
        output == NULL || outputSz == 0)
        return BAD_FUNC_ARG;

#ifdef WOLFSSL_SMALL_STACK
    esd = (ESD*)XMALLOC(sizeof(ESD), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (esd == NULL)
        return MEMORY_E;
#endif

    XMEMSET(esd, 0, sizeof(ESD));
    ret = wc_InitSha(&esd->sha);
    if (ret != 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(esd, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ret;
    }

    if (pkcs7->contentSz != 0)
    {
        wc_ShaUpdate(&esd->sha, pkcs7->content, pkcs7->contentSz);
        esd->contentDigest[0] = ASN_OCTET_STRING;
        esd->contentDigest[1] = SHA_DIGEST_SIZE;
        wc_ShaFinal(&esd->sha, &esd->contentDigest[2]);
    }

    esd->innerOctetsSz = SetOctetString(pkcs7->contentSz, esd->innerOctets);
    esd->innerContSeqSz = SetExplicit(0, esd->innerOctetsSz + pkcs7->contentSz,
                                esd->innerContSeq);
    esd->contentInfoSeqSz = SetSequence(pkcs7->contentSz + esd->innerOctetsSz +
                                    innerOidSz + esd->innerContSeqSz,
                                    esd->contentInfoSeq);

    esd->issuerSnSz = SetSerialNumber(pkcs7->issuerSn, pkcs7->issuerSnSz,
                                     esd->issuerSn);
    signerInfoSz += esd->issuerSnSz;
    esd->issuerNameSz = SetSequence(pkcs7->issuerSz, esd->issuerName);
    signerInfoSz += esd->issuerNameSz + pkcs7->issuerSz;
    esd->issuerSnSeqSz = SetSequence(signerInfoSz, esd->issuerSnSeq);
    signerInfoSz += esd->issuerSnSeqSz;
    esd->signerVersionSz = SetMyVersion(1, esd->signerVersion, 0);
    signerInfoSz += esd->signerVersionSz;
    esd->signerDigAlgoIdSz = SetAlgoID(pkcs7->hashOID, esd->signerDigAlgoId,
                                      hashType, 0);
    signerInfoSz += esd->signerDigAlgoIdSz;
    esd->digEncAlgoIdSz = SetAlgoID(pkcs7->encryptOID, esd->digEncAlgoId,
                                   keyType, 0);
    signerInfoSz += esd->digEncAlgoIdSz;

    if (pkcs7->signedAttribsSz != 0) {
        byte contentTypeOid[] =
                { ASN_OBJECT_ID, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xF7, 0x0d, 0x01,
                                 0x09, 0x03 };
        byte contentType[] =
                { ASN_OBJECT_ID, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01,
                                 0x07, 0x01 };
        byte messageDigestOid[] =
                { ASN_OBJECT_ID, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01,
                                 0x09, 0x04 };

        PKCS7Attrib cannedAttribs[2] =
        {
            { contentTypeOid, sizeof(contentTypeOid),
                             contentType, sizeof(contentType) },
            { messageDigestOid, sizeof(messageDigestOid),
                             esd->contentDigest, sizeof(esd->contentDigest) }
        };
        word32 cannedAttribsCount = sizeof(cannedAttribs)/sizeof(PKCS7Attrib);

        esd->signedAttribsCount += cannedAttribsCount;
        esd->signedAttribsSz += EncodeAttributes(&esd->signedAttribs[0], 2,
                                             cannedAttribs, cannedAttribsCount);

        esd->signedAttribsCount += pkcs7->signedAttribsSz;
        esd->signedAttribsSz += EncodeAttributes(&esd->signedAttribs[2], 4,
                                  pkcs7->signedAttribs, pkcs7->signedAttribsSz);

        flatSignedAttribs = (byte*)XMALLOC(esd->signedAttribsSz, 0, NULL);
        flatSignedAttribsSz = esd->signedAttribsSz;
        if (flatSignedAttribs == NULL) {
#ifdef WOLFSSL_SMALL_STACK
            XFREE(esd, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif   
            return MEMORY_E;
        }
        FlattenAttributes(flatSignedAttribs,
                                   esd->signedAttribs, esd->signedAttribsCount);
        esd->signedAttribSetSz = SetImplicit(ASN_SET, 0, esd->signedAttribsSz,
                                                          esd->signedAttribSet);
    }
    /* Calculate the final hash and encrypt it. */
    {
        int result;
        word32 scratch = 0;

#ifdef WOLFSSL_SMALL_STACK
        byte* digestInfo;
        RsaKey* privKey;
#else
        RsaKey stack_privKey;
        RsaKey* privKey = &stack_privKey;
        byte digestInfo[MAX_SEQ_SZ + MAX_ALGO_SZ +
                        MAX_OCTET_STR_SZ + SHA_DIGEST_SIZE];
#endif
        byte digestInfoSeq[MAX_SEQ_SZ];
        byte digestStr[MAX_OCTET_STR_SZ];
        word32 digestInfoSeqSz, digestStrSz;
        int digIdx = 0;

        if (pkcs7->signedAttribsSz != 0) {
            byte attribSet[MAX_SET_SZ];
            word32 attribSetSz;

            attribSetSz = SetSet(flatSignedAttribsSz, attribSet);

            ret = wc_InitSha(&esd->sha);
            if (ret < 0) {
                XFREE(flatSignedAttribs, 0, NULL);
#ifdef WOLFSSL_SMALL_STACK
                XFREE(esd, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return ret;
            }
            wc_ShaUpdate(&esd->sha, attribSet, attribSetSz);
            wc_ShaUpdate(&esd->sha, flatSignedAttribs, flatSignedAttribsSz);
        }
        wc_ShaFinal(&esd->sha, esd->contentAttribsDigest);

        digestStrSz = SetOctetString(SHA_DIGEST_SIZE, digestStr);
        digestInfoSeqSz = SetSequence(esd->signerDigAlgoIdSz +
                                      digestStrSz + SHA_DIGEST_SIZE,
                                      digestInfoSeq);

#ifdef WOLFSSL_SMALL_STACK
        digestInfo = (byte*)XMALLOC(MAX_SEQ_SZ + MAX_ALGO_SZ +
                                    MAX_OCTET_STR_SZ + SHA_DIGEST_SIZE,
                                    NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (digestInfo == NULL) {
            if (pkcs7->signedAttribsSz != 0)
                XFREE(flatSignedAttribs, 0, NULL);
            XFREE(esd, NULL, DYNAMIC_TYPE_TMP_BUFFER);
            return MEMORY_E;
        }
#endif

        XMEMCPY(digestInfo + digIdx, digestInfoSeq, digestInfoSeqSz);
        digIdx += digestInfoSeqSz;
        XMEMCPY(digestInfo + digIdx,
                                  esd->signerDigAlgoId, esd->signerDigAlgoIdSz);
        digIdx += esd->signerDigAlgoIdSz;
        XMEMCPY(digestInfo + digIdx, digestStr, digestStrSz);
        digIdx += digestStrSz;
        XMEMCPY(digestInfo + digIdx, esd->contentAttribsDigest,
                                                               SHA_DIGEST_SIZE);
        digIdx += SHA_DIGEST_SIZE;

#ifdef WOLFSSL_SMALL_STACK
        privKey = (RsaKey*)XMALLOC(sizeof(RsaKey), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
        if (privKey == NULL) {
            if (pkcs7->signedAttribsSz != 0)
                XFREE(flatSignedAttribs, 0, NULL);
            XFREE(digestInfo, NULL, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(esd,        NULL, DYNAMIC_TYPE_TMP_BUFFER);
            return MEMORY_E;
        }
#endif

        result = wc_InitRsaKey(privKey, NULL);
        if (result == 0)
            result = wc_RsaPrivateKeyDecode(pkcs7->privateKey, &scratch, privKey,
                                         pkcs7->privateKeySz);
        if (result < 0) {
            if (pkcs7->signedAttribsSz != 0)
                XFREE(flatSignedAttribs, 0, NULL);
#ifdef WOLFSSL_SMALL_STACK
            XFREE(privKey,    NULL, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(digestInfo, NULL, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(esd,        NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return PUBLIC_KEY_E;
        }

        result = wc_RsaSSL_Sign(digestInfo, digIdx,
                             esd->encContentDigest,
                             sizeof(esd->encContentDigest),
                             privKey, pkcs7->rng);

        wc_FreeRsaKey(privKey);

#ifdef WOLFSSL_SMALL_STACK
        XFREE(privKey,    NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(digestInfo, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

        if (result < 0) {
            if (pkcs7->signedAttribsSz != 0)
                XFREE(flatSignedAttribs, 0, NULL);
#ifdef WOLFSSL_SMALL_STACK
            XFREE(esd, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return result;
        }
        esd->encContentDigestSz = (word32)result;
    }
    signerInfoSz += flatSignedAttribsSz + esd->signedAttribSetSz;

    esd->signerDigestSz = SetOctetString(esd->encContentDigestSz,
                                                             esd->signerDigest);
    signerInfoSz += esd->signerDigestSz + esd->encContentDigestSz;

    esd->signerInfoSeqSz = SetSequence(signerInfoSz, esd->signerInfoSeq);
    signerInfoSz += esd->signerInfoSeqSz;
    esd->signerInfoSetSz = SetSet(signerInfoSz, esd->signerInfoSet);
    signerInfoSz += esd->signerInfoSetSz;

    esd->certsSetSz = SetImplicit(ASN_SET, 0, pkcs7->singleCertSz,
                                                                 esd->certsSet);

    esd->singleDigAlgoIdSz = SetAlgoID(pkcs7->hashOID, esd->singleDigAlgoId,
                                      hashType, 0);
    esd->digAlgoIdSetSz = SetSet(esd->singleDigAlgoIdSz, esd->digAlgoIdSet);


    esd->versionSz = SetMyVersion(1, esd->version, 0);

    totalSz = esd->versionSz + esd->singleDigAlgoIdSz + esd->digAlgoIdSetSz +
              esd->contentInfoSeqSz + esd->certsSetSz + pkcs7->singleCertSz +
              esd->innerOctetsSz + esd->innerContSeqSz +
              innerOidSz + pkcs7->contentSz +
              signerInfoSz;
    esd->innerSeqSz = SetSequence(totalSz, esd->innerSeq);
    totalSz += esd->innerSeqSz;
    esd->outerContentSz = SetExplicit(0, totalSz, esd->outerContent);
    totalSz += esd->outerContentSz + outerOidSz;
    esd->outerSeqSz = SetSequence(totalSz, esd->outerSeq);
    totalSz += esd->outerSeqSz;

    if (outputSz < totalSz) {
        if (pkcs7->signedAttribsSz != 0)
            XFREE(flatSignedAttribs, 0, NULL);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(esd, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return BUFFER_E;
    }

    idx = 0;
    XMEMCPY(output + idx, esd->outerSeq, esd->outerSeqSz);
    idx += esd->outerSeqSz;
    XMEMCPY(output + idx, outerOid, outerOidSz);
    idx += outerOidSz;
    XMEMCPY(output + idx, esd->outerContent, esd->outerContentSz);
    idx += esd->outerContentSz;
    XMEMCPY(output + idx, esd->innerSeq, esd->innerSeqSz);
    idx += esd->innerSeqSz;
    XMEMCPY(output + idx, esd->version, esd->versionSz);
    idx += esd->versionSz;
    XMEMCPY(output + idx, esd->digAlgoIdSet, esd->digAlgoIdSetSz);
    idx += esd->digAlgoIdSetSz;
    XMEMCPY(output + idx, esd->singleDigAlgoId, esd->singleDigAlgoIdSz);
    idx += esd->singleDigAlgoIdSz;
    XMEMCPY(output + idx, esd->contentInfoSeq, esd->contentInfoSeqSz);
    idx += esd->contentInfoSeqSz;
    XMEMCPY(output + idx, innerOid, innerOidSz);
    idx += innerOidSz;
    XMEMCPY(output + idx, esd->innerContSeq, esd->innerContSeqSz);
    idx += esd->innerContSeqSz;
    XMEMCPY(output + idx, esd->innerOctets, esd->innerOctetsSz);
    idx += esd->innerOctetsSz;
    XMEMCPY(output + idx, pkcs7->content, pkcs7->contentSz);
    idx += pkcs7->contentSz;
    XMEMCPY(output + idx, esd->certsSet, esd->certsSetSz);
    idx += esd->certsSetSz;
    XMEMCPY(output + idx, pkcs7->singleCert, pkcs7->singleCertSz);
    idx += pkcs7->singleCertSz;
    XMEMCPY(output + idx, esd->signerInfoSet, esd->signerInfoSetSz);
    idx += esd->signerInfoSetSz;
    XMEMCPY(output + idx, esd->signerInfoSeq, esd->signerInfoSeqSz);
    idx += esd->signerInfoSeqSz;
    XMEMCPY(output + idx, esd->signerVersion, esd->signerVersionSz);
    idx += esd->signerVersionSz;
    XMEMCPY(output + idx, esd->issuerSnSeq, esd->issuerSnSeqSz);
    idx += esd->issuerSnSeqSz;
    XMEMCPY(output + idx, esd->issuerName, esd->issuerNameSz);
    idx += esd->issuerNameSz;
    XMEMCPY(output + idx, pkcs7->issuer, pkcs7->issuerSz);
    idx += pkcs7->issuerSz;
    XMEMCPY(output + idx, esd->issuerSn, esd->issuerSnSz);
    idx += esd->issuerSnSz;
    XMEMCPY(output + idx, esd->signerDigAlgoId, esd->signerDigAlgoIdSz);
    idx += esd->signerDigAlgoIdSz;

    /* SignerInfo:Attributes */
    if (pkcs7->signedAttribsSz != 0) {
        XMEMCPY(output + idx, esd->signedAttribSet, esd->signedAttribSetSz);
        idx += esd->signedAttribSetSz;
        XMEMCPY(output + idx, flatSignedAttribs, flatSignedAttribsSz);
        idx += flatSignedAttribsSz;
        XFREE(flatSignedAttribs, 0, NULL);
    }

    XMEMCPY(output + idx, esd->digEncAlgoId, esd->digEncAlgoIdSz);
    idx += esd->digEncAlgoIdSz;
    XMEMCPY(output + idx, esd->signerDigest, esd->signerDigestSz);
    idx += esd->signerDigestSz;
    XMEMCPY(output + idx, esd->encContentDigest, esd->encContentDigestSz);
    idx += esd->encContentDigestSz;

#ifdef WOLFSSL_SMALL_STACK
    XFREE(esd, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return idx;
}


/* Finds the certificates in the message and saves it. */
int wc_PKCS7_VerifySignedData(PKCS7* pkcs7, byte* pkiMsg, word32 pkiMsgSz)
{
    word32 idx, contentType;
    int length, version, ret;
    byte* content = NULL;
    byte* sig = NULL;
    byte* cert = NULL;
    int contentSz = 0, sigSz = 0, certSz = 0;

    if (pkcs7 == NULL || pkiMsg == NULL || pkiMsgSz == 0)
        return BAD_FUNC_ARG;

    idx = 0;

    /* Get the contentInfo sequence */
    if (GetSequence(pkiMsg, &idx, &length, pkiMsgSz) < 0)
        return ASN_PARSE_E;

    /* Get the contentInfo contentType */
    if (wc_GetContentType(pkiMsg, &idx, &contentType, pkiMsgSz) < 0)
        return ASN_PARSE_E;

    if (contentType != SIGNED_DATA) {
        WOLFSSL_MSG("PKCS#7 input not of type SignedData");
        return PKCS7_OID_E;
    }

    /* get the ContentInfo content */
    if (pkiMsg[idx++] != (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 0))
        return ASN_PARSE_E;

    if (GetLength(pkiMsg, &idx, &length, pkiMsgSz) < 0)
        return ASN_PARSE_E;

    /* Get the signedData sequence */
    if (GetSequence(pkiMsg, &idx, &length, pkiMsgSz) < 0)
        return ASN_PARSE_E;

    /* Get the version */
    if (GetMyVersion(pkiMsg, &idx, &version) < 0)
        return ASN_PARSE_E;

    if (version != 1) {
        WOLFSSL_MSG("PKCS#7 signedData needs to be of version 1");
        return ASN_VERSION_E;
    }

    /* Get the set of DigestAlgorithmIdentifiers */
    if (GetSet(pkiMsg, &idx, &length, pkiMsgSz) < 0)
        return ASN_PARSE_E;

    /* Skip the set. */
    idx += length;

    /* Get the inner ContentInfo sequence */
    if (GetSequence(pkiMsg, &idx, &length, pkiMsgSz) < 0)
        return ASN_PARSE_E;

    /* Get the inner ContentInfo contentType */
    if (wc_GetContentType(pkiMsg, &idx, &contentType, pkiMsgSz) < 0)
        return ASN_PARSE_E;

    if (contentType != DATA) {
        WOLFSSL_MSG("PKCS#7 inner input not of type Data");
        return PKCS7_OID_E;
    }

    if (pkiMsg[idx++] != (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 0))
        return ASN_PARSE_E;

    if (GetLength(pkiMsg, &idx, &length, pkiMsgSz) < 0)
        return ASN_PARSE_E;

    if (pkiMsg[idx++] != ASN_OCTET_STRING)
        return ASN_PARSE_E;

    if (GetLength(pkiMsg, &idx, &length, pkiMsgSz) < 0)
        return ASN_PARSE_E;

    /* Save the inner data as the content. */
    if (length > 0) {
        /* Local pointer for calculating hashes later */
        pkcs7->content = content = &pkiMsg[idx];
        pkcs7->contentSz = contentSz = length;
        idx += length;
    }

    /* Get the implicit[0] set of certificates */
    if (pkiMsg[idx] == (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 0)) {
        idx++;
        if (GetLength(pkiMsg, &idx, &length, pkiMsgSz) < 0)
            return ASN_PARSE_E;

        if (length > 0) {
            /* At this point, idx is at the first certificate in
             * a set of certificates. There may be more than one,
             * or none, or they may be a PKCS 6 extended
             * certificate. We want to save the first cert if it
             * is X.509. */

            word32 certIdx = idx;

            if (pkiMsg[certIdx++] == (ASN_CONSTRUCTED | ASN_SEQUENCE)) {
                if (GetLength(pkiMsg, &certIdx, &certSz, pkiMsgSz) < 0)
                    return ASN_PARSE_E;

                cert = &pkiMsg[idx];
                certSz += (certIdx - idx);
            }
            wc_PKCS7_InitWithCert(pkcs7, cert, certSz);
        }
        idx += length;
    }

    /* Get the implicit[1] set of crls */
    if (pkiMsg[idx] == (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 1)) {
        idx++;
        if (GetLength(pkiMsg, &idx, &length, pkiMsgSz) < 0)
            return ASN_PARSE_E;

        /* Skip the set */
        idx += length;
    }

    /* Get the set of signerInfos */
    if (GetSet(pkiMsg, &idx, &length, pkiMsgSz) < 0)
        return ASN_PARSE_E;

    if (length > 0) {
        /* Get the sequence of the first signerInfo */
        if (GetSequence(pkiMsg, &idx, &length, pkiMsgSz) < 0)
            return ASN_PARSE_E;

        /* Get the version */
        if (GetMyVersion(pkiMsg, &idx, &version) < 0)
            return ASN_PARSE_E;

        if (version != 1) {
            WOLFSSL_MSG("PKCS#7 signerInfo needs to be of version 1");
            return ASN_VERSION_E;
        }

        /* Get the sequence of IssuerAndSerialNumber */
        if (GetSequence(pkiMsg, &idx, &length, pkiMsgSz) < 0)
            return ASN_PARSE_E;

        /* Skip it */
        idx += length;

        /* Get the sequence of digestAlgorithm */
        if (GetSequence(pkiMsg, &idx, &length, pkiMsgSz) < 0)
            return ASN_PARSE_E;

        /* Skip it */
        idx += length;

        /* Get the IMPLICIT[0] SET OF signedAttributes */
        if (pkiMsg[idx] == (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 0)) {
            idx++;

            if (GetLength(pkiMsg, &idx, &length, pkiMsgSz) < 0)
                return ASN_PARSE_E;

            idx += length;
        }

        /* Get the sequence of digestEncryptionAlgorithm */
        if (GetSequence(pkiMsg, &idx, &length, pkiMsgSz) < 0)
            return ASN_PARSE_E;

        /* Skip it */
        idx += length;

        /* Get the signature */
        if (pkiMsg[idx] == ASN_OCTET_STRING) {
            idx++;

            if (GetLength(pkiMsg, &idx, &length, pkiMsgSz) < 0)
                return ASN_PARSE_E;

            /* save pointer and length */
            sig = &pkiMsg[idx];
            sigSz = length;

            idx += length;
        }

        pkcs7->content = content;
        pkcs7->contentSz = contentSz;

        {
            word32 scratch = 0;
            int plainSz = 0;
            int digestSz = MAX_SEQ_SZ + MAX_ALGO_SZ +
                           MAX_OCTET_STR_SZ + SHA_DIGEST_SIZE;

#ifdef WOLFSSL_SMALL_STACK
            byte* digest;
            RsaKey* key;

            digest = (byte*)XMALLOC(digestSz, NULL, DYNAMIC_TYPE_TMP_BUFFER);

            if (digest == NULL)
                return MEMORY_E;

            key = (RsaKey*)XMALLOC(sizeof(RsaKey), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
            if (key == NULL) {
                XFREE(digest, NULL, DYNAMIC_TYPE_TMP_BUFFER);
                return MEMORY_E;
            }
#else
            byte digest[digestSz];
            RsaKey stack_key;
            RsaKey* key = &stack_key;
#endif

            XMEMSET(digest, 0, digestSz);

            ret = wc_InitRsaKey(key, NULL);
            if (ret != 0) {
#ifdef WOLFSSL_SMALL_STACK
                XFREE(digest, NULL, DYNAMIC_TYPE_TMP_BUFFER);
                XFREE(key,    NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return ret;
            }
            if (wc_RsaPublicKeyDecode(pkcs7->publicKey, &scratch, key,
                                   pkcs7->publicKeySz) < 0) {
                WOLFSSL_MSG("ASN RSA key decode error");
#ifdef WOLFSSL_SMALL_STACK
                XFREE(digest, NULL, DYNAMIC_TYPE_TMP_BUFFER);
                XFREE(key,    NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return PUBLIC_KEY_E;
            }

            plainSz = wc_RsaSSL_Verify(sig, sigSz, digest, digestSz, key);
            wc_FreeRsaKey(key);

#ifdef WOLFSSL_SMALL_STACK
            XFREE(digest, NULL, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(key,    NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

            if (plainSz < 0)
                return plainSz;
        }
    }

    return 0;
}


/* create ASN.1 fomatted RecipientInfo structure, returns sequence size */
WOLFSSL_LOCAL int wc_CreateRecipientInfo(const byte* cert, word32 certSz,
                                     int keyEncAlgo, int blockKeySz,
                                     RNG* rng, byte* contentKeyPlain,
                                     byte* contentKeyEnc,
                                     int* keyEncSz, byte* out, word32 outSz)
{
    word32 idx = 0;
    int ret = 0, totalSz = 0;
    int verSz, issuerSz, snSz, keyEncAlgSz;
    int issuerSeqSz, recipSeqSz, issuerSerialSeqSz;
    int encKeyOctetStrSz;

    byte ver[MAX_VERSION_SZ];
    byte issuerSerialSeq[MAX_SEQ_SZ];
    byte recipSeq[MAX_SEQ_SZ];
    byte issuerSeq[MAX_SEQ_SZ];
    byte encKeyOctetStr[MAX_OCTET_STR_SZ];

#ifdef WOLFSSL_SMALL_STACK
    byte *serial;
    byte *keyAlgArray;
    
    RsaKey* pubKey;
    DecodedCert* decoded;

    serial = (byte*)XMALLOC(MAX_SN_SZ, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    keyAlgArray = (byte*)XMALLOC(MAX_SN_SZ, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    decoded = (DecodedCert*)XMALLOC(sizeof(DecodedCert), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);

    if (decoded == NULL || serial == NULL || keyAlgArray == NULL) {
        if (serial)      XFREE(serial,      NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (keyAlgArray) XFREE(keyAlgArray, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (decoded)     XFREE(decoded,     NULL, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
    
#else
    byte serial[MAX_SN_SZ];
    byte keyAlgArray[MAX_ALGO_SZ];
    
    RsaKey stack_pubKey;
    RsaKey* pubKey = &stack_pubKey;
    DecodedCert stack_decoded;
    DecodedCert* decoded = &stack_decoded;
#endif

    InitDecodedCert(decoded, (byte*)cert, certSz, 0);
    ret = ParseCert(decoded, CA_TYPE, NO_VERIFY, 0);
    if (ret < 0) {
        FreeDecodedCert(decoded);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(serial,      NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(keyAlgArray, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(decoded,     NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ret;
    }

    /* version */
    verSz = SetMyVersion(0, ver, 0);

    /* IssuerAndSerialNumber */
    if (decoded->issuerRaw == NULL || decoded->issuerRawLen == 0) {
        WOLFSSL_MSG("DecodedCert lacks raw issuer pointer and length");
        FreeDecodedCert(decoded);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(serial,      NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(keyAlgArray, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(decoded,     NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return -1;
    }
    issuerSz    = decoded->issuerRawLen;
    issuerSeqSz = SetSequence(issuerSz, issuerSeq);

    if (decoded->serialSz == 0) {
        WOLFSSL_MSG("DecodedCert missing serial number");
        FreeDecodedCert(decoded);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(serial,      NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(keyAlgArray, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(decoded,     NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return -1;
    }
    snSz = SetSerialNumber(decoded->serial, decoded->serialSz, serial);

    issuerSerialSeqSz = SetSequence(issuerSeqSz + issuerSz + snSz,
                                    issuerSerialSeq);

    /* KeyEncryptionAlgorithmIdentifier, only support RSA now */
    if (keyEncAlgo != RSAk) {
        FreeDecodedCert(decoded);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(serial,      NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(keyAlgArray, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(decoded,     NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ALGO_ID_E;
    }

    keyEncAlgSz = SetAlgoID(keyEncAlgo, keyAlgArray, keyType, 0);
    if (keyEncAlgSz == 0) {
        FreeDecodedCert(decoded);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(serial,      NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(keyAlgArray, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(decoded,     NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return BAD_FUNC_ARG;
    }

#ifdef WOLFSSL_SMALL_STACK
    pubKey = (RsaKey*)XMALLOC(sizeof(RsaKey), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (pubKey == NULL) {
        FreeDecodedCert(decoded);
        XFREE(serial,      NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(keyAlgArray, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(decoded,     NULL, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
#endif

    /* EncryptedKey */
    ret = wc_InitRsaKey(pubKey, 0);
    if (ret != 0) {
        FreeDecodedCert(decoded);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(pubKey,      NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(serial,      NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(keyAlgArray, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(decoded,     NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ret;
    }

    if (wc_RsaPublicKeyDecode(decoded->publicKey, &idx, pubKey,
                           decoded->pubKeySize) < 0) {
        WOLFSSL_MSG("ASN RSA key decode error");
        wc_FreeRsaKey(pubKey);
        FreeDecodedCert(decoded);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(pubKey,      NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(serial,      NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(keyAlgArray, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(decoded,     NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return PUBLIC_KEY_E;
    }

    *keyEncSz = wc_RsaPublicEncrypt(contentKeyPlain, blockKeySz, contentKeyEnc,
                                 MAX_ENCRYPTED_KEY_SZ, pubKey, rng);
    wc_FreeRsaKey(pubKey);

#ifdef WOLFSSL_SMALL_STACK
    XFREE(pubKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    if (*keyEncSz < 0) {
        WOLFSSL_MSG("RSA Public Encrypt failed");
        FreeDecodedCert(decoded);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(serial,      NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(keyAlgArray, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(decoded,     NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return *keyEncSz;
    }

    encKeyOctetStrSz = SetOctetString(*keyEncSz, encKeyOctetStr);

    /* RecipientInfo */
    recipSeqSz = SetSequence(verSz + issuerSerialSeqSz + issuerSeqSz +
                             issuerSz + snSz + keyEncAlgSz + encKeyOctetStrSz +
                             *keyEncSz, recipSeq);

    if (recipSeqSz + verSz + issuerSerialSeqSz + issuerSeqSz + snSz +
        keyEncAlgSz + encKeyOctetStrSz + *keyEncSz > (int)outSz) {
        WOLFSSL_MSG("RecipientInfo output buffer too small");
        FreeDecodedCert(decoded);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(serial,      NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(keyAlgArray, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(decoded,     NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return BUFFER_E;
    }

    XMEMCPY(out + totalSz, recipSeq, recipSeqSz);
    totalSz += recipSeqSz;
    XMEMCPY(out + totalSz, ver, verSz);
    totalSz += verSz;
    XMEMCPY(out + totalSz, issuerSerialSeq, issuerSerialSeqSz);
    totalSz += issuerSerialSeqSz;
    XMEMCPY(out + totalSz, issuerSeq, issuerSeqSz);
    totalSz += issuerSeqSz;
    XMEMCPY(out + totalSz, decoded->issuerRaw, issuerSz);
    totalSz += issuerSz;
    XMEMCPY(out + totalSz, serial, snSz);
    totalSz += snSz;
    XMEMCPY(out + totalSz, keyAlgArray, keyEncAlgSz);
    totalSz += keyEncAlgSz;
    XMEMCPY(out + totalSz, encKeyOctetStr, encKeyOctetStrSz);
    totalSz += encKeyOctetStrSz;
    XMEMCPY(out + totalSz, contentKeyEnc, *keyEncSz);
    totalSz += *keyEncSz;

    FreeDecodedCert(decoded);

#ifdef WOLFSSL_SMALL_STACK
    XFREE(serial,      NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(keyAlgArray, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(decoded,     NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return totalSz;
}


/* build PKCS#7 envelopedData content type, return enveloped size */
int wc_PKCS7_EncodeEnvelopedData(PKCS7* pkcs7, byte* output, word32 outputSz)
{
    int i, ret = 0, idx = 0;
    int totalSz = 0, padSz = 0, desOutSz = 0;

    int contentInfoSeqSz, outerContentTypeSz, outerContentSz;
    byte contentInfoSeq[MAX_SEQ_SZ];
    byte outerContentType[MAX_ALGO_SZ];
    byte outerContent[MAX_SEQ_SZ];

    int envDataSeqSz, verSz;
    byte envDataSeq[MAX_SEQ_SZ];
    byte ver[MAX_VERSION_SZ];

    RNG rng;
    int contentKeyEncSz, blockKeySz;
    int dynamicFlag = 0;
    byte contentKeyPlain[MAX_CONTENT_KEY_LEN];
#ifdef WOLFSSL_SMALL_STACK
    byte* contentKeyEnc;
#else
    byte contentKeyEnc[MAX_ENCRYPTED_KEY_SZ];
#endif
    byte* plain;
    byte* encryptedContent;

    int recipSz, recipSetSz;
#ifdef WOLFSSL_SMALL_STACK
    byte* recip;
#else
    byte recip[MAX_RECIP_SZ];
#endif
    byte recipSet[MAX_SET_SZ];

    int encContentOctetSz, encContentSeqSz, contentTypeSz;
    int contentEncAlgoSz, ivOctetStringSz;
    byte encContentSeq[MAX_SEQ_SZ];
    byte contentType[MAX_ALGO_SZ];
    byte contentEncAlgo[MAX_ALGO_SZ];
    byte tmpIv[DES_BLOCK_SIZE];
    byte ivOctetString[MAX_OCTET_STR_SZ];
    byte encContentOctet[MAX_OCTET_STR_SZ];

    if (pkcs7 == NULL || pkcs7->content == NULL || pkcs7->contentSz == 0 ||
        pkcs7->encryptOID == 0 || pkcs7->singleCert == NULL)
        return BAD_FUNC_ARG;

    if (output == NULL || outputSz == 0)
        return BAD_FUNC_ARG;

    /* PKCS#7 only supports DES, 3DES for now */
    switch (pkcs7->encryptOID) {
        case DESb:
            blockKeySz = DES_KEYLEN;
            break;

        case DES3b:
            blockKeySz = DES3_KEYLEN;
            break;

        default:
            WOLFSSL_MSG("Unsupported content cipher type");
            return ALGO_ID_E;
    };

    /* outer content type */
    outerContentTypeSz = wc_SetContentType(ENVELOPED_DATA, outerContentType);

    /* version, defined as 0 in RFC 2315 */
    verSz = SetMyVersion(0, ver, 0);

    /* generate random content encryption key */
    ret = wc_InitRng(&rng);
    if (ret != 0)
        return ret;

    ret = wc_RNG_GenerateBlock(&rng, contentKeyPlain, blockKeySz);
    if (ret != 0) {
        wc_FreeRng(&rng);
        return ret;
    }

#ifdef WOLFSSL_SMALL_STACK
    recip         = (byte*)XMALLOC(MAX_RECIP_SZ, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    contentKeyEnc = (byte*)XMALLOC(MAX_ENCRYPTED_KEY_SZ, NULL, 
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (contentKeyEnc == NULL || recip == NULL) {
        if (recip)         XFREE(recip,         NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (contentKeyEnc) XFREE(contentKeyEnc, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        wc_FreeRng(&rng);
        return MEMORY_E;
    }
    
#endif

    /* build RecipientInfo, only handle 1 for now */
    recipSz = wc_CreateRecipientInfo(pkcs7->singleCert, pkcs7->singleCertSz, RSAk,
                                  blockKeySz, &rng, contentKeyPlain,
                                  contentKeyEnc, &contentKeyEncSz, recip,
                                  MAX_RECIP_SZ);
                                                                      
    ForceZero(contentKeyEnc, MAX_ENCRYPTED_KEY_SZ);
    
#ifdef WOLFSSL_SMALL_STACK
    XFREE(contentKeyEnc, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    if (recipSz < 0) {
        WOLFSSL_MSG("Failed to create RecipientInfo");
        wc_FreeRng(&rng);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(recip, NULL, DYNAMMIC_TYPE_TMP_BUFFER);
#endif
        return recipSz;
    }
    recipSetSz = SetSet(recipSz, recipSet);

    /* generate IV for block cipher */
    ret = wc_RNG_GenerateBlock(&rng, tmpIv, DES_BLOCK_SIZE);
    wc_FreeRng(&rng);
    if (ret != 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(recip, NULL, DYNAMMIC_TYPE_TMP_BUFFER);
#endif
        return ret;
    }

    /* EncryptedContentInfo */
    contentTypeSz = wc_SetContentType(pkcs7->contentOID, contentType);
    if (contentTypeSz == 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(recip, NULL, DYNAMMIC_TYPE_TMP_BUFFER);
#endif
        return BAD_FUNC_ARG;
    }

    /* allocate encrypted content buffer, pad if necessary, PKCS#7 padding */
    padSz = DES_BLOCK_SIZE - (pkcs7->contentSz % DES_BLOCK_SIZE);
    desOutSz = pkcs7->contentSz + padSz;

    if (padSz != 0) {
        plain = (byte*)XMALLOC(desOutSz, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (plain == NULL) {
#ifdef WOLFSSL_SMALL_STACK
            XFREE(recip, NULL, DYNAMMIC_TYPE_TMP_BUFFER);
#endif
            return MEMORY_E;
        }
        XMEMCPY(plain, pkcs7->content, pkcs7->contentSz);
        dynamicFlag = 1;

        for (i = 0; i < padSz; i++) {
            plain[pkcs7->contentSz + i] = padSz;
        }

    } else {
        plain = pkcs7->content;
        desOutSz = pkcs7->contentSz;
    }

    encryptedContent = (byte*)XMALLOC(desOutSz, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (encryptedContent == NULL) {
        if (dynamicFlag)
            XFREE(plain, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(recip, NULL, DYNAMMIC_TYPE_TMP_BUFFER);
#endif
        return MEMORY_E;
    }

    /* put together IV OCTET STRING */
    ivOctetStringSz = SetOctetString(DES_BLOCK_SIZE, ivOctetString);

    /* build up our ContentEncryptionAlgorithmIdentifier sequence,
     * adding (ivOctetStringSz + DES_BLOCK_SIZE) for IV OCTET STRING */
    contentEncAlgoSz = SetAlgoID(pkcs7->encryptOID, contentEncAlgo,
                                 blkType, ivOctetStringSz + DES_BLOCK_SIZE);

    if (contentEncAlgoSz == 0) {
        XFREE(encryptedContent, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (dynamicFlag)
            XFREE(plain, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(recip, NULL, DYNAMMIC_TYPE_TMP_BUFFER);
#endif
        return BAD_FUNC_ARG;
    }

    /* encrypt content */
    if (pkcs7->encryptOID == DESb) {
        Des des;

        ret = wc_Des_SetKey(&des, contentKeyPlain, tmpIv, DES_ENCRYPTION);

        if (ret == 0)
            wc_Des_CbcEncrypt(&des, encryptedContent, plain, desOutSz);

        if (ret != 0) {
            XFREE(encryptedContent, NULL, DYNAMIC_TYPE_TMP_BUFFER);
            if (dynamicFlag)
                XFREE(plain, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#ifdef WOLFSSL_SMALL_STACK
            XFREE(recip, NULL, DYNAMMIC_TYPE_TMP_BUFFER);
#endif
            return ret;
        }
    }
    else if (pkcs7->encryptOID == DES3b) {
        Des3 des3;

        ret = wc_Des3_SetKey(&des3, contentKeyPlain, tmpIv, DES_ENCRYPTION);

        if (ret == 0)
            ret = wc_Des3_CbcEncrypt(&des3, encryptedContent, plain, desOutSz);

        if (ret != 0) {
            XFREE(encryptedContent, NULL, DYNAMIC_TYPE_TMP_BUFFER);
            if (dynamicFlag)
                XFREE(plain, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#ifdef WOLFSSL_SMALL_STACK
            XFREE(recip, NULL, DYNAMMIC_TYPE_TMP_BUFFER);
#endif
            return ret;
        }
    }

    encContentOctetSz = SetImplicit(ASN_OCTET_STRING, 0,
                                    desOutSz, encContentOctet);

    encContentSeqSz = SetSequence(contentTypeSz + contentEncAlgoSz +
                                  ivOctetStringSz + DES_BLOCK_SIZE +
                                  encContentOctetSz + desOutSz, encContentSeq);

    /* keep track of sizes for outer wrapper layering */
    totalSz = verSz + recipSetSz + recipSz + encContentSeqSz + contentTypeSz +
              contentEncAlgoSz + ivOctetStringSz + DES_BLOCK_SIZE +
              encContentOctetSz + desOutSz;

    /* EnvelopedData */
    envDataSeqSz = SetSequence(totalSz, envDataSeq);
    totalSz += envDataSeqSz;

    /* outer content */
    outerContentSz = SetExplicit(0, totalSz, outerContent);
    totalSz += outerContentTypeSz;
    totalSz += outerContentSz;

    /* ContentInfo */
    contentInfoSeqSz = SetSequence(totalSz, contentInfoSeq);
    totalSz += contentInfoSeqSz;

    if (totalSz > (int)outputSz) {
        WOLFSSL_MSG("Pkcs7_encrypt output buffer too small");
        XFREE(encryptedContent, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (dynamicFlag)
            XFREE(plain, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(recip, NULL, DYNAMMIC_TYPE_TMP_BUFFER);
#endif
        return BUFFER_E;
    }

    XMEMCPY(output + idx, contentInfoSeq, contentInfoSeqSz);
    idx += contentInfoSeqSz;
    XMEMCPY(output + idx, outerContentType, outerContentTypeSz);
    idx += outerContentTypeSz;
    XMEMCPY(output + idx, outerContent, outerContentSz);
    idx += outerContentSz;
    XMEMCPY(output + idx, envDataSeq, envDataSeqSz);
    idx += envDataSeqSz;
    XMEMCPY(output + idx, ver, verSz);
    idx += verSz;
    XMEMCPY(output + idx, recipSet, recipSetSz);
    idx += recipSetSz;
    XMEMCPY(output + idx, recip, recipSz);
    idx += recipSz;
    XMEMCPY(output + idx, encContentSeq, encContentSeqSz);
    idx += encContentSeqSz;
    XMEMCPY(output + idx, contentType, contentTypeSz);
    idx += contentTypeSz;
    XMEMCPY(output + idx, contentEncAlgo, contentEncAlgoSz);
    idx += contentEncAlgoSz;
    XMEMCPY(output + idx, ivOctetString, ivOctetStringSz);
    idx += ivOctetStringSz;
    XMEMCPY(output + idx, tmpIv, DES_BLOCK_SIZE);
    idx += DES_BLOCK_SIZE;
    XMEMCPY(output + idx, encContentOctet, encContentOctetSz);
    idx += encContentOctetSz;
    XMEMCPY(output + idx, encryptedContent, desOutSz);
    idx += desOutSz;

    ForceZero(contentKeyPlain, MAX_CONTENT_KEY_LEN);

    if (dynamicFlag)
        XFREE(plain, NULL, DYNAMMIC_TYPE_TMP_BUFFER);
    XFREE(encryptedContent, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    
#ifdef WOLFSSL_SMALL_STACK
    XFREE(recip, NULL, DYNAMMIC_TYPE_TMP_BUFFER);
#endif

    return idx;
}

/* unwrap and decrypt PKCS#7 envelopedData object, return decoded size */
WOLFSSL_API int wc_PKCS7_DecodeEnvelopedData(PKCS7* pkcs7, byte* pkiMsg,
                                         word32 pkiMsgSz, byte* output,
                                         word32 outputSz)
{
    int recipFound = 0;
    int ret, version, length;
    word32 savedIdx = 0, idx = 0;
    word32 contentType, encOID;
    byte   issuerHash[SHA_DIGEST_SIZE];

    int encryptedKeySz, keySz;
    byte tmpIv[DES_BLOCK_SIZE];
    byte* decryptedKey = NULL;

#ifdef WOLFSSL_SMALL_STACK
    mp_int* serialNum;
    byte* encryptedKey;
    RsaKey* privKey;
#else
    mp_int stack_serialNum;
    mp_int* serialNum = &stack_serialNum;
    byte encryptedKey[MAX_ENCRYPTED_KEY_SZ];
    
    RsaKey stack_privKey;
    RsaKey* privKey = &stack_privKey;
#endif
    int encryptedContentSz;
    byte padLen;
    byte* encryptedContent = NULL;

    if (pkcs7 == NULL || pkcs7->singleCert == NULL ||
        pkcs7->singleCertSz == 0 || pkcs7->privateKey == NULL ||
        pkcs7->privateKeySz == 0)
        return BAD_FUNC_ARG;

    if (pkiMsg == NULL || pkiMsgSz == 0 ||
        output == NULL || outputSz == 0)
        return BAD_FUNC_ARG;

    /* read past ContentInfo, verify type is envelopedData */
    if (GetSequence(pkiMsg, &idx, &length, pkiMsgSz) < 0)
        return ASN_PARSE_E;

    if (wc_GetContentType(pkiMsg, &idx, &contentType, pkiMsgSz) < 0)
        return ASN_PARSE_E;

    if (contentType != ENVELOPED_DATA) {
        WOLFSSL_MSG("PKCS#7 input not of type EnvelopedData");
        return PKCS7_OID_E;
    }

    if (pkiMsg[idx++] != (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 0))
        return ASN_PARSE_E;

    if (GetLength(pkiMsg, &idx, &length, pkiMsgSz) < 0)
        return ASN_PARSE_E;

    /* remove EnvelopedData and version */
    if (GetSequence(pkiMsg, &idx, &length, pkiMsgSz) < 0)
        return ASN_PARSE_E;

    if (GetMyVersion(pkiMsg, &idx, &version) < 0)
        return ASN_PARSE_E;

    if (version != 0) {
        WOLFSSL_MSG("PKCS#7 envelopedData needs to be of version 0");
        return ASN_VERSION_E;
    }

    /* walk through RecipientInfo set, find correct recipient */
    if (GetSet(pkiMsg, &idx, &length, pkiMsgSz) < 0)
        return ASN_PARSE_E;
    
#ifdef WOLFSSL_SMALL_STACK
    encryptedKey = (byte*)XMALLOC(MAX_ENCRYPTED_KEY_SZ, NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (encryptedKey == NULL)
        return MEMORY_E;
#endif
    
    savedIdx = idx;
    recipFound = 0;

    /* when looking for next recipient, use first sequence and version to
     * indicate there is another, if not, move on */
    while(recipFound == 0) {

        /* remove RecipientInfo, if we don't have a SEQUENCE, back up idx to
         * last good saved one */
        if (GetSequence(pkiMsg, &idx, &length, pkiMsgSz) < 0) {
            idx = savedIdx;
            break;
        }

        if (GetMyVersion(pkiMsg, &idx, &version) < 0) {
            idx = savedIdx;
            break;
        }

        if (version != 0) {
#ifdef WOLFSSL_SMALL_STACK
            XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return ASN_VERSION_E;
        }
        
        /* remove IssuerAndSerialNumber */
        if (GetSequence(pkiMsg, &idx, &length, pkiMsgSz) < 0) {
#ifdef WOLFSSL_SMALL_STACK
            XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return ASN_PARSE_E;
        }
        
        if (GetNameHash(pkiMsg, &idx, issuerHash, pkiMsgSz) < 0) {
#ifdef WOLFSSL_SMALL_STACK
            XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return ASN_PARSE_E;
        }
        
        /* if we found correct recipient, issuer hashes will match */
        if (XMEMCMP(issuerHash, pkcs7->issuerHash, SHA_DIGEST_SIZE) == 0) {
            recipFound = 1;
        }
        
#ifdef WOLFSSL_SMALL_STACK
        serialNum = (mp_int*)XMALLOC(sizeof(mp_int), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
        if (serialNum == NULL) {
            XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
            return MEMORY_E;
        }
#endif
        
        if (GetInt(serialNum, pkiMsg, &idx, pkiMsgSz) < 0) {
#ifdef WOLFSSL_SMALL_STACK
            XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(serialNum,    NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return ASN_PARSE_E;
        }
        
        mp_clear(serialNum);
        
#ifdef WOLFSSL_SMALL_STACK
        XFREE(serialNum, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        
        if (GetAlgoId(pkiMsg, &idx, &encOID, pkiMsgSz) < 0) {
#ifdef WOLFSSL_SMALL_STACK
            XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return ASN_PARSE_E;
        }
        
        /* key encryption algorithm must be RSA for now */
        if (encOID != RSAk) {
#ifdef WOLFSSL_SMALL_STACK
            XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return ALGO_ID_E;
        }
        
        /* read encryptedKey */
        if (pkiMsg[idx++] != ASN_OCTET_STRING) {
#ifdef WOLFSSL_SMALL_STACK
            XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return ASN_PARSE_E;
        }
        
        if (GetLength(pkiMsg, &idx, &encryptedKeySz, pkiMsgSz) < 0) {
#ifdef WOLFSSL_SMALL_STACK
            XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return ASN_PARSE_E;
        }
          
        if (recipFound == 1)
            XMEMCPY(encryptedKey, &pkiMsg[idx], encryptedKeySz);
        idx += encryptedKeySz;

        /* update good idx */
        savedIdx = idx;
    }

    if (recipFound == 0) {
        WOLFSSL_MSG("No recipient found in envelopedData that matches input");
#ifdef WOLFSSL_SMALL_STACK
        XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return PKCS7_RECIP_E;
    }

    /* remove EncryptedContentInfo */
    if (GetSequence(pkiMsg, &idx, &length, pkiMsgSz) < 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ASN_PARSE_E;
    }
    
    if (wc_GetContentType(pkiMsg, &idx, &contentType, pkiMsgSz) < 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ASN_PARSE_E;
    }

    if (GetAlgoId(pkiMsg, &idx, &encOID, pkiMsgSz) < 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ASN_PARSE_E;
    }
    
    /* get block cipher IV, stored in OPTIONAL parameter of AlgoID */
    if (pkiMsg[idx++] != ASN_OCTET_STRING) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ASN_PARSE_E;
    }
    
    if (GetLength(pkiMsg, &idx, &length, pkiMsgSz) < 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ASN_PARSE_E;
    }
    
    if (length != DES_BLOCK_SIZE) {
        WOLFSSL_MSG("Incorrect IV length, must be of DES_BLOCK_SIZE");
#ifdef WOLFSSL_SMALL_STACK
        XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ASN_PARSE_E;
    }

    XMEMCPY(tmpIv, &pkiMsg[idx], length);
    idx += length;

    /* read encryptedContent, cont[0] */
    if (pkiMsg[idx++] != (ASN_CONTEXT_SPECIFIC | 0)) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ASN_PARSE_E;
    }

    if (GetLength(pkiMsg, &idx, &encryptedContentSz, pkiMsgSz) < 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ASN_PARSE_E;
    }
    
    encryptedContent = (byte*)XMALLOC(encryptedContentSz, NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (encryptedContent == NULL) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return MEMORY_E;
    }

    XMEMCPY(encryptedContent, &pkiMsg[idx], encryptedContentSz);

    /* load private key */
#ifdef WOLFSSL_SMALL_STACK
    privKey = (RsaKey*)XMALLOC(sizeof(RsaKey), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (privKey == NULL) {
        XFREE(encryptedContent, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(encryptedKey,     NULL, DYNAMIC_TYPE_TMP_BUFFER);        return MEMORY_E;
    }
#endif

    ret = wc_InitRsaKey(privKey, 0);
    if (ret != 0) {
        XFREE(encryptedContent, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(privKey,      NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ret;
    }

    idx = 0;

    ret = wc_RsaPrivateKeyDecode(pkcs7->privateKey, &idx, privKey,
                              pkcs7->privateKeySz);
    if (ret != 0) {
        WOLFSSL_MSG("Failed to decode RSA private key");
        XFREE(encryptedContent, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(privKey,      NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ret;
    }

    /* decrypt encryptedKey */
    keySz = wc_RsaPrivateDecryptInline(encryptedKey, encryptedKeySz,
                                    &decryptedKey, privKey);
    wc_FreeRsaKey(privKey);

#ifdef WOLFSSL_SMALL_STACK
    XFREE(privKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    if (keySz <= 0) {
        XFREE(encryptedContent, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return keySz;
    }

    /* decrypt encryptedContent */
    if (encOID == DESb) {
        Des des;
        ret = wc_Des_SetKey(&des, decryptedKey, tmpIv, DES_DECRYPTION);

        if (ret == 0)
            wc_Des_CbcDecrypt(&des, encryptedContent, encryptedContent,
                                 encryptedContentSz);

        if (ret != 0) {
            XFREE(encryptedContent, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#ifdef WOLFSSL_SMALL_STACK
            XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return ret;
        }
    }
    else if (encOID == DES3b) {
        Des3 des;
        ret = wc_Des3_SetKey(&des, decryptedKey, tmpIv, DES_DECRYPTION);
        if (ret == 0)
            ret = wc_Des3_CbcDecrypt(&des, encryptedContent, encryptedContent,
                                  encryptedContentSz);

        if (ret != 0) {
            XFREE(encryptedContent, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#ifdef WOLFSSL_SMALL_STACK
            XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return ret;
        }
    } else {
        WOLFSSL_MSG("Unsupported content encryption OID type");
        XFREE(encryptedContent, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#ifdef WOLFSSL_SMALL_STACK
        XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ALGO_ID_E;
    }

    padLen = encryptedContent[encryptedContentSz-1];

    /* copy plaintext to output */
    XMEMCPY(output, encryptedContent, encryptedContentSz - padLen);

    /* free memory, zero out keys */
    ForceZero(encryptedKey, MAX_ENCRYPTED_KEY_SZ);
    ForceZero(encryptedContent, encryptedContentSz);
    XFREE(encryptedContent, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#ifdef WOLFSSL_SMALL_STACK
    XFREE(encryptedKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
    
    return encryptedContentSz - padLen;
}


#else  /* HAVE_PKCS7 */


#ifdef _MSC_VER
    /* 4206 warning for blank file */
    #pragma warning(disable: 4206)
#endif


#endif /* HAVE_PKCS7 */

