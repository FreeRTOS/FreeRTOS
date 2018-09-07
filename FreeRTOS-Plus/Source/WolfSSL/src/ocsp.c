/* ocsp.c
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

  /* Name change compatibility layer no longer needs to be included here */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifdef HAVE_OCSP

#include <wolfssl/error-ssl.h>
#include <wolfssl/ocsp.h>
#include <wolfssl/internal.h>


int InitOCSP(WOLFSSL_OCSP* ocsp, WOLFSSL_CERT_MANAGER* cm)
{
    WOLFSSL_ENTER("InitOCSP");
    XMEMSET(ocsp, 0, sizeof(*ocsp));
    ocsp->cm = cm;
    if (InitMutex(&ocsp->ocspLock) != 0)
        return BAD_MUTEX_E;

    return 0;
}


static int InitOCSP_Entry(OCSP_Entry* ocspe, DecodedCert* cert)
{
    WOLFSSL_ENTER("InitOCSP_Entry");

    XMEMSET(ocspe, 0, sizeof(*ocspe));
    XMEMCPY(ocspe->issuerHash, cert->issuerHash, SHA_DIGEST_SIZE);
    XMEMCPY(ocspe->issuerKeyHash, cert->issuerKeyHash, SHA_DIGEST_SIZE);

    return 0;
}


static void FreeOCSP_Entry(OCSP_Entry* ocspe)
{
    CertStatus* tmp = ocspe->status;

    WOLFSSL_ENTER("FreeOCSP_Entry");

    while (tmp) {
        CertStatus* next = tmp->next;
        XFREE(tmp, NULL, DYNAMIC_TYPE_OCSP_STATUS);
        tmp = next;
    }
}


void FreeOCSP(WOLFSSL_OCSP* ocsp, int dynamic)
{
    OCSP_Entry* tmp = ocsp->ocspList;

    WOLFSSL_ENTER("FreeOCSP");

    while (tmp) {
        OCSP_Entry* next = tmp->next;
        FreeOCSP_Entry(tmp);
        XFREE(tmp, NULL, DYNAMIC_TYPE_OCSP_ENTRY);
        tmp = next;
    }

    FreeMutex(&ocsp->ocspLock);
    if (dynamic)
        XFREE(ocsp, NULL, DYNAMIC_TYPE_OCSP);
}


static int xstat2err(int stat)
{
    switch (stat) {
        case CERT_GOOD:
            return 0;
        case CERT_REVOKED:
            return OCSP_CERT_REVOKED;
        default:
            return OCSP_CERT_UNKNOWN;
    }
}


int CheckCertOCSP(WOLFSSL_OCSP* ocsp, DecodedCert* cert)
{
    byte* ocspReqBuf = NULL;
    int ocspReqSz = 2048;
    byte* ocspRespBuf = NULL;
    int result = -1;
    OCSP_Entry* ocspe;
    CertStatus* certStatus = NULL;
    const char *url;
    int urlSz;
#ifdef WOLFSSL_SMALL_STACK
    CertStatus* newStatus;
    OcspRequest* ocspRequest;
    OcspResponse* ocspResponse;
#else
    CertStatus newStatus[1];
    OcspRequest ocspRequest[1];
    OcspResponse ocspResponse[1];
#endif

    WOLFSSL_ENTER("CheckCertOCSP");

    if (LockMutex(&ocsp->ocspLock) != 0) {
        WOLFSSL_LEAVE("CheckCertOCSP", BAD_MUTEX_E);
        return BAD_MUTEX_E;
    }

    ocspe = ocsp->ocspList;
    while (ocspe) {
        if (XMEMCMP(ocspe->issuerHash, cert->issuerHash, SHA_DIGEST_SIZE) == 0
            && XMEMCMP(ocspe->issuerKeyHash, cert->issuerKeyHash,
                                                        SHA_DIGEST_SIZE) == 0)
            break;
        else
            ocspe = ocspe->next;
    }

    if (ocspe == NULL) {
        ocspe = (OCSP_Entry*)XMALLOC(sizeof(OCSP_Entry),
                                                NULL, DYNAMIC_TYPE_OCSP_ENTRY);
        if (ocspe != NULL) {
            InitOCSP_Entry(ocspe, cert);
            ocspe->next = ocsp->ocspList;
            ocsp->ocspList = ocspe;
        }
        else {
            UnLockMutex(&ocsp->ocspLock);
            WOLFSSL_LEAVE("CheckCertOCSP", MEMORY_ERROR);
            return MEMORY_ERROR;
        }
    }
    else {
        certStatus = ocspe->status;
        while (certStatus) {
            if (certStatus->serialSz == cert->serialSz &&
                 XMEMCMP(certStatus->serial, cert->serial, cert->serialSz) == 0)
                break;
            else
                certStatus = certStatus->next;
        }
    }

    if (certStatus != NULL) {
        if (!ValidateDate(certStatus->thisDate,
                                        certStatus->thisDateFormat, BEFORE) ||
            (certStatus->nextDate[0] == 0) ||
            !ValidateDate(certStatus->nextDate,
                                        certStatus->nextDateFormat, AFTER)) {
            WOLFSSL_MSG("\tinvalid status date, looking up cert");
        }
        else {
            result = xstat2err(certStatus->status);
            UnLockMutex(&ocsp->ocspLock);
            WOLFSSL_LEAVE("CheckCertOCSP", result);
            return result;
        }
    }

    UnLockMutex(&ocsp->ocspLock);

    if (ocsp->cm->ocspUseOverrideURL) {
        url = ocsp->cm->ocspOverrideURL;
        if (url != NULL && url[0] != '\0')
            urlSz = (int)XSTRLEN(url);
        else
            return OCSP_NEED_URL;
    }
    else if (cert->extAuthInfoSz != 0 && cert->extAuthInfo != NULL) {
        url = (const char *)cert->extAuthInfo;
        urlSz = cert->extAuthInfoSz;
    }
    else {
        /* cert doesn't have extAuthInfo, assuming CERT_GOOD */
        return 0;
    }

    ocspReqBuf = (byte*)XMALLOC(ocspReqSz, NULL, DYNAMIC_TYPE_IN_BUFFER);
    if (ocspReqBuf == NULL) {
        WOLFSSL_LEAVE("CheckCertOCSP", MEMORY_ERROR);
        return MEMORY_ERROR;
    }

#ifdef WOLFSSL_SMALL_STACK
    newStatus = (CertStatus*)XMALLOC(sizeof(CertStatus), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    ocspRequest = (OcspRequest*)XMALLOC(sizeof(OcspRequest), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    ocspResponse = (OcspResponse*)XMALLOC(sizeof(OcspResponse), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);

    if (newStatus == NULL || ocspRequest == NULL || ocspResponse == NULL) {
        if (newStatus)    XFREE(newStatus,    NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (ocspRequest)  XFREE(ocspRequest,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (ocspResponse) XFREE(ocspResponse, NULL, DYNAMIC_TYPE_TMP_BUFFER);

        XFREE(ocspReqBuf, NULL, DYNAMIC_TYPE_TMP_BUFFER);

        WOLFSSL_LEAVE("CheckCertOCSP", MEMORY_ERROR);
        return MEMORY_E;
    }
#endif

    InitOcspRequest(ocspRequest, cert, ocsp->cm->ocspSendNonce,
                                                         ocspReqBuf, ocspReqSz);
    ocspReqSz = EncodeOcspRequest(ocspRequest);
    
    if (ocsp->cm->ocspIOCb)
        result = ocsp->cm->ocspIOCb(ocsp->cm->ocspIOCtx, url, urlSz,
                                           ocspReqBuf, ocspReqSz, &ocspRespBuf);

    if (result >= 0 && ocspRespBuf) {
        XMEMSET(newStatus, 0, sizeof(CertStatus));

        InitOcspResponse(ocspResponse, newStatus, ocspRespBuf, result);
        OcspResponseDecode(ocspResponse);
    
        if (ocspResponse->responseStatus != OCSP_SUCCESSFUL)
            result = OCSP_LOOKUP_FAIL;
        else {
            if (CompareOcspReqResp(ocspRequest, ocspResponse) == 0) {
                result = xstat2err(ocspResponse->status->status);

                if (LockMutex(&ocsp->ocspLock) != 0)
                    result = BAD_MUTEX_E;
                else {
                    if (certStatus != NULL)
                        /* Replace existing certificate entry with updated */
                        XMEMCPY(certStatus, newStatus, sizeof(CertStatus));
                    else {
                        /* Save new certificate entry */
                        certStatus = (CertStatus*)XMALLOC(sizeof(CertStatus),
                                          NULL, DYNAMIC_TYPE_OCSP_STATUS);
                        if (certStatus != NULL) {
                            XMEMCPY(certStatus, newStatus, sizeof(CertStatus));
                            certStatus->next = ocspe->status;
                            ocspe->status = certStatus;
                            ocspe->totalStatus++;
                        }
                    }

                    UnLockMutex(&ocsp->ocspLock);
                }
            }
            else
                result = OCSP_LOOKUP_FAIL;
        }
    }
    else
        result = OCSP_LOOKUP_FAIL;

    XFREE(ocspReqBuf, NULL, DYNAMIC_TYPE_IN_BUFFER);

#ifdef WOLFSSL_SMALL_STACK
    XFREE(newStatus,    NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(ocspRequest,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(ocspResponse, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    if (ocspRespBuf != NULL && ocsp->cm->ocspRespFreeCb)
        ocsp->cm->ocspRespFreeCb(ocsp->cm->ocspIOCtx, ocspRespBuf);

    WOLFSSL_LEAVE("CheckCertOCSP", result);
    return result;
}


#else /* HAVE_OCSP */


#ifdef _MSC_VER
    /* 4206 warning for blank file */
    #pragma warning(disable: 4206)
#endif


#endif /* HAVE_OCSP */

