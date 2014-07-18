/* ocsp.c
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

#ifdef HAVE_OCSP

#include <cyassl/error-ssl.h>
#include <cyassl/ocsp.h>
#include <cyassl/internal.h>


int InitOCSP(CYASSL_OCSP* ocsp, CYASSL_CERT_MANAGER* cm)
{
    CYASSL_ENTER("InitOCSP");
    XMEMSET(ocsp, 0, sizeof(*ocsp));
    ocsp->cm = cm;
    if (InitMutex(&ocsp->ocspLock) != 0)
        return BAD_MUTEX_E;

    return 0;
}


static int InitOCSP_Entry(OCSP_Entry* ocspe, DecodedCert* cert)
{
    CYASSL_ENTER("InitOCSP_Entry");

    XMEMSET(ocspe, 0, sizeof(*ocspe));
    XMEMCPY(ocspe->issuerHash, cert->issuerHash, SHA_DIGEST_SIZE);
    XMEMCPY(ocspe->issuerKeyHash, cert->issuerKeyHash, SHA_DIGEST_SIZE);

    return 0;
}


static void FreeOCSP_Entry(OCSP_Entry* ocspe)
{
    CertStatus* tmp = ocspe->status;

    CYASSL_ENTER("FreeOCSP_Entry");

    while (tmp) {
        CertStatus* next = tmp->next;
        XFREE(tmp, NULL, DYNAMIC_TYPE_OCSP_STATUS);
        tmp = next;
    }
}


void FreeOCSP(CYASSL_OCSP* ocsp, int dynamic)
{
    OCSP_Entry* tmp = ocsp->ocspList;

    CYASSL_ENTER("FreeOCSP");

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


int CheckCertOCSP(CYASSL_OCSP* ocsp, DecodedCert* cert)
{
    byte* ocspReqBuf = NULL;
    int ocspReqSz = 2048;
    byte* ocspRespBuf = NULL;
    OcspRequest ocspRequest;
    OcspResponse ocspResponse;
    int result = -1;
    OCSP_Entry* ocspe;
    CertStatus* certStatus = NULL;
    CertStatus newStatus;
    const char *url;
    int urlSz;

    CYASSL_ENTER("CheckCertOCSP");

    if (LockMutex(&ocsp->ocspLock) != 0) {
        CYASSL_LEAVE("CheckCertOCSP", BAD_MUTEX_E);
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
            CYASSL_LEAVE("CheckCertOCSP", MEMORY_ERROR);
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
            CYASSL_MSG("\tinvalid status date, looking up cert");
        }
        else {
            result = xstat2err(certStatus->status);
            UnLockMutex(&ocsp->ocspLock);
            CYASSL_LEAVE("CheckCertOCSP", result);
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
        CYASSL_LEAVE("CheckCertOCSP", MEMORY_ERROR);
        return MEMORY_ERROR;
    }
    InitOcspRequest(&ocspRequest, cert, ocsp->cm->ocspSendNonce,
                                                         ocspReqBuf, ocspReqSz);
    ocspReqSz = EncodeOcspRequest(&ocspRequest);
    
    if (ocsp->cm->ocspIOCb)
        result = ocsp->cm->ocspIOCb(ocsp->cm->ocspIOCtx, url, urlSz,
                                           ocspReqBuf, ocspReqSz, &ocspRespBuf);

    if (result >= 0 && ocspRespBuf) {
        XMEMSET(&newStatus, 0, sizeof(CertStatus));

        InitOcspResponse(&ocspResponse, &newStatus, ocspRespBuf, result);
        OcspResponseDecode(&ocspResponse);
    
        if (ocspResponse.responseStatus != OCSP_SUCCESSFUL)
            result = OCSP_LOOKUP_FAIL;
        else {
            if (CompareOcspReqResp(&ocspRequest, &ocspResponse) == 0) {
                result = xstat2err(ocspResponse.status->status);

                if (LockMutex(&ocsp->ocspLock) != 0)
                    result = BAD_MUTEX_E;
                else {
                    if (certStatus != NULL)
                        /* Replace existing certificate entry with updated */
                        XMEMCPY(certStatus, &newStatus, sizeof(CertStatus));
                    else {
                        /* Save new certificate entry */
                        certStatus = (CertStatus*)XMALLOC(sizeof(CertStatus),
                                          NULL, DYNAMIC_TYPE_OCSP_STATUS);
                        if (certStatus != NULL) {
                            XMEMCPY(certStatus, &newStatus, sizeof(CertStatus));
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

    if (ocspReqBuf != NULL)
        XFREE(ocspReqBuf, NULL, DYNAMIC_TYPE_IN_BUFFER);

    if (ocspRespBuf != NULL && ocsp->cm->ocspRespFreeCb)
        ocsp->cm->ocspRespFreeCb(ocsp->cm->ocspIOCtx, ocspRespBuf);

    CYASSL_LEAVE("CheckCertOCSP", result);
    return result;
}


#else /* HAVE_OCSP */


#ifdef _MSC_VER
    /* 4206 warning for blank file */
    #pragma warning(disable: 4206)
#endif


#endif /* HAVE_OCSP */

