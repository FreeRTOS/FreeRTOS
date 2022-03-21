/*
 * FreeRTOS V202112.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

 /**
  * @file code_signature_verification_mbedtls.c
  * @brief Code signature verification using mbedtls crypto.
  *
  * The file demonstrates implements the code signature verification functionality on 
  * the specified file using mbedtls for SHA256 ECDSA.
  */

 /* C runtime includes. */
#include <string.h>

 /* FreeRTOS includes. */
#include "FreeRTOS.h"

/* mbedTLS includes. */
#if !defined( MBEDTLS_CONFIG_FILE )
#include "mbedtls/config.h"
#else
#include MBEDTLS_CONFIG_FILE
#endif
#include "mbedtls/platform.h"
#include "mbedtls/sha256.h"
#include "mbedtls/sha1.h"
#include "mbedtls/pk.h"
#include "mbedtls/x509_crt.h"

/* OTA includes. */
#include "ota.h"

/* Signature verification includes. */
#include "code_signature_verification.h"
#include "aws_ota_codesigner_certificate.h"

/**
 * @brief SHA256 buffer size for storing cryptographic hash computation results.
 */
#define SHA256_DIGEST_BYTES    32

 /* Size of buffer used in file operations on this platform (Windows). */
#define OTA_PAL_WIN_BUF_SIZE ( ( size_t ) 4096UL )

/**
 * @brief Library-independent cryptographic algorithm identifiers.
 */
#define HASH_ALGORITHM_SHA1           1
#define HASH_ALGORITHM_SHA256         2
#define ASYMMETRIC_ALGORITHM_RSA      1
#define ASYMMETRIC_ALGORITHM_ECDSA    2

 /**
  * @brief Internal signature verification context structure.
  */
typedef struct SignatureVerificationState
{
    BaseType_t xAsymmetricAlgorithm;
    BaseType_t xHashAlgorithm;
    mbedtls_sha256_context xSHA256Context;
} SignatureVerificationState_t, * SignatureVerificationStatePtr_t;

/**
 * @brief Initializes digital signature verification.
 *
 * @param[out] ppvContext Opaque context structure.
 * @param[in] xAsymmetricAlgorithm Cryptographic public key cryptosystem.
 * @param[in] xHashAlgorithm Cryptographic hash algorithm that was used for signing.
 *
 * @return pdTRUE if initialization succeeds, or pdFALSE otherwise.
 */
static BaseType_t prvSignatureVerificationStart(void** ppvContext,
    BaseType_t xAsymmetricAlgorithm,
    BaseType_t xHashAlgorithm);

/**
 * @brief Updates a cryptographic hash computation with the specified byte array.
 *
 * @param[in] pvContext Opaque context structure.
 * @param[in] pucData Byte array that was signed.
 * @param[in] xDataLength Length in bytes of data that was signed.
 */
static void prvSignatureVerificationUpdate(void* pvContext,
    const uint8_t* pucData,
    size_t xDataLength);

/**
 * @brief Verifies a digital signature computation using the public key from the
 * specified certificate.
 *
 * @param[in] pvContext Opaque context structure.
 * @param[in] pucSignerCertificate Base64 and DER encoded X.509 certificate of the
 * signer.
 * @param[in] xSignerCertificateLength Length in bytes of the certificate.
 * @param[in] pucSignature Digital signature result to verify.
 * @param[in] xSignatureLength in bytes of digital signature result.
 *
 * @return pdTRUE if the signature is correct or pdFALSE if the signature is invalid.
 */
static BaseType_t prvSignatureVerificationFinal(void* pvContext,
    char* pcSignerCertificate,
    size_t xSignerCertificateLength,
    uint8_t* pucSignature,
    size_t xSignatureLength);

/* Read the specified signer certificate from the filesystem into a local buffer. The allocated
 * memory becomes the property of the caller who is responsible for freeing it.
 */

static uint8_t* otaPal_ReadAndAssumeCertificate(const uint8_t* const pucCertName,
    uint32_t* const ulSignerCertSize)
{
    FILE* pFile;
    uint8_t* pucSignerCert = NULL;
    uint8_t* pucCertData = NULL;
    int32_t lSize = 0; /* For MISRA mandatory. */
    int32_t lWindowsError;

    pFile = fopen((const char*)pucCertName, "rb"); /*lint !e586
                                                            * C standard library call is being used for portability. */

    if (pFile != NULL)
    {
        lWindowsError = fseek(pFile, 0, SEEK_END);         /*lint !e586
                                                                * C standard library call is being used for portability. */

        if (lWindowsError == 0)                               /* fseek returns a non-zero value on error. */
        {
            lSize = (int32_t)ftell(pFile);                  /*lint !e586 Allow call in this context. */

            if (lSize != -1L)                                 /* ftell returns -1 on error. */
            {
                lWindowsError = fseek(pFile, 0, SEEK_SET); /*lint !e586
                                                                * C standard library call is being used for portability. */
            }
            else /* ftell returned an error, pucSignerCert remains NULL. */
            {
                lWindowsError = -1L;
            }
        } /* else fseek returned an error, pucSignerCert remains NULL. */

        if (lWindowsError == 0)
        {
            /* Allocate memory for the signer certificate plus a terminating zero so we can load and return it to the caller. */
            pucSignerCert = pvPortMalloc(lSize + 1); /*lint !e732 !e9034 !e9079 Allow conversion. */
        }

        if (pucSignerCert != NULL)
        {
            if (fread(pucSignerCert, 1, lSize, pFile) == (size_t)lSize) /*lint !e586 !e732 !e9034
                                                                                 * C standard library call is being used for portability. */
            {
                /* The crypto code requires the terminating zero to be part of the length so add 1 to the size. */
                *ulSignerCertSize = lSize + 1;
                pucSignerCert[lSize] = 0;
            }
            else
            {   /* There was a problem reading the certificate file so free the memory and abort. */
                vPortFree(pucSignerCert);
                pucSignerCert = NULL;
            }
        }
        else
        {
            LogError(("Failed to allocate memory for signer cert contents.\r\n"));
            /* Nothing special to do. */
        }

        lWindowsError = fclose(pFile); /*lint !e586
                                            * C standard library call is being used for portability. */

        if (lWindowsError != 0)
        {
            LogError(("File pointer operation failed.\r\n"));
            pucSignerCert = NULL;
        }
    }
    else
    {
        LogError(("No such certificate file: %s. Using aws_ota_codesigner_certificate.h.\r\n",
            (const char*)pucCertName));

        /* Allocate memory for the signer certificate plus a terminating zero so we can copy it and return to the caller. */
        lSize = sizeof(signingcredentialSIGNING_CERTIFICATE_PEM);
        pucSignerCert = pvPortMalloc(lSize);                           /*lint !e9029 !e9079 !e838 malloc proto requires void*. */
        pucCertData = (uint8_t*)signingcredentialSIGNING_CERTIFICATE_PEM; /*lint !e9005 we don't modify the cert but it could be set by PKCS11 so it's not const. */

        if (pucSignerCert != NULL)
        {
            memcpy(pucSignerCert, pucCertData, lSize);
            *ulSignerCertSize = lSize;
        }
        else
        {
            LogError(("No memory for certificate of size %d!\r\n", lSize));
        }
    }

    return pucSignerCert; /*lint !e480 !e481 fopen and fclose are being used by-design. */
}

/**
 * @brief Verifies a cryptographic signature based on the signer
 * certificate, hash algorithm, and the data that was signed.
 */
static BaseType_t prvVerifySignature(char* pcSignerCertificate,
    size_t xSignerCertificateLength,
    BaseType_t xHashAlgorithm,
    uint8_t* pucHash,
    size_t xHashLength,
    uint8_t* pucSignature,
    size_t xSignatureLength)
{
    BaseType_t xResult = pdTRUE;
    mbedtls_x509_crt xCertCtx;
    mbedtls_md_type_t xMbedHashAlg = MBEDTLS_MD_SHA256;

    (void)xHashAlgorithm;

    memset(&xCertCtx, 0, sizeof(mbedtls_x509_crt));

    /*
     * Decode and create a certificate context
     */
    mbedtls_x509_crt_init(&xCertCtx);

    if (0 != mbedtls_x509_crt_parse(
        &xCertCtx, (const unsigned char*)pcSignerCertificate, xSignerCertificateLength))
    {
        xResult = pdFALSE;
    }

    /*
     * Verify the signature using the public key from the decoded certificate
     */
    if (pdTRUE == xResult)
    {
        if (0 != mbedtls_pk_verify(
            &xCertCtx.pk,
            xMbedHashAlg,
            pucHash,
            xHashLength,
            pucSignature,
            xSignatureLength))
        {
            xResult = pdFALSE;
        }
    }

    /*
     * Clean-up
     */
    mbedtls_x509_crt_free(&xCertCtx);

    return xResult;
}



/**
 * @brief Creates signature verification context.
 */
static BaseType_t prvSignatureVerificationStart(void** ppvContext,
    BaseType_t xAsymmetricAlgorithm,
    BaseType_t xHashAlgorithm)
{
    BaseType_t xResult = pdTRUE;
    SignatureVerificationState_t* pxCtx = NULL;

    /*
     * Allocate the context
     */
    if (NULL == (pxCtx = (SignatureVerificationStatePtr_t)pvPortMalloc(
        sizeof(*pxCtx)))) /*lint !e9087 Allow casting void* to other types. */
    {
        xResult = pdFALSE;
    }

    if (pdTRUE == xResult)
    {
        *ppvContext = pxCtx;

        /*
         * Store the algorithm identifiers
         */
        pxCtx->xAsymmetricAlgorithm = xAsymmetricAlgorithm;
        pxCtx->xHashAlgorithm = xHashAlgorithm;

        /*
         * Initialize the requested hash type
         */
        mbedtls_sha256_init(&pxCtx->xSHA256Context);
        (void)mbedtls_sha256_starts_ret(&pxCtx->xSHA256Context, 0);
    }

    return xResult;
}

/**
 * @brief Adds bytes to an in-progress hash for subsequent signature verification.
 */
static void prvSignatureVerificationUpdate(void* pvContext,
    const uint8_t* pucData,
    size_t xDataLength)
{
    SignatureVerificationState_t* pxCtx = (SignatureVerificationStatePtr_t)pvContext; /*lint !e9087 Allow casting void* to other types. */

    /*
     * Add the data to the hash of the requested type
     */
    (void)mbedtls_sha256_update_ret(&pxCtx->xSHA256Context, pucData, xDataLength);

}

/**
 * @brief Performs signature verification on a cryptographic hash.
 */
static BaseType_t prvSignatureVerificationFinal(void* pvContext,
    char* pcSignerCertificate,
    size_t xSignerCertificateLength,
    uint8_t* pucSignature,
    size_t xSignatureLength)
{
    BaseType_t xResult = pdFALSE;

    if (pvContext != NULL)
    {
        SignatureVerificationStatePtr_t pxCtx = (SignatureVerificationStatePtr_t)pvContext; /*lint !e9087 Allow casting void* to other types. */
        uint8_t ucSHA256[SHA256_DIGEST_BYTES];                                      /* Reserve enough space for the larger for SHA256 results. */
        uint8_t* pucHash = NULL;
        size_t xHashLength = 0;

        if ((pcSignerCertificate != NULL) &&
            (pucSignature != NULL) &&
            (xSignerCertificateLength > 0UL) &&
            (xSignatureLength > 0UL))
        {
            /*
             * Finish the hash.
             */
            (void)mbedtls_sha256_finish_ret(&pxCtx->xSHA256Context, ucSHA256);
            pucHash = ucSHA256;
            xHashLength = SHA256_DIGEST_BYTES;

            /*
             * Verify the signature.
             */
            xResult = prvVerifySignature(pcSignerCertificate,
                xSignerCertificateLength,
                pxCtx->xHashAlgorithm,
                pucHash,
                xHashLength,
                pucSignature,
                xSignatureLength);
        }
        else
        {
            /* Allow function to be called with only the context pointer for cleanup after a failure. */
        }

        /*
         * Clean-up
         */
        vPortFree(pxCtx);
    }

    return xResult;
}

/* Verify the signature of the specified file. */
OtaPalMainStatus_t xValidateImageSignature(OtaFileContext_t* const C)
{
    OtaPalMainStatus_t eResult = OtaPalSuccess;
    uint32_t ulBytesRead;
    uint32_t ulSignerCertSize;
    uint8_t* pucBuf, * pucSignerCert;
    void* pvSigVerifyContext;

        /* Verify an ECDSA-SHA256 signature. */
        if (pdFALSE == prvSignatureVerificationStart(&pvSigVerifyContext, ASYMMETRIC_ALGORITHM_ECDSA, HASH_ALGORITHM_SHA256))
        {
            eResult = OtaPalSignatureCheckFailed;
        }
        else
        {
            LogInfo(("Started %s signature verification, file: %s\r\n",
                OTA_JsonFileSignatureKey, (const char*)C->pCertFilepath));
            pucSignerCert = otaPal_ReadAndAssumeCertificate((const uint8_t* const)C->pCertFilepath, &ulSignerCertSize);

            if (pucSignerCert != NULL)
            {
                pucBuf = pvPortMalloc( OTA_PAL_WIN_BUF_SIZE ); /*lint !e9079 Allow conversion. */

                if (pucBuf != NULL)
                {
                    /* Rewind the received file to the beginning. */
                    if (fseek(C->pFile, 0L, SEEK_SET) == 0) /*lint !e586
                                                                  * C standard library call is being used for portability. */
                    {
                        do
                        {
                            ulBytesRead = fread(pucBuf, 1, OTA_PAL_WIN_BUF_SIZE, C->pFile); /*lint !e586
                                                                                               * C standard library call is being used for portability. */
                                                                                               /* Include the file chunk in the signature validation. Zero size is OK. */
                            prvSignatureVerificationUpdate(pvSigVerifyContext, pucBuf, ulBytesRead);
                        } while (ulBytesRead > 0UL);

                        if (pdFALSE == prvSignatureVerificationFinal(pvSigVerifyContext,
                            (char*)pucSignerCert,
                            (size_t)ulSignerCertSize,
                            C->pSignature->data,
                            C->pSignature->size)) /*lint !e732 !e9034 Allow comparison in this context. */
                        {
                            eResult = OtaPalSignatureCheckFailed;
                        }
                        pvSigVerifyContext = NULL;	/* The context has been freed by prvSignatureVerificationFinal(). */
                    }
                    else
                    {
                        /* Nothing special to do. */
                    }

                    /* Free the temporary file page buffer. */
                    vPortFree(pucBuf);
                }
                else
                {
                    LogError(("Failed to allocate buffer memory.\r\n"));
                    eResult = OtaPalOutOfMemory;
                }

                /* Free the signer certificate that we now own after prvReadAndAssumeCertificate(). */
                vPortFree(pucSignerCert);
            }
            else
            {
                eResult = OtaPalBadSignerCert;
            }
        }

    return eResult;
}