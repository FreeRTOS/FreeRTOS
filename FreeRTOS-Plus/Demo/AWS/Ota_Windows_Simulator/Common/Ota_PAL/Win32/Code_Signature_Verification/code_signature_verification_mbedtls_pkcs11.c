/*
 * FreeRTOS V202012.00
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

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Ota includes. */
#include "ota_config.h"
#include "ota_pal.h"

/* Pkcs includes. */
#include "core_pkcs11.h"
#include "core_pki_utils.h"

#include "code_signature_verification.h"

/**
 * @brief The crypto algorithm used for the digital signature.
 */
#define CRYPTO_ALGORITHM          cryptoASYMMETRIC_ALGORITHM_ECDSA

/**
 * @brief The signature method used for calculating the signature.
 */
#define SIGNATURE_METHOD          cryptoHASH_ALGORITHM_SHA256

/**
 * @brief Length of block of firmware image to be read at once from flash
 * to calculate the signature.
 */
#define OTA_IMAGE_BLOCK_LENGTH    ( 4096 )

/**
 * @brief Opens a PKCS11 Session.
 *
 * @param[out] xSession Handle to the session opened.
 * @return CKR_OK if succesful.
 */
static CK_RV prvOpenPKCS11Session( CK_SESSION_HANDLE_PTR pSession );

/**
 * @brief Closes a PKCS11 Session.
 *
 * @param[out] xSession Session to be closed.
 * @return CKR_OK if succesful.
 */
static CK_RV prvClosePKCS11Session( CK_SESSION_HANDLE xSession );

/**
 * @brief Gets the handle for a certificate stored in a PKCS11 slot.
 *
 * @param[in] xSession PKCS11 session being opened.
 * @param[in] pcLabelName String containing the label name for the certificate slot.
 * @param[out] pxCertHandle The handle for the certificate slot.
 * @return CKR_OK if succesful
 */
static CK_RV prvPKCS11GetCertificateHandle( CK_SESSION_HANDLE xSession,
                                            const char * pcLabelName,
                                            CK_OBJECT_HANDLE_PTR pxCertHandle );


/**
 * @brief Verifies the firmware image signature using PKCS11 APIs.
 * Uses PKCS11 SHA256 hash APIS to calculate running checksum of the image and  verify
 * the signature using the certificate handle stored in a PKCS11 slot.
 *
 * @param[in] session PKCS11 session handle being opened.
 * @param[in] certificateHandle Certificate handle used for signature validation.
 * @param[in] pFile File context for the fimrware image.
 * @param[in] pSignature Signature as received from OTA library.
 * @param[in] signatureLength Length of the signature.
 * @return CKR_OK if the firmware image is valid.
 */
CK_RV xVerifyImageSignatureUsingPKCS11( CK_SESSION_HANDLE session,
                                        CK_OBJECT_HANDLE certificateHandle,
                                        OtaFileContext_t * pFile,
                                        uint8_t * pSignature,
                                        size_t signatureLength );

static CK_RV prvPKCS11GetCertificateHandle( CK_SESSION_HANDLE xSession,
                                            const char * pcLabelName,
                                            CK_OBJECT_HANDLE_PTR pxCertHandle )
{
    CK_ATTRIBUTE xTemplate;
    CK_RV xResult = CKR_OK;
    CK_ULONG ulCount = 0;
    CK_BBOOL xFindInit = CK_FALSE;
    CK_FUNCTION_LIST_PTR xFunctionList;

    xResult = C_GetFunctionList( &xFunctionList );

    /* Get the certificate handle. */
    if( CKR_OK == xResult )
    {
        xTemplate.type = CKA_LABEL;
        xTemplate.ulValueLen = strlen( pcLabelName ) + 1;
        xTemplate.pValue = ( char * ) pcLabelName;
        xResult = xFunctionList->C_FindObjectsInit( xSession, &xTemplate, 1 );
    }

    if( CKR_OK == xResult )
    {
        xFindInit = CK_TRUE;
        xResult = xFunctionList->C_FindObjects( xSession,
                                                ( CK_OBJECT_HANDLE_PTR ) pxCertHandle,
                                                1,
                                                &ulCount );
    }

    if( ( CK_TRUE == xFindInit ) && ( xResult == 0 ) )
    {
        xResult = xFunctionList->C_FindObjectsFinal( xSession );
    }

    return xResult;
}

static CK_RV prvOpenPKCS11Session( CK_SESSION_HANDLE_PTR pSession )
{
    /* Find the certificate */
    CK_RV xResult;
    CK_FUNCTION_LIST_PTR xFunctionList;
    CK_SLOT_ID xSlotId;
    CK_ULONG xCount = 1;

    xResult = C_GetFunctionList( &xFunctionList );

    if( CKR_OK == xResult )
    {
        xResult = xFunctionList->C_Initialize( NULL );
    }

    if( ( CKR_OK == xResult ) || ( CKR_CRYPTOKI_ALREADY_INITIALIZED == xResult ) )
    {
        xResult = xFunctionList->C_GetSlotList( CK_TRUE, &xSlotId, &xCount );
    }

    if( CKR_OK == xResult )
    {
        xResult = xFunctionList->C_OpenSession( xSlotId, CKF_SERIAL_SESSION, NULL, NULL, pSession );
    }

    return xResult;
}

static CK_RV prvClosePKCS11Session( CK_SESSION_HANDLE xSession )
{
    CK_RV xResult = CKR_OK;
    CK_FUNCTION_LIST_PTR xFunctionList;

    xResult = C_GetFunctionList( &xFunctionList );

    if( xResult == CKR_OK )
    {
        xResult = xFunctionList->C_CloseSession( xSession );
    }

    return xResult;
}

CK_RV xVerifyImageSignatureUsingPKCS11( CK_SESSION_HANDLE session,
                                        CK_OBJECT_HANDLE certificateHandle,
                                        OtaFileContext_t * pFileCtx,
                                        uint8_t * pSignature,
                                        size_t signatureLength )

{
    /* The ECDSA mechanism will be used to verify the message digest. */
    CK_MECHANISM mechanism = { CKM_ECDSA, NULL, 0 };

    /* SHA 256  will be used to calculate the digest. */
    CK_MECHANISM xDigestMechanism = { CKM_SHA256, NULL, 0 };

    /* The buffer used to hold the calculated SHA25 digest of the image. */
    CK_BYTE digestResult[ pkcs11SHA256_DIGEST_LENGTH ] = { 0 };
    CK_ULONG digestLength = pkcs11SHA256_DIGEST_LENGTH;

    CK_RV result = CKR_OK;

    CK_FUNCTION_LIST_PTR functionList;

    /* Buffer used to fetch blocks from image to calculate the digest. */
    static uint8_t buffer[ OTA_IMAGE_BLOCK_LENGTH ] = { 0 };

    size_t offset = 0, bufLength;

    result = C_GetFunctionList( &functionList );

    /* Calculate the digest of the image. */
    if( result == CKR_OK )
    {
        result = functionList->C_DigestInit( session,
                                             &xDigestMechanism );
    }

    /* Rewind the received file to the beginning. */
    fseek(pFileCtx->pFile, 0L, SEEK_SET);

    do
    {
        bufLength = fread( buffer, 1, OTA_IMAGE_BLOCK_LENGTH, ( pFileCtx->pFile ) );

        if( bufLength > 0 )
        {
            result = functionList->C_DigestUpdate( session, buffer, bufLength );

            if( result != CKR_OK )
            {
                break;
            }

            offset += bufLength;
        }
    } while( bufLength == OTA_IMAGE_BLOCK_LENGTH );

    if( bufLength < 0 )
    {
        LogError( ( "Failed to read a block of data from the image.\r\n" ) );
        result = CKR_GENERAL_ERROR;
    }

    if( result == CKR_OK )
    {
        result = functionList->C_DigestFinal( session,
                                              NULL,
                                              &digestLength );
    }

    /* Now that digestLength contains the required byte length, retrieve the
     * digest buffer.
     */
    if( result == CKR_OK )
    {
        result = functionList->C_DigestFinal( session,
                                              digestResult,
                                              &digestLength );
    }

    if( result == CKR_OK )
    {
        result = functionList->C_VerifyInit( session,
                                             &mechanism,
                                             certificateHandle );
    }

    if( result == CKR_OK )
    {
        result = functionList->C_Verify( session,
                                         digestResult,
                                         pkcs11SHA256_DIGEST_LENGTH,
                                         pSignature,
                                         signatureLength );
    }

    return result;
}


BaseType_t xValidateImageSignature( uint8_t * pFilePath,
                                    char * pCertificatePath,
                                    uint8_t * pSignature,
                                    size_t signatureLength )
{
    OtaFileContext_t fileContext = { 0 };
    CK_SESSION_HANDLE session = CKR_SESSION_HANDLE_INVALID;
    CK_RV xPKCS11Status = CKR_OK;
    CK_OBJECT_HANDLE certHandle;
    BaseType_t result = pdTRUE;
    uint8_t pkcs11Signature[ pkcs11ECDSA_P256_SIGNATURE_LENGTH ] = { 0 };

    (void)signatureLength;

    LogInfo( ( "Validating the integrity of OTA image.\r\n" ) );

    fileContext.pFilePath = pFilePath;

    if( result == pdTRUE )
    {
        if( PKI_mbedTLSSignatureToPkcs11Signature( pkcs11Signature, pSignature ) != 0 )
        {
            LogError( ( "Cannot convert signature to PKCS11 format.\r\n" ) );
            result = pdFALSE;
        }
    }

    if( result == pdTRUE )
    {
        xPKCS11Status = prvOpenPKCS11Session( &session );

        if( xPKCS11Status == CKR_OK )
        {
            xPKCS11Status = prvPKCS11GetCertificateHandle( session, pCertificatePath, &certHandle );
        }

        if( xPKCS11Status == CKR_OK )
        {
            xPKCS11Status = xVerifyImageSignatureUsingPKCS11( session,
                                                              certHandle,
                                                              &fileContext,
                                                              pkcs11Signature,
                                                              pkcs11ECDSA_P256_SIGNATURE_LENGTH );
        }

        if( xPKCS11Status != CKR_OK )
        {
            LogError( ( "Image verification failed with PKCS11 status %d\r\n", xPKCS11Status ) );
            result = pdFALSE;
        }
    }

    if( session != CKR_SESSION_HANDLE_INVALID )
    {
        ( void ) prvClosePKCS11Session( session );
    }

    return result;
}
