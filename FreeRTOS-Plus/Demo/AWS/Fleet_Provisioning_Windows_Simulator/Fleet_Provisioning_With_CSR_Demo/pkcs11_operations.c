/*
 * FreeRTOS V202212.00
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
 * @file pkcs11_operations.c
 *
 * @brief This file provides wrapper functions for PKCS11 operations.
 */

/* Standard includes. */
#include <errno.h>
#include <assert.h>

/* Config include. */
#include "demo_config.h"

/* Interface include. */
#include "pkcs11_operations.h"

/* PKCS #11 include. */
#include "core_pkcs11_config.h"
#include "core_pki_utils.h"
#include "mbedtls_utils.h"
#include "mbedtls_pkcs11.h"

/* MbedTLS include. */
#include "mbedtls/error.h"
#include "mbedtls/oid.h"
#include "mbedtls/pk.h"
#include "mbedtls/sha256.h"
#include "mbedtls/x509_crt.h"
#include "mbedtls/x509_csr.h"

/*-----------------------------------------------------------*/

/**
 * @brief Delete the specified crypto object from storage.
 *
 * @param[in] xSession The PKCS #11 session.
 * @param[in] pxPkcsLabelsPtr The list of labels to remove.
 * @param[in] pxClass The list of corresponding classes.
 * @param[in] xCount The length of #pxPkcsLabelsPtr and #pxClass.
 */
static CK_RV prvDestroyProvidedObjects( CK_SESSION_HANDLE xSession,
                                        CK_BYTE_PTR * pxPkcsLabelsPtr,
                                        CK_OBJECT_CLASS * pxClass,
                                        CK_ULONG xCount );

/**
 * @brief Generate a new ECDSA key pair using PKCS #11.
 *
 * @param[in] xSession The PKCS #11 session.
 * @param[in] pcPrivateKeyLabel The label to store the private key.
 * @param[in] pcPublicKeyLabel The label to store the public key.
 * @param[out] xPrivateKeyHandlePtr The handle of the private key.
 * @param[out] xPublicKeyHandlePtr The handle of the public key.
 */
static CK_RV prvGenerateKeyPairEC( CK_SESSION_HANDLE xSession,
                                   const char * pcPrivateKeyLabel,
                                   const char * pcPublicKeyLabel,
                                   CK_OBJECT_HANDLE_PTR xPrivateKeyHandlePtr,
                                   CK_OBJECT_HANDLE_PTR xPublicKeyHandlePtr );

/*-----------------------------------------------------------*/

static CK_RV prvDestroyProvidedObjects( CK_SESSION_HANDLE xSession,
                                        CK_BYTE_PTR * pxPkcsLabelsPtr,
                                        CK_OBJECT_CLASS * pxClass,
                                        CK_ULONG xCount )
{
    CK_RV xResult;
    CK_FUNCTION_LIST_PTR xFunctionList;
    CK_OBJECT_HANDLE xObjectHandle;
    CK_BYTE * pxLabelPtr;
    CK_ULONG xIndex = 0;

    xResult = C_GetFunctionList( &xFunctionList );

    if( xResult != CKR_OK )
    {
        LogError( ( "Could not get a PKCS #11 function pointer." ) );
    }
    else
    {
        for( xIndex = 0; xIndex < xCount; xIndex++ )
        {
            pxLabelPtr = pxPkcsLabelsPtr[ xIndex ];

            xResult = xFindObjectWithLabelAndClass( xSession, ( char * ) pxLabelPtr,
                                                    strnlen( ( char * ) pxLabelPtr, pkcs11configMAX_LABEL_LENGTH ),
                                                    pxClass[ xIndex ], &xObjectHandle );

            while( ( xResult == CKR_OK ) && ( xObjectHandle != CK_INVALID_HANDLE ) )
            {
                xResult = xFunctionList->C_DestroyObject( xSession, xObjectHandle );

                /* PKCS #11 allows a module to maintain multiple objects with the same
                 * label and type. The intent of this loop is to try to delete all of
                 * them. However, to avoid getting stuck, we won't try to find another
                 * object of the same label/type if the previous delete failed. */
                if( xResult == CKR_OK )
                {
                    xResult = xFindObjectWithLabelAndClass( xSession, ( char * ) pxLabelPtr,
                                                            strnlen( ( char * ) pxLabelPtr, pkcs11configMAX_LABEL_LENGTH ),
                                                            pxClass[ xIndex ], &xObjectHandle );
                }
                else
                {
                    break;
                }
            }
        }
    }

    return xResult;
}

/*-----------------------------------------------------------*/

static CK_RV prvGenerateKeyPairEC( CK_SESSION_HANDLE xSession,
                                   const char * pcPrivateKeyLabel,
                                   const char * pcPublicKeyLabel,
                                   CK_OBJECT_HANDLE_PTR xPrivateKeyHandlePtr,
                                   CK_OBJECT_HANDLE_PTR xPublicKeyHandlePtr )
{
    CK_RV xResult;
    CK_MECHANISM xMechanism = { CKM_EC_KEY_PAIR_GEN, NULL_PTR, 0 };
    CK_FUNCTION_LIST_PTR xFunctionList;
    CK_BYTE pxEcParams[] = pkcs11DER_ENCODED_OID_P256; /* prime256v1 */
    CK_KEY_TYPE xKeyType = CKK_EC;

    CK_BBOOL xTrueObject = CK_TRUE;
    CK_ATTRIBUTE pxPublicKeyTemplate[] =
    {
        { CKA_KEY_TYPE,  NULL /* &keyType */,         sizeof( xKeyType )             },
        { CKA_VERIFY,    NULL /* &trueObject */,      sizeof( xTrueObject )          },
        { CKA_EC_PARAMS, NULL /* ecParams */,         sizeof( pxEcParams )           },
        { CKA_LABEL,     ( void * ) pcPublicKeyLabel, strnlen( pcPublicKeyLabel, pkcs11configMAX_LABEL_LENGTH )}
    };

    /* Aggregate initializers must not use the address of an automatic variable. */
    pxPublicKeyTemplate[ 0 ].pValue = &xKeyType;
    pxPublicKeyTemplate[ 1 ].pValue = &xTrueObject;
    pxPublicKeyTemplate[ 2 ].pValue = &pxEcParams;

    CK_ATTRIBUTE privateKeyTemplate[] =
    {
        { CKA_KEY_TYPE, NULL /* &keyType */,          sizeof( xKeyType )             },
        { CKA_TOKEN,    NULL /* &trueObject */,       sizeof( xTrueObject )          },
        { CKA_PRIVATE,  NULL /* &trueObject */,       sizeof( xTrueObject )          },
        { CKA_SIGN,     NULL /* &trueObject */,       sizeof( xTrueObject )          },
        { CKA_LABEL,    ( void * ) pcPrivateKeyLabel, strnlen( pcPrivateKeyLabel, pkcs11configMAX_LABEL_LENGTH )}
    };

    /* Aggregate initializers must not use the address of an automatic variable. */
    privateKeyTemplate[ 0 ].pValue = &xKeyType;
    privateKeyTemplate[ 1 ].pValue = &xTrueObject;
    privateKeyTemplate[ 2 ].pValue = &xTrueObject;
    privateKeyTemplate[ 3 ].pValue = &xTrueObject;

    xResult = C_GetFunctionList( &xFunctionList );

    if( xResult != CKR_OK )
    {
        LogError( ( "Could not get a PKCS #11 function pointer." ) );
    }
    else
    {
        xResult = xFunctionList->C_GenerateKeyPair( xSession,
                                                    &xMechanism,
                                                    pxPublicKeyTemplate,
                                                    sizeof( pxPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                                    privateKeyTemplate, sizeof( privateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                                    xPublicKeyHandlePtr,
                                                    xPrivateKeyHandlePtr );
    }

    return xResult;
}

/*-----------------------------------------------------------*/

bool xGenerateKeyAndCsr( CK_SESSION_HANDLE xP11Session,
                         const char * pcPrivKeyLabel,
                         const char * pcPubKeyLabel,
                         char * pcCsrBuffer,
                         size_t xCsrBufferLength,
                         size_t * pxOutCsrLength )
{
    CK_OBJECT_HANDLE xPrivKeyHandle;
    CK_OBJECT_HANDLE xPubKeyHandle;
    CK_RV xPkcs11Ret = CKR_OK;
    mbedtls_pk_context xPrivKey;
    mbedtls_ecdsa_context xEcdsaContext;
    mbedtls_x509write_csr xReq;
    int32_t ulMbedtlsRet = -1;
    const mbedtls_pk_info_t * pxHeader = mbedtls_pk_info_from_type( MBEDTLS_PK_ECKEY );

    configASSERT( pcPrivKeyLabel != NULL );
    configASSERT( pcPubKeyLabel != NULL );
    configASSERT( pcCsrBuffer != NULL );
    configASSERT( pxOutCsrLength != NULL );

    xPkcs11Ret = prvGenerateKeyPairEC( xP11Session,
                                       pcPrivKeyLabel,
                                       pcPubKeyLabel,
                                       &xPrivKeyHandle,
                                       &xPubKeyHandle );

    if( xPkcs11Ret == CKR_OK )
    {
        xPkcs11Ret = xPKCS11_initMbedtlsPkContext( &xPrivKey, xP11Session, xPrivKeyHandle );
    }

    if( xPkcs11Ret == CKR_OK )
    {
        mbedtls_x509write_csr_init( &xReq );
        mbedtls_x509write_csr_set_md_alg( &xReq, MBEDTLS_MD_SHA256 );

        ulMbedtlsRet = mbedtls_x509write_csr_set_key_usage( &xReq, MBEDTLS_X509_KU_DIGITAL_SIGNATURE );

        if( ulMbedtlsRet == 0 )
        {
            ulMbedtlsRet = mbedtls_x509write_csr_set_ns_cert_type( &xReq, MBEDTLS_X509_NS_CERT_TYPE_SSL_CLIENT );
        }

        if( ulMbedtlsRet == 0 )
        {
            ulMbedtlsRet = mbedtls_x509write_csr_set_subject_name( &xReq, democonfigCSR_SUBJECT_NAME );
        }

        if( ulMbedtlsRet == 0 )
        {
            mbedtls_x509write_csr_set_key( &xReq, &xPrivKey );

            ulMbedtlsRet = mbedtls_x509write_csr_pem( &xReq, ( unsigned char * ) pcCsrBuffer,
                                                      xCsrBufferLength, &lMbedCryptoRngCallbackPKCS11,
                                                      &xP11Session );
        }

        mbedtls_x509write_csr_free( &xReq );

        mbedtls_pk_free( &xPrivKey );
    }

    *pxOutCsrLength = strlen( pcCsrBuffer );

    return( ulMbedtlsRet == 0 );
}

/*-----------------------------------------------------------*/

bool xLoadCertificate( CK_SESSION_HANDLE xP11Session,
                       const char * pcCertificate,
                       const char * pcLabel,
                       size_t xCertificateLength )
{
    PKCS11_CertificateTemplate_t xCertificateTemplate;
    CK_OBJECT_CLASS xCertificateClass = CKO_CERTIFICATE;
    CK_CERTIFICATE_TYPE xCertificateType = CKC_X_509;
    CK_FUNCTION_LIST_PTR xFunctionList = NULL;
    CK_RV xResult = CKR_OK;
    uint8_t * pucDerObject = NULL;
    int32_t ulConversion = 0;
    size_t xDerLen = 0;
    CK_BBOOL xTokenStorage = CK_TRUE;
    CK_BYTE pxSubject[] = "TestSubject";
    CK_OBJECT_HANDLE xObjectHandle = CK_INVALID_HANDLE;

    configASSERT( pcLabel != NULL );

    if( pcCertificate == NULL )
    {
        LogError( ( "Certificate cannot be null." ) );
        xResult = CKR_ATTRIBUTE_VALUE_INVALID;
    }

    if( xResult == CKR_OK )
    {
        /* Convert the certificate to DER format from PEM. The DER key should
         * be about 3/4 the size of the PEM key, so mallocing the PEM key size
         * is sufficient. */
        pucDerObject = ( uint8_t * ) malloc( xCertificateLength + 1 );
        xDerLen = xCertificateLength + 1;

        if( pucDerObject != NULL )
        {
            ulConversion = convert_pem_to_der( ( unsigned char * ) pcCertificate,
                                               xCertificateLength + 1,
                                               pucDerObject, &xDerLen );

            if( 0 != ulConversion )
            {
                LogError( ( "Failed to convert provided certificate." ) );
                xResult = CKR_ARGUMENTS_BAD;
            }
        }
        else
        {
            LogError( ( "Failed to allocate buffer for converting certificate to DER." ) );
            xResult = CKR_HOST_MEMORY;
        }
    }

    if( xResult == CKR_OK )
    {
        xResult = C_GetFunctionList( &xFunctionList );

        if( xResult != CKR_OK )
        {
            LogError( ( "Could not get a PKCS #11 function pointer." ) );
        }
    }

    if( xResult == CKR_OK )
    {
        /* Initialize the client certificate template. */
        xCertificateTemplate.xObjectClass.type = CKA_CLASS;
        xCertificateTemplate.xObjectClass.pValue = &xCertificateClass;
        xCertificateTemplate.xObjectClass.ulValueLen = sizeof( xCertificateClass );
        xCertificateTemplate.xSubject.type = CKA_SUBJECT;
        xCertificateTemplate.xSubject.pValue = pxSubject;
        xCertificateTemplate.xSubject.ulValueLen = strlen( ( const char * ) pxSubject );
        xCertificateTemplate.xValue.type = CKA_VALUE;
        xCertificateTemplate.xValue.pValue = pucDerObject;
        xCertificateTemplate.xValue.ulValueLen = xDerLen;
        xCertificateTemplate.xLabel.type = CKA_LABEL;
        xCertificateTemplate.xLabel.pValue = ( CK_VOID_PTR ) pcLabel;
        xCertificateTemplate.xLabel.ulValueLen = strnlen( pcLabel, pkcs11configMAX_LABEL_LENGTH );
        xCertificateTemplate.xCertificateType.type = CKA_CERTIFICATE_TYPE;
        xCertificateTemplate.xCertificateType.pValue = &xCertificateType;
        xCertificateTemplate.xCertificateType.ulValueLen = sizeof( CK_CERTIFICATE_TYPE );
        xCertificateTemplate.xTokenObject.type = CKA_TOKEN;
        xCertificateTemplate.xTokenObject.pValue = &xTokenStorage;
        xCertificateTemplate.xTokenObject.ulValueLen = sizeof( xTokenStorage );

        /* Best effort clean-up of the existing object, if it exists. */
        prvDestroyProvidedObjects( xP11Session, ( CK_BYTE_PTR * ) &pcLabel, &xCertificateClass, 1 );

        /* Create an object using the encoded client certificate. */
        LogInfo( ( "Writing certificate into label \"%s\".", pcLabel ) );

        xResult = xFunctionList->C_CreateObject( xP11Session,
                                                 ( CK_ATTRIBUTE_PTR ) &xCertificateTemplate,
                                                 sizeof( xCertificateTemplate ) / sizeof( CK_ATTRIBUTE ),
                                                 &xObjectHandle );
    }

    if( pucDerObject != NULL )
    {
        free( pucDerObject );
    }

    return( xResult == CKR_OK );
}

/*-----------------------------------------------------------*/

bool xPkcs11CloseSession( CK_SESSION_HANDLE xP11Session )
{
    CK_RV xResult = CKR_OK;
    CK_FUNCTION_LIST_PTR xFunctionList = NULL;

    xResult = C_GetFunctionList( &xFunctionList );

    if( xResult == CKR_OK )
    {
        xResult = xFunctionList->C_CloseSession( xP11Session );
    }

    if( xResult == CKR_OK )
    {
        xResult = xFunctionList->C_Finalize( NULL );
    }

    return( xResult == CKR_OK );
}

/*-----------------------------------------------------------*/
