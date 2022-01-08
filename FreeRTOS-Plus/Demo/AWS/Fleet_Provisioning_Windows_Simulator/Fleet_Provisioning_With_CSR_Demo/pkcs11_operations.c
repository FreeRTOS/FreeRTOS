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

/* MbedTLS include. */
#include "mbedtls/ctr_drbg.h"
#include "mbedtls/entropy.h"
#include "mbedtls/entropy_poll.h"
#include "mbedtls/error.h"
#include "mbedtls/oid.h"
#include "mbedtls/pk.h"
#include "mbedtls/pk_internal.h"
#include "mbedtls/sha256.h"
#include "mbedtls/x509_crt.h"
#include "mbedtls/x509_csr.h"

/**
 * @brief Represents string to be logged when mbedTLS returned error
 * does not contain a high-level code.
 */
static const char * pcNoHighLevelMbedTlsCodeStr = "<No-High-Level-Code>";

/**
 * @brief Represents string to be logged when mbedTLS returned error
 * does not contain a low-level code.
 */
static const char * pcNoLowLevelMbedTlsCodeStr = "<No-Low-Level-Code>";

/**
 * @brief Utility for converting the high-level code in an mbedTLS error to
 * string, if the code-contains a high-level code; otherwise, using a default
 * string.
 */
#define mbedtlsHighLevelCodeOrDefault( mbedTlsCode )     \
    ( mbedtls_high_level_strerr( mbedTlsCode ) != NULL ) \
    ? mbedtls_high_level_strerr( mbedTlsCode )           \
    : pcNoHighLevelMbedTlsCodeStr

/**
 * @brief Utility for converting the level-level code in an mbedTLS error to
 * string, if the code-contains a level-level code; otherwise, using a default
 * string.
 */
#define mbedtlsLowLevelCodeOrDefault( mbedTlsCode )     \
    ( mbedtls_low_level_strerr( mbedTlsCode ) != NULL ) \
    ? mbedtls_low_level_strerr( mbedTlsCode )           \
    : pcNoLowLevelMbedTlsCodeStr

/**
 * @brief Struct containing parameters needed by the signing callback.
 */
typedef struct SigningCallbackContext
{
    CK_SESSION_HANDLE p11Session;
    CK_OBJECT_HANDLE p11PrivateKey;
} SigningCallbackContext_t;

/**
 * @brief Parameters for the signing callback. This needs to be global as
 * MbedTLS passes the key context to the signing function, so we cannot pass
 * our own.
 */
static SigningCallbackContext_t xSigningContext = { 0 };

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
 * @brief Read the specified ECDSA public key into the MbedTLS ECDSA context.
 *
 * @param[in] xP11Session The PKCS #11 session.
 * @param[in] pxEcdsaContext The context in which to store the key.
 * @param[in] xPublicKey The public key to read.
 */
static int prvExtractEcPublicKey( CK_SESSION_HANDLE xP11Session,
                                  mbedtls_ecdsa_context * pxEcdsaContext,
                                  CK_OBJECT_HANDLE xPublicKey );

/**
 * @brief MbedTLS callback for signing using the provisioned private key. Used for
 * signing the CSR.
 *
 * @param[in] pxContext Unused.
 * @param[in] xMdAlg Unused.
 * @param[in] pucHash Data to sign.
 * @param[in] xHashLen Length of #pucHash.
 * @param[out] pucSig The signature
 * @param[out] pxSigLen The length of the signature.
 * @param[in] pxRng Unused.
 * @param[in] pxRngContext Unused.
 */
static int32_t prvPrivateKeySigningCallback( void * pxContext,
                                             mbedtls_md_type_t xMdAlg,
                                             const unsigned char * pucHash,
                                             size_t xHashLen,
                                             unsigned char * pucSig,
                                             size_t * pxSigLen,
                                             int ( * pxRng )( void *, unsigned char *, size_t ),
                                             void * pxRngContext );

/**
 * @brief MbedTLS random generation callback to generate random values with
 * PKCS #11.
 *
 * @param[in] pxCtx Pointer to the PKCS #11 session handle.
 * @param[out] pucRandom Buffer to write random data to.
 * @param[in] xRandomLength Length of random data to write.
 */
static int prvRandomCallback( void * pxCtx,
                              unsigned char * pucRandom,
                              size_t xRandomLength );

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

static int prvExtractEcPublicKey( CK_SESSION_HANDLE xP11Session,
                                  mbedtls_ecdsa_context * pxEcdsaContext,
                                  CK_OBJECT_HANDLE xPublicKey )
{
    CK_ATTRIBUTE xEcTemplate = { 0 };
    int xMbedtlsRet = -1;
    CK_RV xPkcs11ret = CKR_OK;
    CK_BYTE pxEcPoint[ 67 ] = { 0 };
    CK_FUNCTION_LIST_PTR xP11FunctionList;

    mbedtls_ecdsa_init( pxEcdsaContext );
    mbedtls_ecp_group_init( &( pxEcdsaContext->grp ) );

    xPkcs11ret = C_GetFunctionList( &xP11FunctionList );

    if( xPkcs11ret != CKR_OK )
    {
        LogError( ( "Could not get a PKCS #11 function pointer." ) );
    }
    else
    {
        xEcTemplate.type = CKA_EC_POINT;
        xEcTemplate.pValue = pxEcPoint;
        xEcTemplate.ulValueLen = sizeof( pxEcPoint );
        xPkcs11ret = xP11FunctionList->C_GetAttributeValue( xP11Session, xPublicKey, &xEcTemplate, 1 );

        if( xPkcs11ret != CKR_OK )
        {
            LogError( ( "Failed to extract EC public key. Could not get attribute value. "
                        "C_GetAttributeValue failed with %lu.", xPkcs11ret ) );
        }
    }

    if( xPkcs11ret == CKR_OK )
    {
        xMbedtlsRet = mbedtls_ecp_group_load( &( pxEcdsaContext->grp ), MBEDTLS_ECP_DP_SECP256R1 );

        if( xMbedtlsRet != 0 )
        {
            LogError( ( "Failed creating an EC key. "
                        "mbedtls_ecp_group_load failed: MbedTLS"
                        "error = %s : %s.",
                        mbedtlsHighLevelCodeOrDefault( xMbedtlsRet ),
                        mbedtlsLowLevelCodeOrDefault( xMbedtlsRet ) ) );
            xPkcs11ret = CKR_FUNCTION_FAILED;
        }
        else
        {
            xMbedtlsRet = mbedtls_ecp_point_read_binary( &( pxEcdsaContext->grp ), &( pxEcdsaContext->Q ), &pxEcPoint[ 2 ], xEcTemplate.ulValueLen - 2 );

            if( xMbedtlsRet != 0 )
            {
                LogError( ( "Failed creating an EC key. "
                            "mbedtls_ecp_group_load failed: MbedTLS"
                            "error = %s : %s.",
                            mbedtlsHighLevelCodeOrDefault( xMbedtlsRet ),
                            mbedtlsLowLevelCodeOrDefault( xMbedtlsRet ) ) );
                xPkcs11ret = CKR_FUNCTION_FAILED;
            }
        }
    }

    return xMbedtlsRet;
}

/*-----------------------------------------------------------*/

static int32_t prvPrivateKeySigningCallback( void * pxContext,
                                             mbedtls_md_type_t xMdAlg,
                                             const unsigned char * pucHash,
                                             size_t xHashLen,
                                             unsigned char * pucSig,
                                             size_t * pxSigLen,
                                             int ( * pxRng )( void *, unsigned char *, size_t ),
                                             void * pxRngContext )
{
    CK_RV xRet = CKR_OK;
    int32_t usResult = 0;
    CK_MECHANISM xMech = { 0 };
    CK_BYTE pxToBeSigned[ 256 ];
    CK_ULONG xToBeSignedLen = sizeof( pxToBeSigned );
    CK_FUNCTION_LIST_PTR xFunctionList = NULL;

    /* Unreferenced parameters. */
    ( void ) ( pxContext );
    ( void ) ( pxRng );
    ( void ) ( pxRngContext );
    ( void ) ( xMdAlg );

    /* Sanity check buffer length. */
    if( xHashLen > sizeof( pxToBeSigned ) )
    {
        xRet = CKR_ARGUMENTS_BAD;
    }

    xMech.mechanism = CKM_ECDSA;
    memcpy( pxToBeSigned, pucHash, xHashLen );
    xToBeSignedLen = xHashLen;

    if( xRet == CKR_OK )
    {
        xRet = C_GetFunctionList( &xFunctionList );
    }

    if( xRet == CKR_OK )
    {
        xRet = xFunctionList->C_SignInit( xSigningContext.p11Session, &xMech,
                                          xSigningContext.p11PrivateKey );
    }

    if( xRet == CKR_OK )
    {
        *pxSigLen = sizeof( pxToBeSigned );
        xRet = xFunctionList->C_Sign( xSigningContext.p11Session, pxToBeSigned,
                                      xToBeSignedLen, pucSig, ( CK_ULONG_PTR ) pxSigLen );
    }

    if( xRet == CKR_OK )
    {
        /* PKCS #11 for P256 returns a 64-byte signature with 32 bytes for R and 32
         * bytes for S. This must be converted to an ASN.1 encoded array. */
        if( *pxSigLen != pkcs11ECDSA_P256_SIGNATURE_LENGTH )
        {
            xRet = CKR_FUNCTION_FAILED;
            LogError( ( "Failed to sign message using PKCS #11. Expected signature "
                        "length of %lu, but received %lu.",
                        ( unsigned long ) pkcs11ECDSA_P256_SIGNATURE_LENGTH,
                        ( unsigned long ) *pxSigLen ) );
        }

        if( xRet == CKR_OK )
        {
            PKI_pkcs11SignatureTombedTLSSignature( pucSig, pxSigLen );
        }
    }

    if( xRet != CKR_OK )
    {
        LogError( ( "Failed to sign message using PKCS #11 with error code %lu.", xRet ) );
        usResult = -1;
    }

    return usResult;
}

/*-----------------------------------------------------------*/

static int prvRandomCallback( void * pxCtx,
                              unsigned char * pucRandom,
                              size_t xRandomLength )
{
    CK_SESSION_HANDLE * pxP11Session = ( CK_SESSION_HANDLE * ) pxCtx;
    CK_RV xRes;
    CK_FUNCTION_LIST_PTR xP11FunctionList;

    xRes = C_GetFunctionList( &xP11FunctionList );

    if( xRes != CKR_OK )
    {
        LogError( ( "Failed to generate a random number in RNG callback. Could not get a "
                    "PKCS #11 function pointer." ) );
    }
    else
    {
        xRes = xP11FunctionList->C_GenerateRandom( *pxP11Session, pucRandom, xRandomLength );

        if( xRes != CKR_OK )
        {
            LogError( ( "Failed to generate a random number in RNG callback. "
                        "C_GenerateRandom failed with %lu.", ( unsigned long ) xRes ) );
        }
    }

    return ( int ) xRes;
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
    mbedtls_pk_info_t xPrivKeyInfo;
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
            mbedtls_pk_init( &xPrivKey );
        }

        if( ulMbedtlsRet == 0 )
        {
            ulMbedtlsRet = prvExtractEcPublicKey( xP11Session, &xEcdsaContext, xPubKeyHandle );
        }

        if( ulMbedtlsRet == 0 )
        {
            xSigningContext.p11Session = xP11Session;
            xSigningContext.p11PrivateKey = xPrivKeyHandle;

            memcpy( &xPrivKeyInfo, pxHeader, sizeof( mbedtls_pk_info_t ) );

            xPrivKeyInfo.sign_func = prvPrivateKeySigningCallback;
            xPrivKey.pk_info = &xPrivKeyInfo;
            xPrivKey.pk_ctx = &xEcdsaContext;

            mbedtls_x509write_csr_set_key( &xReq, &xPrivKey );

            ulMbedtlsRet = mbedtls_x509write_csr_pem( &xReq, ( unsigned char * ) pcCsrBuffer,
                                                      xCsrBufferLength, &prvRandomCallback,
                                                      &xP11Session );
        }

        mbedtls_x509write_csr_free( &xReq );
        mbedtls_ecdsa_free( &xEcdsaContext );
        mbedtls_ecp_group_free( &( xEcdsaContext.grp ) );
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
