/*
 * FreeRTOS V202111.00
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
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
 * @brief Size of buffer in which to hold the certificate signing request (CSR).
 */
#define pkcs11opCLAIM_CERT_BUFFER_LENGTH           2048

/**
 * @brief Size of buffer in which to hold the certificate signing request (CSR).
 */
#define pkcs11opCLAIM_PRIVATE_KEY_BUFFER_LENGTH    2048

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

/* Length parameters for importing RSA-2048 private keys. */
#define MODULUS_LENGTH        pkcs11RSA_2048_MODULUS_BITS / 8
#define E_LENGTH              3
#define D_LENGTH              pkcs11RSA_2048_MODULUS_BITS / 8
#define PRIME_1_LENGTH        128
#define PRIME_2_LENGTH        128
#define EXPONENT_1_LENGTH     128
#define EXPONENT_2_LENGTH     128
#define COEFFICIENT_LENGTH    128

#define EC_PARAMS_LENGTH      10
#define EC_D_LENGTH           32

/**
 * @brief Struct for holding parsed RSA-2048 private keys.
 */
typedef struct RsaParams_t
{
    CK_BYTE modulus[ MODULUS_LENGTH + 1 ];
    CK_BYTE e[ E_LENGTH + 1 ];
    CK_BYTE d[ D_LENGTH + 1 ];
    CK_BYTE prime1[ PRIME_1_LENGTH + 1 ];
    CK_BYTE prime2[ PRIME_2_LENGTH + 1 ];
    CK_BYTE exponent1[ EXPONENT_1_LENGTH + 1 ];
    CK_BYTE exponent2[ EXPONENT_2_LENGTH + 1 ];
    CK_BYTE coefficient[ COEFFICIENT_LENGTH + 1 ];
} RsaParams_t;

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
 * @brief Reads a file into the given buffer.
 *
 * @param[in] pcPath Path of the file.
 * @param[out] pcBuffer Buffer to read file contents into.
 * @param[in] xBufferLength Length of #pcBuffer.
 * @param[out] pxOutWrittenLength Length of contents written to #pcBuffer.
 */
static bool prvReadFile( const char * pcPath,
                         char * pcBuffer,
                         size_t xBufferLength,
                         size_t * pxOutWrittenLength );

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
 * @brief Import the specified ECDSA private key into storage.
 *
 * @param[in] xSession The PKCS #11 session.
 * @param[in] pcLabel The label to store the key.
 * @param[in] pxMbedPkContext The private key to store.
 */
static CK_RV prvProvisionPrivateECKey( CK_SESSION_HANDLE xSession,
                                       const char * pcLabel,
                                       mbedtls_pk_context * pxMbedPkContext );



/**
 * @brief Import the specified RSA private key into storage.
 *
 * @param[in] xSession The PKCS #11 session.
 * @param[in] pcLabel The label to store the key.
 * @param[in] pxMbedPkContext The private key to store.
 */
static CK_RV prvProvisionPrivateRSAKey( CK_SESSION_HANDLE xSession,
                                        const char * pcLabel,
                                        mbedtls_pk_context * pxMbedPkContext );


/**
 * @brief Import the specified private key into storage.
 *
 * @param[in] xSession The PKCS #11 session.
 * @param[in] pcPrivateKey The private key to store, in PEM format.
 * @param[in] xPrivateKeyLength The length of the key, including null terminator.
 * @param[in] pcLabel The label to store the key.
 */
static CK_RV prvProvisionPrivateKey( CK_SESSION_HANDLE xSession,
                                     const char * pcPrivateKey,
                                     size_t xPrivateKeyLength,
                                     const char * pcLabel );

/**
 * @brief Import the specified X.509 client certificate into storage.
 *
 * @param[in] xSession The PKCS #11 session.
 * @param[in] pcCertificate The certificate to store, in PEM format.
 * @param[in] xCertificateLength The length of the certificate, including the null terminator.
 * @param[in] pcLabel The label to store the certificate.
 */
static CK_RV prvProvisionCertificate( CK_SESSION_HANDLE xSession,
                                      const char * pcCertificate,
                                      size_t xCertificateLength,
                                      const char * pcLabel );

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

static bool prvReadFile( const char * pcPath,
                         char * pcBuffer,
                         size_t xBufferLength,
                         size_t * pxOutWrittenLength )
{
    FILE * pxFile;
    size_t xLength = 0;
    bool xStatus = true;

    /* Get the file descriptor for the CSR file. */
    pxFile = fopen( pcPath, "rb" );

    if( pxFile == NULL )
    {
        LogError( ( "Error opening file at path: %s. Error: %s.",
                    pcPath, strerror( errno ) ) );
        xStatus = false;
    }
    else
    {
        int result;
        /* Seek to the end of the file, so that we can get the file size. */
        result = fseek( pxFile, 0L, SEEK_END );

        if( result == -1 )
        {
            LogError( ( "Failed while moving to end of file. Path: %s. Error: %s.",
                        pcPath, strerror( errno ) ) );
            xStatus = false;
        }
        else
        {
            long lenResult = -1;
            /* Get the current position which is the file size. */
            lenResult = ftell( pxFile );

            if( lenResult == -1 )
            {
                LogError( ( "Failed to get length of file. Path: %s. Error: %s.", pcPath,
                            strerror( errno ) ) );
                xStatus = false;
            }
            else
            {
                xLength = ( size_t ) lenResult;
            }
        }

        if( xStatus == true )
        {
            if( xLength > xBufferLength )
            {
                LogError( ( "Buffer too small for file. Buffer size: %ld. Required size: %ld.",
                            xBufferLength, xLength ) );
                xStatus = false;
            }
        }

        if( xStatus == true )
        {
            /* Return to the beginning of the file. */
            result = fseek( pxFile, 0L, SEEK_SET );

            if( result == -1 )
            {
                LogError( ( "Failed to move to beginning of file. Path: %s. Error: %s.",
                            pcPath, strerror( errno ) ) );
                xStatus = false;
            }
        }

        if( xStatus == true )
        {
            size_t written = 0;
            /* Read the CSR into our buffer. */
            written = fread( pcBuffer, 1, xLength, pxFile );

            if( written != xLength )
            {
                LogError( ( "Failed reading file. Path: %s. Error: %s.", pcPath,
                            strerror( errno ) ) );
                xStatus = false;
            }
            else
            {
                *pxOutWrittenLength = xLength;
            }
        }

        fclose( pxFile );
    }

    return xStatus;
}

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
                                                    strlen( ( char * ) pxLabelPtr ),
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
                                                            strlen( ( char * ) pxLabelPtr ),
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

static CK_RV prvProvisionPrivateECKey( CK_SESSION_HANDLE xSession,
                                       const char * pcLabel,
                                       mbedtls_pk_context * pxMbedPkContext )
{
    CK_RV xResult = CKR_OK;
    CK_FUNCTION_LIST_PTR xFunctionList = NULL;
    CK_BYTE * pxDPtr = NULL;        /* Private value D. */
    CK_BYTE * pxEcParamsPtr = NULL; /* DER-encoding of an ANSI X9.62 Parameters value */
    int xMbedResult = 0;
    CK_BBOOL xTrueObject = CK_TRUE;
    CK_KEY_TYPE xPrivateKeyType = CKK_EC;
    CK_OBJECT_CLASS xPrivateKeyClass = CKO_PRIVATE_KEY;
    CK_OBJECT_HANDLE xObjectHandle = CK_INVALID_HANDLE;
    mbedtls_ecp_keypair * pxKeyPair = ( mbedtls_ecp_keypair * ) pxMbedPkContext->pk_ctx;

    xResult = C_GetFunctionList( &xFunctionList );

    if( xResult != CKR_OK )
    {
        LogError( ( "Could not get a PKCS #11 function pointer." ) );
    }
    else
    {
        pxDPtr = ( CK_BYTE * ) malloc( EC_D_LENGTH );

        if( pxDPtr == NULL )
        {
            xResult = CKR_HOST_MEMORY;
        }
    }

    if( xResult == CKR_OK )
    {
        xMbedResult = mbedtls_mpi_write_binary( &( pxKeyPair->d ), pxDPtr, EC_D_LENGTH );

        if( xMbedResult != 0 )
        {
            LogError( ( "Failed to parse EC private key components." ) );
            xResult = CKR_ATTRIBUTE_VALUE_INVALID;
        }
    }

    if( xResult == CKR_OK )
    {
        if( pxKeyPair->grp.id == MBEDTLS_ECP_DP_SECP256R1 )
        {
            pxEcParamsPtr = ( CK_BYTE * ) ( "\x06\x08" MBEDTLS_OID_EC_GRP_SECP256R1 );
        }
        else
        {
            xResult = CKR_CURVE_NOT_SUPPORTED;
        }
    }

    if( xResult == CKR_OK )
    {
        CK_ATTRIBUTE privateKeyTemplate[] =
        {
            { CKA_CLASS,     NULL /* &privateKeyClass*/, sizeof( CK_OBJECT_CLASS )      },
            { CKA_KEY_TYPE,  NULL /* &privateKeyType*/,  sizeof( CK_KEY_TYPE )          },
            { CKA_LABEL,     ( void * ) pcLabel,         ( CK_ULONG ) strlen( pcLabel ) },
            { CKA_TOKEN,     NULL /* &trueObject*/,      sizeof( CK_BBOOL )             },
            { CKA_SIGN,      NULL /* &trueObject*/,      sizeof( CK_BBOOL )             },
            { CKA_EC_PARAMS, NULL /* ecParamsPtr*/,      EC_PARAMS_LENGTH               },
            { CKA_VALUE,     NULL /* DPtr*/,             EC_D_LENGTH                    }
        };

        /* Aggregate initializers must not use the address of an automatic variable. */
        privateKeyTemplate[ 0 ].pValue = &xPrivateKeyClass;
        privateKeyTemplate[ 1 ].pValue = &xPrivateKeyType;
        privateKeyTemplate[ 3 ].pValue = &xTrueObject;
        privateKeyTemplate[ 4 ].pValue = &xTrueObject;
        privateKeyTemplate[ 5 ].pValue = pxEcParamsPtr;
        privateKeyTemplate[ 6 ].pValue = pxDPtr;

        xResult = xFunctionList->C_CreateObject( xSession,
                                                 ( CK_ATTRIBUTE_PTR ) &privateKeyTemplate,
                                                 sizeof( privateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                                 &xObjectHandle );
    }

    if( pxDPtr != NULL )
    {
        free( pxDPtr );
    }

    return xResult;
}

/*-----------------------------------------------------------*/

static CK_RV prvProvisionPrivateRSAKey( CK_SESSION_HANDLE xSession,
                                        const char * pcLabel,
                                        mbedtls_pk_context * pxMbedPkContext )
{
    CK_RV xResult = CKR_OK;
    CK_FUNCTION_LIST_PTR xFunctionList = NULL;
    int xMbedResult = 0;
    CK_KEY_TYPE xPrivateKeyType = CKK_RSA;
    mbedtls_rsa_context * pxRsaContext = ( mbedtls_rsa_context * ) pxMbedPkContext->pk_ctx;
    CK_OBJECT_CLASS xPrivateKeyClass = CKO_PRIVATE_KEY;
    RsaParams_t * pxRsaParams = NULL;
    CK_BBOOL xTrueObject = CK_TRUE;
    CK_OBJECT_HANDLE xObjectHandle = CK_INVALID_HANDLE;

    xResult = C_GetFunctionList( &xFunctionList );

    if( xResult != CKR_OK )
    {
        LogError( ( "Could not get a PKCS #11 function pointer." ) );
    }
    else
    {
        pxRsaParams = ( RsaParams_t * ) malloc( sizeof( RsaParams_t ) );

        if( pxRsaParams == NULL )
        {
            xResult = CKR_HOST_MEMORY;
        }
    }

    if( xResult == CKR_OK )
    {
        memset( pxRsaParams, 0, sizeof( RsaParams_t ) );

        xMbedResult = mbedtls_rsa_export_raw( pxRsaContext,
                                              pxRsaParams->modulus, MODULUS_LENGTH + 1,
                                              pxRsaParams->prime1, PRIME_1_LENGTH + 1,
                                              pxRsaParams->prime2, PRIME_2_LENGTH + 1,
                                              pxRsaParams->d, D_LENGTH + 1,
                                              pxRsaParams->e, E_LENGTH + 1 );

        if( xMbedResult != 0 )
        {
            LogError( ( "Failed to parse RSA private key components." ) );
            xResult = CKR_ATTRIBUTE_VALUE_INVALID;
        }

        /* Export Exponent 1, Exponent 2, Coefficient. */
        xMbedResult |= mbedtls_mpi_write_binary( ( mbedtls_mpi const * ) &pxRsaContext->DP, pxRsaParams->exponent1, EXPONENT_1_LENGTH + 1 );
        xMbedResult |= mbedtls_mpi_write_binary( ( mbedtls_mpi const * ) &pxRsaContext->DQ, pxRsaParams->exponent2, EXPONENT_2_LENGTH + 1 );
        xMbedResult |= mbedtls_mpi_write_binary( ( mbedtls_mpi const * ) &pxRsaContext->QP, pxRsaParams->coefficient, COEFFICIENT_LENGTH + 1 );

        if( xMbedResult != 0 )
        {
            LogError( ( "Failed to parse RSA private key Chinese Remainder Theorem variables." ) );
            xResult = CKR_ATTRIBUTE_VALUE_INVALID;
        }
    }

    if( xResult == CKR_OK )
    {
        /* When importing the fields, the pointer is incremented by 1
         * to remove the leading 0 padding (if it existed) and the original field
         * length is used */

        CK_ATTRIBUTE privateKeyTemplate[] =
        {
            { CKA_CLASS,            NULL /* &privateKeyClass */,  sizeof( CK_OBJECT_CLASS )      },
            { CKA_KEY_TYPE,         NULL /* &privateKeyType */,   sizeof( CK_KEY_TYPE )          },
            { CKA_LABEL,            ( void * ) pcLabel,           ( CK_ULONG ) strlen( pcLabel ) },
            { CKA_TOKEN,            NULL /* &trueObject */,       sizeof( CK_BBOOL )             },
            { CKA_SIGN,             NULL /* &trueObject */,       sizeof( CK_BBOOL )             },
            { CKA_MODULUS,          pxRsaParams->modulus + 1,     MODULUS_LENGTH                 },
            { CKA_PRIVATE_EXPONENT, pxRsaParams->d + 1,           D_LENGTH                       },
            { CKA_PUBLIC_EXPONENT,  pxRsaParams->e + 1,           E_LENGTH                       },
            { CKA_PRIME_1,          pxRsaParams->prime1 + 1,      PRIME_1_LENGTH                 },
            { CKA_PRIME_2,          pxRsaParams->prime2 + 1,      PRIME_2_LENGTH                 },
            { CKA_EXPONENT_1,       pxRsaParams->exponent1 + 1,   EXPONENT_1_LENGTH              },
            { CKA_EXPONENT_2,       pxRsaParams->exponent2 + 1,   EXPONENT_2_LENGTH              },
            { CKA_COEFFICIENT,      pxRsaParams->coefficient + 1, COEFFICIENT_LENGTH             }
        };

        /* Aggregate initializers must not use the address of an automatic variable. */
        privateKeyTemplate[ 0 ].pValue = &xPrivateKeyClass;
        privateKeyTemplate[ 1 ].pValue = &xPrivateKeyType;
        privateKeyTemplate[ 3 ].pValue = &xTrueObject;
        privateKeyTemplate[ 4 ].pValue = &xTrueObject;

        xResult = xFunctionList->C_CreateObject( xSession,
                                                 ( CK_ATTRIBUTE_PTR ) &privateKeyTemplate,
                                                 sizeof( privateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                                 &xObjectHandle );
    }

    if( NULL != pxRsaParams )
    {
        free( pxRsaParams );
    }

    return xResult;
}

/*-----------------------------------------------------------*/

static CK_RV prvProvisionPrivateKey( CK_SESSION_HANDLE xSession,
                                     const char * pcPrivateKey,
                                     size_t xPrivateKeyLength,
                                     const char * pcLabel )
{
    CK_RV xResult = CKR_OK;
    mbedtls_pk_type_t xMbedKeyType = MBEDTLS_PK_NONE;
    int xMbedResult = 0;
    mbedtls_pk_context xMbedPkContext = { 0 };

    mbedtls_pk_init( &xMbedPkContext );
    xMbedResult = mbedtls_pk_parse_key( &xMbedPkContext, ( const uint8_t * ) pcPrivateKey,
                                        xPrivateKeyLength, NULL, 0 );

    if( xMbedResult != 0 )
    {
        LogError( ( "Unable to parse private key." ) );
        xResult = CKR_ARGUMENTS_BAD;
    }

    /* Determine whether the key to be imported is RSA or EC. */
    if( xResult == CKR_OK )
    {
        xMbedKeyType = mbedtls_pk_get_type( &xMbedPkContext );

        if( xMbedKeyType == MBEDTLS_PK_RSA )
        {
            xResult = prvProvisionPrivateRSAKey( xSession, pcLabel, &xMbedPkContext );
        }
        else if( ( xMbedKeyType == MBEDTLS_PK_ECDSA ) ||
                 ( xMbedKeyType == MBEDTLS_PK_ECKEY ) ||
                 ( xMbedKeyType == MBEDTLS_PK_ECKEY_DH ) )
        {
            xResult = prvProvisionPrivateECKey( xSession, pcLabel, &xMbedPkContext );
        }
        else
        {
            LogError( ( "Invalid private key type provided. Only RSA-2048 and "
                        "EC P-256 keys are supported." ) );
            xResult = CKR_ARGUMENTS_BAD;
        }
    }

    mbedtls_pk_free( &xMbedPkContext );

    return xResult;
}

/*-----------------------------------------------------------*/

static CK_RV prvProvisionCertificate( CK_SESSION_HANDLE xSession,
                                      const char * pcCertificate,
                                      size_t xCertificateLength,
                                      const char * pcLabel )
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

    /* Initialize the client certificate template. */
    xCertificateTemplate.xObjectClass.type = CKA_CLASS;
    xCertificateTemplate.xObjectClass.pValue = &xCertificateClass;
    xCertificateTemplate.xObjectClass.ulValueLen = sizeof( xCertificateClass );
    xCertificateTemplate.xSubject.type = CKA_SUBJECT;
    xCertificateTemplate.xSubject.pValue = pxSubject;
    xCertificateTemplate.xSubject.ulValueLen = strlen( ( const char * ) pxSubject );
    xCertificateTemplate.xValue.type = CKA_VALUE;
    xCertificateTemplate.xValue.pValue = ( CK_VOID_PTR ) pcCertificate;
    xCertificateTemplate.xValue.ulValueLen = ( CK_ULONG ) xCertificateLength;
    xCertificateTemplate.xLabel.type = CKA_LABEL;
    xCertificateTemplate.xLabel.pValue = ( CK_VOID_PTR ) pcLabel;
    xCertificateTemplate.xLabel.ulValueLen = strlen( pcLabel );
    xCertificateTemplate.xCertificateType.type = CKA_CERTIFICATE_TYPE;
    xCertificateTemplate.xCertificateType.pValue = &xCertificateType;
    xCertificateTemplate.xCertificateType.ulValueLen = sizeof( CK_CERTIFICATE_TYPE );
    xCertificateTemplate.xTokenObject.type = CKA_TOKEN;
    xCertificateTemplate.xTokenObject.pValue = &xTokenStorage;
    xCertificateTemplate.xTokenObject.ulValueLen = sizeof( xTokenStorage );

    if( pcCertificate == NULL )
    {
        LogError( ( "Certificate cannot be null." ) );
        xResult = CKR_ATTRIBUTE_VALUE_INVALID;
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
        /* Convert the certificate to DER format from PEM. The DER key should
         * be about 3/4 the size of the PEM key, so mallocing the PEM key size
         * is sufficient. */
        pucDerObject = ( uint8_t * ) malloc( xCertificateTemplate.xValue.ulValueLen );
        xDerLen = xCertificateTemplate.xValue.ulValueLen;

        if( pucDerObject != NULL )
        {
            ulConversion = convert_pem_to_der( ( unsigned char * ) xCertificateTemplate.xValue.pValue,
                                               xCertificateTemplate.xValue.ulValueLen,
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
        /* Set the template pointers to refer to the DER converted objects. */
        xCertificateTemplate.xValue.pValue = pucDerObject;
        xCertificateTemplate.xValue.ulValueLen = xDerLen;

        /* Best effort clean-up of the existing object, if it exists. */
        prvDestroyProvidedObjects( xSession, ( CK_BYTE_PTR * ) &pcLabel, &xCertificateClass, 1 );

        /* Create an object using the encoded client certificate. */
        LogInfo( ( "Writing certificate into label \"%s\".", pcLabel ) );

        xResult = xFunctionList->C_CreateObject( xSession,
                                                 ( CK_ATTRIBUTE_PTR ) &xCertificateTemplate,
                                                 sizeof( xCertificateTemplate ) / sizeof( CK_ATTRIBUTE ),
                                                 &xObjectHandle );
    }

    if( pucDerObject != NULL )
    {
        free( pucDerObject );
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
                        "C_GenerateRandom failed with %lu.", xRes ) );
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
        { CKA_KEY_TYPE,  NULL /* &keyType */,         sizeof( xKeyType )         },
        { CKA_VERIFY,    NULL /* &trueObject */,      sizeof( xTrueObject )      },
        { CKA_EC_PARAMS, NULL /* ecParams */,         sizeof( pxEcParams )       },
        { CKA_LABEL,     ( void * ) pcPublicKeyLabel, strlen( pcPublicKeyLabel ) }
    };

    /* Aggregate initializers must not use the address of an automatic variable. */
    pxPublicKeyTemplate[ 0 ].pValue = &xKeyType;
    pxPublicKeyTemplate[ 1 ].pValue = &xTrueObject;
    pxPublicKeyTemplate[ 2 ].pValue = &pxEcParams;

    CK_ATTRIBUTE privateKeyTemplate[] =
    {
        { CKA_KEY_TYPE, NULL /* &keyType */,          sizeof( xKeyType )          },
        { CKA_TOKEN,    NULL /* &trueObject */,       sizeof( xTrueObject )       },
        { CKA_PRIVATE,  NULL /* &trueObject */,       sizeof( xTrueObject )       },
        { CKA_SIGN,     NULL /* &trueObject */,       sizeof( xTrueObject )       },
        { CKA_LABEL,    ( void * ) pcPrivateKeyLabel, strlen( pcPrivateKeyLabel ) }
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
    int32_t usMbedtlsRet = -1;
    const mbedtls_pk_info_t * pxHeader = mbedtls_pk_info_from_type( MBEDTLS_PK_ECKEY );

    assert( pcPrivKeyLabel != NULL );
    assert( pcPubKeyLabel != NULL );
    assert( pcCsrBuffer != NULL );
    assert( pxOutCsrLength != NULL );

    xPkcs11Ret = prvGenerateKeyPairEC( xP11Session,
                                       pcPrivKeyLabel,
                                       pcPubKeyLabel,
                                       &xPrivKeyHandle,
                                       &xPubKeyHandle );

    if( xPkcs11Ret == CKR_OK )
    {
        mbedtls_x509write_csr_init( &xReq );
        mbedtls_x509write_csr_set_md_alg( &xReq, MBEDTLS_MD_SHA256 );

        usMbedtlsRet = mbedtls_x509write_csr_set_key_usage( &xReq, MBEDTLS_X509_KU_DIGITAL_SIGNATURE );

        if( usMbedtlsRet == 0 )
        {
            usMbedtlsRet = mbedtls_x509write_csr_set_ns_cert_type( &xReq, MBEDTLS_X509_NS_CERT_TYPE_SSL_CLIENT );
        }

        if( usMbedtlsRet == 0 )
        {
            usMbedtlsRet = mbedtls_x509write_csr_set_subject_name( &xReq, democonfigCSR_SUBJECT_NAME );
        }

        if( usMbedtlsRet == 0 )
        {
            mbedtls_pk_init( &xPrivKey );
        }

        if( usMbedtlsRet == 0 )
        {
            usMbedtlsRet = prvExtractEcPublicKey( xP11Session, &xEcdsaContext, xPubKeyHandle );
        }

        if( usMbedtlsRet == 0 )
        {
            xSigningContext.p11Session = xP11Session;
            xSigningContext.p11PrivateKey = xPrivKeyHandle;

            memcpy( &xPrivKeyInfo, pxHeader, sizeof( mbedtls_pk_info_t ) );

            xPrivKeyInfo.sign_func = prvPrivateKeySigningCallback;
            xPrivKey.pk_info = &xPrivKeyInfo;
            xPrivKey.pk_ctx = &xEcdsaContext;

            mbedtls_x509write_csr_set_key( &xReq, &xPrivKey );

            usMbedtlsRet = mbedtls_x509write_csr_pem( &xReq, ( unsigned char * ) pcCsrBuffer,
                                                      xCsrBufferLength, &prvRandomCallback,
                                                      &xP11Session );
        }

        mbedtls_x509write_csr_free( &xReq );
        mbedtls_ecdsa_free( &xEcdsaContext );
        mbedtls_ecp_group_free( &( xEcdsaContext.grp ) );
    }

    *pxOutCsrLength = strlen( pcCsrBuffer );

    return( usMbedtlsRet == 0 );
}

/*-----------------------------------------------------------*/

bool xLoadCertificate( CK_SESSION_HANDLE xP11Session,
                       const char * pcCertificate,
                       const char * pcLabel,
                       size_t xCertificateLength )
{
    CK_RV xRet;

    assert( pcCertificate != NULL );
    assert( pcLabel != NULL );

    xRet = prvProvisionCertificate( xP11Session,
                                    pcCertificate,
                                    xCertificateLength + 1, /* MbedTLS includes null character in length for PEM objects. */
                                    pcLabel );

    return( xRet == CKR_OK );
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
