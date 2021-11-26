/*
 * AWS IoT Device SDK for Embedded C 202108.00
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
#define CLAIM_CERT_BUFFER_LENGTH           2048

/**
 * @brief Size of buffer in which to hold the certificate signing request (CSR).
 */
#define CLAIM_PRIVATE_KEY_BUFFER_LENGTH    2048

/**
 * @brief Represents string to be logged when mbedTLS returned error
 * does not contain a high-level code.
 */
static const char * pNoHighLevelMbedTlsCodeStr = "<No-High-Level-Code>";

/**
 * @brief Represents string to be logged when mbedTLS returned error
 * does not contain a low-level code.
 */
static const char * pNoLowLevelMbedTlsCodeStr = "<No-Low-Level-Code>";

/**
 * @brief Utility for converting the high-level code in an mbedTLS error to
 * string, if the code-contains a high-level code; otherwise, using a default
 * string.
 */
#define mbedtlsHighLevelCodeOrDefault( mbedTlsCode )     \
    ( mbedtls_high_level_strerr( mbedTlsCode ) != NULL ) \
    ? mbedtls_high_level_strerr( mbedTlsCode )           \
    : pNoHighLevelMbedTlsCodeStr

/**
 * @brief Utility for converting the level-level code in an mbedTLS error to
 * string, if the code-contains a level-level code; otherwise, using a default
 * string.
 */
#define mbedtlsLowLevelCodeOrDefault( mbedTlsCode )     \
    ( mbedtls_low_level_strerr( mbedTlsCode ) != NULL ) \
    ? mbedtls_low_level_strerr( mbedTlsCode )           \
    : pNoLowLevelMbedTlsCodeStr

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
static SigningCallbackContext_t signingContext = { 0 };

/*-----------------------------------------------------------*/

/**
 * @brief Reads a file into the given buffer.
 *
 * @param[in] path Path of the file.
 * @param[out] pBuffer Buffer to read file contents into.
 * @param[in] bufferLength Length of #pBuffer.
 * @param[out] pOutWrittenLength Length of contents written to #pBuffer.
 */
static bool readFile( const char * path,
                      char * pBuffer,
                      size_t bufferLength,
                      size_t * pOutWrittenLength );

/**
 * @brief Delete the specified crypto object from storage.
 *
 * @param[in] session The PKCS #11 session.
 * @param[in] pkcsLabelsPtr The list of labels to remove.
 * @param[in] pClass The list of corresponding classes.
 * @param[in] count The length of #pkcsLabelsPtr and #pClass.
 */
static CK_RV destroyProvidedObjects( CK_SESSION_HANDLE session,
                                     CK_BYTE_PTR * pkcsLabelsPtr,
                                     CK_OBJECT_CLASS * pClass,
                                     CK_ULONG count );


/**
 * @brief Import the specified ECDSA private key into storage.
 *
 * @param[in] session The PKCS #11 session.
 * @param[in] label The label to store the key.
 * @param[in] mbedPkContext The private key to store.
 */
static CK_RV provisionPrivateECKey( CK_SESSION_HANDLE session,
                                    const char * label,
                                    mbedtls_pk_context * mbedPkContext );



/**
 * @brief Import the specified RSA private key into storage.
 *
 * @param[in] session The PKCS #11 session.
 * @param[in] label The label to store the key.
 * @param[in] mbedPkContext The private key to store.
 */
static CK_RV provisionPrivateRSAKey( CK_SESSION_HANDLE session,
                                     const char * label,
                                     mbedtls_pk_context * mbedPkContext );


/**
 * @brief Import the specified private key into storage.
 *
 * @param[in] session The PKCS #11 session.
 * @param[in] privateKey The private key to store, in PEM format.
 * @param[in] privateKeyLength The length of the key, including null terminator.
 * @param[in] label The label to store the key.
 */
static CK_RV provisionPrivateKey( CK_SESSION_HANDLE session,
                                  const char * privateKey,
                                  size_t privateKeyLength,
                                  const char * label );

/**
 * @brief Import the specified X.509 client certificate into storage.
 *
 * @param[in] session The PKCS #11 session.
 * @param[in] certificate The certificate to store, in PEM format.
 * @param[in] certificateLength The length of the certificate, including the null terminator.
 * @param[in] label The label to store the certificate.
 */
static CK_RV provisionCertificate( CK_SESSION_HANDLE session,
                                   const char * certificate,
                                   size_t certificateLength,
                                   const char * label );

/**
 * @brief Read the specified ECDSA public key into the MbedTLS ECDSA context.
 *
 * @param[in] p11Session The PKCS #11 session.
 * @param[in] pEcdsaContext The context in which to store the key.
 * @param[in] publicKey The public key to read.
 */
static int extractEcPublicKey( CK_SESSION_HANDLE p11Session,
                               mbedtls_ecdsa_context * pEcdsaContext,
                               CK_OBJECT_HANDLE publicKey );

/**
 * @brief MbedTLS callback for signing using the provisioned private key. Used for
 * signing the CSR.
 *
 * @param[in] pContext Unused.
 * @param[in] mdAlg Unused.
 * @param[in] pHash Data to sign.
 * @param[in] hashLen Length of #pHash.
 * @param[out] pSig The signature
 * @param[out] pSigLen The length of the signature.
 * @param[in] pRng Unused.
 * @param[in] pRngContext Unused.
 */
static int32_t privateKeySigningCallback( void * pContext,
                                          mbedtls_md_type_t mdAlg,
                                          const unsigned char * pHash,
                                          size_t hashLen,
                                          unsigned char * pSig,
                                          size_t * pSigLen,
                                          int ( *pRng )( void *, unsigned char *, size_t ),
                                          void * pRngContext );

/**
 * @brief MbedTLS random generation callback to generate random values with
 * PKCS #11.
 *
 * @param[in] pCtx Pointer to the PKCS #11 session handle.
 * @param[out] pRandom Buffer to write random data to.
 * @param[in] randomLength Length of random data to write.
 */
static int randomCallback( void * pCtx,
                           unsigned char * pRandom,
                           size_t randomLength );

/**
 * @brief Generate a new ECDSA key pair using PKCS #11.
 *
 * @param[in] session The PKCS #11 session.
 * @param[in] privateKeyLabel The label to store the private key.
 * @param[in] publicKeyLabel The label to store the public key.
 * @param[out] privateKeyHandlePtr The handle of the private key.
 * @param[out] publicKeyHandlePtr The handle of the public key.
 */
static CK_RV generateKeyPairEC( CK_SESSION_HANDLE session,
                                const char * privateKeyLabel,
                                const char * publicKeyLabel,
                                CK_OBJECT_HANDLE_PTR privateKeyHandlePtr,
                                CK_OBJECT_HANDLE_PTR publicKeyHandlePtr );

/*-----------------------------------------------------------*/

static bool readFile( const char * path,
                      char * pBuffer,
                      size_t bufferLength,
                      size_t * pOutWrittenLength )
{
    FILE * file;
    size_t length = 0;
    bool status = true;

    /* Get the file descriptor for the CSR file. */
    file = fopen( path, "rb" );

    if( file == NULL )
    {
        LogError( ( "Error opening file at path: %s. Error: %s.",
                    path, strerror( errno ) ) );
        status = false;
    }
    else
    {
        int result;
        /* Seek to the end of the file, so that we can get the file size. */
        result = fseek( file, 0L, SEEK_END );

        if( result == -1 )
        {
            LogError( ( "Failed while moving to end of file. Path: %s. Error: %s.",
                        path, strerror( errno ) ) );
            status = false;
        }
        else
        {
            long lenResult = -1;
            /* Get the current position which is the file size. */
            lenResult = ftell( file );

            if( lenResult == -1 )
            {
                LogError( ( "Failed to get length of file. Path: %s. Error: %s.", path,
                            strerror( errno ) ) );
                status = false;
            }
            else
            {
                length = ( size_t ) lenResult;
            }
        }

        if( status == true )
        {
            if( length > bufferLength )
            {
                LogError( ( "Buffer too small for file. Buffer size: %ld. Required size: %ld.",
                            bufferLength, length ) );
                status = false;
            }
        }

        if( status == true )
        {
            /* Return to the beginning of the file. */
            result = fseek( file, 0L, SEEK_SET );

            if( result == -1 )
            {
                LogError( ( "Failed to move to beginning of file. Path: %s. Error: %s.",
                            path, strerror( errno ) ) );
                status = false;
            }
        }

        if( status == true )
        {
            size_t written = 0;
            /* Read the CSR into our buffer. */
            written = fread( pBuffer, 1, length, file );

            if( written != length )
            {
                LogError( ( "Failed reading file. Path: %s. Error: %s.", path,
                            strerror( errno ) ) );
                status = false;
            }
            else
            {
                *pOutWrittenLength = length;
            }
        }

        fclose( file );
    }

    return status;
}

/*-----------------------------------------------------------*/

static CK_RV destroyProvidedObjects( CK_SESSION_HANDLE session,
                                     CK_BYTE_PTR * pkcsLabelsPtr,
                                     CK_OBJECT_CLASS * pClass,
                                     CK_ULONG count )
{
    CK_RV result;
    CK_FUNCTION_LIST_PTR functionList;
    CK_OBJECT_HANDLE objectHandle;
    CK_BYTE * labelPtr;
    CK_ULONG index = 0;

    result = C_GetFunctionList( &functionList );

    if( result != CKR_OK )
    {
        LogError( ( "Could not get a PKCS #11 function pointer." ) );
    }
    else
    {
        for( index = 0; index < count; index++ )
        {
            labelPtr = pkcsLabelsPtr[ index ];

            result = xFindObjectWithLabelAndClass( session, ( char * ) labelPtr,
                                                   strlen( ( char * ) labelPtr ),
                                                   pClass[ index ], &objectHandle );

            while( ( result == CKR_OK ) && ( objectHandle != CK_INVALID_HANDLE ) )
            {
                result = functionList->C_DestroyObject( session, objectHandle );

                /* PKCS #11 allows a module to maintain multiple objects with the same
                 * label and type. The intent of this loop is to try to delete all of
                 * them. However, to avoid getting stuck, we won't try to find another
                 * object of the same label/type if the previous delete failed. */
                if( result == CKR_OK )
                {
                    result = xFindObjectWithLabelAndClass( session, ( char * ) labelPtr,
                                                           strlen( ( char * ) labelPtr ),
                                                           pClass[ index ], &objectHandle );
                }
                else
                {
                    break;
                }
            }
        }
    }

    return result;
}

/*-----------------------------------------------------------*/

static CK_RV provisionPrivateECKey( CK_SESSION_HANDLE session,
                                    const char * label,
                                    mbedtls_pk_context * mbedPkContext )
{
    CK_RV result = CKR_OK;
    CK_FUNCTION_LIST_PTR functionList = NULL;
    CK_BYTE * DPtr = NULL;        /* Private value D. */
    CK_BYTE * ecParamsPtr = NULL; /* DER-encoding of an ANSI X9.62 Parameters value */
    int mbedResult = 0;
    CK_BBOOL trueObject = CK_TRUE;
    CK_KEY_TYPE privateKeyType = CKK_EC;
    CK_OBJECT_CLASS privateKeyClass = CKO_PRIVATE_KEY;
    CK_OBJECT_HANDLE objectHandle = CK_INVALID_HANDLE;
    mbedtls_ecp_keypair * keyPair = ( mbedtls_ecp_keypair * ) mbedPkContext->pk_ctx;

    result = C_GetFunctionList( &functionList );

    if( result != CKR_OK )
    {
        LogError( ( "Could not get a PKCS #11 function pointer." ) );
    }
    else
    {
        DPtr = ( CK_BYTE * ) malloc( EC_D_LENGTH );

        if( DPtr == NULL )
        {
            result = CKR_HOST_MEMORY;
        }
    }

    if( result == CKR_OK )
    {
        mbedResult = mbedtls_mpi_write_binary( &( keyPair->d ), DPtr, EC_D_LENGTH );

        if( mbedResult != 0 )
        {
            LogError( ( "Failed to parse EC private key components." ) );
            result = CKR_ATTRIBUTE_VALUE_INVALID;
        }
    }

    if( result == CKR_OK )
    {
        if( keyPair->grp.id == MBEDTLS_ECP_DP_SECP256R1 )
        {
            ecParamsPtr = ( CK_BYTE * ) ( "\x06\x08" MBEDTLS_OID_EC_GRP_SECP256R1 );
        }
        else
        {
            result = CKR_CURVE_NOT_SUPPORTED;
        }
    }

    if( result == CKR_OK )
    {
        CK_ATTRIBUTE privateKeyTemplate[] =
        {
            { CKA_CLASS,     NULL /* &privateKeyClass*/, sizeof( CK_OBJECT_CLASS )    },
            { CKA_KEY_TYPE,  NULL /* &privateKeyType*/,  sizeof( CK_KEY_TYPE )        },
            { CKA_LABEL,     ( void * ) label,           ( CK_ULONG ) strlen( label ) },
            { CKA_TOKEN,     NULL /* &trueObject*/,      sizeof( CK_BBOOL )           },
            { CKA_SIGN,      NULL /* &trueObject*/,      sizeof( CK_BBOOL )           },
            { CKA_EC_PARAMS, NULL /* ecParamsPtr*/,      EC_PARAMS_LENGTH             },
            { CKA_VALUE,     NULL /* DPtr*/,             EC_D_LENGTH                  }
        };

        /* Aggregate initializers must not use the address of an automatic variable. */
        privateKeyTemplate[ 0 ].pValue = &privateKeyClass;
        privateKeyTemplate[ 1 ].pValue = &privateKeyType;
        privateKeyTemplate[ 3 ].pValue = &trueObject;
        privateKeyTemplate[ 4 ].pValue = &trueObject;
        privateKeyTemplate[ 5 ].pValue = ecParamsPtr;
        privateKeyTemplate[ 6 ].pValue = DPtr;

        result = functionList->C_CreateObject( session,
                                               ( CK_ATTRIBUTE_PTR ) &privateKeyTemplate,
                                               sizeof( privateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                               &objectHandle );
    }

    if( DPtr != NULL )
    {
        free( DPtr );
    }

    return result;
}

/*-----------------------------------------------------------*/

static CK_RV provisionPrivateRSAKey( CK_SESSION_HANDLE session,
                                     const char * label,
                                     mbedtls_pk_context * mbedPkContext )
{
    CK_RV result = CKR_OK;
    CK_FUNCTION_LIST_PTR functionList = NULL;
    int mbedResult = 0;
    CK_KEY_TYPE privateKeyType = CKK_RSA;
    mbedtls_rsa_context * rsaContext = ( mbedtls_rsa_context * ) mbedPkContext->pk_ctx;
    CK_OBJECT_CLASS privateKeyClass = CKO_PRIVATE_KEY;
    RsaParams_t * rsaParams = NULL;
    CK_BBOOL trueObject = CK_TRUE;
    CK_OBJECT_HANDLE objectHandle = CK_INVALID_HANDLE;

    result = C_GetFunctionList( &functionList );

    if( result != CKR_OK )
    {
        LogError( ( "Could not get a PKCS #11 function pointer." ) );
    }
    else
    {
        rsaParams = ( RsaParams_t * ) malloc( sizeof( RsaParams_t ) );

        if( rsaParams == NULL )
        {
            result = CKR_HOST_MEMORY;
        }
    }

    if( result == CKR_OK )
    {
        memset( rsaParams, 0, sizeof( RsaParams_t ) );

        mbedResult = mbedtls_rsa_export_raw( rsaContext,
                                             rsaParams->modulus, MODULUS_LENGTH + 1,
                                             rsaParams->prime1, PRIME_1_LENGTH + 1,
                                             rsaParams->prime2, PRIME_2_LENGTH + 1,
                                             rsaParams->d, D_LENGTH + 1,
                                             rsaParams->e, E_LENGTH + 1 );

        if( mbedResult != 0 )
        {
            LogError( ( "Failed to parse RSA private key components." ) );
            result = CKR_ATTRIBUTE_VALUE_INVALID;
        }

        /* Export Exponent 1, Exponent 2, Coefficient. */
        mbedResult |= mbedtls_mpi_write_binary( ( mbedtls_mpi const * ) &rsaContext->DP, rsaParams->exponent1, EXPONENT_1_LENGTH + 1 );
        mbedResult |= mbedtls_mpi_write_binary( ( mbedtls_mpi const * ) &rsaContext->DQ, rsaParams->exponent2, EXPONENT_2_LENGTH + 1 );
        mbedResult |= mbedtls_mpi_write_binary( ( mbedtls_mpi const * ) &rsaContext->QP, rsaParams->coefficient, COEFFICIENT_LENGTH + 1 );

        if( mbedResult != 0 )
        {
            LogError( ( "Failed to parse RSA private key Chinese Remainder Theorem variables." ) );
            result = CKR_ATTRIBUTE_VALUE_INVALID;
        }
    }

    if( result == CKR_OK )
    {
        /* When importing the fields, the pointer is incremented by 1
         * to remove the leading 0 padding (if it existed) and the original field
         * length is used */

        CK_ATTRIBUTE privateKeyTemplate[] =
        {
            { CKA_CLASS,            NULL /* &privateKeyClass */, sizeof( CK_OBJECT_CLASS )    },
            { CKA_KEY_TYPE,         NULL /* &privateKeyType */,  sizeof( CK_KEY_TYPE )        },
            { CKA_LABEL,            ( void * ) label,            ( CK_ULONG ) strlen( label ) },
            { CKA_TOKEN,            NULL /* &trueObject */,      sizeof( CK_BBOOL )           },
            { CKA_SIGN,             NULL /* &trueObject */,      sizeof( CK_BBOOL )           },
            { CKA_MODULUS,          rsaParams->modulus + 1,      MODULUS_LENGTH               },
            { CKA_PRIVATE_EXPONENT, rsaParams->d + 1,            D_LENGTH                     },
            { CKA_PUBLIC_EXPONENT,  rsaParams->e + 1,            E_LENGTH                     },
            { CKA_PRIME_1,          rsaParams->prime1 + 1,       PRIME_1_LENGTH               },
            { CKA_PRIME_2,          rsaParams->prime2 + 1,       PRIME_2_LENGTH               },
            { CKA_EXPONENT_1,       rsaParams->exponent1 + 1,    EXPONENT_1_LENGTH            },
            { CKA_EXPONENT_2,       rsaParams->exponent2 + 1,    EXPONENT_2_LENGTH            },
            { CKA_COEFFICIENT,      rsaParams->coefficient + 1,  COEFFICIENT_LENGTH           }
        };

        /* Aggregate initializers must not use the address of an automatic variable. */
        privateKeyTemplate[ 0 ].pValue = &privateKeyClass;
        privateKeyTemplate[ 1 ].pValue = &privateKeyType;
        privateKeyTemplate[ 3 ].pValue = &trueObject;
        privateKeyTemplate[ 4 ].pValue = &trueObject;

        result = functionList->C_CreateObject( session,
                                               ( CK_ATTRIBUTE_PTR ) &privateKeyTemplate,
                                               sizeof( privateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                               &objectHandle );
    }

    if( NULL != rsaParams )
    {
        free( rsaParams );
    }

    return result;
}

/*-----------------------------------------------------------*/

static CK_RV provisionPrivateKey( CK_SESSION_HANDLE session,
                                  const char * privateKey,
                                  size_t privateKeyLength,
                                  const char * label )
{
    CK_RV result = CKR_OK;
    mbedtls_pk_type_t mbedKeyType = MBEDTLS_PK_NONE;
    int mbedResult = 0;
    mbedtls_pk_context mbedPkContext = { 0 };

    mbedtls_pk_init( &mbedPkContext );
    mbedResult = mbedtls_pk_parse_key( &mbedPkContext, ( const uint8_t * ) privateKey,
                                       privateKeyLength, NULL, 0 );

    if( mbedResult != 0 )
    {
        LogError( ( "Unable to parse private key." ) );
        result = CKR_ARGUMENTS_BAD;
    }

    /* Determine whether the key to be imported is RSA or EC. */
    if( result == CKR_OK )
    {
        mbedKeyType = mbedtls_pk_get_type( &mbedPkContext );

        if( mbedKeyType == MBEDTLS_PK_RSA )
        {
            result = provisionPrivateRSAKey( session, label, &mbedPkContext );
        }
        else if( ( mbedKeyType == MBEDTLS_PK_ECDSA ) ||
                 ( mbedKeyType == MBEDTLS_PK_ECKEY ) ||
                 ( mbedKeyType == MBEDTLS_PK_ECKEY_DH ) )
        {
            result = provisionPrivateECKey( session, label, &mbedPkContext );
        }
        else
        {
            LogError( ( "Invalid private key type provided. Only RSA-2048 and "
                        "EC P-256 keys are supported." ) );
            result = CKR_ARGUMENTS_BAD;
        }
    }

    mbedtls_pk_free( &mbedPkContext );

    return result;
}

/*-----------------------------------------------------------*/

static CK_RV provisionCertificate( CK_SESSION_HANDLE session,
                                   const char * certificate,
                                   size_t certificateLength,
                                   const char * label )
{
    PKCS11_CertificateTemplate_t certificateTemplate;
    CK_OBJECT_CLASS certificateClass = CKO_CERTIFICATE;
    CK_CERTIFICATE_TYPE certificateType = CKC_X_509;
    CK_FUNCTION_LIST_PTR functionList = NULL;
    CK_RV result = CKR_OK;
    uint8_t * derObject = NULL;
    int32_t conversion = 0;
    size_t derLen = 0;
    CK_BBOOL tokenStorage = CK_TRUE;
    CK_BYTE subject[] = "TestSubject";
    CK_OBJECT_HANDLE objectHandle = CK_INVALID_HANDLE;

    /* Initialize the client certificate template. */
    certificateTemplate.xObjectClass.type = CKA_CLASS;
    certificateTemplate.xObjectClass.pValue = &certificateClass;
    certificateTemplate.xObjectClass.ulValueLen = sizeof( certificateClass );
    certificateTemplate.xSubject.type = CKA_SUBJECT;
    certificateTemplate.xSubject.pValue = subject;
    certificateTemplate.xSubject.ulValueLen = strlen( ( const char * ) subject );
    certificateTemplate.xValue.type = CKA_VALUE;
    certificateTemplate.xValue.pValue = ( CK_VOID_PTR ) certificate;
    certificateTemplate.xValue.ulValueLen = ( CK_ULONG ) certificateLength;
    certificateTemplate.xLabel.type = CKA_LABEL;
    certificateTemplate.xLabel.pValue = ( CK_VOID_PTR ) label;
    certificateTemplate.xLabel.ulValueLen = strlen( label );
    certificateTemplate.xCertificateType.type = CKA_CERTIFICATE_TYPE;
    certificateTemplate.xCertificateType.pValue = &certificateType;
    certificateTemplate.xCertificateType.ulValueLen = sizeof( CK_CERTIFICATE_TYPE );
    certificateTemplate.xTokenObject.type = CKA_TOKEN;
    certificateTemplate.xTokenObject.pValue = &tokenStorage;
    certificateTemplate.xTokenObject.ulValueLen = sizeof( tokenStorage );

    if( certificate == NULL )
    {
        LogError( ( "Certificate cannot be null." ) );
        result = CKR_ATTRIBUTE_VALUE_INVALID;
    }

    if( result == CKR_OK )
    {
        result = C_GetFunctionList( &functionList );

        if( result != CKR_OK )
        {
            LogError( ( "Could not get a PKCS #11 function pointer." ) );
        }
    }

    if( result == CKR_OK )
    {
        /* Convert the certificate to DER format from PEM. The DER key should
         * be about 3/4 the size of the PEM key, so mallocing the PEM key size
         * is sufficient. */
        derObject = ( uint8_t * ) malloc( certificateTemplate.xValue.ulValueLen );
        derLen = certificateTemplate.xValue.ulValueLen;

        if( derObject != NULL )
        {
            conversion = convert_pem_to_der( ( unsigned char * ) certificateTemplate.xValue.pValue,
                                             certificateTemplate.xValue.ulValueLen,
                                             derObject, &derLen );

            if( 0 != conversion )
            {
                LogError( ( "Failed to convert provided certificate." ) );
                result = CKR_ARGUMENTS_BAD;
            }
        }
        else
        {
            LogError( ( "Failed to allocate buffer for converting certificate to DER." ) );
            result = CKR_HOST_MEMORY;
        }
    }

    if( result == CKR_OK )
    {
        /* Set the template pointers to refer to the DER converted objects. */
        certificateTemplate.xValue.pValue = derObject;
        certificateTemplate.xValue.ulValueLen = derLen;

        /* Best effort clean-up of the existing object, if it exists. */
        destroyProvidedObjects( session, ( CK_BYTE_PTR * ) &label, &certificateClass, 1 );

        /* Create an object using the encoded client certificate. */
        LogInfo( ( "Writing certificate into label \"%s\".", label ) );

        result = functionList->C_CreateObject( session,
                                               ( CK_ATTRIBUTE_PTR ) &certificateTemplate,
                                               sizeof( certificateTemplate ) / sizeof( CK_ATTRIBUTE ),
                                               &objectHandle );
    }

    if( derObject != NULL )
    {
        free( derObject );
    }

    return result;
}

/*-----------------------------------------------------------*/

bool loadClaimCredentials( CK_SESSION_HANDLE p11Session,
                           const char * pClaimCertPath,
                           const char * pClaimCertLabel,
                           const char * pClaimPrivKeyPath,
                           const char * pClaimPrivKeyLabel )
{
    bool status;
    char claimCert[ CLAIM_CERT_BUFFER_LENGTH ] = { 0 };
    size_t claimCertLength = 0;
    char claimPrivateKey[ CLAIM_PRIVATE_KEY_BUFFER_LENGTH ] = { 0 };
    size_t claimPrivateKeyLength = 0;
    CK_RV ret;

    assert( pClaimCertPath != NULL );
    assert( pClaimCertLabel != NULL );
    assert( pClaimPrivKeyPath != NULL );
    assert( pClaimPrivKeyLabel != NULL );

    status = readFile( pClaimCertPath, claimCert, CLAIM_CERT_BUFFER_LENGTH,
                       &claimCertLength );

    if( status == true )
    {
        status = readFile( pClaimPrivKeyPath, claimPrivateKey,
                           CLAIM_PRIVATE_KEY_BUFFER_LENGTH, &claimPrivateKeyLength );
    }

    if( status == true )
    {
        ret = provisionPrivateKey( p11Session, claimPrivateKey,
                                   claimPrivateKeyLength + 1, /* MbedTLS includes null character in length for PEM objects. */
                                   pClaimPrivKeyLabel );
        status = ( ret == CKR_OK );
    }

    if( status == true )
    {
        ret = provisionCertificate( p11Session, claimCert,
                                    claimCertLength + 1, /* MbedTLS includes null character in length for PEM objects. */
                                    pClaimCertLabel );
        status = ( ret == CKR_OK );
    }

    return status;
}

/*-----------------------------------------------------------*/

static int extractEcPublicKey( CK_SESSION_HANDLE p11Session,
                               mbedtls_ecdsa_context * pEcdsaContext,
                               CK_OBJECT_HANDLE publicKey )
{
    CK_ATTRIBUTE ecTemplate = { 0 };
    int mbedtlsRet = -1;
    CK_RV pkcs11ret = CKR_OK;
    CK_BYTE ecPoint[ 67 ] = { 0 };
    CK_FUNCTION_LIST_PTR pP11FunctionList;

    mbedtls_ecdsa_init( pEcdsaContext );
    mbedtls_ecp_group_init( &( pEcdsaContext->grp ) );

    pkcs11ret = C_GetFunctionList( &pP11FunctionList );

    if( pkcs11ret != CKR_OK )
    {
        LogError( ( "Could not get a PKCS #11 function pointer." ) );
    }
    else
    {
        ecTemplate.type = CKA_EC_POINT;
        ecTemplate.pValue = ecPoint;
        ecTemplate.ulValueLen = sizeof( ecPoint );
        pkcs11ret = pP11FunctionList->C_GetAttributeValue( p11Session, publicKey, &ecTemplate, 1 );

        if( pkcs11ret != CKR_OK )
        {
            LogError( ( "Failed to extract EC public key. Could not get attribute value. "
                        "C_GetAttributeValue failed with %lu.", pkcs11ret ) );
        }
    }

    if( pkcs11ret == CKR_OK )
    {
        mbedtlsRet = mbedtls_ecp_group_load( &( pEcdsaContext->grp ), MBEDTLS_ECP_DP_SECP256R1 );

        if( mbedtlsRet != 0 )
        {
            LogError( ( "Failed creating an EC key. "
                        "mbedtls_ecp_group_load failed: MbedTLS"
                        "error = %s : %s.",
                        mbedtlsHighLevelCodeOrDefault( mbedtlsRet ),
                        mbedtlsLowLevelCodeOrDefault( mbedtlsRet ) ) );
            pkcs11ret = CKR_FUNCTION_FAILED;
        }
        else
        {
            mbedtlsRet = mbedtls_ecp_point_read_binary( &( pEcdsaContext->grp ), &( pEcdsaContext->Q ), &ecPoint[ 2 ], ecTemplate.ulValueLen - 2 );

            if( mbedtlsRet != 0 )
            {
                LogError( ( "Failed creating an EC key. "
                            "mbedtls_ecp_group_load failed: MbedTLS"
                            "error = %s : %s.",
                            mbedtlsHighLevelCodeOrDefault( mbedtlsRet ),
                            mbedtlsLowLevelCodeOrDefault( mbedtlsRet ) ) );
                pkcs11ret = CKR_FUNCTION_FAILED;
            }
        }
    }

    return mbedtlsRet;
}

/*-----------------------------------------------------------*/

static int32_t privateKeySigningCallback( void * pContext,
                                          mbedtls_md_type_t mdAlg,
                                          const unsigned char * pHash,
                                          size_t hashLen,
                                          unsigned char * pSig,
                                          size_t * pSigLen,
                                          int ( *pRng )( void *, unsigned char *, size_t ),
                                          void * pRngContext )
{
    CK_RV ret = CKR_OK;
    int32_t result = 0;
    CK_MECHANISM mech = { 0 };
    CK_BYTE toBeSigned[ 256 ];
    CK_ULONG toBeSignedLen = sizeof( toBeSigned );
    CK_FUNCTION_LIST_PTR functionList = NULL;

    /* Unreferenced parameters. */
    ( void ) ( pContext );
    ( void ) ( pRng );
    ( void ) ( pRngContext );
    ( void ) ( mdAlg );

    /* Sanity check buffer length. */
    if( hashLen > sizeof( toBeSigned ) )
    {
        ret = CKR_ARGUMENTS_BAD;
    }

    mech.mechanism = CKM_ECDSA;
    memcpy( toBeSigned, pHash, hashLen );
    toBeSignedLen = hashLen;

    if( ret == CKR_OK )
    {
        ret = C_GetFunctionList( &functionList );
    }

    if( ret == CKR_OK )
    {
        ret = functionList->C_SignInit( signingContext.p11Session, &mech,
                                        signingContext.p11PrivateKey );
    }

    if( ret == CKR_OK )
    {
        *pSigLen = sizeof( toBeSigned );
        ret = functionList->C_Sign( signingContext.p11Session, toBeSigned,
                                    toBeSignedLen, pSig, ( CK_ULONG_PTR ) pSigLen );
    }

    if( ret == CKR_OK )
    {
        /* PKCS #11 for P256 returns a 64-byte signature with 32 bytes for R and 32
         * bytes for S. This must be converted to an ASN.1 encoded array. */
        if( *pSigLen != pkcs11ECDSA_P256_SIGNATURE_LENGTH )
        {
            ret = CKR_FUNCTION_FAILED;
            LogError( ( "Failed to sign message using PKCS #11. Expected signature "
                        "length of %lu, but received %lu.",
                        ( unsigned long ) pkcs11ECDSA_P256_SIGNATURE_LENGTH,
                        ( unsigned long ) *pSigLen ) );
        }

        if( ret == CKR_OK )
        {
            PKI_pkcs11SignatureTombedTLSSignature( pSig, pSigLen );
        }
    }

    if( ret != CKR_OK )
    {
        LogError( ( "Failed to sign message using PKCS #11 with error code %lu.", ret ) );
        result = -1;
    }

    return result;
}

/*-----------------------------------------------------------*/

static int randomCallback( void * pCtx,
                           unsigned char * pRandom,
                           size_t randomLength )
{
    CK_SESSION_HANDLE * p11Session = ( CK_SESSION_HANDLE * ) pCtx;
    CK_RV res;
    CK_FUNCTION_LIST_PTR pP11FunctionList;

    res = C_GetFunctionList( &pP11FunctionList );

    if( res != CKR_OK )
    {
        LogError( ( "Failed to generate a random number in RNG callback. Could not get a "
                    "PKCS #11 function pointer." ) );
    }
    else
    {
        res = pP11FunctionList->C_GenerateRandom( *p11Session, pRandom, randomLength );

        if( res != CKR_OK )
        {
            LogError( ( "Failed to generate a random number in RNG callback. "
                        "C_GenerateRandom failed with %lu.", res ) );
        }
    }

    return ( int ) res;
}

/*-----------------------------------------------------------*/

static CK_RV generateKeyPairEC( CK_SESSION_HANDLE session,
                                const char * privateKeyLabel,
                                const char * publicKeyLabel,
                                CK_OBJECT_HANDLE_PTR privateKeyHandlePtr,
                                CK_OBJECT_HANDLE_PTR publicKeyHandlePtr )
{
    CK_RV result;
    CK_MECHANISM mechanism = { CKM_EC_KEY_PAIR_GEN, NULL_PTR, 0 };
    CK_FUNCTION_LIST_PTR functionList;
    CK_BYTE ecParams[] = pkcs11DER_ENCODED_OID_P256; /* prime256v1 */
    CK_KEY_TYPE keyType = CKK_EC;

    CK_BBOOL trueObject = CK_TRUE;
    CK_ATTRIBUTE publicKeyTemplate[] =
    {
        { CKA_KEY_TYPE,  NULL /* &keyType */,       sizeof( keyType )        },
        { CKA_VERIFY,    NULL /* &trueObject */,    sizeof( trueObject )     },
        { CKA_EC_PARAMS, NULL /* ecParams */,       sizeof( ecParams )       },
        { CKA_LABEL,     ( void * ) publicKeyLabel, strlen( publicKeyLabel ) }
    };

    /* Aggregate initializers must not use the address of an automatic variable. */
    publicKeyTemplate[ 0 ].pValue = &keyType;
    publicKeyTemplate[ 1 ].pValue = &trueObject;
    publicKeyTemplate[ 2 ].pValue = &ecParams;

    CK_ATTRIBUTE privateKeyTemplate[] =
    {
        { CKA_KEY_TYPE, NULL /* &keyType */,        sizeof( keyType )         },
        { CKA_TOKEN,    NULL /* &trueObject */,     sizeof( trueObject )      },
        { CKA_PRIVATE,  NULL /* &trueObject */,     sizeof( trueObject )      },
        { CKA_SIGN,     NULL /* &trueObject */,     sizeof( trueObject )      },
        { CKA_LABEL,    ( void * ) privateKeyLabel, strlen( privateKeyLabel ) }
    };

    /* Aggregate initializers must not use the address of an automatic variable. */
    privateKeyTemplate[ 0 ].pValue = &keyType;
    privateKeyTemplate[ 1 ].pValue = &trueObject;
    privateKeyTemplate[ 2 ].pValue = &trueObject;
    privateKeyTemplate[ 3 ].pValue = &trueObject;

    result = C_GetFunctionList( &functionList );

    if( result != CKR_OK )
    {
        LogError( ( "Could not get a PKCS #11 function pointer." ) );
    }
    else
    {
        result = functionList->C_GenerateKeyPair( session,
                                                  &mechanism,
                                                  publicKeyTemplate,
                                                  sizeof( publicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                                  privateKeyTemplate, sizeof( privateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                                  publicKeyHandlePtr,
                                                  privateKeyHandlePtr );
    }

    return result;
}

/*-----------------------------------------------------------*/

bool generateKeyAndCsr( CK_SESSION_HANDLE p11Session,
                        const char * pPrivKeyLabel,
                        const char * pPubKeyLabel,
                        char * pCsrBuffer,
                        size_t csrBufferLength,
                        size_t * pOutCsrLength )
{
    CK_OBJECT_HANDLE privKeyHandle;
    CK_OBJECT_HANDLE pubKeyHandle;
    CK_RV pkcs11Ret = CKR_OK;
    mbedtls_pk_context privKey;
    mbedtls_pk_info_t privKeyInfo;
    mbedtls_ecdsa_context xEcdsaContext;
    mbedtls_x509write_csr req;
    int32_t mbedtlsRet = -1;
    const mbedtls_pk_info_t * header = mbedtls_pk_info_from_type( MBEDTLS_PK_ECKEY );

    assert( pPrivKeyLabel != NULL );
    assert( pPubKeyLabel != NULL );
    assert( pCsrBuffer != NULL );
    assert( pOutCsrLength != NULL );

    pkcs11Ret = generateKeyPairEC( p11Session,
                                   pPrivKeyLabel,
                                   pPubKeyLabel,
                                   &privKeyHandle,
                                   &pubKeyHandle );

    if( pkcs11Ret == CKR_OK )
    {
        mbedtls_x509write_csr_init( &req );
        mbedtls_x509write_csr_set_md_alg( &req, MBEDTLS_MD_SHA256 );

        mbedtlsRet = mbedtls_x509write_csr_set_key_usage( &req, MBEDTLS_X509_KU_DIGITAL_SIGNATURE );

        if( mbedtlsRet == 0 )
        {
            mbedtlsRet = mbedtls_x509write_csr_set_ns_cert_type( &req, MBEDTLS_X509_NS_CERT_TYPE_SSL_CLIENT );
        }

        if( mbedtlsRet == 0 )
        {
            mbedtlsRet = mbedtls_x509write_csr_set_subject_name( &req, CSR_SUBJECT_NAME );
        }

        if( mbedtlsRet == 0 )
        {
            mbedtls_pk_init( &privKey );
        }

        if( mbedtlsRet == 0 )
        {
            mbedtlsRet = extractEcPublicKey( p11Session, &xEcdsaContext, pubKeyHandle );
        }

        if( mbedtlsRet == 0 )
        {
            signingContext.p11Session = p11Session;
            signingContext.p11PrivateKey = privKeyHandle;

            memcpy( &privKeyInfo, header, sizeof( mbedtls_pk_info_t ) );

            privKeyInfo.sign_func = privateKeySigningCallback;
            privKey.pk_info = &privKeyInfo;
            privKey.pk_ctx = &xEcdsaContext;

            mbedtls_x509write_csr_set_key( &req, &privKey );

            mbedtlsRet = mbedtls_x509write_csr_pem( &req, ( unsigned char * ) pCsrBuffer,
                                                    csrBufferLength, &randomCallback,
                                                    &p11Session );
        }

        mbedtls_x509write_csr_free( &req );
        mbedtls_ecdsa_free( &xEcdsaContext );
        mbedtls_ecp_group_free( &( xEcdsaContext.grp ) );
    }

    *pOutCsrLength = strlen( pCsrBuffer );

    return( mbedtlsRet == 0 );
}

/*-----------------------------------------------------------*/

bool loadCertificate( CK_SESSION_HANDLE p11Session,
                      const char * pCertificate,
                      const char * pLabel,
                      size_t certificateLength )
{
    CK_RV ret;

    assert( pCertificate != NULL );
    assert( pLabel != NULL );

    ret = provisionCertificate( p11Session,
                                pCertificate,
                                certificateLength + 1, /* MbedTLS includes null character in length for PEM objects. */
                                pLabel );

    return( ret == CKR_OK );
}

/*-----------------------------------------------------------*/

bool pkcs11CloseSession( CK_SESSION_HANDLE p11Session )
{
    CK_RV result = CKR_OK;
    CK_FUNCTION_LIST_PTR functionList = NULL;

    result = C_GetFunctionList( &functionList );

    if( result == CKR_OK )
    {
        result = functionList->C_CloseSession( p11Session );
    }

    if( result == CKR_OK )
    {
        result = functionList->C_Finalize( NULL );
    }

    return( result == CKR_OK );
}

/*-----------------------------------------------------------*/
