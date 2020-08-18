/*
 * FreeRTOS PKCS #11 V2.0.3
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file iot_pkcs11_mbedtls.c
 * @brief mbedTLS-based PKCS#11 implementation for software keys. This
 * file deviates from the FreeRTOS style standard for some function names and
 * data types in order to maintain compliance with the PKCS #11 standard.
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* PKCS #11 includes. */
#include "iot_pkcs11_config.h"
#include "iot_pkcs11.h"
#include "iot_pkcs11_pal.h"
#include "iot_pki_utils.h"

/* mbedTLS includes. */
#include "mbedtls/pk.h"
#include "mbedtls/pk_internal.h"
#include "mbedtls/x509_crt.h"
#include "mbedtls/ctr_drbg.h"
#include "mbedtls/entropy.h"
#include "mbedtls/sha256.h"
#include "mbedtls/base64.h"
#include "threading_alt.h"

/* Custom mbedtls utils include. */
#include "mbedtls_error.h"

/* C runtime includes. */
#include <stdio.h>
#include <string.h>

/*-----------------------------------------------------------*/

/**
 * @brief Default EC operations to ON.
 *
 */
#ifndef pkcs11configSUPPRESS_ECDSA_MECHANISM
    #define pkcs11configSUPPRESS_ECDSA_MECHANISM    0
#endif

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
 * @brief Utility for converting the high-level code in an mbedTLS error to string,
 * if the code-contains a high-level code; otherwise, using a default string.
 */
#define mbedtlsHighLevelCodeOrDefault( mbedTlsCode )        \
    ( mbedtls_strerror_highlevel( mbedTlsCode ) != NULL ) ? \
    mbedtls_strerror_highlevel( mbedTlsCode ) : pNoHighLevelMbedTlsCodeStr

/**
 * @brief Utility for converting the level-level code in an mbedTLS error to string,
 * if the code-contains a level-level code; otherwise, using a default string.
 */
#define mbedtlsLowLevelCodeOrDefault( mbedTlsCode )        \
    ( mbedtls_strerror_lowlevel( mbedTlsCode ) != NULL ) ? \
    mbedtls_strerror_lowlevel( mbedTlsCode ) : pNoLowLevelMbedTlsCodeStr

/**
 * @ingroup pkcs11_macros
 * @brief Macro for logging in PKCS #11.
 *
 */
#define PKCS11_PRINT( X )            configPRINTF( X )

/**
 * @ingroup pkcs11_macros
 * @brief Macro for logging warnings in PKCS #11.
 *
 */
#define PKCS11_WARNING_PRINT( X )    /* configPRINTF( X ) */

/**
 * @ingroup pkcs11_macros
 * @brief Indicates that no PKCS #11 operation is underway for given session.
 *
 */
#define pkcs11NO_OPERATION     ( ( CK_MECHANISM_TYPE ) -1 )

/**
 * @ingroup pkcs11_macros
 * @brief Max size of a public key.
 * TODO: How long is a typical RSA key anyhow?
 */
#define MAX_PUBLIC_KEY_SIZE    3000


/**
 * @ingroup pkcs11_macros
 * @brief Max key length of a key.
 * TODO: How long is a typical RSA key anyhow?
 */
#define MAX_LENGTH_KEY                3000

/**
 * @ingroup pkcs11_macros
 * @brief The size of the buffer malloc'ed for the exported public key in C_GenerateKeyPair.
 *
 */
#define pkcs11KEY_GEN_MAX_DER_SIZE    200

/**
 * @ingroup pkcs11_macros
 * @brief The slot ID to be returned by this PKCS #11 implementation.
 *
 * @note that this implementation does not have a concept of "slots" so this number is arbitrary.
 */
#define pkcs11SLOT_ID                 1

/**
 * @ingroup pkcs11_macros
 * @brief Private defines for checking that attribute templates are complete.
 */
#define LABEL_IN_TEMPLATE             ( 1U )           /**< Bit set for label in template. */
#define PRIVATE_IN_TEMPLATE           ( 1U << 1 )      /**< Bit set for private key in in template. */
#define SIGN_IN_TEMPLATE              ( 1U << 2 )      /**< Bit set for sign in template. */
#define EC_PARAMS_IN_TEMPLATE         ( 1U << 3 )      /**< Bit set for EC params in template. */
#define VERIFY_IN_TEMPLATE            ( 1U << 4 )      /**< Bit set for verify in template. */

/**
 * @ingroup pkcs11_macros
 * @brief Macro to signify an invalid PKCS #11 key type.
 */
#define PKCS11_INVALID_KEY_TYPE       ( ( CK_KEY_TYPE ) 0xFFFFFFFFUL )

/**
 * @ingroup pkcs11_datatypes
 * @brief PKCS #11 object container.
 *
 * Maps a PKCS #11 object handle to it's label.
 *
 */
typedef struct P11Object_t
{
    CK_OBJECT_HANDLE xHandle;                           /**< @brief The "PAL Handle". */
    CK_BYTE xLabel[ pkcs11configMAX_LABEL_LENGTH + 1 ]; /**< @brief Plus 1 for the null terminator. */
} P11Object_t;

/**
 * @ingroup pkcs11_datatypes
 * @brief PKCS #11 object container list.
 *
 * This structure helps the iot_pkcs11_mbedtls.c maintain a mapping of all objects in one place.
 * Because some objects exist in device NVM and must be called by their "PAL Handles", and other
 * objects do not have designated NVM storage locations, the ObjectList maintains a list
 * of what object handles are available.
 */
typedef struct P11ObjectList_t
{
    SemaphoreHandle_t xMutex;                            /**< @brief Mutex that protects write operations to the xObjects array. */
    StaticSemaphore_t xMutexBuffer;                      /**< @brief Mutex buffer in order to avoid calling Malloc. */
    P11Object_t xObjects[ pkcs11configMAX_NUM_OBJECTS ]; /**< @brief List of PKCS #11 objects. */
} P11ObjectList_t;

/**
 * @ingroup pkcs11_datatypes
 * @brief PKCS #11 Module Object
 *
 */
typedef struct P11Struct_t
{
    CK_BBOOL xIsInitialized;                     /**< @brief Indicates whether PKCS #11 module has been initialized with a call to C_Initialize. */
    mbedtls_ctr_drbg_context xMbedDrbgCtx;       /**< @brief CTR-DRBG context for PKCS #11 module - used to generate pseudo-random numbers. */
    mbedtls_entropy_context xMbedEntropyContext; /**< @brief Entropy context for PKCS #11 module - used to collect entropy for RNG. */
    SemaphoreHandle_t xSessionMutex;             /**< @brief Mutex that protects write operations to the pxSession array. */
    StaticSemaphore_t xSessionMutexBuffer;       /**< @brief Mutex buffer in order to avoid calling Malloc. */
    P11ObjectList_t xObjectList;                 /**< @brief List of PKCS #11 objects that have been found/created since module initialization.
                                                  *         The array position indicates the "App Handle"  */
} P11Struct_t;


/**
 * @ingroup pkcs11_datatypes
 * @brief Session structure.
 */
typedef struct P11Session
{
    CK_ULONG ulState;                            /**< @brief Stores the session flags. */
    CK_BBOOL xOpened;                            /**< @brief Set to CK_TRUE upon opening PKCS #11 session. */
    CK_MECHANISM_TYPE xOperationDigestMechanism; /**< @brief Indicates if a digest operation is in progress. */
    CK_BYTE * pxFindObjectLabel;                 /**< @brief Pointer to the label for the search in progress. Should be NULL if no search in progress. */
    uint8_t xFindObjectLabelLength;              /**< @brief Find object length flag. */
    CK_MECHANISM_TYPE xOperationVerifyMechanism; /**< @brief The mechanism of verify operation in progress. Set during C_VerifyInit. */
    SemaphoreHandle_t xVerifyMutex;              /**< @brief Protects the verification key from being modified while in use. */
    mbedtls_pk_context xVerifyKey;               /**< @brief Verification key.  Set during C_VerifyInit. */
    CK_MECHANISM_TYPE xOperationSignMechanism;   /**< @brief Mechanism of the sign operation in progress. Set during C_SignInit. */
    SemaphoreHandle_t xSignMutex;                /**< @brief Protects the signing key from being modified while in use. */
    mbedtls_pk_context xSignKey;                 /**< @brief Signing key.  Set during C_SignInit. */
    mbedtls_sha256_context xSHA256Context;       /**< @brief Context for in progress digest operation. */
} P11Session_t;

/*-----------------------------------------------------------*/

/**
 * @brief The global PKCS #11 module object.
 * Entropy/randomness and object lists are shared across PKCS #11 sessions.
 */
static P11Struct_t xP11Context;

/**
 * @brief The global PKCS #11 session list.
 */
static P11Session_t pxP11Sessions[ pkcs11configMAX_SESSIONS ] = { 0 };

/**
 * @brief Helper to check if the current session is initialized and valid.
 */
static CK_RV prvCheckValidSessionAndModule( const P11Session_t * pxSession )
{
    CK_RV xResult = CKR_OK;

    /** MISRA Rule 10.5 - Cannot cast from unsigned to signed.
     * The rule 10.5 is violated because type of the boolean macros defined by PKCS #11
     * are 0 and 1, which results in a signed integer, meanwhile the underlying
     * type of CK_BBOOL is an unsigned char.
     *
     * This means that our implementation conforms to the exception provided by MISRA
     * To quote MISRA: "An integer constant expression with the value 0 or 1 of either signedness
     * may be cast to a type which is defined as essentially Boolean.
     * This allows the implementation of non-C99 Boolean models."
     */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    if( xP11Context.xIsInitialized == ( CK_BBOOL ) CK_FALSE )
    {
        xResult = CKR_CRYPTOKI_NOT_INITIALIZED;
    }
    else if( pxSession == NULL )
    {
        xResult = CKR_SESSION_HANDLE_INVALID;
    }
    /* coverity[misra_c_2012_rule_10_5_violation] */
    else if( pxSession->xOpened == ( CK_BBOOL ) CK_FALSE )
    {
        xResult = CKR_SESSION_HANDLE_INVALID;
    }
    else
    {
        /* Session is initialized and valid. */
    }

    return xResult;
}

/**
 * @brief Maps an opaque caller session handle into its internal state structure.
 */
static P11Session_t * prvSessionPointerFromHandle( CK_SESSION_HANDLE xSession )
{
    P11Session_t * pxSession = NULL;

    if( ( xSession >= 1 ) && ( xSession <= pkcs11configMAX_SESSIONS ) )
    {
        /* Decrement by 1, invalid handles in PKCS #11 are defined to be 0. */
        pxSession = &pxP11Sessions[ xSession - 1 ];
    }

    return pxSession;
}

/**
 * @brief Determines if an operation is in progress.
 */
static CK_BBOOL prvOperationActive( const P11Session_t * pxSession )
{
    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    CK_BBOOL xResult = ( CK_BBOOL ) CK_FALSE;

    if( ( pxSession->xOperationDigestMechanism != pkcs11NO_OPERATION ) ||
        ( pxSession->xOperationSignMechanism != pkcs11NO_OPERATION ) ||
        ( pxSession->xOperationVerifyMechanism != pkcs11NO_OPERATION ) ||
        ( pxSession->pxFindObjectLabel != NULL ) )
    {
        /* See explanation in prvCheckValidSessionAndModule for this exception. */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        xResult = ( CK_BBOOL ) CK_TRUE;
    }

    return xResult;
}

/*
 * PKCS#11 module implementation.
 */

/**
 * @functions_page{pkcs11_mbedtls,PKCS #11 mbedTLS, PKCS #11 mbedTLS}
 * @functions_brief{PKCS #11 mbedTLS implementation}
 * - @function_name{pkcs11_mbedtls_function_c_initialize}
 * @function_brief{pkcs11_mbedtls_function_c_initialize}
 * - @function_name{pkcs11_mbedtls_function_c_finalize}
 * @function_brief{pkcs11_mbedtls_function_c_finalize}
 * - @function_name{pkcs11_mbedtls_function_c_getfunctionlist}
 * @function_brief{pkcs11_mbedtls_function_c_getfunctionlist}
 * - @function_name{pkcs11_mbedtls_function_c_getslotlist}
 * @function_brief{pkcs11_mbedtls_function_c_getslotlist}
 * - @function_name{pkcs11_mbedtls_function_c_gettokeninfo}
 * @function_brief{pkcs11_mbedtls_function_c_gettokeninfo}
 * - @function_name{pkcs11_mbedtls_function_c_getmechanisminfo}
 * @function_brief{pkcs11_mbedtls_function_c_getmechanisminfo}
 * - @function_name{pkcs11_mbedtls_function_c_inittoken}
 * @function_brief{pkcs11_mbedtls_function_c_inittoken}
 * - @function_name{pkcs11_mbedtls_function_c_opensession}
 * @function_brief{pkcs11_mbedtls_function_c_opensession}
 * - @function_name{pkcs11_mbedtls_function_c_closesession}
 * @function_brief{pkcs11_mbedtls_function_c_closesession}
 * - @function_name{pkcs11_mbedtls_function_c_login}
 * @function_brief{pkcs11_mbedtls_function_c_login}
 * - @function_name{pkcs11_mbedtls_function_c_createobject}
 * @function_brief{pkcs11_mbedtls_function_c_createobject}
 * - @function_name{pkcs11_mbedtls_function_c_destroyobject}
 * @function_brief{pkcs11_mbedtls_function_c_destroyobject}
 * - @function_name{pkcs11_mbedtls_function_c_getattributevalue}
 * @function_brief{pkcs11_mbedtls_function_c_getattributevalue}
 * - @function_name{pkcs11_mbedtls_function_c_findobjectsinit}
 * @function_brief{pkcs11_mbedtls_function_c_findobjectsinit}
 * - @function_name{pkcs11_mbedtls_function_c_findobjects}
 * @function_brief{pkcs11_mbedtls_function_c_findobjects}
 * - @function_name{pkcs11_mbedtls_function_c_findobjectsfinal}
 * @function_brief{pkcs11_mbedtls_function_c_findobjectsfinal}
 * - @function_name{pkcs11_mbedtls_function_c_digestinit}
 * @function_brief{pkcs11_mbedtls_function_c_digestinit}
 * - @function_name{pkcs11_mbedtls_function_c_digestupdate}
 * @function_brief{pkcs11_mbedtls_function_c_digestupdate}
 * - @function_name{pkcs11_mbedtls_function_c_digestfinal}
 * @function_brief{pkcs11_mbedtls_function_c_digestfinal}
 * - @function_name{pkcs11_mbedtls_function_c_signinit}
 * @function_brief{pkcs11_mbedtls_function_c_signinit}
 * - @function_name{pkcs11_mbedtls_function_c_sign}
 * - @function_name{pkcs11_mbedtls_function_c_verifyinit}
 * @function_brief{pkcs11_mbedtls_function_c_verifyinit}
 * - @function_name{pkcs11_mbedtls_function_c_verify}
 * @function_brief{pkcs11_mbedtls_function_c_verify}
 * - @function_name{pkcs11_mbedtls_function_c_generatekeypair}
 * @function_brief{pkcs11_mbedtls_function_c_generatekeypair}
 * - @function_name{pkcs11_mbedtls_function_c_generaterandom}
 * @function_brief{pkcs11_mbedtls_function_c_generaterandom}
 */

/**
 * @function_page{C_Initialize,pkcs11_mbedtls,c_initialize}
 * @function_snippet{pkcs11_mbedtls,c_initialize,this}
 * @copydoc C_Initialize
 * @function_page{C_Finalize,pkcs11_mbedtls,c_finalize}
 * @function_snippet{pkcs11_mbedtls,c_finalize,this}
 * @copydoc C_Finalize
 * @function_page{C_GetFunctionList,pkcs11_mbedtls,c_getfunctionlist}
 * @function_snippet{pkcs11_mbedtls,c_getfunctionlist,this}
 * @copydoc C_GetFunctionList
 * @function_page{C_GetSlotList,pkcs11_mbedtls,c_getslotlist}
 * @function_snippet{pkcs11_mbedtls,c_getslotlist,this}
 * @copydoc C_GetSlotList
 * @function_page{C_GetTokenInfo,pkcs11_mbedtls,c_gettokeninfo}
 * @function_snippet{pkcs11_mbedtls,c_gettokeninfo,this}
 * @copydoc C_GetTokenInfo
 * @function_page{C_GetMechanismInfo,pkcs11_mbedtls,c_getmechanisminfo}
 * @function_snippet{pkcs11_mbedtls,c_getmechanisminfo,this}
 * @copydoc C_GetMechanismInfo
 * @function_page{C_InitToken,pkcs11_mbedtls,c_inittoken}
 * @function_snippet{pkcs11_mbedtls,c_inittoken,this}
 * @copydoc C_InitToken
 * @function_page{C_OpenSession,pkcs11_mbedtls,c_opensession}
 * @function_snippet{pkcs11_mbedtls,c_opensession,this}
 * @copydoc C_OpenSession
 * @function_page{C_CloseSession,pkcs11_mbedtls,c_closesession}
 * @function_snippet{pkcs11_mbedtls,c_closesession,this}
 * @copydoc C_CloseSession
 * @function_page{C_Login,pkcs11_mbedtls,c_login}
 * @function_snippet{pkcs11_mbedtls,c_login,this}
 * @copydoc C_Login
 * @function_page{C_CreateObject,pkcs11_mbedtls,c_createobject}
 * @function_snippet{pkcs11_mbedtls,c_createobject,this}
 * @copydoc C_CreateObject
 * @function_page{C_DestroyObject,pkcs11_mbedtls,c_destroyobject}
 * @function_snippet{pkcs11_mbedtls,c_destroyobject,this}
 * @copydoc C_DestroyObject
 * @function_page{C_GetAttributeValue,pkcs11_mbedtls,c_getattributevalue}
 * @function_snippet{pkcs11_mbedtls,c_getattributevalue,this}
 * @copydoc C_GetAttributeValue
 * @function_page{C_FindObjectsInit,pkcs11_mbedtls,c_findobjectsinit}
 * @function_snippet{pkcs11_mbedtls,c_findobjectsinit,this}
 * @copydoc C_FindObjectsInit
 * @function_page{C_FindObjects,pkcs11_mbedtls,c_findobjects}
 * @function_snippet{pkcs11_mbedtls,c_findobjects,this}
 * @copydoc C_FindObjects
 * @function_page{C_FindObjectsFinal,pkcs11_mbedtls,c_findobjectsfinal}
 * @function_snippet{pkcs11_mbedtls,c_findobjectsfinal,this}
 * @copydoc C_FindObjectsFinal
 * @function_page{C_DigestInit,pkcs11_mbedtls,c_digestinit}
 * @function_snippet{pkcs11_mbedtls,c_digestinit,this}
 * @copydoc C_DigestInit
 * @function_page{C_DigestUpdate,pkcs11_mbedtls,c_digestupdate}
 * @function_snippet{pkcs11_mbedtls,c_digestupdate,this}
 * @copydoc C_DigestUpdate
 * @function_page{C_DigestFinal,pkcs11_mbedtls,c_digestfinal}
 * @function_snippet{pkcs11_mbedtls,c_digestfinal,this}
 * @copydoc C_DigestFinal
 * @function_page{C_SignInit,pkcs11_mbedtls,c_signinit}
 * @function_snippet{pkcs11_mbedtls,c_signinit,this}
 * @copydoc C_SignInit
 * @function_page{C_Sign,pkcs11_mbedtls,c_sign}
 * @function_snippet{pkcs11_mbedtls,c_sign,this}
 * @copydoc C_Sign
 * @function_page{C_VerifyInit,pkcs11_mbedtls,c_verifyinit}
 * @function_snippet{pkcs11_mbedtls,c_verifyinit,this}
 * @copydoc C_VerifyInit
 * @function_page{C_Verify,pkcs11_mbedtls,c_verify}
 * @function_snippet{pkcs11_mbedtls,c_verify,this}
 * @copydoc C_Verify
 * @function_page{C_GenerateKeyPair,pkcs11_mbedtls,c_generatekeypair}
 * @function_snippet{pkcs11_mbedtls,c_generatekeypair,this}
 * @copydoc C_GenerateKeyPair
 * @function_page{C_GenerateRandom,pkcs11_mbedtls,c_generaterandom}
 * @function_snippet{pkcs11_mbedtls,c_generate_random,this}
 * @copydoc C_GenerateRandom
 */
/*-----------------------------------------------------------*/

/**
 * @brief Initialize mbedTLS
 * @note: Before prvMbedTLS_Initialize can be called, CRYPTO_Init()
 * must be called to initialize the mbedTLS mutex functions.
 */
static CK_RV prvMbedTLS_Initialize( void )
{
    CK_RV xResult = CKR_OK;

    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    if( xP11Context.xIsInitialized == ( CK_BBOOL ) CK_TRUE )
    {
        xResult = CKR_CRYPTOKI_ALREADY_INITIALIZED;
    }
    else
    {
        ( void ) memset( &xP11Context, 0, sizeof( xP11Context ) );
        xP11Context.xObjectList.xMutex = xSemaphoreCreateMutexStatic(
            &xP11Context.xObjectList.xMutexBuffer );

        xP11Context.xSessionMutex = xSemaphoreCreateMutexStatic(
            &xP11Context.xSessionMutexBuffer );

        if( ( xP11Context.xObjectList.xMutex == NULL ) || ( xP11Context.xSessionMutex == NULL ) )
        {
            xResult = CKR_HOST_MEMORY;
        }
    }

    if( xResult == CKR_OK )
    {
        /* Initialize the entropy source and DRBG for the PKCS#11 module */
        mbedtls_entropy_init( &xP11Context.xMbedEntropyContext );
        mbedtls_ctr_drbg_init( &xP11Context.xMbedDrbgCtx );

        if( 0 != mbedtls_ctr_drbg_seed( &xP11Context.xMbedDrbgCtx,
                                        mbedtls_entropy_func,
                                        &xP11Context.xMbedEntropyContext,
                                        NULL,
                                        0 ) )
        {
            xResult = CKR_FUNCTION_FAILED;
        }
        else
        {
            /* See explanation in prvCheckValidSessionAndModule for this exception. */
            /* coverity[misra_c_2012_rule_10_5_violation] */
            xP11Context.xIsInitialized = ( CK_BBOOL ) CK_TRUE;
        }
    }

    return xResult;
}

/**
 * @brief Searches a template for the CKA_CLASS attribute.
 *
 */
static CK_RV prvGetObjectClass( const CK_ATTRIBUTE * pxTemplate,
                                CK_ULONG ulCount,
                                CK_OBJECT_CLASS * pxClass )
{
    CK_RV xResult = CKR_TEMPLATE_INCOMPLETE;
    uint32_t ulIndex = 0;

    /* Search template for class attribute. */
    for( ulIndex = 0; ulIndex < ulCount; ulIndex++ )
    {
        CK_ATTRIBUTE xAttribute = pxTemplate[ ulIndex ];

        if( xAttribute.type == CKA_CLASS )
        {
            ( void ) memcpy( pxClass, xAttribute.pValue, sizeof( CK_OBJECT_CLASS ) );
            xResult = CKR_OK;
            break;
        }
    }

    return xResult;
}

/**
 * @brief Parses attribute values for a certificate.
 *
 */
static CK_RV prvCertAttParse( CK_ATTRIBUTE * pxAttribute,
                              CK_CERTIFICATE_TYPE * pxCertificateType,
                              CK_BYTE_PTR * ppxCertificateValue,
                              CK_ULONG * pxCertificateLength,
                              CK_ATTRIBUTE ** ppxLabel )
{
    CK_RV xResult = CKR_OK;
    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    CK_BBOOL xBool = ( CK_BBOOL ) CK_FALSE;

    switch( pxAttribute->type )
    {
        case ( CKA_VALUE ):
            *ppxCertificateValue = pxAttribute->pValue;
            *pxCertificateLength = pxAttribute->ulValueLen;
            break;

        case ( CKA_LABEL ):

            if( pxAttribute->ulValueLen <= pkcs11configMAX_LABEL_LENGTH )
            {
                *ppxLabel = pxAttribute;
            }
            else
            {
                xResult = CKR_DATA_LEN_RANGE;
            }

            break;

        case ( CKA_CERTIFICATE_TYPE ):
            ( void ) memcpy( pxCertificateType, pxAttribute->pValue, sizeof( CK_CERTIFICATE_TYPE ) );

            if( *pxCertificateType != CKC_X_509 )
            {
                xResult = CKR_ATTRIBUTE_VALUE_INVALID;
            }

            break;

        case ( CKA_TOKEN ):
            ( void ) memcpy( &xBool, pxAttribute->pValue, sizeof( CK_BBOOL ) );

            /* See explanation in prvCheckValidSessionAndModule for this exception. */
            /* coverity[misra_c_2012_rule_10_5_violation] */
            if( xBool != ( CK_BBOOL ) CK_TRUE )
            {
                PKCS11_PRINT( ( "ERROR: Only token key object is supported. \r\n" ) );
                xResult = CKR_ATTRIBUTE_VALUE_INVALID;
            }

            break;

        case ( CKA_CLASS ):
        case ( CKA_SUBJECT ):

            /* Do nothing.  This was already parsed out of the template previously. */
            break;

        default:
            xResult = CKR_ATTRIBUTE_TYPE_INVALID;
            break;
    }

    return xResult;
}

/**
 * @brief Parses attribute values for a RSA Key.
 *
 */
static CK_RV prvRsaKeyAttParse( const CK_ATTRIBUTE * pxAttribute,
                                const mbedtls_pk_context * pxMbedContext )
{
    CK_RV xResult = CKR_OK;
    int32_t lMbedReturn = 0;
    CK_BBOOL xBool;
    mbedtls_rsa_context * pxRsaContext = ( mbedtls_rsa_context * ) pxMbedContext->pk_ctx;

    switch( pxAttribute->type )
    {
        case ( CKA_CLASS ):
        case ( CKA_KEY_TYPE ):
        case ( CKA_LABEL ):
            /* Do nothing. These values were parsed previously. */
            break;

        case ( CKA_SIGN ):
        case ( CKA_TOKEN ):
            ( void ) memcpy( &xBool, pxAttribute->pValue, pxAttribute->ulValueLen );

            /* See explanation in prvCheckValidSessionAndModule for this exception. */
            /* coverity[misra_c_2012_rule_10_5_violation] */
            if( xBool != ( CK_BBOOL ) CK_TRUE )
            {
                PKCS11_PRINT( ( "Only RSA private keys with signing permissions supported. \r\n" ) );
                xResult = CKR_ATTRIBUTE_VALUE_INVALID;
            }

            break;

        case ( CKA_MODULUS ):
            lMbedReturn = mbedtls_rsa_import_raw( pxRsaContext,
                                                  pxAttribute->pValue, pxAttribute->ulValueLen, /* N */
                                                  NULL, 0,                                      /* P */
                                                  NULL, 0,                                      /* Q */
                                                  NULL, 0,                                      /* D */
                                                  NULL, 0 );                                    /* E */
            break;

        case ( CKA_PUBLIC_EXPONENT ):
            lMbedReturn = mbedtls_rsa_import_raw( pxRsaContext,
                                                  NULL, 0,                                        /* N */
                                                  NULL, 0,                                        /* P */
                                                  NULL, 0,                                        /* Q */
                                                  NULL, 0,                                        /* D */
                                                  pxAttribute->pValue, pxAttribute->ulValueLen ); /* E */
            break;

        case ( CKA_PRIME_1 ):
            lMbedReturn = mbedtls_rsa_import_raw( pxRsaContext,
                                                  NULL, 0,                                      /* N */
                                                  pxAttribute->pValue, pxAttribute->ulValueLen, /* P */
                                                  NULL, 0,                                      /* Q */
                                                  NULL, 0,                                      /* D */
                                                  NULL, 0 );                                    /* E */
            break;

        case ( CKA_PRIME_2 ):
            lMbedReturn = mbedtls_rsa_import_raw( pxRsaContext,
                                                  NULL, 0,                                      /* N */
                                                  NULL, 0,                                      /* P */
                                                  pxAttribute->pValue, pxAttribute->ulValueLen, /* Q */
                                                  NULL, 0,                                      /* D */
                                                  NULL, 0 );                                    /* E */
            break;

        case ( CKA_PRIVATE_EXPONENT ):
            lMbedReturn = mbedtls_rsa_import_raw( pxRsaContext,
                                                  NULL, 0,                                      /* N */
                                                  NULL, 0,                                      /* P */
                                                  NULL, 0,                                      /* Q */
                                                  pxAttribute->pValue, pxAttribute->ulValueLen, /* D */
                                                  NULL, 0 );                                    /* E */
            break;

        case ( CKA_EXPONENT_1 ):
            lMbedReturn = mbedtls_mpi_read_binary( &pxRsaContext->DP, pxAttribute->pValue, pxAttribute->ulValueLen );
            break;

        case ( CKA_EXPONENT_2 ):
            lMbedReturn = mbedtls_mpi_read_binary( &pxRsaContext->DQ, pxAttribute->pValue, pxAttribute->ulValueLen );
            break;

        case ( CKA_COEFFICIENT ):
            lMbedReturn = mbedtls_mpi_read_binary( &pxRsaContext->QP, pxAttribute->pValue, pxAttribute->ulValueLen );
            break;

        default:
            PKCS11_PRINT( ( "Unknown attribute found for RSA private key. %d \r\n", pxAttribute->type ) );
            xResult = CKR_ATTRIBUTE_TYPE_INVALID;
            break;
    }

    if( lMbedReturn != 0 )
    {
        PKCS11_PRINT( ( "mbedTLS create private RSA key failed with error %s : ",
                        mbedtlsHighLevelCodeOrDefault( lMbedReturn ) ) );
        PKCS11_PRINT( ( "%s \r\n",
                        mbedtlsLowLevelCodeOrDefault( lMbedReturn ) ) );
        xResult = CKR_FUNCTION_FAILED;
    }

    return xResult;
}

/**
 * @brief Parses attribute values for a private EC Key.
 *
 */
static CK_RV prvEcPrivKeyAttParse( const CK_ATTRIBUTE * pxAttribute,
                                   const mbedtls_pk_context * pxMbedContext )
{
    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    CK_BBOOL xBool = ( CK_BBOOL ) CK_FALSE;
    int32_t lMbedReturn = 0;
    CK_RV xResult = CKR_OK;
    mbedtls_ecp_keypair * pxKeyPair = ( mbedtls_ecp_keypair * ) pxMbedContext->pk_ctx;

    if( pxAttribute->type == CKA_SIGN )
    {
        ( void ) memcpy( &xBool, pxAttribute->pValue, sizeof( CK_BBOOL ) );

        /* See explanation in prvCheckValidSessionAndModule for this exception. */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        if( xBool == ( CK_BBOOL ) CK_FALSE )
        {
            xResult = CKR_ATTRIBUTE_VALUE_INVALID;
            PKCS11_PRINT( ( "ERROR: Only EC private keys with signing privileges are supported. \r\n" ) );
        }
    }
    else
    {
        lMbedReturn = mbedtls_mpi_read_binary( &pxKeyPair->d,
                                               pxAttribute->pValue,
                                               pxAttribute->ulValueLen );

        if( lMbedReturn != 0 )
        {
            xResult = CKR_FUNCTION_FAILED;
            PKCS11_PRINT( ( "mbedTLS mpi read binary failed with error %s : ",
                            mbedtlsHighLevelCodeOrDefault( lMbedReturn ) ) );
            PKCS11_PRINT( ( "%s \r\n",
                            mbedtlsLowLevelCodeOrDefault( lMbedReturn ) ) );
        }
    }

    return xResult;
}

/**
 * @brief Parses attribute values for a public EC Key.
 *
 */
static CK_RV prvEcPubKeyAttParse( const CK_ATTRIBUTE * pxAttribute,
                                  const mbedtls_pk_context * pxMbedContext )
{
    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    CK_BBOOL xBool = ( CK_BBOOL ) CK_FALSE;
    int32_t lMbedReturn = 0;
    CK_RV xResult = CKR_OK;
    mbedtls_ecp_keypair * pxKeyPair = ( mbedtls_ecp_keypair * ) pxMbedContext->pk_ctx;

    if( pxAttribute->type == CKA_VERIFY )
    {
        ( void ) memcpy( &xBool, pxAttribute->pValue, pxAttribute->ulValueLen );

        /* See explanation in prvCheckValidSessionAndModule for this exception. */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        if( xBool == ( CK_BBOOL ) CK_FALSE )
        {
            xResult = CKR_ATTRIBUTE_VALUE_INVALID;
            PKCS11_PRINT( ( "Only EC public keys with verify permissions supported. \r\n" ) );
        }
    }
    else
    {
        lMbedReturn = mbedtls_ecp_point_read_binary( &pxKeyPair->grp,
                                                     &pxKeyPair->Q,
                                                     ( ( uint8_t * ) ( pxAttribute->pValue ) + 2U ),
                                                     ( pxAttribute->ulValueLen - 2U ) );

        if( lMbedReturn != 0 )
        {
            xResult = CKR_FUNCTION_FAILED;
            PKCS11_PRINT( ( "mbedTLS ecp point read binary failed with %s : ",
                            mbedtlsHighLevelCodeOrDefault( lMbedReturn ) ) );
            PKCS11_PRINT( ( "%s \r\n",
                            mbedtlsLowLevelCodeOrDefault( lMbedReturn ) ) );
        }
    }

    return xResult;
}

/**
 * @brief Parses attribute values for an EC Key.
 *
 */
static CK_RV prvEcKeyAttParse( const CK_ATTRIBUTE * pxAttribute,
                               const mbedtls_pk_context * pxMbedContext,
                               CK_BBOOL xIsPrivate )
{
    CK_RV xResult = CKR_OK;
    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    CK_BBOOL xBool = ( CK_BBOOL ) CK_FALSE;
    const CK_BYTE pxEcCurve[] = pkcs11DER_ENCODED_OID_P256;
    const CK_BYTE * pxEcAttVal = NULL;
    const CK_BBOOL * pxEcBoolAtt = NULL;

    /* Common EC key attributes. */
    switch( pxAttribute->type )
    {
        case ( CKA_CLASS ):
        case ( CKA_KEY_TYPE ):
        case ( CKA_LABEL ):
            /* Do nothing. These attribute types were checked previously. */
            break;

        case ( CKA_TOKEN ):
            pxEcBoolAtt = ( CK_BBOOL * ) pxAttribute->pValue;
            ( void ) memcpy( &xBool, pxEcBoolAtt, sizeof( CK_BBOOL ) );

            /* See explanation in prvCheckValidSessionAndModule for this exception. */
            /* coverity[misra_c_2012_rule_10_5_violation] */
            if( xBool != ( CK_BBOOL ) CK_TRUE )
            {
                PKCS11_PRINT( ( "ERROR: Only token key creation is supported. \r\n" ) );
                xResult = CKR_ATTRIBUTE_VALUE_INVALID;
            }

            break;

        case ( CKA_EC_PARAMS ):
            pxEcAttVal = ( CK_BYTE * ) pxAttribute->pValue;

            if( memcmp( pxEcCurve, pxEcAttVal, pxAttribute->ulValueLen ) != 0 )
            {
                xResult = CKR_TEMPLATE_INCONSISTENT;
                PKCS11_PRINT( ( "ERROR: Only elliptic curve P-256 is supported.\r\n" ) );
            }

            break;

        case ( CKA_VERIFY ):
        case ( CKA_EC_POINT ):

            /* See explanation in prvCheckValidSessionAndModule for this exception. */
            /* coverity[misra_c_2012_rule_10_5_violation] */
            if( xIsPrivate == ( CK_BBOOL ) CK_FALSE )
            {
                xResult = prvEcPubKeyAttParse( pxAttribute, pxMbedContext );
            }
            else
            {
                xResult = CKR_ATTRIBUTE_VALUE_INVALID;
            }

            break;

        case ( CKA_SIGN ):
        case ( CKA_VALUE ):

            /* See explanation in prvCheckValidSessionAndModule for this exception. */
            /* coverity[misra_c_2012_rule_10_5_violation] */
            if( xIsPrivate == ( CK_BBOOL ) CK_TRUE )
            {
                xResult = prvEcPrivKeyAttParse( pxAttribute, pxMbedContext );
            }
            else
            {
                xResult = CKR_ATTRIBUTE_VALUE_INVALID;
            }

            break;

        default:
            PKCS11_PRINT( ( "Unknown attribute found for an EC public key. %d \r\n", pxAttribute->type ) );
            xResult = CKR_ATTRIBUTE_TYPE_INVALID;
            break;
    }

    return xResult;
}

/*-----------------------------------------------------------------------*/
/* Functions for maintaining the PKCS #11 module's label-handle lookups. */
/*-----------------------------------------------------------------------*/


/**
 * @brief Searches the PKCS #11 module's object list for label and provides handle.
 *
 * @param[in] pcLabel            Array containing label.
 * @param[in] xLabelLength       Length of the label, in bytes.
 * @param[out] pxPalHandle       Pointer to the PAL handle to be provided.
 *                               CK_INVALID_HANDLE if no object found.
 * @param[out] pxAppHandle       Pointer to the application handle to be provided.
 *                               CK_INVALID_HANDLE if no object found.
 */
static void prvFindObjectInListByLabel( const uint8_t * pcLabel,
                                        size_t xLabelLength,
                                        CK_OBJECT_HANDLE_PTR pxPalHandle,
                                        CK_OBJECT_HANDLE_PTR pxAppHandle )
{
    uint32_t ulIndex;

    *pxPalHandle = CK_INVALID_HANDLE;
    *pxAppHandle = CK_INVALID_HANDLE;

    for( ulIndex = 0; ulIndex < pkcs11configMAX_NUM_OBJECTS; ulIndex++ )
    {
        if( 0 == memcmp( pcLabel, xP11Context.xObjectList.xObjects[ ulIndex ].xLabel, xLabelLength ) )
        {
            *pxPalHandle = xP11Context.xObjectList.xObjects[ ulIndex ].xHandle;
            *pxAppHandle = ulIndex + 1UL; /* Zero is not a valid handle, so let's offset by 1. */
            break;
        }
    }
}

/**
 * @brief Looks up a PKCS #11 object's label and PAL handle given an application handle.
 *
 * @param[in] xAppHandle         The handle of the object being lookedup for, used by the application.
 * @param[out] pxPalHandle        Pointer to the handle corresponding to xPalHandle being used by the PAL.
 * @param[out] ppcLabel          Pointer to an array containing label.  NULL if object not found.
 * @param[out] pxLabelLength     Pointer to label length (includes a string null terminator).
 *                               0 if no object found.
 */
static void prvFindObjectInListByHandle( CK_OBJECT_HANDLE xAppHandle,
                                         CK_OBJECT_HANDLE_PTR pxPalHandle,
                                         uint8_t ** ppcLabel,
                                         size_t * pxLabelLength )
{
    uint32_t ulIndex = xAppHandle - 1UL;

    *ppcLabel = NULL;
    *pxLabelLength = 0;
    *pxPalHandle = CK_INVALID_HANDLE;

    if( ulIndex < pkcs11configMAX_NUM_OBJECTS )
    {
        if( xP11Context.xObjectList.xObjects[ ulIndex ].xHandle != CK_INVALID_HANDLE )
        {
            *ppcLabel = xP11Context.xObjectList.xObjects[ ulIndex ].xLabel;
            *pxLabelLength = strlen( ( const char * ) xP11Context.xObjectList.xObjects[ ulIndex ].xLabel ) + 1UL;
            *pxPalHandle = xP11Context.xObjectList.xObjects[ ulIndex ].xHandle;
        }
    }
}

/**
 * @brief Removes an object from the module object list (xP11Context.xObjectList)
 *
 * @warning This does not delete the object from NVM.
 *
 * @param[in] xAppHandle     Application handle of the object to be deleted.
 *
 */
static CK_RV prvDeleteObjectFromList( CK_OBJECT_HANDLE xAppHandle )
{
    CK_RV xResult = CKR_OK;
    BaseType_t xGotSemaphore = pdFALSE;
    uint32_t ulIndex = xAppHandle - 1;

    if( ulIndex >= pkcs11configMAX_NUM_OBJECTS )
    {
        xResult = CKR_OBJECT_HANDLE_INVALID;
    }

    if( xResult == CKR_OK )
    {
        xGotSemaphore = xSemaphoreTake( xP11Context.xObjectList.xMutex, portMAX_DELAY );
    }

    if( xGotSemaphore == pdTRUE )
    {
        if( xP11Context.xObjectList.xObjects[ ulIndex ].xHandle != CK_INVALID_HANDLE )
        {
            ( void ) memset( &xP11Context.xObjectList.xObjects[ ulIndex ], 0, sizeof( P11Object_t ) );
        }
        else
        {
            xResult = CKR_OBJECT_HANDLE_INVALID;
        }

        ( void ) xSemaphoreGive( xP11Context.xObjectList.xMutex );
    }
    else
    {
        xResult = CKR_CANT_LOCK;
    }

    return xResult;
}


/**
 * @brief Add an object that exists in NVM to the application object array.
 *
 * @param[in] xPalHandle         The handle used by the PKCS #11 PAL for object.
 * @param[out] pxAppHandle       Updated to contain the application handle corresponding to xPalHandle.
 * @param[in]  pcLabel           Pointer to object label.
 * @param[in] xLabelLength       Length of the PKCS #11 label.
 *
 */
static CK_RV prvAddObjectToList( CK_OBJECT_HANDLE xPalHandle,
                                 CK_OBJECT_HANDLE_PTR pxAppHandle,
                                 const uint8_t * pcLabel,
                                 size_t xLabelLength )
{
    CK_RV xResult = CKR_OK;
    BaseType_t xGotSemaphore;

    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    CK_BBOOL xObjectFound = ( CK_BBOOL ) CK_FALSE;
    int32_t lInsertIndex = -1;
    int32_t lSearchIndex = pkcs11configMAX_NUM_OBJECTS - 1;

    xGotSemaphore = xSemaphoreTake( xP11Context.xObjectList.xMutex, portMAX_DELAY );

    if( xGotSemaphore == pdTRUE )
    {
        for( lSearchIndex = pkcs11configMAX_NUM_OBJECTS - 1; lSearchIndex >= 0; lSearchIndex-- )
        {
            if( xP11Context.xObjectList.xObjects[ lSearchIndex ].xHandle == xPalHandle )
            {
                /* Object already exists in list. */
                /* See explanation in prvCheckValidSessionAndModule for this exception. */
                /* coverity[misra_c_2012_rule_10_5_violation] */
                xObjectFound = ( CK_BBOOL ) CK_TRUE;
                break;
            }
            else if( xP11Context.xObjectList.xObjects[ lSearchIndex ].xHandle == CK_INVALID_HANDLE )
            {
                lInsertIndex = lSearchIndex;
            }
            else
            {
                /* Ignore other object handles. */
            }
        }

        /* See explanation in prvCheckValidSessionAndModule for this exception. */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        if( xObjectFound == ( CK_BBOOL ) CK_FALSE )
        {
            if( lInsertIndex != -1 )
            {
                if( xLabelLength < pkcs11configMAX_LABEL_LENGTH )
                {
                    xP11Context.xObjectList.xObjects[ lInsertIndex ].xHandle = xPalHandle;
                    ( void ) memcpy( xP11Context.xObjectList.xObjects[ lInsertIndex ].xLabel, pcLabel, xLabelLength );
                    *pxAppHandle = lInsertIndex + 1;
                }
                else
                {
                    xResult = CKR_DATA_LEN_RANGE;
                }
            }
        }

        ( void ) xSemaphoreGive( xP11Context.xObjectList.xMutex );
    }
    else
    {
        xResult = CKR_CANT_LOCK;
    }

    return xResult;
}

/**
 * @brief Save a DER formatted key in the PKCS #11 PAL.
 *
 */
static CK_RV prvSaveDerKeyToPal( mbedtls_pk_context * pxMbedContext,
                                 CK_OBJECT_HANDLE_PTR pxObject,
                                 CK_ATTRIBUTE * pxLabel,
                                 CK_KEY_TYPE xKeyType,
                                 CK_BBOOL xIsPrivate )
{
    CK_RV xResult = CKR_OK;
    CK_BYTE_PTR pxDerKey;
    int32_t lDerKeyLength = 0;
    uint32_t ulActualKeyLength = 0;
    int32_t lCompare = 0;
    CK_OBJECT_HANDLE xPalHandle = CK_INVALID_HANDLE;

    pxDerKey = pvPortMalloc( MAX_PUBLIC_KEY_SIZE );

    if( pxDerKey == NULL )
    {
        xResult = CKR_HOST_MEMORY;
    }

    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    if( ( xResult == CKR_OK ) && ( xIsPrivate == ( CK_BBOOL ) CK_TRUE ) )
    {
        lDerKeyLength = mbedtls_pk_write_key_der( pxMbedContext, pxDerKey, MAX_PUBLIC_KEY_SIZE );
    }
    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    else if( ( xResult == CKR_OK ) && ( xIsPrivate == ( CK_BBOOL ) CK_FALSE ) )
    {
        lDerKeyLength = mbedtls_pk_write_pubkey_der( pxMbedContext, pxDerKey, MAX_PUBLIC_KEY_SIZE );
    }
    else
    {
        /* This function should only be called for a private or public key. */
    }

    if( xResult == CKR_OK )
    {
        if( lDerKeyLength < 0 )
        {
            PKCS11_PRINT( ( "mbedTLS sign failed with error %s : ",
                            mbedtlsHighLevelCodeOrDefault( lDerKeyLength ) ) );
            PKCS11_PRINT( ( "%s \r\n",
                            mbedtlsLowLevelCodeOrDefault( lDerKeyLength ) ) );
            xResult = CKR_FUNCTION_FAILED;
        }
        else
        {
            /* Cast to unsigned int as the result was not negative. */
            ulActualKeyLength = ( uint32_t ) lDerKeyLength;
        }
    }

    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    if( ( xResult == CKR_OK ) && ( xIsPrivate == ( CK_BBOOL ) CK_TRUE ) && ( xKeyType == CKK_EC ) )
    {
        /*
         * mbedtls_pk_write_key_der appends empty public
         * key data when saving EC private key
         * that does not have a public key associated with it.
         * a1 04        -> Application identifier of length 4
         * 03 02     -> Bit string of length 2
         *    00 00  -> "Public key"
         * https://forums.mbed.com/t/how-do-i-write-an-ec-private-key-w-no-public-key-to-der-format/4728 */

        /* If there was no public key in the structure, this byte
         * array will be appended to the valid private key.
         * It must be removed so that we can read the private
         * key back at a later time. */
        uint8_t emptyPubKey[ 6 ] = { 0xa1, 0x04, 0x03, 0x02, 0x00, 0x00 };
        lCompare = memcmp( &pxDerKey[ MAX_LENGTH_KEY - 6 ], emptyPubKey, 6 );

        if( ( lCompare == 0 ) && ( ulActualKeyLength >= 6UL ) )
        {
            /* Do not write the last 6 bytes to key storage. */
            pxDerKey[ MAX_LENGTH_KEY - lDerKeyLength + 1 ] -= ( uint8_t ) 6;
            ulActualKeyLength -= 6UL;
        }
    }

    if( xResult == CKR_OK )
    {
        xPalHandle = PKCS11_PAL_SaveObject( pxLabel,
                                            pxDerKey + ( MAX_LENGTH_KEY - lDerKeyLength ),
                                            ulActualKeyLength );

        if( xPalHandle == CK_INVALID_HANDLE )
        {
            xResult = CKR_DEVICE_MEMORY;
        }
    }

    if( xResult == CKR_OK )
    {
        xResult = prvAddObjectToList( xPalHandle, pxObject, pxLabel->pValue, pxLabel->ulValueLen );
    }

    vPortFree( pxDerKey );

    return xResult;
}


#if ( pkcs11configPAL_DESTROY_SUPPORTED != 1 )
    CK_RV PKCS11_PAL_DestroyObject( CK_OBJECT_HANDLE xHandle )
    {
        uint8_t * pcLabel = NULL;
        size_t xLabelLength = 0;
        uint32_t ulObjectLength = 0;
        /* See explanation in prvCheckValidSessionAndModule for this exception. */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        CK_BBOOL xIsPrivate = ( CK_BBOOL ) CK_TRUE;
        CK_RV xResult = CKR_OK;
        uint8_t * pxObject = NULL;
        CK_ATTRIBUTE xLabel = { 0 };
        CK_OBJECT_HANDLE xPalHandle = CK_INVALID_HANDLE;
        CK_OBJECT_HANDLE xPalHandle2 = CK_INVALID_HANDLE;
        CK_OBJECT_HANDLE xAppHandle2 = CK_INVALID_HANDLE;
        CK_BYTE_PTR pxZeroedData = NULL;

        prvFindObjectInListByHandle( xHandle, &xPalHandle, &pcLabel, &xLabelLength );

        if( pcLabel != NULL )
        {
            xResult = PKCS11_PAL_GetObjectValue( xPalHandle, &pxObject, &ulObjectLength, &xIsPrivate );

            if( xResult == CKR_OK )
            {
                /* Some ports return a pointer to memory for which using memset directly won't work. */
                pxZeroedData = pvPortMalloc( ulObjectLength );

                if( NULL != pxZeroedData )
                {
                    /* Zero out the object. */
                    ( void ) memset( pxZeroedData, 0x0, ulObjectLength );
                    /* Create an object label attribute. */
                    xLabel.type = CKA_LABEL;
                    xLabel.pValue = pcLabel;
                    xLabel.ulValueLen = xLabelLength;
                    /* Overwrite the object in NVM with zeros. */
                    xPalHandle2 = PKCS11_PAL_SaveObject( &xLabel, pxZeroedData, ulObjectLength );

                    if( xPalHandle2 != xPalHandle )
                    {
                        xResult = CKR_GENERAL_ERROR;
                    }
                }
                else
                {
                    xResult = CKR_HOST_MEMORY;
                }

                vPortFree( pxZeroedData );
            }
        }
        else
        {
            xResult = CKR_ATTRIBUTE_VALUE_INVALID;
        }

        if( xResult == CKR_OK )
        {
            if( 0 == strncmp( xLabel.pValue, pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS, xLabel.ulValueLen ) )
            {
                prvFindObjectInListByLabel( ( uint8_t * ) pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS, strlen( ( char * ) pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS ), &xPalHandle, &xAppHandle2 );
            }
            else if( 0 == strncmp( xLabel.pValue, pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS, xLabel.ulValueLen ) )
            {
                prvFindObjectInListByLabel( ( uint8_t * ) pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS, strlen( ( char * ) pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS ), &xPalHandle, &xAppHandle2 );
            }
            else
            {
                PKCS11_WARNING_PRINT( ( "Warning: Trying to destroy an object with an unknown label. \r\n" ) );
            }

            if( xPalHandle != CK_INVALID_HANDLE )
            {
                xResult = prvDeleteObjectFromList( xAppHandle2 );
            }

            if( xResult != CKR_OK )
            {
                PKCS11_WARNING_PRINT( ( "Warning: Failed to remove xAppHandle2 from object list when destroying object memory. \r\n" ) );
            }

            xResult = prvDeleteObjectFromList( xHandle );
        }

        PKCS11_PAL_GetObjectValueCleanup( pxObject, ulObjectLength );

        return xResult;
    }
#endif /* if ( pkcs11configPAL_DESTROY_SUPPORTED != 1 ) */

/*-------------------------------------------------------------*/

/**
 * @brief Initializes Cryptoki.
 *
 * @note C_Initialize is not thread-safe.
 *
 * C_Initialize should be called (and allowed to return) before
 * any additional PKCS #11 operations are invoked.
 *
 * In this implementation, all arguments are ignored.
 * Thread protection for the rest of PKCS #11 functions
 * default to FreeRTOS primitives.
 *
 * @param[in] pInitArgs    This parameter is ignored.
 *
 * @return CKR_OK if successful.
 * CKR_CRYPTOKI_ALREADY_INITIALIZED if C_Initialize was previously called.
 * All other errors indicate that the PKCS #11 module is not ready to be used.
 * See <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_initialize] */
CK_DECLARE_FUNCTION( CK_RV, C_Initialize )( CK_VOID_PTR pInitArgs )
{
    ( void ) ( pInitArgs );

    CK_RV xResult = CKR_OK;

    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    if( xP11Context.xIsInitialized != ( CK_BBOOL ) CK_TRUE )
    {
        xResult = PKCS11_PAL_Initialize();

        if( xResult == CKR_OK )
        {
            xResult = prvMbedTLS_Initialize();
        }
    }
    else
    {
        xResult = CKR_CRYPTOKI_ALREADY_INITIALIZED;
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_initialize] */

/**
 * @brief Clean up miscellaneous Cryptoki-associated resources.
 */
/* @[declare_pkcs11_mbedtls_c_finalize] */
CK_DECLARE_FUNCTION( CK_RV, C_Finalize )( CK_VOID_PTR pReserved )
{
    CK_RV xResult = CKR_OK;

    if( pReserved != NULL )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    if( xResult == CKR_OK )
    {
        /* See explanation in prvCheckValidSessionAndModule for this exception. */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        if( xP11Context.xIsInitialized == ( CK_BBOOL ) CK_FALSE )
        {
            xResult = CKR_CRYPTOKI_NOT_INITIALIZED;
        }
    }

    if( xResult == CKR_OK )
    {
        mbedtls_entropy_free( &xP11Context.xMbedEntropyContext );
        mbedtls_ctr_drbg_free( &xP11Context.xMbedDrbgCtx );

        if( xP11Context.xObjectList.xMutex != NULL )
        {
            vSemaphoreDelete( xP11Context.xObjectList.xMutex );
        }

        /* See explanation in prvCheckValidSessionAndModule for this exception. */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        xP11Context.xIsInitialized = ( CK_BBOOL ) CK_FALSE;
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_finalize] */

/**
 * @brief Obtains entry points of Cryptoki library functions.
 *
 * All other PKCS #11 functions should be invoked using the returned
 * function list.
 *
 * @warning Do not overwrite the function list.
 *
 * \param[in] ppFunctionList       Pointer to the location where
 *                                  pointer to function list will be placed.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_getfunctionlist] */
CK_DECLARE_FUNCTION( CK_RV, C_GetFunctionList )( CK_FUNCTION_LIST_PTR_PTR ppFunctionList )
{
    CK_RV xResult = CKR_OK;

    static CK_FUNCTION_LIST prvP11FunctionList =
    {
        { CRYPTOKI_VERSION_MAJOR, CRYPTOKI_VERSION_MINOR },
        C_Initialize,
        C_Finalize,
        NULL, /*C_GetInfo */
        C_GetFunctionList,
        C_GetSlotList,
        NULL, /*C_GetSlotInfo*/
        C_GetTokenInfo,
        NULL, /*C_GetMechanismList*/
        C_GetMechanismInfo,
        C_InitToken,
        NULL, /*C_InitPIN*/
        NULL, /*C_SetPIN*/
        C_OpenSession,
        C_CloseSession,
        NULL,    /*C_CloseAllSessions*/
        NULL,    /*C_GetSessionInfo*/
        NULL,    /*C_GetOperationState*/
        NULL,    /*C_SetOperationState*/
        C_Login, /*C_Login*/
        NULL,    /*C_Logout*/
        C_CreateObject,
        NULL,    /*C_CopyObject*/
        C_DestroyObject,
        NULL,    /*C_GetObjectSize*/
        C_GetAttributeValue,
        NULL,    /*C_SetAttributeValue*/
        C_FindObjectsInit,
        C_FindObjects,
        C_FindObjectsFinal,
        NULL, /*C_EncryptInit*/
        NULL, /*C_Encrypt*/
        NULL, /*C_EncryptUpdate*/
        NULL, /*C_EncryptFinal*/
        NULL, /*C_DecryptInit*/
        NULL, /*C_Decrypt*/
        NULL, /*C_DecryptUpdate*/
        NULL, /*C_DecryptFinal*/
        C_DigestInit,
        NULL, /*C_Digest*/
        C_DigestUpdate,
        NULL, /* C_DigestKey*/
        C_DigestFinal,
        C_SignInit,
        C_Sign,
        NULL, /*C_SignUpdate*/
        NULL, /*C_SignFinal*/
        NULL, /*C_SignRecoverInit*/
        NULL, /*C_SignRecover*/
        C_VerifyInit,
        C_Verify,
        NULL, /*C_VerifyUpdate*/
        NULL, /*C_VerifyFinal*/
        NULL, /*C_VerifyRecoverInit*/
        NULL, /*C_VerifyRecover*/
        NULL, /*C_DigestEncryptUpdate*/
        NULL, /*C_DecryptDigestUpdate*/
        NULL, /*C_SignEncryptUpdate*/
        NULL, /*C_DecryptVerifyUpdate*/
        NULL, /*C_GenerateKey*/
        C_GenerateKeyPair,
        NULL, /*C_WrapKey*/
        NULL, /*C_UnwrapKey*/
        NULL, /*C_DeriveKey*/
        NULL, /*C_SeedRandom*/
        C_GenerateRandom,
        NULL, /*C_GetFunctionStatus*/
        NULL, /*C_CancelFunction*/
        NULL  /*C_WaitForSlotEvent*/
    };

    if( NULL == ppFunctionList )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }
    else
    {
        *ppFunctionList = &prvP11FunctionList;
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_getfunctionlist] */

/**
 * @brief Obtains a list of slots in the system.
 *
 * This port does not implement the concept of separate slots/tokens.
 *
 *  \param[in]  tokenPresent   This parameter is unused by this port.
 *  \param[in]  pSlotList      Pointer to an array of slot IDs.
 *                              At this time, only 1 slot is implemented.
 *  \param[in,out]  pulCount    Length of the slot list pxSlotList. Updated
 *                              to contain the actual number of slots written
 *                              to the list.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_getslotlist] */
CK_DECLARE_FUNCTION( CK_RV, C_GetSlotList )( CK_BBOOL tokenPresent,
                                             CK_SLOT_ID_PTR pSlotList,
                                             CK_ULONG_PTR pulCount )
{
    CK_RV xResult = CKR_OK;

    /* Since the mbedTLS implementation of PKCS#11 does not depend
     * on a physical token, this parameter is ignored. */
    ( void ) ( tokenPresent );

    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    if( xP11Context.xIsInitialized != ( CK_BBOOL ) CK_TRUE )
    {
        xResult = CKR_CRYPTOKI_NOT_INITIALIZED;
    }

    if( NULL == pulCount )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    if( xResult == CKR_OK )
    {
        if( NULL == pSlotList )
        {
            *pulCount = 1;
        }
        else
        {
            if( 0u == *pulCount )
            {
                xResult = CKR_BUFFER_TOO_SMALL;
            }
            else
            {
                pSlotList[ 0 ] = pkcs11SLOT_ID;
                *pulCount = 1;
            }
        }
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_getslotlist] */


/**
 * @brief Obtains information about a particular token.
 *
 * @param[in]  slotID         This parameter is unused in this port.
 * @param[out] pInfo           This parameter is unused in this port.
 *
 * C_GetTokenInfo() is only implemented for compatibility with other ports.
 * All inputs to this function are ignored, and calling this
 * function on this port does provide any information about
 * the PKCS #11 token.
 *
 * @return CKR_OK.
 */
/* @[declare_pkcs11_mbedtls_c_gettokeninfo] */
CK_DECLARE_FUNCTION( CK_RV, C_GetTokenInfo )( CK_SLOT_ID slotID,
                                              CK_TOKEN_INFO_PTR pInfo )
{
    /* Avoid compiler warnings about unused variables. */
    ( void ) slotID;
    ( void ) pInfo;

    return CKR_OK;
}
/* @[declare_pkcs11_mbedtls_c_gettokeninfo] */

/**
 * @brief Obtains information about a particular mechanism.
 *
 *  \param[in]  slotID         This parameter is unused in this port.
 *  \param[in]  type            The cryptographic capability for which support
 *                              information is being queried.
 *  \param[out] pInfo           Algorithm sizes and flags for the requested
 *                              mechanism, if supported.
 *
 * @return CKR_OK if the mechanism is supported. Otherwise, CKR_MECHANISM_INVALID.
 */
/* @[declare_pkcs11_mbedtls_c_getmechanisminfo] */
CK_DECLARE_FUNCTION( CK_RV, C_GetMechanismInfo )( CK_SLOT_ID slotID,
                                                  CK_MECHANISM_TYPE type,
                                                  CK_MECHANISM_INFO_PTR pInfo )
{
    /* Disable unused parameter warning. */
    ( void ) slotID;

    CK_RV xResult = CKR_MECHANISM_INVALID;

    if( pInfo == NULL )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    struct CryptoMechanisms
    {
        CK_MECHANISM_TYPE xType;
        CK_MECHANISM_INFO xInfo;
    }
    pxSupportedMechanisms[] =
    {
        { CKM_RSA_PKCS,        { 2048, 2048, CKF_SIGN              } },
        { CKM_RSA_X_509,       { 2048, 2048, CKF_VERIFY            } },
        #if ( pkcs11configSUPPRESS_ECDSA_MECHANISM != 1 )
            { CKM_ECDSA,           { 256,  256,  CKF_SIGN | CKF_VERIFY } },
            { CKM_EC_KEY_PAIR_GEN, { 256,  256,  CKF_GENERATE_KEY_PAIR } },
        #endif
        { CKM_SHA256,          { 0,    0,    CKF_DIGEST            } }
    };
    uint32_t ulMech = 0;

    if( xResult == CKR_MECHANISM_INVALID )
    {
        /* Look for the requested mechanism in the above table. */
        for( ; ulMech < sizeof( pxSupportedMechanisms ) / sizeof( pxSupportedMechanisms[ 0 ] ); ulMech++ )
        {
            if( pxSupportedMechanisms[ ulMech ].xType == type )
            {
                /* The mechanism is supported. Copy out the details and break
                 * out of the loop. */
                ( void ) memcpy( pInfo, &( pxSupportedMechanisms[ ulMech ].xInfo ), sizeof( CK_MECHANISM_INFO ) );
                xResult = CKR_OK;
                break;
            }
        }
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_getmechanisminfo] */

/**
 * @brief Initializes a token. This function is not implemented for this port.
 *
 * C_InitToken() is only implemented for compatibility with other ports.
 * All inputs to this function are ignored, and calling this
 * function on this port does not add any security.
 *
 * @return CKR_OK.
 */
/* @[declare_pkcs11_mbedtls_c_inittoken] */
CK_DECLARE_FUNCTION( CK_RV, C_InitToken )( CK_SLOT_ID slotID,
                                           CK_UTF8CHAR_PTR pPin,
                                           CK_ULONG ulPinLen,
                                           CK_UTF8CHAR_PTR pLabel )
{
    /* Avoid compiler warnings about unused variables. */
    ( void ) slotID;
    ( void ) pPin;
    ( void ) ulPinLen;
    ( void ) pLabel;

    return CKR_OK;
}
/* @[declare_pkcs11_mbedtls_c_inittoken] */

/**
 * @brief Opens a connection between an application and a particular token or sets up an application callback for token insertion.
 *
 * \note PKCS #11 module must have been previously initialized with a call to
 * C_Initialize() before calling C_OpenSession().
 *
 *
 *  \param[in]  slotID          This parameter is unused in this port.
 *  \param[in]  flags           Session flags - CKF_SERIAL_SESSION is a
 *                              mandatory flag.
 *  \param[in]  pApplication    This parameter is unused in this port.
 *  \param[in]  Notify          This parameter is unused in this port.
 *  \param[in]  phSession       Pointer to the location that the created
 *                              session's handle will be placed.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_opensession] */
CK_DECLARE_FUNCTION( CK_RV, C_OpenSession )( CK_SLOT_ID slotID,
                                             CK_FLAGS flags,
                                             CK_VOID_PTR pApplication,
                                             CK_NOTIFY Notify,
                                             CK_SESSION_HANDLE_PTR phSession )
{
    CK_RV xResult = CKR_OK;
    P11Session_t * pxSessionObj = NULL;
    uint32_t ulSessionCount = 0;

    ( void ) ( slotID );
    ( void ) ( pApplication );

    /* Allow unused parameters to be cast to void to silence compiler warnings.
     * Even if they are a function pointer. */
    /* coverity[misra_c_2012_rule_11_1_violation] */
    ( void ) Notify;

    /* Check that the PKCS #11 module is initialized. */
    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    if( xP11Context.xIsInitialized != ( CK_BBOOL ) CK_TRUE )
    {
        xResult = CKR_CRYPTOKI_NOT_INITIALIZED;
    }

    /* Check arguments. */
    if( NULL == phSession )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    /* For legacy reasons, the CKF_SERIAL_SESSION bit MUST always be set. */
    if( ( CKR_OK == xResult ) && ( 0UL == ( CKF_SERIAL_SESSION & flags ) ) )
    {
        xResult = CKR_SESSION_PARALLEL_NOT_SUPPORTED;
    }

    /*
     * Make space for the context.
     */
    if( CKR_OK == xResult )
    {
        /* Get next open session slot. */
        if( xSemaphoreTake( xP11Context.xSessionMutex, portMAX_DELAY ) == pdTRUE )
        {
            for( ulSessionCount = 0; ulSessionCount < ( uint32_t ) pkcs11configMAX_SESSIONS; ++ulSessionCount )
            {
                /* coverity[misra_c_2012_rule_10_5_violation] */
                if( pxP11Sessions[ ulSessionCount ].xOpened == ( CK_BBOOL ) CK_FALSE )
                {
                    xResult = CKR_OK;
                    pxSessionObj = &pxP11Sessions[ ulSessionCount ];
                    /* coverity[misra_c_2012_rule_10_5_violation] */
                    pxSessionObj->xOpened = ( CK_BBOOL ) CK_TRUE;
                    break;
                }
                else
                {
                    /* No available session. */
                    xResult = CKR_SESSION_COUNT;
                }
            }

            ( void ) xSemaphoreGive( xP11Context.xSessionMutex );
        }
        else
        {
            xResult = CKR_FUNCTION_FAILED;
        }

        if( CKR_OK == xResult )
        {
            pxSessionObj->xSignMutex = xSemaphoreCreateMutex();

            if( NULL == pxSessionObj->xSignMutex )
            {
                xResult = CKR_HOST_MEMORY;
            }

            pxSessionObj->xVerifyMutex = xSemaphoreCreateMutex();

            if( NULL == pxSessionObj->xVerifyMutex )
            {
                xResult = CKR_HOST_MEMORY;
            }
        }
    }

    if( CKR_OK == xResult )
    {
        /*
         * Assign the session.
         */
        pxSessionObj->ulState =
            ( 0UL != ( flags & CKF_RW_SESSION ) ) ? CKS_RW_PUBLIC_SESSION : CKS_RO_PUBLIC_SESSION;
    }

    /*
     *   Initialize the operation in progress.
     */
    if( CKR_OK == xResult )
    {
        pxSessionObj->xOperationDigestMechanism = pkcs11NO_OPERATION;
        pxSessionObj->xOperationVerifyMechanism = pkcs11NO_OPERATION;
        pxSessionObj->xOperationSignMechanism = pkcs11NO_OPERATION;
    }

    if( CKR_OK != xResult )
    {
        PKCS11_PRINT( ( "Failed to open a new session with error %d \r\n", xResult ) );

        if( pxSessionObj != NULL )
        {
            if( pxSessionObj->xSignMutex != NULL )
            {
                vSemaphoreDelete( pxSessionObj->xSignMutex );
            }

            if( pxSessionObj->xVerifyMutex != NULL )
            {
                vSemaphoreDelete( pxSessionObj->xVerifyMutex );
            }

            ( void ) memset( pxSessionObj, 0, sizeof( P11Session_t ) );
            *phSession = CK_INVALID_HANDLE;
        }
    }
    else
    {
        /* Increment by one, as invalid handles in PKCS #11 are 0. */
        ++ulSessionCount;
        *phSession = ulSessionCount;
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_opensession] */

/**
 * @brief Closes a session.
 *
 * @param[in]   hSession        The session handle to
 *                              be terminated.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_closesession] */
CK_DECLARE_FUNCTION( CK_RV, C_CloseSession )( CK_SESSION_HANDLE hSession )
{
    P11Session_t * pxSession = prvSessionPointerFromHandle( hSession );
    CK_RV xResult = CKR_OK;

    /* coverity[misra_c_2012_rule_10_5_violation] */
    if( xP11Context.xIsInitialized == ( CK_BBOOL ) CK_FALSE )
    {
        xResult = CKR_CRYPTOKI_NOT_INITIALIZED;
    }
    else if( pxSession == NULL )
    {
        xResult = CKR_SESSION_HANDLE_INVALID;
    }
    /* coverity[misra_c_2012_rule_10_5_violation] */
    else if( pxSession->xOpened == ( CK_BBOOL ) CK_TRUE )
    {
        /*
         * Tear down the session.
         */
        mbedtls_pk_free( &pxSession->xSignKey );

        if( NULL != pxSession->xSignMutex )
        {
            vSemaphoreDelete( pxSession->xSignMutex );
        }

        /* Free the public key context if it exists. */
        mbedtls_pk_free( &pxSession->xVerifyKey );

        if( NULL != pxSession->xVerifyMutex )
        {
            vSemaphoreDelete( pxSession->xVerifyMutex );
        }

        mbedtls_sha256_free( &pxSession->xSHA256Context );

        /* memset clears the open flag, so there is no need to set it to CK_FALSE */
        ( void ) memset( pxSession, 0, sizeof( P11Session_t ) );
    }
    else
    {
        /* MISRA */
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_closesession] */


/**
 * @brief Logs into a token. This function is not implemented for this port.
 *
 * C_Login() is only implemented for compatibility with other ports.
 * All inputs to this function are ignored, and calling this
 * function on this port does not add any security.
 *
 * @return CKR_OK.
 */
/* @[declare_pkcs11_mbedtls_c_login] */
CK_DECLARE_FUNCTION( CK_RV, C_Login )( CK_SESSION_HANDLE hSession,
                                       CK_USER_TYPE userType,
                                       CK_UTF8CHAR_PTR pPin,
                                       CK_ULONG ulPinLen )
{
    /* Avoid warnings about unused parameters. */
    ( void ) hSession;
    ( void ) userType;
    ( void ) pPin;
    ( void ) ulPinLen;

    /* THIS FUNCTION IS NOT IMPLEMENTED FOR MBEDTLS-BASED PORTS.
     * If login capability is required, implement it here.
     * Defined for compatibility with other PKCS #11 ports. */
    return CKR_OK;
}
/* @[declare_pkcs11_mbedtls_c_login] */

/**
 * @brief Helper function for parsing the templates of device certificates for C_CreateObject.
 *
 * @param[in] pxTemplate    Pointer to PKCS #11 attribute template.
 * @param[in] ulCount       length of templates array.
 * @param[in] pxObject      Pointer to PKCS #11 object.
 * @return CKR_OK.
 */
static CK_RV prvCreateCertificate( CK_ATTRIBUTE * pxTemplate,
                                   CK_ULONG ulCount,
                                   CK_OBJECT_HANDLE_PTR pxObject )
{
    CK_RV xResult = CKR_OK;
    CK_BYTE_PTR pxCertificateValue = NULL;
    CK_ULONG xCertificateLength = 0;
    CK_ATTRIBUTE_PTR pxLabel = NULL;
    CK_OBJECT_HANDLE xPalHandle = CK_INVALID_HANDLE;
    CK_CERTIFICATE_TYPE xCertificateType = 0;
    uint32_t ulIndex = 0;

    /* Search for the pointer to the certificate VALUE. */
    for( ulIndex = 0; ulIndex < ulCount; ulIndex++ )
    {
        xResult = prvCertAttParse( &pxTemplate[ ulIndex ], &xCertificateType,
                                   &pxCertificateValue, &xCertificateLength,
                                   &pxLabel );

        if( xResult != CKR_OK )
        {
            break;
        }
    }

    if( ( xResult == CKR_OK ) && ( ( pxCertificateValue == NULL ) || ( pxLabel == NULL ) ) )
    {
        xResult = CKR_TEMPLATE_INCOMPLETE;
    }

    if( xResult == CKR_OK )
    {
        xPalHandle = PKCS11_PAL_SaveObject( pxLabel, pxCertificateValue, xCertificateLength );

        if( xPalHandle == 0UL ) /*Invalid handle. */
        {
            xResult = CKR_DEVICE_MEMORY;
        }
    }

    if( xResult == CKR_OK )
    {
        xResult = prvAddObjectToList( xPalHandle, pxObject, pxLabel->pValue, pxLabel->ulValueLen );
        /* TODO: If this fails, should the object be wiped back out of flash?  But what if that fails?!?!? */
    }

    return xResult;
}


/**
 * @brief Helper to search an attribute for the key type attribute.
 *
 * @param[out] pxKeyType pointer to key type.
 * @param[in] pxTemplate templates to search for a key in.
 * @param[in] ulCount length of templates array.
 *
 */
static void prvGetKeyType( CK_KEY_TYPE * pxKeyType,
                           const CK_ATTRIBUTE * pxTemplate,
                           CK_ULONG ulCount )
{
    uint32_t ulIndex;
    CK_ATTRIBUTE xAttribute;

    *pxKeyType = PKCS11_INVALID_KEY_TYPE;

    for( ulIndex = 0; ulIndex < ulCount; ulIndex++ )
    {
        xAttribute = pxTemplate[ ulIndex ];

        if( xAttribute.type == CKA_KEY_TYPE )
        {
            ( void ) memcpy( pxKeyType, xAttribute.pValue, sizeof( CK_KEY_TYPE ) );
            break;
        }
    }
}

/**
 * @brief Helper to search a template for the label attribute.
 *
 * @param[out] ppxLabel pointer to label.
 * @param[in] pxTemplate templates to search for a key in.
 * @param[in] ulCount length of templates array.
 *
 */
static void prvGetLabel( CK_ATTRIBUTE ** ppxLabel,
                         CK_ATTRIBUTE * pxTemplate,
                         CK_ULONG ulCount )
{
    CK_ATTRIBUTE xAttribute;
    uint32_t ulIndex;

    *ppxLabel = NULL;

    for( ulIndex = 0; ulIndex < ulCount; ulIndex++ )
    {
        xAttribute = pxTemplate[ ulIndex ];

        if( xAttribute.type == CKA_LABEL )
        {
            *ppxLabel = &pxTemplate[ ulIndex ];
            break;
        }
    }
}


/**
 * @brief Helper to search a template for the label attribute.
 *
 * @param[in] pxPalHandle opaque handle to PKCS #11 object.
 * @param[in] pxMbedContext mbedTLS pk context for parsing.
 * @param[in] pxLabel label of PKCS #11 object.
 *
 * @note Because public and private keys are stored in the same slot for this port,
 * importing one after the other requires a read of what was previously in the slot,
 * combination of the public and private key in DER format, and re-import of the
 * combination.
 */
static CK_RV prvGetExistingKeyComponent( CK_OBJECT_HANDLE_PTR pxPalHandle,
                                         mbedtls_pk_context * pxMbedContext,
                                         const CK_ATTRIBUTE * pxLabel )
{
    uint8_t * pucData = NULL;
    uint32_t ulDataLength = 0;
    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    CK_BBOOL xIsPrivate = ( CK_BBOOL ) CK_TRUE;
    CK_RV xResult = CKR_OK;
    int32_t lMbedResult = 0;

    *pxPalHandle = CK_INVALID_HANDLE;

    if( 0 == strncmp( pxLabel->pValue, pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS, pxLabel->ulValueLen ) )
    {
        *pxPalHandle = PKCS11_PAL_FindObject( ( uint8_t * ) pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS, ( uint8_t ) pxLabel->ulValueLen );
    }
    else if( 0 == strncmp( pxLabel->pValue, pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS, pxLabel->ulValueLen ) )
    {
        *pxPalHandle = PKCS11_PAL_FindObject( ( uint8_t * ) pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS, ( uint8_t ) pxLabel->ulValueLen );
        /* See explanation in prvCheckValidSessionAndModule for this exception. */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        xIsPrivate = ( CK_BBOOL ) CK_FALSE;
    }
    else
    {
        /* Unknown label passed to function */
    }

    if( *pxPalHandle != CK_INVALID_HANDLE )
    {
        xResult = PKCS11_PAL_GetObjectValue( *pxPalHandle, &pucData, &ulDataLength, &xIsPrivate );
    }

    if( xResult == CKR_OK )
    {
        /* See explanation in prvCheckValidSessionAndModule for this exception. */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        if( xIsPrivate == ( CK_BBOOL ) CK_TRUE )
        {
            lMbedResult = mbedtls_pk_parse_key( pxMbedContext, pucData, ulDataLength, NULL, 0 );
        }
        else
        {
            lMbedResult = mbedtls_pk_parse_public_key( pxMbedContext, pucData, ulDataLength );
        }

        PKCS11_PAL_GetObjectValueCleanup( pucData, ulDataLength );
    }

    if( lMbedResult != 0 )
    {
        PKCS11_PRINT( ( "mbedTLS pk parse failed with error %s : ",
                        mbedtlsHighLevelCodeOrDefault( lMbedResult ) ) );
        PKCS11_PRINT( ( "%s \r\n",
                        mbedtlsLowLevelCodeOrDefault( lMbedResult ) ) );
        *pxPalHandle = CK_INVALID_HANDLE;
    }

    return xResult;
}

/**
 * @brief Helper function for importing elliptic curve keys from
 * template using C_CreateObject.
 * @param[in] pxTemplate templates to search for a key in.
 * @param[in] ulCount length of templates array.
 * @param[in] pxObject PKCS #11 object handle.
 * @param[in] xIsPrivate boolean indicating whether the key is private or public.
 *
 */
static CK_RV prvCreateECKey( CK_ATTRIBUTE * pxTemplate,
                             CK_ULONG ulCount,
                             CK_OBJECT_HANDLE_PTR pxObject,
                             CK_BBOOL xIsPrivate )


{
    CK_RV xResult = CKR_OK;
    uint32_t ulIndex;
    CK_ATTRIBUTE_PTR pxLabel = NULL;
    CK_OBJECT_HANDLE xPalHandle = CK_INVALID_HANDLE;
    int32_t lMbedTLSReturn = 0;
    mbedtls_pk_context xMbedContext;
    mbedtls_ecp_keypair * pxKeyPair;

    mbedtls_pk_init( &xMbedContext );

    prvGetLabel( &pxLabel, pxTemplate, ulCount );

    if( pxLabel == NULL )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }
    else
    {
        xResult = prvGetExistingKeyComponent( &xPalHandle, &xMbedContext, pxLabel );
    }

    if( ( xResult == CKR_OK ) && ( xPalHandle == CK_INVALID_HANDLE ) )
    {
        /* An mbedTLS key is comprised of 2 pieces of data- an "info" and a "context".
         * Since a valid key was not found by prvGetExistingKeyComponent, we are going to initialize
         * the structure so that the mbedTLS structures will look the same as they would if a key
         * had been found, minus the private key component. */

        /* If a key had been found by prvGetExistingKeyComponent, the keypair context
         * would have been malloc'ed. */
        pxKeyPair = pvPortMalloc( sizeof( mbedtls_ecp_keypair ) );

        if( pxKeyPair != NULL )
        {
            /* Initialize the info. */
            xMbedContext.pk_info = &mbedtls_eckey_info;

            /* Initialize the context. */
            xMbedContext.pk_ctx = pxKeyPair;
            mbedtls_ecp_keypair_init( pxKeyPair );
            mbedtls_ecp_group_init( &pxKeyPair->grp );

            /* At this time, only P-256 curves are supported. */
            lMbedTLSReturn = mbedtls_ecp_group_load( &pxKeyPair->grp,
                                                     MBEDTLS_ECP_DP_SECP256R1 );

            if( lMbedTLSReturn != 0 )
            {
                PKCS11_PRINT( ( "mbedTLS ECP curve load failed with error %s : ",
                                mbedtlsHighLevelCodeOrDefault( lMbedTLSReturn ) ) );
                PKCS11_PRINT( ( "%s \r\n",
                                mbedtlsLowLevelCodeOrDefault( lMbedTLSReturn ) ) );
                xResult = CKR_FUNCTION_FAILED;
            }
        }
        else
        {
            xResult = CKR_HOST_MEMORY;
        }
    }

    /* Key will be assembled in the mbedTLS key context and then exported to DER for storage. */

    if( xResult == CKR_OK )
    {
        for( ulIndex = 0; ulIndex < ulCount; ulIndex++ )
        {
            xResult = prvEcKeyAttParse( &pxTemplate[ ulIndex ], &xMbedContext, xIsPrivate );

            if( xResult != CKR_OK )
            {
                break;
            }
        }
    }

    if( xResult == CKR_OK )
    {
        xResult = prvSaveDerKeyToPal( &xMbedContext,
                                      pxObject,
                                      pxLabel,
                                      CKK_EC,
                                      xIsPrivate );
    }

    /* Clean up the mbedTLS key context. */
    mbedtls_pk_free( &xMbedContext );

    return xResult;
}

/**
 * @brief Helper function for parsing RSA Private Key attribute templates
 * for C_CreateObject.
 * @param[in] pxTemplate templates to search for a key in.
 * @param[in] ulCount length of templates array.
 * @param[in] pxObject PKCS #11 object handle.
 *
 */
static CK_RV prvCreateRsaPrivateKey( CK_ATTRIBUTE * pxTemplate,
                                     CK_ULONG ulCount,
                                     CK_OBJECT_HANDLE_PTR pxObject )
{
    CK_RV xResult = CKR_OK;
    mbedtls_pk_context xMbedContext = { 0 };
    uint32_t ulIndex;
    CK_ATTRIBUTE_PTR pxLabel = NULL;

    /* mbedtls_rsa_context must be malloc'ed to use with mbedtls_pk_free function. */
    mbedtls_rsa_context * pxRsaCtx = pvPortMalloc( sizeof( mbedtls_rsa_context ) );

    prvGetLabel( &pxLabel, pxTemplate, ulCount );

    if( pxLabel == NULL )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    if( pxRsaCtx != NULL )
    {
        mbedtls_pk_init( &xMbedContext );
        xMbedContext.pk_ctx = pxRsaCtx;
        xMbedContext.pk_info = &mbedtls_rsa_info;
        mbedtls_rsa_init( pxRsaCtx, MBEDTLS_RSA_PKCS_V15, 0 /*ignored.*/ );
    }
    else
    {
        xResult = CKR_HOST_MEMORY;
    }

    if( xResult == CKR_OK )
    {
        /* Parse template and collect the relevant parts. */
        for( ulIndex = 0; ulIndex < ulCount; ulIndex++ )
        {
            xResult = prvRsaKeyAttParse( &pxTemplate[ ulIndex ], &xMbedContext );

            if( xResult != CKR_OK )
            {
                break;
            }
        }
    }

    if( xResult == CKR_OK )
    {
        xResult = prvSaveDerKeyToPal( &xMbedContext,
                                      pxObject,
                                      pxLabel,
                                      CKK_RSA,
                                      /* See explanation in prvCheckValidSessionAndModule for this exception. */
                                      /* coverity[misra_c_2012_rule_10_5_violation] */
                                      ( CK_BBOOL ) CK_TRUE );
    }

    /* Clean up the mbedTLS key context. */
    mbedtls_pk_free( &xMbedContext );

    return xResult;
}

/**
 * @brief Helper function for importing private keys using template
 * C_CreateObject.
 * @param[in] pxTemplate templates to search for a key in.
 * @param[in] ulCount length of templates array.
 * @param[in] pxObject PKCS #11 object handle.
 *
 */
static CK_RV prvCreatePrivateKey( CK_ATTRIBUTE * pxTemplate,
                                  CK_ULONG ulCount,
                                  CK_OBJECT_HANDLE_PTR pxObject )
{
    CK_RV xResult = CKR_OK;
    CK_KEY_TYPE xKeyType;

    prvGetKeyType( &xKeyType, pxTemplate, ulCount );

    if( xKeyType == CKK_RSA )
    {
        xResult = prvCreateRsaPrivateKey( pxTemplate,
                                          ulCount,
                                          pxObject );
    }

    #if ( pkcs11configSUPPRESS_ECDSA_MECHANISM != 1 )
        /* CKK_EC = CKK_ECDSA. */
        else if( xKeyType == CKK_EC )
        {
            xResult = prvCreateECKey( pxTemplate,
                                      ulCount,
                                      pxObject,
                                      /* See explanation in prvCheckValidSessionAndModule for this exception. */
                                      /* coverity[misra_c_2012_rule_10_5_violation] */
                                      ( CK_BBOOL ) CK_TRUE );
        }
    #endif /* if ( pkcs11configSUPPRESS_ECDSA_MECHANISM != 1 ) */
    else
    {
        xResult = CKR_MECHANISM_INVALID;
    }

    return xResult;
}


/**
 * @brief Helper function for importing public keys using
 * C_CreateObject.
 * @param[in] pxTemplate templates to search for a key in.
 * @param[in] ulCount length of templates array.
 * @param[in] pxObject PKCS #11 object handle.
 *
 */
static CK_RV prvCreatePublicKey( CK_ATTRIBUTE * pxTemplate,
                                 CK_ULONG ulCount,
                                 CK_OBJECT_HANDLE_PTR pxObject )
{
    CK_KEY_TYPE xKeyType = 0;
    CK_RV xResult = CKR_OK;

    prvGetKeyType( &xKeyType, pxTemplate, ulCount );

    if( xKeyType == CKK_RSA )
    {
        xResult = CKR_ATTRIBUTE_TYPE_INVALID;
    }

    #if ( pkcs11configSUPPRESS_ECDSA_MECHANISM != 1 )
        else if( xKeyType == CKK_EC ) /* CKK_EC = CKK_ECDSA. */
        {
            /* See explanation in prvCheckValidSessionAndModule for this exception. */
            /* coverity[misra_c_2012_rule_10_5_violation] */
            xResult = prvCreateECKey( pxTemplate, ulCount, pxObject, ( CK_BBOOL ) CK_FALSE );
        }
    #endif /* if ( pkcs11configSUPPRESS_ECDSA_MECHANISM != 1 ) */
    else
    {
        PKCS11_PRINT( ( "Invalid key type %d \r\n", xKeyType ) );
        xResult = CKR_MECHANISM_INVALID;
    }

    return xResult;
}


/**
 * @brief Creates an object.
 *
 * @param[in] hSession                   Handle of a valid PKCS #11 session.
 * @param[in] pTemplate                  List of attributes of the object to
 *                                       be created.
 * @param[in] ulCount                    Number of attributes in pTemplate.
 * @param[out] phObject                  Pointer to the location where the created
 *                                       object's handle will be placed.
 *
 * <table>
 * <tr><th> Object Type             <th> Template Attributes
 * <tr><td rowspan="6">Certificate<td>CKA_CLASS
 * <tr>                           <td>CKA_VALUE
 * <tr>                              <td>CKA_TOKEN
 * <tr>                              <td>CKA_LABEL
 * <tr>                              <td>CKA_CERTIFICATE_TYPE
 * <tr>                              <td>CKA_VALUE
 * <tr><td rowspan="7">EC Private Key<td>CKA_CLASS
 * <tr>                              <td>CKA_KEY_TYPE
 * <tr>                              <td>CKA_TOKEN
 * <tr>                              <td>CKA_LABEL
 * <tr>                              <td>CKA_SIGN
 * <tr>                              <td>CKA_EC_PARAMS
 * <tr>                              <td>CKA_VALUE
 * <tr><td rowspan="7">EC Public Key<td>CKA_CLASS
 * <tr>                              <td>CKA_KEY_TYPE
 * <tr>                              <td>CKA_TOKEN
 * <tr>                              <td>CKA_VERIFY
 * <tr>                              <td>CKA_LABEL
 * <tr>                              <td>CKA_EC_PARAMS
 * <tr>                              <td>CKA_EC_POINT
 * <tr><td rowspan="13">RSA Private Key<td>CKA_CLASS
 * <tr>                               <td>CKA_KEY_TYPE
 * <tr>                               <td>CKA_TOKEN
 * <tr>                               <td>CKA_LABEL
 * <tr>                               <td>CKA_SIGN
 * <tr>                               <td>CKA_MODULUS
 * <tr>                               <td>CKA_PUBLIC_EXPONENT
 * <tr>                               <td>CKA_PRIME_1
 * <tr>                               <td>CKA_PRIME_2
 * <tr>                               <td>CKA_PRIVATE_EXPONENT
 * <tr>                               <td>CKA_EXPONENT_1
 * <tr>                               <td>CKA_EXPONENT_2
 * <tr>                               <td>CKA_COEFFICIENT
 * </table>
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_createobject] */
CK_DECLARE_FUNCTION( CK_RV, C_CreateObject )( CK_SESSION_HANDLE hSession,
                                              CK_ATTRIBUTE_PTR pTemplate,
                                              CK_ULONG ulCount,
                                              CK_OBJECT_HANDLE_PTR phObject )
{
    CK_OBJECT_CLASS xClass = 0;

    const P11Session_t * pxSession = prvSessionPointerFromHandle( hSession );
    CK_RV xResult = prvCheckValidSessionAndModule( pxSession );

    if( ( NULL == pTemplate ) ||
        ( NULL == phObject ) )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    if( xResult == CKR_OK )
    {
        xResult = prvGetObjectClass( pTemplate, ulCount, &xClass );
    }

    if( xResult == CKR_OK )
    {
        switch( xClass )
        {
            case CKO_CERTIFICATE:
                xResult = prvCreateCertificate( pTemplate, ulCount, phObject );
                break;

            case CKO_PRIVATE_KEY:
                xResult = prvCreatePrivateKey( pTemplate, ulCount, phObject );
                break;

            case CKO_PUBLIC_KEY:
                xResult = prvCreatePublicKey( pTemplate, ulCount, phObject );
                break;

            default:
                xResult = CKR_ATTRIBUTE_VALUE_INVALID;
                break;
        }
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_createobject] */

/**
 * @brief Destroys an object.
 *
 * @param[in] hSession                   Handle of a valid PKCS #11 session.
 * @param[in] hObject                    Handle of the object to be destroyed.
 *
 * @warning In this implementation, if either the device public key or the device
 * private key (labels pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS and
 * pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS) are deleted, both keys will
 * be destroyed.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_destroyobject] */
CK_DECLARE_FUNCTION( CK_RV, C_DestroyObject )( CK_SESSION_HANDLE hSession,
                                               CK_OBJECT_HANDLE hObject )
{
    const P11Session_t * pxSession = prvSessionPointerFromHandle( hSession );
    CK_RV xResult = prvCheckValidSessionAndModule( pxSession );

    if( xResult == CKR_OK )
    {
        xResult = PKCS11_PAL_DestroyObject( hObject );
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_destroyobject] */

/**
 * @brief Obtains an attribute value of an object.
 * @param[in] hSession                   Handle of a valid PKCS #11 session.
 * @param[in] hObject                    PKCS #11 object handle to be queried.
 * @param[in,out] pTemplate              Attribute template.
 *                                       pxTemplate.pValue should be set to the attribute
 *                                       to be queried. pxTemplate.ulValueLen should be
 *                                       set to the length of the buffer allocated at
 *                                       pxTemplate.pValue, and will be updated to contain
 *                                       the actual length of the data copied.
 *                                       pxTemplate.pValue should be set to point to
 *                                       a buffer to receive the attribute value data.
 *                                       If parameter length is unknown,
 *                                       pxTemplate.pValue may be set to NULL, and
 *                                       this function will set the required buffer length
 *                                       in pxTemplate.ulValueLen.
 * @param[in] ulCount                    The number of attributes in the template.
 *
 * <table>
 * <tr><th> Object Type             <th> Queryable Attributes
 * <tr><td rowspan="2">Certificate<td>CKA_CLASS
 * <tr>                           <td>CKA_VALUE
 * <tr><td rowspan="3">EC Private Key<td>CKA_CLASS
 * <tr>                              <td>CKA_KEY_TYPE
 * <tr>                              <td>CKA_EC_PARAMS
 * <tr><td rowspan="4">EC Public Key<td>CKA_CLASS
 * <tr>                             <td>CKA_KEY_TYPE
 * <tr>                             <td>CKA_EC_PARAMS
 * <tr>                             <td>CKA_EC_POINT
 * <tr><td rowspan="2">RSA Private Key<td>CKA_CLASS
 * <tr>                               <td>CKA_KEY_TYPE
 * <tr><td rowspan="2">RSA Public Key<td>CKA_CLASS
 * <tr>                               <td>CKA_KEY_TYPE
 * </table>
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_getattributevalue] */
CK_DECLARE_FUNCTION( CK_RV, C_GetAttributeValue )( CK_SESSION_HANDLE hSession,
                                                   CK_OBJECT_HANDLE hObject,
                                                   CK_ATTRIBUTE_PTR pTemplate,
                                                   CK_ULONG ulCount )
{
    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    CK_BBOOL xIsPrivate = ( CK_BBOOL ) CK_TRUE;
    CK_ULONG iAttrib;
    mbedtls_pk_context xKeyContext = { 0 };
    mbedtls_pk_type_t xKeyType;
    const mbedtls_ecp_keypair * pxKeyPair;
    CK_KEY_TYPE xPkcsKeyType = ( CK_KEY_TYPE ) ~0UL;
    CK_OBJECT_CLASS xClass;
    uint8_t * pxObjectValue = NULL;
    uint32_t ulLength = 0;
    const uint8_t ucP256Oid[] = pkcs11DER_ENCODED_OID_P256;
    int32_t lMbedTLSResult = 0;
    CK_OBJECT_HANDLE xPalHandle = CK_INVALID_HANDLE;
    size_t xSize;
    uint8_t * pcLabel = NULL;

    const P11Session_t * pxSession = prvSessionPointerFromHandle( hSession );
    CK_RV xResult = prvCheckValidSessionAndModule( pxSession );

    if( ( CKR_OK == xResult ) && ( ( ( NULL == pTemplate ) ) || ( 0UL == ulCount ) ) )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    if( ( CKR_OK == xResult ) && ( CK_INVALID_HANDLE == hObject ) )
    {
        xResult = CKR_OBJECT_HANDLE_INVALID;
    }

    if( xResult == CKR_OK )
    {
        /*
         * Copy the object into a buffer.
         */

        prvFindObjectInListByHandle( hObject, &xPalHandle, &pcLabel, &xSize ); /*pcLabel and xSize are ignored. */

        if( xPalHandle != CK_INVALID_HANDLE )
        {
            xResult = PKCS11_PAL_GetObjectValue( xPalHandle, &pxObjectValue, &ulLength, &xIsPrivate );
        }
        else
        {
            xResult = CKR_OBJECT_HANDLE_INVALID;
        }
    }

    /* Determine what kind of object we are dealing with. */
    if( xResult == CKR_OK )
    {
        /* Is it a key? */
        mbedtls_pk_init( &xKeyContext );

        if( 0 == mbedtls_pk_parse_key( &xKeyContext, pxObjectValue, ulLength, NULL, 0 ) )
        {
            /* See explanation in prvCheckValidSessionAndModule for this exception. */
            /* coverity[misra_c_2012_rule_10_5_violation] */
            if( xIsPrivate == ( CK_BBOOL ) CK_TRUE )
            {
                xClass = CKO_PRIVATE_KEY;
            }
            else
            {
                xClass = CKO_PUBLIC_KEY;
            }
        }
        else if( 0 == mbedtls_pk_parse_public_key( &xKeyContext, pxObjectValue, ulLength ) )
        {
            xClass = CKO_PUBLIC_KEY;
        }
        else
        {
            /* TODO: Do we want to safety parse the cert?
             * Assume certificate. */
            xClass = CKO_CERTIFICATE;
        }
    }

    if( xResult == CKR_OK )
    {
        for( iAttrib = 0; iAttrib < ulCount; iAttrib++ )
        {
            if( xResult != CKR_OK )
            {
                break;
            }

            switch( pTemplate[ iAttrib ].type )
            {
                case CKA_CLASS:

                    if( pTemplate[ iAttrib ].pValue == NULL )
                    {
                        pTemplate[ iAttrib ].ulValueLen = sizeof( CK_OBJECT_CLASS );
                    }
                    else
                    {
                        if( pTemplate[ iAttrib ].ulValueLen >= sizeof( CK_OBJECT_CLASS ) )
                        {
                            ( void ) memcpy( pTemplate[ iAttrib ].pValue, &xClass, sizeof( CK_OBJECT_CLASS ) );
                        }
                        else
                        {
                            xResult = CKR_BUFFER_TOO_SMALL;
                        }
                    }

                    break;

                case CKA_VALUE:

                    /* See explanation in prvCheckValidSessionAndModule for this exception. */
                    /* coverity[misra_c_2012_rule_10_5_violation] */
                    if( xIsPrivate == ( CK_BBOOL ) CK_TRUE )
                    {
                        pTemplate[ iAttrib ].ulValueLen = CK_UNAVAILABLE_INFORMATION;
                        xResult = CKR_ATTRIBUTE_SENSITIVE;
                    }
                    else
                    {
                        if( pTemplate[ iAttrib ].pValue == NULL )
                        {
                            pTemplate[ iAttrib ].ulValueLen = ulLength;
                        }
                        else if( pTemplate[ iAttrib ].ulValueLen < ulLength )
                        {
                            xResult = CKR_BUFFER_TOO_SMALL;
                        }
                        else
                        {
                            ( void ) memcpy( pTemplate[ iAttrib ].pValue, pxObjectValue, ulLength );
                        }
                    }

                    break;

                case CKA_KEY_TYPE:

                    if( pTemplate[ iAttrib ].pValue == NULL )
                    {
                        pTemplate[ iAttrib ].ulValueLen = sizeof( CK_KEY_TYPE );
                    }
                    else if( pTemplate[ iAttrib ].ulValueLen < sizeof( CK_KEY_TYPE ) )
                    {
                        xResult = CKR_BUFFER_TOO_SMALL;
                    }
                    else
                    {
                        xKeyType = mbedtls_pk_get_type( &xKeyContext );

                        switch( xKeyType )
                        {
                            case MBEDTLS_PK_RSA:
                            case MBEDTLS_PK_RSA_ALT:
                            case MBEDTLS_PK_RSASSA_PSS:
                                xPkcsKeyType = CKK_RSA;
                                break;

                            case MBEDTLS_PK_ECKEY:
                            case MBEDTLS_PK_ECKEY_DH:
                                xPkcsKeyType = CKK_EC;
                                break;

                            case MBEDTLS_PK_ECDSA:
                                xPkcsKeyType = CKK_ECDSA;
                                break;

                            default:
                                xResult = CKR_ATTRIBUTE_VALUE_INVALID;
                                break;
                        }

                        ( void ) memcpy( pTemplate[ iAttrib ].pValue, &xPkcsKeyType, sizeof( CK_KEY_TYPE ) );
                    }

                    break;

                case CKA_PRIVATE_EXPONENT:

                    xResult = CKR_ATTRIBUTE_SENSITIVE;

                    break;

                case CKA_EC_PARAMS:

                    /* TODO: Add check that is key, is ec key. */

                    pTemplate[ iAttrib ].ulValueLen = sizeof( ucP256Oid );

                    if( pTemplate[ iAttrib ].pValue != NULL )
                    {
                        if( pTemplate[ iAttrib ].ulValueLen < sizeof( ucP256Oid ) )
                        {
                            xResult = CKR_BUFFER_TOO_SMALL;
                        }
                        else
                        {
                            ( void ) memcpy( pTemplate[ iAttrib ].pValue, ucP256Oid, sizeof( ucP256Oid ) );
                        }
                    }

                    break;

                case CKA_EC_POINT:

                    if( pTemplate[ iAttrib ].pValue == NULL )
                    {
                        pTemplate[ iAttrib ].ulValueLen = 67; /* TODO: Is this large enough?*/
                    }
                    else
                    {
                        pxKeyPair = ( mbedtls_ecp_keypair * ) xKeyContext.pk_ctx;
                        *( ( uint8_t * ) pTemplate[ iAttrib ].pValue ) = 0x04; /* Mark the point as uncompressed. */
                        lMbedTLSResult = mbedtls_ecp_tls_write_point( &pxKeyPair->grp,
                                                                      &pxKeyPair->Q,
                                                                      MBEDTLS_ECP_PF_UNCOMPRESSED,
                                                                      &xSize,
                                                                      ( uint8_t * ) pTemplate[ iAttrib ].pValue + 1,
                                                                      pTemplate[ iAttrib ].ulValueLen - 1UL );

                        if( lMbedTLSResult < 0 )
                        {
                            if( lMbedTLSResult == MBEDTLS_ERR_ECP_BUFFER_TOO_SMALL )
                            {
                                xResult = CKR_BUFFER_TOO_SMALL;
                            }
                            else
                            {
                                xResult = CKR_FUNCTION_FAILED;
                            }
                        }
                        else
                        {
                            pTemplate[ iAttrib ].ulValueLen = xSize + 1UL;
                        }
                    }

                    break;

                default:
                    xResult = CKR_ATTRIBUTE_TYPE_INVALID;
                    break;
            }
        }

        /* Free the buffer where object was stored. */
        PKCS11_PAL_GetObjectValueCleanup( pxObjectValue, ulLength );

        /* Free the mbedTLS structure used to parse the key. */
        mbedtls_pk_free( &xKeyContext );
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_getattributevalue] */

/**
 * @brief Initializes an object search operation.
 *
 * \sa C_FindObjects() and C_FindObjectsFinal() which must be called
 * after C_FindObjectsInit().
 *
 * \note FindObjects parameters are shared by a session.  Calling
 * C_FindObjectsInit(), C_FindObjects(), and C_FindObjectsFinal() with the
 * same session across different tasks may lead to unexpected results.
 *
 * @param[in] hSession                      Handle of a valid PKCS #11 session.
 * @param[in] pTemplate                     Pointer to a template which specifies
 *                                          the object attributes to match.
 *                                          In this port, the only searchable attribute
 *                                          is object label.  All other attributes will
 *                                          be ignored.
 * @param[in] ulCount                       The number of attributes in pTemplate.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_findobjectsinit] */
CK_DECLARE_FUNCTION( CK_RV, C_FindObjectsInit )( CK_SESSION_HANDLE hSession,
                                                 CK_ATTRIBUTE_PTR pTemplate,
                                                 CK_ULONG ulCount )
{
    P11Session_t * pxSession = prvSessionPointerFromHandle( hSession );
    CK_RV xResult = prvCheckValidSessionAndModule( pxSession );
    CK_BYTE * pxFindObjectLabel = NULL;
    uint32_t ulIndex;
    CK_ATTRIBUTE xAttribute;

    if( NULL == pTemplate )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    if( ( ulCount != 1UL ) && ( ulCount != 2UL ) )
    {
        xResult = CKR_ARGUMENTS_BAD;
        PKCS11_PRINT( ( "ERROR: Find objects does not support searching by %d attributes. \r\n", ulCount ) );
    }

    if( xResult == CKR_OK )
    {
        /* See explanation in prvCheckValidSessionAndModule for this exception. */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        if( prvOperationActive( pxSession ) == ( CK_BBOOL ) CK_TRUE )
        {
            xResult = CKR_OPERATION_ACTIVE;
            PKCS11_PRINT( ( "ERROR: Find object operation already in progress. \r\n" ) );
        }
    }

    /* Malloc space to save template information. */
    if( xResult == CKR_OK )
    {
        pxFindObjectLabel = pvPortMalloc( pTemplate->ulValueLen + 1UL ); /* Add 1 to guarantee null termination for PAL. */
        pxSession->pxFindObjectLabel = pxFindObjectLabel;

        if( pxFindObjectLabel != NULL )
        {
            ( void ) memset( pxFindObjectLabel, 0, pTemplate->ulValueLen + 1UL );
        }
        else
        {
            xResult = CKR_HOST_MEMORY;
        }
    }

    /* Search template for label.
     * NOTE: This port only supports looking up objects by CKA_LABEL and all
     * other search attributes are ignored. */
    if( xResult == CKR_OK )
    {
        xResult = CKR_TEMPLATE_INCOMPLETE;

        for( ulIndex = 0; ulIndex < ulCount; ulIndex++ ) /* TODO: Re-evaluate the need for this for loop... we are making bad assumptions if 2 objects have the same label anyhow! */
        {
            xAttribute = pTemplate[ ulIndex ];

            if( xAttribute.type == CKA_LABEL )
            {
                ( void ) memcpy( pxSession->pxFindObjectLabel, xAttribute.pValue, xAttribute.ulValueLen );
                xResult = CKR_OK;
            }
            else
            {
                PKCS11_WARNING_PRINT( ( "WARNING: Search parameters other than label are ignored.\r\n" ) );
            }
        }
    }

    /* Clean up memory if there was an error parsing the template. */
    if( ( pxSession != NULL ) && ( xResult != CKR_OK ) )
    {
        vPortFree( pxFindObjectLabel );
        pxSession->pxFindObjectLabel = NULL;
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_findobjectsinit] */

/**
 * @brief Initializes an object search operation.
 *
 * \sa C_FindObjectsInit() which must be called before calling C_FindObjects()
 * and C_FindObjectsFinal(), which must be called after.
 *
 * \note FindObjects parameters are shared by a session.  Calling
 * C_FindObjectsInit(), C_FindObjects(), and C_FindObjectsFinal() with the
 * same session across different tasks may lead to unexpected results.
 *
 * @param[in] hSession                      Handle of a valid PKCS #11 session.
 * @param[out] phObject                     Points to the handle of the object to
 *                                          be found.
 * @param[in] ulMaxObjectCount              The size of the phObject object handle
 *                                          array. In this port, this value should
 *                                          always be set to 1, as searching for
 *                                          multiple objects is not supported.
 * @param[out] pulObjectCount               The actual number of objects that are
 *                                          found. In this port, if an object is found
 *                                          this value will be 1, otherwise if the
 *                                          object is not found, it will be set to 0.
 *
 * \note In the event that an object does not exist, CKR_OK will be returned, but
 * pulObjectCount will be set to 0.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_findobjects] */
CK_DECLARE_FUNCTION( CK_RV, C_FindObjects )( CK_SESSION_HANDLE hSession,
                                             CK_OBJECT_HANDLE_PTR phObject,
                                             CK_ULONG ulMaxObjectCount,
                                             CK_ULONG_PTR pulObjectCount )
{
    P11Session_t * pxSession = prvSessionPointerFromHandle( hSession );
    CK_RV xResult = prvCheckValidSessionAndModule( pxSession );

    uint8_t * pucObjectValue = NULL;
    uint32_t xObjectLength = 0;
    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    CK_BBOOL xIsPrivate = ( CK_BBOOL ) CK_TRUE;
    CK_BYTE xByte = 0;
    CK_OBJECT_HANDLE xPalHandle = CK_INVALID_HANDLE;
    uint32_t ulIndex;

    /*
     * Check parameters.
     */
    if( ( NULL == phObject ) ||
        ( NULL == pulObjectCount ) )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    if( xResult == CKR_OK )
    {
        if( pxSession->pxFindObjectLabel == NULL )
        {
            xResult = CKR_OPERATION_NOT_INITIALIZED;
        }

        if( 1u != ulMaxObjectCount )
        {
            xResult = CKR_ARGUMENTS_BAD;
            PKCS11_WARNING_PRINT( ( "WARN: Searching for anything other than 1 object not supported. \r\n" ) );
        }
    }

    if( xResult == CKR_OK )
    {
        /* Try to find the object in module's list first. */
        prvFindObjectInListByLabel( pxSession->pxFindObjectLabel, strlen( ( const char * ) pxSession->pxFindObjectLabel ), &xPalHandle, phObject );

        /* Check with the PAL if the object was previously stored. */
        if( *phObject == CK_INVALID_HANDLE )
        {
            xPalHandle = PKCS11_PAL_FindObject( pxSession->pxFindObjectLabel, ( uint8_t ) strlen( ( const char * ) pxSession->pxFindObjectLabel ) );
        }

        if( xPalHandle != CK_INVALID_HANDLE )
        {
            xResult = PKCS11_PAL_GetObjectValue( xPalHandle, ( uint8_t ** ) &pucObjectValue, ( uint32_t * ) &xObjectLength, &xIsPrivate );

            if( xResult == CKR_OK )
            {
                for( ulIndex = 0; ulIndex < xObjectLength; ulIndex++ )
                {
                    xByte = pucObjectValue[ ulIndex ];

                    if( xByte != 0UL )
                    {
                        break;
                    }
                }

                if( xByte == 0UL ) /* Deleted objects are overwritten completely w/ zero. */
                {
                    *phObject = CK_INVALID_HANDLE;
                }
                else
                {
                    xResult = prvAddObjectToList( xPalHandle, phObject, pxSession->pxFindObjectLabel, strlen( ( const char * ) pxSession->pxFindObjectLabel ) );
                    *pulObjectCount = 1;
                }

                PKCS11_PAL_GetObjectValueCleanup( pucObjectValue, xObjectLength );
            }
        }
        else
        {
            /* Note: Objects living in header files are not destroyed. */
            /* According to the PKCS #11 standard, not finding an object results in a CKR_OK return value with an object count of 0. */
            *pulObjectCount = 0;
            PKCS11_WARNING_PRINT( ( "WARN: Object with label '%s' not found. \r\n", ( char * ) pxSession->pxFindObjectLabel ) );
        }
    }

    /* Clean up memory if there was an error finding the object. */
    if( xResult != CKR_OK )
    {
        if( pxSession != NULL )
        {
            vPortFree( pxSession->pxFindObjectLabel );
            pxSession->pxFindObjectLabel = NULL;
        }
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_findobjects] */

/**
 * @brief Finishes an object search operation.
 *
 * \sa C_FindObjectsInit(), C_FindObjects() which must be called before
 * calling C_FindObjectsFinal().
 *
 * \note FindObjects parameters are shared by a session.  Calling
 * C_FindObjectsInit(), C_FindObjects(), and C_FindObjectsFinal() with the
 * same session across different tasks may lead to unexpected results.
 *
 *
 * @param[in] hSession                      Handle of a valid PKCS #11 session.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_findobjectsfinal] */
CK_DECLARE_FUNCTION( CK_RV, C_FindObjectsFinal )( CK_SESSION_HANDLE hSession )
{
    P11Session_t * pxSession = prvSessionPointerFromHandle( hSession );
    CK_RV xResult = prvCheckValidSessionAndModule( pxSession );

    /*
     * Check parameters.
     */
    if( xResult == CKR_OK )
    {
        if( pxSession->pxFindObjectLabel == NULL )
        {
            xResult = CKR_OPERATION_NOT_INITIALIZED;
        }
    }

    if( xResult == CKR_OK )
    {
        /*
         * Clean-up find objects state.
         */
        vPortFree( pxSession->pxFindObjectLabel );
        pxSession->pxFindObjectLabel = NULL;
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_findobjectsfinal] */

/**
 * @brief Initializes a message-digesting operation.
 *
 * \sa C_DigestUpdate(), C_DigestFinal()
 *
 * \note Digest parameters are shared by a session.  Calling
 * C_DigestInit(), C_DigestUpdate(), and C_DigestFinal() with the
 * same session across different tasks may lead to unexpected results.
 *
 *
 * @param[in] hSession                      Handle of a valid PKCS #11 session.
 * @param[in] pMechanism                    Digesting mechanism.  This port only supports
 *                                          the mechanism CKM_SHA256.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_digestinit] */
CK_DECLARE_FUNCTION( CK_RV, C_DigestInit )( CK_SESSION_HANDLE hSession,
                                            CK_MECHANISM_PTR pMechanism )
{
    P11Session_t * pxSession = prvSessionPointerFromHandle( hSession );
    CK_RV xResult = prvCheckValidSessionAndModule( pxSession );

    if( pMechanism == NULL )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    if( xResult == CKR_OK )
    {
        /* See explanation in prvCheckValidSessionAndModule for this exception. */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        if( prvOperationActive( pxSession ) == ( CK_BBOOL ) CK_TRUE )
        {
            xResult = CKR_OPERATION_ACTIVE;
        }
    }

    if( xResult == CKR_OK )
    {
        if( pMechanism->mechanism != CKM_SHA256 )
        {
            xResult = CKR_MECHANISM_INVALID;
        }
    }

    /*
     * Initialize the requested hash type
     */
    if( xResult == CKR_OK )
    {
        mbedtls_sha256_init( &pxSession->xSHA256Context );

        if( 0 != mbedtls_sha256_starts_ret( &pxSession->xSHA256Context, 0 ) )
        {
            xResult = CKR_FUNCTION_FAILED;
        }
        else
        {
            pxSession->xOperationDigestMechanism = pMechanism->mechanism;
        }
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_digestinit] */


/**
 * @brief Continues a multiple-part digesting operation.
 *
 * \sa C_DigestInit(), C_DigestFinal()
 *
 * \note Digest parameters are shared by a session.  Calling
 * C_DigestInit(), C_DigestUpdate(), and C_DigestFinal() with the
 * same session across different tasks may lead to unexpected results.
 *
 *
 * @param[in] hSession                      Handle of a valid PKCS #11 session.
 * @param[in] pPart                         Pointer to the data to be added to the digest.
 * @param[in] ulPartLen                     Length of the data located at pPart.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_digestupdate] */
CK_DECLARE_FUNCTION( CK_RV, C_DigestUpdate )( CK_SESSION_HANDLE hSession,
                                              CK_BYTE_PTR pPart,
                                              CK_ULONG ulPartLen )
{
    P11Session_t * pxSession = prvSessionPointerFromHandle( hSession );
    CK_RV xResult = prvCheckValidSessionAndModule( pxSession );

    if( pPart == NULL )
    {
        PKCS11_PRINT( ( "ERROR: Null digest mechanism provided. \r\n" ) );
        xResult = CKR_ARGUMENTS_BAD;
    }

    if( xResult == CKR_OK )
    {
        if( pxSession->xOperationDigestMechanism != CKM_SHA256 )
        {
            xResult = CKR_OPERATION_NOT_INITIALIZED;
        }
    }

    if( xResult == CKR_OK )
    {
        if( 0 != mbedtls_sha256_update_ret( &pxSession->xSHA256Context, pPart, ulPartLen ) )
        {
            xResult = CKR_FUNCTION_FAILED;
            pxSession->xOperationDigestMechanism = pkcs11NO_OPERATION;
        }
    }

    if( ( xResult != CKR_OK ) && ( xResult != CKR_SESSION_HANDLE_INVALID ) )
    {
        pxSession->xOperationDigestMechanism = pkcs11NO_OPERATION;
        mbedtls_sha256_free( &pxSession->xSHA256Context );
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_digestupdate] */

/**
 * @brief Finishes a multiple-part digesting operation.
 *
 * \sa C_DigestInit(), C_DigestUpdate()
 *
 * \note Digest parameters are shared by a session.  Calling
 * C_DigestInit(), C_DigestUpdate(), and C_DigestFinal() with the
 * same session across different tasks may lead to unexpected results.
 *
 *
 * @param[in] hSession                      Handle of a valid PKCS #11 session.
 * @param[out] pDigest                      Pointer to the location that receives
 *                                          the message digest.  Memory must be allocated
 *                                          by the caller.                                          Caller is responsible for allocating memory.
 *                                          Providing NULL for this input will cause
 *                                          pulDigestLen to be updated for length of
 *                                          buffer required.
 * @param[in,out] pulDigestLen              Points to the location that holds the length
 *                                          of the message digest.  If pDigest is NULL,
 *                                          this value is updated to contain the length
 *                                          of the buffer needed to hold the digest. Else
 *                                          it is updated to contain the actual length of
 *                                          the digest placed in pDigest.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_digestfinal] */
CK_DECLARE_FUNCTION( CK_RV, C_DigestFinal )( CK_SESSION_HANDLE hSession,
                                             CK_BYTE_PTR pDigest,
                                             CK_ULONG_PTR pulDigestLen )
{
    P11Session_t * pxSession = prvSessionPointerFromHandle( hSession );
    CK_RV xResult = prvCheckValidSessionAndModule( pxSession );


    if( pulDigestLen == NULL )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    if( xResult == CKR_OK )
    {
        if( pxSession->xOperationDigestMechanism != CKM_SHA256 )
        {
            xResult = CKR_OPERATION_NOT_INITIALIZED;
            pxSession->xOperationDigestMechanism = pkcs11NO_OPERATION;
        }
    }

    if( xResult == CKR_OK )
    {
        if( pDigest == NULL )
        {
            /* Supply the required buffer size. */
            *pulDigestLen = ( CK_ULONG ) pkcs11SHA256_DIGEST_LENGTH;
        }
        else
        {
            if( *pulDigestLen < ( CK_ULONG ) pkcs11SHA256_DIGEST_LENGTH )
            {
                xResult = CKR_BUFFER_TOO_SMALL;
            }
            else
            {
                if( 0 != mbedtls_sha256_finish_ret( &pxSession->xSHA256Context, pDigest ) )
                {
                    xResult = CKR_FUNCTION_FAILED;
                }

                pxSession->xOperationDigestMechanism = pkcs11NO_OPERATION;
            }
        }
    }

    if( ( xResult != CKR_OK ) && ( xResult != CKR_BUFFER_TOO_SMALL ) && ( xResult != CKR_SESSION_HANDLE_INVALID ) )
    {
        pxSession->xOperationDigestMechanism = pkcs11NO_OPERATION;
        mbedtls_sha256_free( &pxSession->xSHA256Context );
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_digestfinal] */

/**
 * @brief Initializes a signature operation.
 *
 * \sa C_Sign() completes signatures initiated by C_SignInit().
 *
 * \note C_Sign() parameters are shared by a session.  Calling
 * C_SignInit() & C_Sign() with the same session across different
 * tasks may lead to unexpected results.
 *
 *
 * @param[in] hSession                      Handle of a valid PKCS #11 session.
 * @param[in] pMechanism                    Mechanism used to sign.
 *                                          This port supports the following mechanisms:
 *                                          - CKM_RSA_PKCS for RSA signatures
 *                                          - CKM_ECDSA for elliptic curve signatures
 *                                          Note that neither of these mechanisms perform
 *                                          hash operations.
 * @param[in] hKey                          The handle of the private key to be used for
 *                                          signature. Key must be compatible with the
 *                                          mechanism chosen by pMechanism.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_signinit] */
CK_DECLARE_FUNCTION( CK_RV, C_SignInit )( CK_SESSION_HANDLE hSession,
                                          CK_MECHANISM_PTR pMechanism,
                                          CK_OBJECT_HANDLE hKey )
{
    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    CK_BBOOL xIsPrivate = ( CK_BBOOL ) CK_TRUE;
    CK_OBJECT_HANDLE xPalHandle;
    uint8_t * pxLabel = NULL;
    size_t xLabelLength = 0;
    mbedtls_pk_type_t xKeyType;

    P11Session_t * pxSession = prvSessionPointerFromHandle( hSession );
    CK_RV xResult = prvCheckValidSessionAndModule( pxSession );
    uint8_t * pulKeyData = NULL;
    uint32_t ulKeyDataLength = 0;
    int32_t lMbedTLSResult = 0;


    if( NULL == pMechanism )
    {
        PKCS11_PRINT( ( "ERROR: Null signing mechanism provided. \r\n" ) );
        xResult = CKR_ARGUMENTS_BAD;
    }

    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    if( ( xResult == CKR_OK ) && ( prvOperationActive( pxSession ) == ( CK_BBOOL ) CK_TRUE ) )
    {
        xResult = CKR_OPERATION_ACTIVE;
    }

    /* Retrieve key value from storage. */
    if( xResult == CKR_OK )
    {
        prvFindObjectInListByHandle( hKey,
                                     &xPalHandle,
                                     &pxLabel,
                                     &xLabelLength );

        if( xPalHandle != CK_INVALID_HANDLE )
        {
            xResult = PKCS11_PAL_GetObjectValue( xPalHandle, &pulKeyData, &ulKeyDataLength, &xIsPrivate );

            if( xResult != CKR_OK )
            {
                PKCS11_PRINT( ( "ERROR: Unable to retrieve value of private key for signing %d. \r\n", xResult ) );
                xResult = CKR_KEY_HANDLE_INVALID;
            }
        }
    }

    /* Check that a private key was retrieved. */
    if( xResult == CKR_OK )
    {
        /* See explanation in prvCheckValidSessionAndModule for this exception. */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        if( xIsPrivate != ( CK_BBOOL ) CK_TRUE )
        {
            PKCS11_PRINT( ( "ERROR: Sign operation attempted with public key. \r\n" ) );
            xResult = CKR_KEY_TYPE_INCONSISTENT;
        }
    }

    /* Convert the private key from storage format to mbedTLS usable format. */
    if( xResult == CKR_OK )
    {
        /* Grab the sign mutex.  This ensures that no signing operation
         * is underway on another thread where modification of key would lead to hard fault.*/
        if( pdTRUE == xSemaphoreTake( pxSession->xSignMutex, portMAX_DELAY ) )
        {
            /* Free the private key context if it exists.
             * TODO: Check if the key is the same as was used previously. */
            mbedtls_pk_free( &pxSession->xSignKey );

            mbedtls_pk_init( &pxSession->xSignKey );
            lMbedTLSResult = mbedtls_pk_parse_key( &pxSession->xSignKey, pulKeyData, ulKeyDataLength, NULL, 0 );

            if( lMbedTLSResult != 0 )
            {
                PKCS11_PRINT( ( "mbedTLS unable to parse private key for signing. %s : ",
                                mbedtlsHighLevelCodeOrDefault( lMbedTLSResult ) ) );
                PKCS11_PRINT( ( "%s \r\n",
                                mbedtlsLowLevelCodeOrDefault( lMbedTLSResult ) ) );
                xResult = CKR_KEY_HANDLE_INVALID;
            }

            ( void ) xSemaphoreGive( pxSession->xSignMutex );

            /* Key has been parsed into mbedTLS pk structure.
             * Free the memory allocated to copy the key out of flash. */
            PKCS11_PAL_GetObjectValueCleanup( pulKeyData, ulKeyDataLength );
        }
        else
        {
            xResult = CKR_CANT_LOCK;
        }
    }

    /* Check that the mechanism and key type are compatible, supported. */
    if( xResult == CKR_OK )
    {
        xKeyType = mbedtls_pk_get_type( &pxSession->xSignKey );

        if( pMechanism->mechanism == CKM_RSA_PKCS )
        {
            if( xKeyType != MBEDTLS_PK_RSA )
            {
                PKCS11_PRINT( ( "ERROR: Signing key type (%d) does not match RSA mechanism \r\n", xKeyType ) );
                xResult = CKR_KEY_TYPE_INCONSISTENT;
            }
        }
        else if( pMechanism->mechanism == CKM_ECDSA )
        {
            if( ( xKeyType != MBEDTLS_PK_ECDSA ) && ( xKeyType != MBEDTLS_PK_ECKEY ) )
            {
                PKCS11_PRINT( ( "ERROR: Signing key type (%d) does not match ECDSA mechanism \r\n", xKeyType ) );
                xResult = CKR_KEY_TYPE_INCONSISTENT;
            }
        }
        else
        {
            PKCS11_PRINT( ( "ERROR: Unsupported mechanism type %d \r\n", pMechanism->mechanism ) );
            xResult = CKR_MECHANISM_INVALID;
        }
    }

    if( xResult == CKR_OK )
    {
        pxSession->xOperationSignMechanism = pMechanism->mechanism;
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_signinit] */

/**
 * @brief Signs single-part data.
 *
 * \sa C_SignInit() initiates signatures signature creation.
 *
 * \note C_Sign() parameters are shared by a session.  Calling
 * C_SignInit() & C_Sign() with the same session across different
 * tasks may lead to unexpected results.
 *
 *
 * @param[in] hSession                      Handle of a valid PKCS #11 session.
 * @param[in] pData                         Data to be signed.
 *                                          Note: Some applications may require this data to
 *                                          be hashed before passing to C_Sign().
 * @param[in] ulDataLen                      Length of pucData, in bytes.
 * @param[out] pSignature                   Buffer where signature will be placed.
 *                                          Caller is responsible for allocating memory.
 *                                          Providing NULL for this input will cause
 *                                          pulSignatureLen to be updated for length of
 *                                          buffer required.
 * @param[in,out] pulSignatureLen           Length of pucSignature buffer.
 *                                          If pucSignature is non-NULL, pulSignatureLen is
 *                                          updated to contain the actual signature length.
 *                                          If pucSignature is NULL, pulSignatureLen is
 *                                          updated to the buffer length required for signature
 *                                          data.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_sign] */
CK_DECLARE_FUNCTION( CK_RV, C_Sign )( CK_SESSION_HANDLE hSession,
                                      CK_BYTE_PTR pData,
                                      CK_ULONG ulDataLen,
                                      CK_BYTE_PTR pSignature,
                                      CK_ULONG_PTR pulSignatureLen )
{
    P11Session_t * pxSessionObj = prvSessionPointerFromHandle( hSession );
    CK_RV xResult = prvCheckValidSessionAndModule( pxSessionObj );

    CK_ULONG xSignatureLength = 0;
    size_t xExpectedInputLength = 0;
    CK_BYTE_PTR pxSignatureBuffer = pSignature;
    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    CK_BBOOL xSignatureGenerated = ( CK_BBOOL ) CK_FALSE;
    uint8_t ecSignature[ pkcs11ECDSA_P256_SIGNATURE_LENGTH + 15 ]; /*TODO: Figure out this length. */
    int32_t lMbedTLSResult;


    if( ( NULL == pulSignatureLen ) || ( NULL == pData ) )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    if( CKR_OK == xResult )
    {
        /* Update the signature length. */
        if( pxSessionObj->xOperationSignMechanism == CKM_RSA_PKCS )
        {
            xSignatureLength = pkcs11RSA_2048_SIGNATURE_LENGTH;
            xExpectedInputLength = pkcs11RSA_SIGNATURE_INPUT_LENGTH;
        }
        else if( pxSessionObj->xOperationSignMechanism == CKM_ECDSA )
        {
            xSignatureLength = pkcs11ECDSA_P256_SIGNATURE_LENGTH;
            xExpectedInputLength = pkcs11SHA256_DIGEST_LENGTH;
            pxSignatureBuffer = ecSignature;
        }
        else
        {
            xResult = CKR_OPERATION_NOT_INITIALIZED;
        }
    }

    if( xResult == CKR_OK )
    {
        /* Calling application is trying to determine length needed for signature buffer. */
        if( NULL != pSignature )
        {
            /* Check that the signature buffer is long enough. */
            if( *pulSignatureLen < xSignatureLength )
            {
                xResult = CKR_BUFFER_TOO_SMALL;
            }

            /* Check that input data to be signed is the expected length. */
            if( CKR_OK == xResult )
            {
                if( xExpectedInputLength != ulDataLen )
                {
                    xResult = CKR_DATA_LEN_RANGE;
                }
            }

            /* Sign the data.*/
            if( CKR_OK == xResult )
            {
                if( pdTRUE == xSemaphoreTake( pxSessionObj->xSignMutex, portMAX_DELAY ) )
                {
                    lMbedTLSResult = mbedtls_pk_sign( &pxSessionObj->xSignKey,
                                                      MBEDTLS_MD_NONE,
                                                      pData,
                                                      ulDataLen,
                                                      pxSignatureBuffer,
                                                      &xExpectedInputLength,
                                                      mbedtls_ctr_drbg_random,
                                                      &xP11Context.xMbedDrbgCtx );

                    if( lMbedTLSResult != 0 )
                    {
                        PKCS11_PRINT( ( "mbedTLS sign failed with error %s : ",
                                        mbedtlsHighLevelCodeOrDefault( lMbedTLSResult ) ) );
                        PKCS11_PRINT( ( "%s \r\n",
                                        mbedtlsLowLevelCodeOrDefault( lMbedTLSResult ) ) );
                        xResult = CKR_FUNCTION_FAILED;
                    }

                    ( void ) xSemaphoreGive( pxSessionObj->xSignMutex );
                    /* See explanation in prvCheckValidSessionAndModule for this exception. */
                    /* coverity[misra_c_2012_rule_10_5_violation] */
                    xSignatureGenerated = ( CK_BBOOL ) CK_TRUE;
                }
                else
                {
                    xResult = CKR_CANT_LOCK;
                }
            }
        }
    }

    if( xResult == CKR_OK )
    {
        /* If this an EC signature, reformat from ASN.1 encoded to 64-byte R & S components */
        /* See explanation in prvCheckValidSessionAndModule for this exception. */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        if( ( pxSessionObj->xOperationSignMechanism == CKM_ECDSA ) && ( xSignatureGenerated == ( CK_BBOOL ) CK_TRUE ) )
        {
            lMbedTLSResult = PKI_mbedTLSSignatureToPkcs11Signature( pSignature, ecSignature );

            if( lMbedTLSResult != 0 )
            {
                xResult = CKR_FUNCTION_FAILED;
            }
        }
    }

    if( ( xResult == CKR_OK ) || ( xResult == CKR_BUFFER_TOO_SMALL ) )
    {
        *pulSignatureLen = xSignatureLength;
    }

    /* Complete the operation in the context. */
    if( ( xResult != CKR_BUFFER_TOO_SMALL ) && ( xResult != CKR_SESSION_HANDLE_INVALID ) )
    {
        pxSessionObj->xOperationSignMechanism = pkcs11NO_OPERATION;
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_sign] */

/**
 * @brief Initializes a verification operation.
 *
 * \sa C_Verify() completes verifications initiated by C_VerifyInit().
 *
 * \note C_Verify() parameters are shared by a session.  Calling
 * C_VerifyInit() & C_Verify() with the same session across different
 * tasks may lead to unexpected results.
 *
 *
 * @param[in] hSession                      Handle of a valid PKCS #11 session.
 * @param[in] pMechanism                   Mechanism used to verify signature.
 *                                          This port supports the following mechanisms:
 *                                          - CKM_RSA_X_509 for RSA verifications
 *                                          - CKM_ECDSA for elliptic curve verifications
 * @param[in] hKey                          The handle of the public key to be used for
 *                                          verification. Key must be compatible with the
 *                                          mechanism chosen by pxMechanism.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_verifyinit] */
CK_DECLARE_FUNCTION( CK_RV, C_VerifyInit )( CK_SESSION_HANDLE hSession,
                                            CK_MECHANISM_PTR pMechanism,
                                            CK_OBJECT_HANDLE hKey )
{
    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    CK_BBOOL xIsPrivate = ( CK_BBOOL ) CK_TRUE;
    P11Session_t * pxSession;
    uint8_t * pucKeyData = NULL;
    uint32_t ulKeyDataLength = 0;
    mbedtls_pk_type_t xKeyType;
    CK_OBJECT_HANDLE xPalHandle = CK_INVALID_HANDLE;
    uint8_t * pxLabel = NULL;
    size_t xLabelLength = 0;

    pxSession = prvSessionPointerFromHandle( hSession );
    CK_RV xResult = prvCheckValidSessionAndModule( pxSession );

    if( NULL == pMechanism )
    {
        PKCS11_PRINT( ( "ERROR: Null verification mechanism provided. \r\n" ) );
        xResult = CKR_ARGUMENTS_BAD;
    }

    /* See explanation in prvCheckValidSessionAndModule for this exception. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    if( ( xResult == CKR_OK ) && ( prvOperationActive( pxSession ) == ( CK_BBOOL ) CK_TRUE ) )
    {
        xResult = CKR_OPERATION_ACTIVE;
    }

    /* Retrieve key value from storage. */
    if( xResult == CKR_OK )
    {
        prvFindObjectInListByHandle( hKey,
                                     &xPalHandle,
                                     &pxLabel,
                                     &xLabelLength );

        if( xPalHandle != CK_INVALID_HANDLE )
        {
            xResult = PKCS11_PAL_GetObjectValue( xPalHandle, &pucKeyData, &ulKeyDataLength, &xIsPrivate );

            if( xResult != CKR_OK )
            {
                PKCS11_PRINT( ( "ERROR: Unable to retrieve value of private key for signing %d. \r\n", xResult ) );
            }
        }
        else
        {
            xResult = CKR_KEY_HANDLE_INVALID;
        }
    }

    /* Check that a public key was retrieved. */
    if( xResult == CKR_OK )
    {
        /* See explanation in prvCheckValidSessionAndModule for this exception. */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        if( xIsPrivate != ( CK_BBOOL ) CK_FALSE )
        {
            PKCS11_PRINT( ( "ERROR: Verify operation attempted with private key. \r\n" ) );
            xResult = CKR_KEY_TYPE_INCONSISTENT;
        }
    }

    if( xResult == CKR_OK )
    {
        if( pdTRUE == xSemaphoreTake( pxSession->xVerifyMutex, portMAX_DELAY ) )
        {
            /* Free the public key context if it exists.
             * TODO: Check if the key is the same as used by last verify operation. */
            mbedtls_pk_free( &pxSession->xVerifyKey );

            mbedtls_pk_init( &pxSession->xVerifyKey );

            if( 0 != mbedtls_pk_parse_public_key( &pxSession->xVerifyKey, pucKeyData, ulKeyDataLength ) )
            {
                if( 0 != mbedtls_pk_parse_key( &pxSession->xVerifyKey, pucKeyData, ulKeyDataLength, NULL, 0 ) )
                {
                    PKCS11_PRINT( ( "ERROR: Unable to parse public key for verification. \r\n" ) );
                    xResult = CKR_KEY_HANDLE_INVALID;
                }
            }

            ( void ) xSemaphoreGive( pxSession->xVerifyMutex );
            PKCS11_PAL_GetObjectValueCleanup( pucKeyData, ulKeyDataLength );
        }
        else
        {
            xResult = CKR_CANT_LOCK;
        }
    }

    /* Check that the mechanism and key type are compatible, supported. */
    if( xResult == CKR_OK )
    {
        xKeyType = mbedtls_pk_get_type( &pxSession->xSignKey );

        if( pMechanism->mechanism == CKM_RSA_X_509 )
        {
            if( xKeyType != MBEDTLS_PK_RSA )
            {
                PKCS11_PRINT( ( "ERROR: Verification key type (%d) does not match RSA mechanism \r\n", xKeyType ) );
                xResult = CKR_KEY_TYPE_INCONSISTENT;
            }
        }
        else if( pMechanism->mechanism == CKM_ECDSA )
        {
            if( ( xKeyType != MBEDTLS_PK_ECDSA ) && ( xKeyType != MBEDTLS_PK_ECKEY ) )
            {
                PKCS11_PRINT( ( "ERROR: Verification key type (%d) does not match ECDSA mechanism \r\n", xKeyType ) );
                xResult = CKR_KEY_TYPE_INCONSISTENT;
            }
        }
        else
        {
            PKCS11_PRINT( ( "ERROR: Unsupported mechanism type %d \r\n", pMechanism->mechanism ) );
            xResult = CKR_MECHANISM_INVALID;
        }
    }

    if( xResult == CKR_OK )
    {
        pxSession->xOperationVerifyMechanism = pMechanism->mechanism;
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_verifyinit] */

/**
 * @brief Verifies a signature on single-part data.
 *
 * \note C_VerifyInit() must have been called previously.
 *
 * \note C_Verify() parameters are shared by a session.  Calling
 * C_VerifyInit() & C_Verify() with the same session across different
 * tasks may lead to unexpected results.
 *
 *
 * @param[in] hSession                      Handle of a valid PKCS #11 session.
 * @param[in] pData                         Data who's signature is to be verified.
 *                                          Note: In this implementation, this is generally
 *                                          expected to be the hash of the data.
 * @param[in] ulDataLen                     Length of pucData.
 * @param[in] pSignature                    The signature to be verified.
 * @param[in] ulSignatureLen                Length of pucSignature in bytes.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_verify] */
CK_DECLARE_FUNCTION( CK_RV, C_Verify )( CK_SESSION_HANDLE hSession,
                                        CK_BYTE_PTR pData,
                                        CK_ULONG ulDataLen,
                                        CK_BYTE_PTR pSignature,
                                        CK_ULONG ulSignatureLen )
{
    P11Session_t * pxSessionObj;
    int32_t lMbedTLSResult;

    pxSessionObj = prvSessionPointerFromHandle( hSession );
    CK_RV xResult = prvCheckValidSessionAndModule( pxSessionObj );

    /* Check parameters. */
    if( ( NULL == pData ) ||
        ( NULL == pSignature ) )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    /* Check that the signature and data are the expected length.
     * These PKCS #11 mechanism expect data to be pre-hashed/formatted. */
    if( xResult == CKR_OK )
    {
        if( pxSessionObj->xOperationVerifyMechanism == CKM_RSA_X_509 )
        {
            if( ulDataLen != pkcs11RSA_2048_SIGNATURE_LENGTH )
            {
                xResult = CKR_DATA_LEN_RANGE;
            }

            if( ulSignatureLen != pkcs11RSA_2048_SIGNATURE_LENGTH )
            {
                xResult = CKR_SIGNATURE_LEN_RANGE;
            }
        }
        else if( pxSessionObj->xOperationVerifyMechanism == CKM_ECDSA )
        {
            if( ulDataLen != pkcs11SHA256_DIGEST_LENGTH )
            {
                xResult = CKR_DATA_LEN_RANGE;
            }

            if( ulSignatureLen != pkcs11ECDSA_P256_SIGNATURE_LENGTH )
            {
                xResult = CKR_SIGNATURE_LEN_RANGE;
            }
        }
        else
        {
            xResult = CKR_OPERATION_NOT_INITIALIZED;
        }
    }

    /* Verification step. */
    if( xResult == CKR_OK )
    {
        /* Perform an RSA verification. */
        if( pxSessionObj->xOperationVerifyMechanism == CKM_RSA_X_509 )
        {
            if( pdTRUE == xSemaphoreTake( pxSessionObj->xVerifyMutex, portMAX_DELAY ) )
            {
                /* Verify the signature. If a public key is present, use it. */
                if( NULL != pxSessionObj->xVerifyKey.pk_ctx )
                {
                    if( 0 != mbedtls_pk_verify( &pxSessionObj->xVerifyKey,
                                                MBEDTLS_MD_SHA256,
                                                pData,
                                                ulDataLen,
                                                pSignature,
                                                ulSignatureLen ) )
                    {
                        xResult = CKR_SIGNATURE_INVALID;
                    }
                }

                ( void ) xSemaphoreGive( pxSessionObj->xVerifyMutex );
            }
            else
            {
                xResult = CKR_CANT_LOCK;
            }
        }
        /* Perform an ECDSA verification. */
        else if( pxSessionObj->xOperationVerifyMechanism == CKM_ECDSA )
        {
            /* TODO: Refactor w/ test code
             * An ECDSA signature is comprised of 2 components - R & S.  C_Sign returns them one after another. */
            mbedtls_ecdsa_context * pxEcdsaContext;
            mbedtls_mpi xR;
            mbedtls_mpi xS;
            mbedtls_mpi_init( &xR );
            mbedtls_mpi_init( &xS );

            lMbedTLSResult = mbedtls_mpi_read_binary( &xR, &pSignature[ 0 ], 32 );

            if( lMbedTLSResult == 0 )
            {
                lMbedTLSResult = mbedtls_mpi_read_binary( &xS, &pSignature[ 32 ], 32 );
            }

            if( lMbedTLSResult != 0 )
            {
                xResult = CKR_SIGNATURE_INVALID;
                PKCS11_PRINT( ( "Failed to parse EC signature: %s : ",
                                mbedtlsHighLevelCodeOrDefault( lMbedTLSResult ) ) );
                PKCS11_PRINT( ( "%s \r\n",
                                mbedtlsLowLevelCodeOrDefault( lMbedTLSResult ) ) );
            }

            if( xResult == CKR_OK )
            {
                if( pdTRUE == xSemaphoreTake( pxSessionObj->xVerifyMutex, portMAX_DELAY ) )
                {
                    /* Verify the signature. If a public key is present, use it. */
                    if( NULL != pxSessionObj->xVerifyKey.pk_ctx )
                    {
                        pxEcdsaContext = pxSessionObj->xVerifyKey.pk_ctx;
                        lMbedTLSResult = mbedtls_ecdsa_verify( &pxEcdsaContext->grp, pData, ulDataLen, &pxEcdsaContext->Q, &xR, &xS );
                    }

                    ( void ) xSemaphoreGive( pxSessionObj->xVerifyMutex );

                    if( lMbedTLSResult != 0 )
                    {
                        xResult = CKR_SIGNATURE_INVALID;
                        PKCS11_PRINT( ( "Failed to parse EC signature: %s : ",
                                        mbedtlsHighLevelCodeOrDefault( lMbedTLSResult ) ) );
                        PKCS11_PRINT( ( "%s \r\n",
                                        mbedtlsLowLevelCodeOrDefault( lMbedTLSResult ) ) );
                    }
                }
            }

            mbedtls_mpi_free( &xR );
            mbedtls_mpi_free( &xS );
        }
        else
        {
            xResult = CKR_TEMPLATE_INCONSISTENT;
        }
    }

    if( xResult != CKR_SESSION_HANDLE_INVALID )
    {
        pxSessionObj->xOperationVerifyMechanism = pkcs11NO_OPERATION;
    }

    /* Return the signature verification result. */
    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_verify] */

/**
 * @brief Checks that the private key template provided for C_GenerateKeyPair
 * contains all necessary attributes, and does not contain any invalid
 * attributes.
 *
 * @param[out] ppxLabel                       Pointer to PKCS #11 label.
 * @param[in] pxTemplate                      PKCS #11 templates to search.
 * @param[in] pulAttributeMap                 Flag to track whether all required attribute
 *                                            are in the key generation template.
 * @return CKR_OK if successful.
 */
static CK_RV prvCheckGenerateKeyPairPrivateTemplate( CK_ATTRIBUTE ** ppxLabel,
                                                     CK_ATTRIBUTE * pxAttribute,
                                                     uint32_t * pulAttributeMap )
{
    CK_RV xResult = CKR_OK;
    CK_BBOOL xBool;
    CK_ULONG xTemp;

    switch( pxAttribute->type )
    {
        case ( CKA_LABEL ):
            *ppxLabel = pxAttribute;
            *pulAttributeMap |= LABEL_IN_TEMPLATE;
            break;

        case ( CKA_KEY_TYPE ):
            ( void ) memcpy( &xTemp, pxAttribute->pValue, sizeof( CK_ULONG ) );

            if( xTemp != CKK_EC )
            {
                PKCS11_PRINT( ( "ERROR: Only EC key pair generation is supported. \r\n" ) );
                xResult = CKR_TEMPLATE_INCONSISTENT;
            }

            break;

        case ( CKA_SIGN ):
            ( void ) memcpy( &xBool, pxAttribute->pValue, sizeof( CK_BBOOL ) );

            /* See explanation in prvCheckValidSessionAndModule for this exception. */
            /* coverity[misra_c_2012_rule_10_5_violation] */
            if( xBool != ( CK_BBOOL ) CK_TRUE )
            {
                PKCS11_PRINT( ( "ERROR: Generating private keys that cannot sign is not supported. \r\n" ) );
                xResult = CKR_TEMPLATE_INCONSISTENT;
            }

            *pulAttributeMap |= SIGN_IN_TEMPLATE;
            break;

        case ( CKA_PRIVATE ):
            ( void ) memcpy( &xBool, pxAttribute->pValue, sizeof( CK_BBOOL ) );

            /* See explanation in prvCheckValidSessionAndModule for this exception. */
            /* coverity[misra_c_2012_rule_10_5_violation] */
            if( xBool != ( CK_BBOOL ) CK_TRUE )
            {
                PKCS11_PRINT( ( "ERROR: Private must be set to true in order to generate a private key. \r\n" ) );
                xResult = CKR_TEMPLATE_INCONSISTENT;
            }

            *pulAttributeMap |= PRIVATE_IN_TEMPLATE;
            break;

        case ( CKA_TOKEN ):
            ( void ) memcpy( &xBool, pxAttribute->pValue, sizeof( CK_BBOOL ) );

            /* See explanation in prvCheckValidSessionAndModule for this exception. */
            /* coverity[misra_c_2012_rule_10_5_violation] */
            if( xBool != ( CK_BBOOL ) CK_TRUE )
            {
                PKCS11_PRINT( ( "ERROR: Generating private keys that are false for attribute CKA_TOKEN is not supported. \r\n" ) );
                xResult = CKR_TEMPLATE_INCONSISTENT;
            }

            break;

        default:
            xResult = CKR_ATTRIBUTE_TYPE_INVALID;
            break;
    }

    return xResult;
}

/**
 * @brief  Checks that the public key template provided for C_GenerateKeyPair
 * contains all necessary attributes, and does not contain any invalid
 * attributes.
 *
 * @param[out] ppxLabel                       Pointer to PKCS #11 label.
 * @param[in] pxTemplate                      PKCS #11 templates to search.
 * @param[in] pulAttributeMap                 Flag to track whether all required attribute
 *                                            are in the key generation template.
 *
 * @return CKR_OK if successful.
 */
static CK_RV prvCheckGenerateKeyPairPublicTemplate( CK_ATTRIBUTE ** ppxLabel,
                                                    CK_ATTRIBUTE * pxAttribute,
                                                    uint32_t * pulAttributeMap )
{
    CK_RV xResult = CKR_OK;
    CK_BBOOL xBool;
    CK_KEY_TYPE xKeyType;
    const CK_BYTE pxEcParams[] = pkcs11DER_ENCODED_OID_P256;
    const CK_BYTE * pxEcAttVal;

    switch( pxAttribute->type )
    {
        case ( CKA_LABEL ):
            *ppxLabel = pxAttribute;
            *pulAttributeMap |= LABEL_IN_TEMPLATE;
            break;

        case ( CKA_KEY_TYPE ):
            ( void ) memcpy( &xKeyType, ( CK_KEY_TYPE * ) pxAttribute->pValue, sizeof( CK_KEY_TYPE ) );

            if( xKeyType != CKK_EC )
            {
                PKCS11_PRINT( ( "ERROR: Only EC key pair generation is supported. \r\n" ) );
                xResult = CKR_TEMPLATE_INCONSISTENT;
            }

            break;

        case ( CKA_EC_PARAMS ):
            pxEcAttVal = ( CK_BYTE * ) pxAttribute->pValue;

            if( memcmp( pxEcParams, pxEcAttVal, sizeof( pxEcParams ) ) != 0 )
            {
                PKCS11_PRINT( ( "ERROR: Only P-256 key generation is supported. \r\n" ) );
                xResult = CKR_TEMPLATE_INCONSISTENT;
            }

            *pulAttributeMap |= EC_PARAMS_IN_TEMPLATE;
            break;

        case ( CKA_VERIFY ):
            ( void ) memcpy( &xBool, pxAttribute->pValue, sizeof( CK_BBOOL ) );

            /* See explanation in prvCheckValidSessionAndModule for this exception. */
            /* coverity[misra_c_2012_rule_10_5_violation] */
            if( xBool != ( CK_BBOOL ) CK_TRUE )
            {
                PKCS11_PRINT( ( "ERROR: Generating public keys that are false for attribute CKA_VERIFY is not supported. \r\n" ) );
                xResult = CKR_TEMPLATE_INCONSISTENT;
            }

            *pulAttributeMap |= VERIFY_IN_TEMPLATE;
            break;

        case ( CKA_TOKEN ):
            ( void ) memcpy( &xBool, pxAttribute->pValue, sizeof( CK_BBOOL ) );

            /* See explanation in prvCheckValidSessionAndModule for this exception. */
            /* coverity[misra_c_2012_rule_10_5_violation] */
            if( xBool != ( CK_BBOOL ) CK_TRUE )
            {
                PKCS11_PRINT( ( "ERROR: Only token key generation is supported. \r\n" ) );
                xResult = CKR_ATTRIBUTE_VALUE_INVALID;
            }
            break;

        default:
            xResult = CKR_TEMPLATE_INCONSISTENT;
            break;
    }

    return xResult;
}


/**
 * @brief Generates a public-key/private-key pair.
 *
 * This port only supports generating elliptic curve P-256
 * key pairs.
 *
 * @param[in] hSession                      Handle of a valid PKCS #11 session.
 * @param[in] pMechanism                    Pointer to a mechanism. At this time,
 *                                          CKM_EC_KEY_PAIR_GEN is the only supported mechanism.
 * @param[in] pPublicKeyTemplate           Pointer to a list of attributes that the generated
 *                                          public key should possess.
 *                                          Public key template must have the following attributes:
 *                                          - CKA_LABEL
 *                                              - Label should be no longer than pkcs11configMAX_LABEL_LENGTH
 *                                              and must be supported by port's PKCS #11 PAL.
 *                                          - CKA_EC_PARAMS
 *                                              - Must equal pkcs11DER_ENCODED_OID_P256.
 *                                              Only P-256 keys are supported.
 *                                          - CKA_VERIFY
 *                                              - Must be set to true.  Only public keys used
 *                                              for verification are supported.
 *                                          Public key templates may have the following attributes:
 *                                          - CKA_KEY_TYPE
 *                                              - Must be set to CKK_EC. Only elliptic curve key
 *                                              generation is supported.
 *                                          - CKA_TOKEN
 *                                              - Must be set to CK_TRUE.
 * @param[in] ulPublicKeyAttributeCount     Number of attributes in pPublicKeyTemplate.
 * @param[in] pPrivateKeyTemplate          Pointer to a list of attributes that the generated
 *                                          private key should possess.
 *                                          Private key template must have the following attributes:
 *                                          - CKA_LABEL
 *                                              - Label should be no longer than pkcs11configMAX_LABEL_LENGTH
 *                                              and must be supported by port's PKCS #11 PAL.
 *                                          - CKA_PRIVATE
 *                                              - Must be set to true.
 *                                          - CKA_SIGN
 *                                              - Must be set to true.  Only private keys used
 *                                              for signing are supported.
 *                                          Private key template may have the following attributes:
 *                                          - CKA_KEY_TYPE
 *                                              - Must be set to CKK_EC. Only elliptic curve key
 *                                              generation is supported.
 *                                          - CKA_TOKEN
 *                                              - Must be set to CK_TRUE.
 *
 * @param[in] ulPrivateKeyAttributeCount    Number of attributes in pPrivateKeyTemplate.
 * @param[out] phPublicKey                  Pointer to the handle of the public key to be created.
 * @param[out] phPrivateKey                 Pointer to the handle of the private key to be created.
 *
 * \note Not all attributes specified by the PKCS #11 standard are supported.
 * \note CKA_LOCAL attribute is not supported.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_generatekeypair] */
CK_DECLARE_FUNCTION( CK_RV, C_GenerateKeyPair )( CK_SESSION_HANDLE hSession,
                                                 CK_MECHANISM_PTR pMechanism,
                                                 CK_ATTRIBUTE_PTR pPublicKeyTemplate,
                                                 CK_ULONG ulPublicKeyAttributeCount,
                                                 CK_ATTRIBUTE_PTR pPrivateKeyTemplate,
                                                 CK_ULONG ulPrivateKeyAttributeCount,
                                                 CK_OBJECT_HANDLE_PTR phPublicKey,
                                                 CK_OBJECT_HANDLE_PTR phPrivateKey )
{
    uint8_t * pucDerFile = pvPortMalloc( pkcs11KEY_GEN_MAX_DER_SIZE );
    int32_t lMbedResult = 0;
    uint32_t ulIndex = 0;
    mbedtls_pk_context xCtx = { 0 };
    CK_ATTRIBUTE_PTR pxPrivateLabel = NULL;
    CK_ATTRIBUTE_PTR pxPublicLabel = NULL;
    CK_OBJECT_HANDLE xPalPublic = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xPalPrivate = CK_INVALID_HANDLE;
    uint32_t xPublicRequiredAttributeMap = ( LABEL_IN_TEMPLATE | EC_PARAMS_IN_TEMPLATE | VERIFY_IN_TEMPLATE );
    uint32_t xPrivateRequiredAttributeMap = ( LABEL_IN_TEMPLATE | PRIVATE_IN_TEMPLATE | SIGN_IN_TEMPLATE );
    uint32_t xAttributeMap = 0;

    const P11Session_t * pxSession = prvSessionPointerFromHandle( hSession );
    CK_RV xResult = prvCheckValidSessionAndModule( pxSession );

    #if ( pkcs11configSUPPRESS_ECDSA_MECHANISM == 1 )
        if( xResult == CKR_OK )
        {
            xResult = CKR_MECHANISM_INVALID;
        }
    #endif

    if( xResult == CKR_OK )
    {
        if( ( pPublicKeyTemplate == NULL ) ||
            ( pPrivateKeyTemplate == NULL ) ||
            ( phPublicKey == NULL ) ||
            ( phPrivateKey == NULL ) ||
            ( pMechanism == NULL ) )
        {
            xResult = CKR_ARGUMENTS_BAD;
        }
    }

    if( xResult == CKR_OK )
    {
        if( pucDerFile == NULL )
        {
            xResult = CKR_HOST_MEMORY;
        }
    }

    if( xResult == CKR_OK )
    {
        if( CKM_EC_KEY_PAIR_GEN != pMechanism->mechanism )
        {
            xResult = CKR_MECHANISM_INVALID;
        }
    }

    if( xResult == CKR_OK )
    {
        for( ulIndex = 0; ulIndex < ulPrivateKeyAttributeCount; ++ulIndex )
        {
            xResult = prvCheckGenerateKeyPairPrivateTemplate( &pxPrivateLabel,
                                                              &pPrivateKeyTemplate[ ulIndex ],
                                                              &xAttributeMap );

            if( xResult != CKR_OK )
            {
                break;
            }
        }

        if( ( xResult == CKR_OK ) && ( ( xAttributeMap & xPrivateRequiredAttributeMap ) != xPrivateRequiredAttributeMap ) )
        {
            xResult = CKR_TEMPLATE_INCOMPLETE;
        }
    }

    if( xResult == CKR_OK )
    {
        xAttributeMap = 0;

        for( ulIndex = 0; ulIndex < ulPublicKeyAttributeCount; ++ulIndex )
        {
            xResult = prvCheckGenerateKeyPairPublicTemplate( &pxPublicLabel,
                                                             &pPublicKeyTemplate[ ulIndex ],
                                                             &xAttributeMap );

            if( xResult != CKR_OK )
            {
                break;
            }
        }

        if( ( xResult == CKR_OK ) && ( ( xAttributeMap & xPublicRequiredAttributeMap ) != xPublicRequiredAttributeMap ) )
        {
            xResult = CKR_TEMPLATE_INCOMPLETE;
        }
    }

    if( xResult == CKR_OK )
    {
        mbedtls_pk_init( &xCtx );
        lMbedResult = mbedtls_pk_setup( &xCtx, mbedtls_pk_info_from_type( MBEDTLS_PK_ECKEY ) );
    }

    if( lMbedResult != 0 )
    {
        xResult = CKR_FUNCTION_FAILED;
    }

    if( xResult == CKR_OK )
    {
        if( 0 != mbedtls_ecp_gen_key( MBEDTLS_ECP_DP_SECP256R1,
                                      mbedtls_pk_ec( xCtx ),
                                      mbedtls_ctr_drbg_random,
                                      &xP11Context.xMbedDrbgCtx ) )
        {
            xResult = CKR_FUNCTION_FAILED;
        }
    }

    if( xResult == CKR_OK )
    {
        lMbedResult = mbedtls_pk_write_pubkey_der( &xCtx, pucDerFile, pkcs11KEY_GEN_MAX_DER_SIZE );

        if( lMbedResult > 0 )
        {
            xPalPublic = PKCS11_PAL_SaveObject( pxPublicLabel, pucDerFile + pkcs11KEY_GEN_MAX_DER_SIZE - lMbedResult, ( uint32_t ) lMbedResult );
        }
        else
        {
            xResult = CKR_GENERAL_ERROR;
        }
    }

    if( xResult == CKR_OK )
    {
        lMbedResult = mbedtls_pk_write_key_der( &xCtx, pucDerFile, pkcs11KEY_GEN_MAX_DER_SIZE );

        if( lMbedResult > 0 )
        {
            xPalPrivate = PKCS11_PAL_SaveObject( pxPrivateLabel, pucDerFile + pkcs11KEY_GEN_MAX_DER_SIZE - lMbedResult, ( uint32_t ) lMbedResult );
        }
        else
        {
            xResult = CKR_GENERAL_ERROR;
        }
    }

    if( ( xPalPublic != CK_INVALID_HANDLE ) && ( xPalPrivate != CK_INVALID_HANDLE ) )
    {
        xResult = prvAddObjectToList( xPalPrivate, phPrivateKey, pxPrivateLabel->pValue, pxPrivateLabel->ulValueLen );

        if( xResult == CKR_OK )
        {
            xResult = prvAddObjectToList( xPalPublic, phPublicKey, pxPublicLabel->pValue, pxPublicLabel->ulValueLen );

            if( xResult != CKR_OK )
            {
                ( void ) PKCS11_PAL_DestroyObject( *phPrivateKey );
            }
        }
    }

    /* Clean up. */
    vPortFree( pucDerFile );
    mbedtls_pk_free( &xCtx );

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_generatekeypair] */

/**
 * @brief Generates random data.
 *
 * @param[in] hSession          Handle of a valid PKCS #11 session.
 * @param[out] RandomData       Pointer to location that random data will be placed.
 *                              It is the responsiblity of the application to allocate
 *                              this memory.
 * @param[in] ulRandomLen       Length of data (in bytes) to be generated.
 *
 * @return CKR_OK if successful.
 * Else, see <a href="https://tiny.amazon.com/wtscrttv">PKCS #11 specification</a>
 * for more information.
 */
/* @[declare_pkcs11_mbedtls_c_generate_random] */
CK_DECLARE_FUNCTION( CK_RV, C_GenerateRandom )( CK_SESSION_HANDLE hSession,
                                                CK_BYTE_PTR RandomData,
                                                CK_ULONG ulRandomLen )
{
    CK_RV xResult = CKR_OK;
    int32_t lMbedResult = 0;

    const P11Session_t * pxSession = prvSessionPointerFromHandle( hSession );

    xResult = prvCheckValidSessionAndModule( pxSession );

    if( ( NULL == RandomData ) ||
        ( ulRandomLen == 0UL ) )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    if( xResult == CKR_OK )
    {
        lMbedResult = mbedtls_ctr_drbg_random( &xP11Context.xMbedDrbgCtx, RandomData, ulRandomLen );

        if( lMbedResult != 0 )
        {
            PKCS11_PRINT( ( "ERROR: DRBG failed %d \r\n", lMbedResult ) );
            xResult = CKR_FUNCTION_FAILED;
        }
    }

    return xResult;
}
/* @[declare_pkcs11_mbedtls_c_generate_random] */
