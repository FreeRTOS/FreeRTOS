/*
 * FreeRTOS PKCS #11 V1.0.1
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

#include "iot_pkcs11_config.h"
#include "iot_pkcs11.h"
#include "FreeRTOS.h"

/* C runtime includes. */
#include <stdio.h>
#include <stdint.h>
#include <string.h>

/**
 * @file iot_pkcs11.c
 * @brief FreeRTOS PKCS #11 Interface.
 * The following definitions are required by the PKCS #11 standard public
 * headers.
 */

/*-----------------------------------------------------------*/

/* @[declare pkcs11_iot_xgetslotlist] */
CK_RV xGetSlotList( CK_SLOT_ID ** ppxSlotId,
                    CK_ULONG * pxSlotCount )
{
    CK_RV xResult;
    CK_FUNCTION_LIST_PTR pxFunctionList;
    CK_SLOT_ID * pxSlotId = NULL;

    xResult = C_GetFunctionList( &pxFunctionList );

    if( xResult == CKR_OK )
    {
        xResult = pxFunctionList->C_GetSlotList( CK_TRUE, /* Token Present. */
                                                 NULL,    /* We just want to know how many slots there are. */
                                                 pxSlotCount );
    }

    if( xResult == CKR_OK )
    {
        /* Allocate memory for the slot list. */
        pxSlotId = pvPortMalloc( sizeof( CK_SLOT_ID ) * ( *pxSlotCount ) );

        if( pxSlotId == NULL )
        {
            xResult = CKR_HOST_MEMORY;
        }
        else
        {
            *ppxSlotId = pxSlotId;
        }
    }

    if( xResult == CKR_OK )
    {
        xResult = pxFunctionList->C_GetSlotList( CK_TRUE, pxSlotId, pxSlotCount );
    }

    if( ( xResult != CKR_OK ) && ( pxSlotId != NULL ) )
    {
        vPortFree( pxSlotId );
    }

    return xResult;
}
/* @[declare pkcs11_iot_xgetslotlist] */

/*-----------------------------------------------------------*/

/* @brief Open a PKCS #11 Session.
 *
 *  \param[out] pxSession   Pointer to the session handle to be created.
 *  \param[out] xSlotId     Slot ID to be used for the session.
 *
 *  \return CKR_OK or PKCS #11 error code. (PKCS #11 error codes are positive).
 */
CK_RV prvOpenSession( CK_SESSION_HANDLE * pxSession,
                      CK_SLOT_ID xSlotId )
{
    CK_RV xResult;
    CK_FUNCTION_LIST_PTR pxFunctionList;

    xResult = C_GetFunctionList( &pxFunctionList );

    if( xResult == CKR_OK )
    {
        xResult = pxFunctionList->C_OpenSession( xSlotId,
                                                 CKF_SERIAL_SESSION | CKF_RW_SESSION,
                                                 NULL, /* Application defined pointer. */
                                                 NULL, /* Callback function. */
                                                 pxSession );
    }

    return xResult;
}

/*-----------------------------------------------------------*/

#ifdef CreateMutex
    #undef CreateMutex /* This is a workaround because CreateMutex is redefined to CreateMutexW in synchapi.h in windows. :/ */
#endif

/*-----------------------------------------------------------*/

/* @[declare pkcs11_iot_xinitializepkcs11] */
CK_RV xInitializePKCS11( void )
{
    CK_RV xResult;
    CK_FUNCTION_LIST_PTR pxFunctionList;
    CK_C_INITIALIZE_ARGS xInitArgs;

    xInitArgs.CreateMutex = NULL;
    xInitArgs.DestroyMutex = NULL;
    xInitArgs.LockMutex = NULL;
    xInitArgs.UnlockMutex = NULL;
    xInitArgs.flags = CKF_OS_LOCKING_OK;
    xInitArgs.pReserved = NULL;

    xResult = C_GetFunctionList( &pxFunctionList );

    /* Initialize the PKCS #11 module. */
    if( xResult == CKR_OK )
    {
        xResult = pxFunctionList->C_Initialize( &xInitArgs );
    }

    return xResult;
}
/* @[declare pkcs11_iot_xinitializepkcs11] */

/*-----------------------------------------------------------*/

/* Perform common token initialization as per the PKCS #11 standard. For
 * compatibility reasons, this may include authentication with a static PIN. */
/* @[declare pkcs11_iot_xinitializepkcs11token] */
CK_RV xInitializePkcs11Token( void )
{
    CK_RV xResult;

    CK_FUNCTION_LIST_PTR pxFunctionList;
    CK_SLOT_ID * pxSlotId = NULL;
    CK_ULONG xSlotCount;
    CK_FLAGS xTokenFlags = 0;
    CK_TOKEN_INFO_PTR pxTokenInfo = NULL;

    xResult = C_GetFunctionList( &pxFunctionList );

    if( xResult == CKR_OK )
    {
        xResult = xInitializePKCS11();
    }

    if( ( xResult == CKR_OK ) || ( xResult == CKR_CRYPTOKI_ALREADY_INITIALIZED ) )
    {
        xResult = xGetSlotList( &pxSlotId, &xSlotCount );
    }

    if( ( xResult == CKR_OK ) &&
        ( NULL != pxFunctionList->C_GetTokenInfo ) &&
        ( NULL != pxFunctionList->C_InitToken ) )
    {
        /* Check if the token requires further initialization. */
        pxTokenInfo = pvPortMalloc( sizeof( CK_TOKEN_INFO ) );

        if( pxTokenInfo != NULL )
        {
            /* We will take the first slot available. If your application
             * has multiple slots, insert logic for selecting an appropriate
             * slot here.
             */
            xResult = pxFunctionList->C_GetTokenInfo( pxSlotId[ 0 ], pxTokenInfo );
        }
        else
        {
            xResult = CKR_HOST_MEMORY;
        }

        if( CKR_OK == xResult )
        {
            xTokenFlags = pxTokenInfo->flags;
        }

        if( ( CKR_OK == xResult ) && !( CKF_TOKEN_INITIALIZED & xTokenFlags ) )
        {
            /* Initialize the token if it is not already. */
            xResult = pxFunctionList->C_InitToken( pxSlotId[ 0 ],
                                                   ( CK_UTF8CHAR_PTR ) configPKCS11_DEFAULT_USER_PIN,
                                                   sizeof( configPKCS11_DEFAULT_USER_PIN ) - 1,
                                                   ( CK_UTF8CHAR_PTR ) "FreeRTOS" );
        }
    }

    if( pxTokenInfo != NULL )
    {
        vPortFree( pxTokenInfo );
    }

    if( pxSlotId != NULL )
    {
        vPortFree( pxSlotId );
    }

    return xResult;
}
/* @[declare pkcs11_iot_xinitializepkcs11token] */

/*-----------------------------------------------------------*/

/* @[declare pkcs11_iot_xinitializepkcs11session] */
CK_RV xInitializePkcs11Session( CK_SESSION_HANDLE * pxSession )
{
    CK_RV xResult;
    CK_SLOT_ID * pxSlotId = NULL;
    CK_FUNCTION_LIST_PTR pxFunctionList;
    CK_ULONG xSlotCount;

    xResult = C_GetFunctionList( &pxFunctionList );

    if( pxSession == NULL )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    /* Initialize the module. */
    if( xResult == CKR_OK )
    {
        xResult = xInitializePKCS11();

        if( xResult == CKR_CRYPTOKI_ALREADY_INITIALIZED )
        {
            xResult = CKR_OK;
        }
    }

    /* Get a list of slots available. */
    if( xResult == CKR_OK )
    {
        xResult = xGetSlotList( &pxSlotId, &xSlotCount );
    }

    /* Open a PKCS #11 session. */
    if( xResult == CKR_OK )
    {
        /* We will take the first slot available.
         * If your application has multiple slots, insert logic
         * for selecting an appropriate slot here.
         */
        xResult = prvOpenSession( pxSession, pxSlotId[ 0 ] );

        /* Free the memory allocated by xGetSlotList. */
        vPortFree( pxSlotId );
    }

    if( ( xResult == CKR_OK ) && ( pxFunctionList->C_Login != NULL ) )
    {
        xResult = pxFunctionList->C_Login( *pxSession,
                                           CKU_USER,
                                           ( CK_UTF8CHAR_PTR ) configPKCS11_DEFAULT_USER_PIN,
                                           sizeof( configPKCS11_DEFAULT_USER_PIN ) - 1 );
    }

    return xResult;
}
/* @[declare pkcs11_iot_xinitializepkcs11session] */

/* Note: This is not a threadsafe initialization.
 * The first time xGetRandomNumber is invoked should not be from multiple threads. */
/* @[declare pkcs11_iot_xinitializepkcs11session] */
CK_RV prvGetRandomnessSession( CK_SESSION_HANDLE_PTR pxSession )
{
    static CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_RV xResult = CKR_OK;

    if( xSession == CK_INVALID_HANDLE )
    {
        xResult = xInitializePkcs11Session( &xSession );
    }

    *pxSession = xSession;
    return xResult;
}

CK_RV xGetRandomNumber( uint8_t * pRandomNumber,
                        size_t xNumBytes )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession;
    CK_FUNCTION_LIST_PTR pxFunctionList;

    if( ( pRandomNumber == NULL ) || ( xNumBytes == 0 ) )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    if( xResult == CKR_OK )
    {
        xResult = C_GetFunctionList( &pxFunctionList );
    }

    if( xResult == CKR_OK )
    {
        xResult = prvGetRandomnessSession( &xSession );
    }

    if( xResult == CKR_OK )
    {
        xResult = pxFunctionList->C_GenerateRandom( xSession, pRandomNumber, xNumBytes );
    }

    return xResult;
}

/*-----------------------------------------------------------*/

/* @brief Finds an object with a given label if it exists.
 *
 *   This function wraps C_FindObjectsInit, C_FindObjects, and C_FindObjectsFinal.
 *
 *   \param[in] xSession         A valid PKCS #11 session.
 *   \param[in] pcLabelName      The label of the object to be found.
 *   \param[out] pxHandle        Pointer to the handle of the found object,
 *                               or 0 if no object is found.
 *   \return CKR_OK if PKCS #11 calls were successful.  PKCS #11
 *   error code if not.
 *
 *   \note This function returns CKR_OK even if an object with the given
 *   CKA_LABEL is not found.  It is critical that functions verify that
 *   the object handle value is not equal to 0 (the invalid handle)
 *   before attempting to use the handle.
 */
/* @[declare pkcs11_iot_xfindobjectwithlabelandclass] */
CK_RV xFindObjectWithLabelAndClass( CK_SESSION_HANDLE xSession,
                                    const char * pcLabelName,
                                    CK_OBJECT_CLASS xClass,
                                    CK_OBJECT_HANDLE_PTR pxHandle )
{
    CK_RV xResult = CKR_OK;
    CK_ULONG ulCount = 0;
    CK_BBOOL xFindInit = CK_FALSE;
    CK_FUNCTION_LIST_PTR pxFunctionList;
    CK_ATTRIBUTE xTemplate[ 2 ] =
    {
        { CKA_LABEL, ( char * ) pcLabelName, strlen( pcLabelName )     },
        { CKA_CLASS, &xClass,                sizeof( CK_OBJECT_CLASS ) }
    };

    xResult = C_GetFunctionList( &pxFunctionList );

    if( ( pcLabelName == NULL ) || ( pxHandle == NULL ) )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    /* Get the certificate handle. */
    if( CKR_OK == xResult )
    {
        xResult = pxFunctionList->C_FindObjectsInit( xSession, xTemplate, sizeof( xTemplate ) / sizeof( CK_ATTRIBUTE ) );
    }

    if( CKR_OK == xResult )
    {
        xFindInit = CK_TRUE;
        xResult = pxFunctionList->C_FindObjects( xSession,
                                                 pxHandle,
                                                 1,
                                                 &ulCount );
    }

    if( ( CKR_OK == xResult ) && ( CK_TRUE == xFindInit ) )
    {
        xResult = pxFunctionList->C_FindObjectsFinal( xSession );
    }

    if( ( CKR_OK == xResult ) && ( ulCount == 0 ) )
    {
        *pxHandle = CK_INVALID_HANDLE;
    }

    return xResult;
}
/* @[declare pkcs11_iot_xfindobjectwithlabelandclass] */

/*-----------------------------------------------------------*/

/* @[declare pkcs11_iot_vappendsha256algorithmidentifiersequence] */
CK_RV vAppendSHA256AlgorithmIdentifierSequence( uint8_t * x32ByteHashedMessage,
                                                uint8_t * x51ByteHashOidBuffer )
{
    CK_RV xResult = CKR_OK;
    uint8_t xOidSequence[] = pkcs11STUFF_APPENDED_TO_RSA_SIG;

    if( ( x32ByteHashedMessage == NULL ) || ( x51ByteHashOidBuffer == NULL ) )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    if( xResult == CKR_OK )
    {
        memcpy( x51ByteHashOidBuffer, xOidSequence, sizeof( xOidSequence ) );
        memcpy( &x51ByteHashOidBuffer[ sizeof( xOidSequence ) ], x32ByteHashedMessage, 32 );
    }

    return xResult;
}
/* @[declare pkcs11_iot_vappendsha256algorithmidentifiersequence] */

/*-----------------------------------------------------------*/
