/*
 * FreeRTOS PKCS #11 V1.1.0
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
 *
 * This file contains wrapper functions for common PKCS #11 operations.
 */

/*-----------------------------------------------------------*/

/** @brief Open a PKCS #11 Session.
 *
 *  \param[out] pxSession   Pointer to the session handle to be created.
 *  \param[out] xSlotId     Slot ID to be used for the session.
 *
 *  \return CKR_OK or PKCS #11 error code. (PKCS #11 error codes are positive).
 */
static CK_RV prvOpenSession( CK_SESSION_HANDLE * pxSession,
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

CK_RV xGetSlotList( CK_SLOT_ID ** ppxSlotId,
                    CK_ULONG * pxSlotCount )
{
    CK_RV xResult = CKR_OK;
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

/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/

#ifdef CreateMutex
    #undef CreateMutex /* This is a workaround because CreateMutex is redefined to CreateMutexW in synchapi.h in windows. :/ */
#endif

/*-----------------------------------------------------------*/

CK_RV xInitializePKCS11( void )
{
    CK_RV xResult = CKR_OK;
    CK_FUNCTION_LIST_PTR pxFunctionList = NULL;
    CK_C_INITIALIZE_ARGS xInitArgs = { 0 };

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

/*-----------------------------------------------------------*/

CK_RV xInitializePkcs11Token( void )
{
    CK_RV xResult = CKR_OK;

    CK_FUNCTION_LIST_PTR pxFunctionList = NULL;
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

        if( ( CKR_OK == xResult ) && ( ( CKF_TOKEN_INITIALIZED & xTokenFlags ) != CKF_TOKEN_INITIALIZED ) )
        {
            /* Initialize the token if it is not already. */
            xResult = pxFunctionList->C_InitToken( pxSlotId[ 0 ],
                                                   ( CK_UTF8CHAR_PTR ) configPKCS11_DEFAULT_USER_PIN,
                                                   sizeof( configPKCS11_DEFAULT_USER_PIN ) - 1UL,
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

/*-----------------------------------------------------------*/

CK_RV xInitializePkcs11Session( CK_SESSION_HANDLE * pxSession )
{
    CK_RV xResult = CKR_OK;
    CK_SLOT_ID * pxSlotId = NULL;
    CK_FUNCTION_LIST_PTR pxFunctionList = NULL;
    CK_ULONG xSlotCount = 0;

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
                                           sizeof( configPKCS11_DEFAULT_USER_PIN ) - 1UL );
    }

    return xResult;
}
/*-----------------------------------------------------------*/

CK_RV xFindObjectWithLabelAndClass( CK_SESSION_HANDLE xSession,
                                    char * pcLabelName,
                                    CK_OBJECT_CLASS xClass,
                                    CK_OBJECT_HANDLE_PTR pxHandle )
{
    CK_RV xResult = CKR_OK;
    CK_ULONG ulCount = 0;
    CK_FUNCTION_LIST_PTR pxFunctionList = NULL;
    CK_ATTRIBUTE xTemplate[ 2 ] = { 0 };

    if( ( pcLabelName == NULL ) || ( pxHandle == NULL ) )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }
    else
    {
        xTemplate[ 0 ].type = CKA_LABEL;
        xTemplate[ 0 ].pValue = ( CK_VOID_PTR ) pcLabelName;
        xTemplate[ 0 ].ulValueLen = strlen( pcLabelName );

        xTemplate[ 1 ].type = CKA_CLASS;
        xTemplate[ 1 ].pValue = &xClass;
        xTemplate[ 1 ].ulValueLen = sizeof( CK_OBJECT_CLASS );

        xResult = C_GetFunctionList( &pxFunctionList );
    }

    /* Initialize the FindObject state in the underlying PKCS #11 module based
     * on the search template provided by the caller. */
    if( CKR_OK == xResult )
    {
        xResult = pxFunctionList->C_FindObjectsInit( xSession, xTemplate, sizeof( xTemplate ) / sizeof( CK_ATTRIBUTE ) );
    }

    if( CKR_OK == xResult )
    {
        /* Find the first matching object, if any. */
        xResult = pxFunctionList->C_FindObjects( xSession,
                                                 pxHandle,
                                                 1,
                                                 &ulCount );
    }

    if( CKR_OK == xResult )
    {
        xResult = pxFunctionList->C_FindObjectsFinal( xSession );
    }

    if( ( NULL != pxHandle ) && ( ulCount == 0UL ) )
    {
        *pxHandle = CK_INVALID_HANDLE;
    }

    return xResult;
}

/*-----------------------------------------------------------*/

CK_RV vAppendSHA256AlgorithmIdentifierSequence( const uint8_t * puc32ByteHashedMessage,
                                                uint8_t * puc51ByteHashOidBuffer )
{
    CK_RV xResult = CKR_OK;
    const uint8_t pucOidSequence[] = pkcs11STUFF_APPENDED_TO_RSA_SIG;

    if( ( puc32ByteHashedMessage == NULL ) || ( puc51ByteHashOidBuffer == NULL ) )
    {
        xResult = CKR_ARGUMENTS_BAD;
    }

    if( xResult == CKR_OK )
    {
        ( void ) memcpy( puc51ByteHashOidBuffer, pucOidSequence, sizeof( pucOidSequence ) );
        ( void ) memcpy( &puc51ByteHashOidBuffer[ sizeof( pucOidSequence ) ], puc32ByteHashedMessage, 32 );
    }

    return xResult;
}

/*-----------------------------------------------------------*/
