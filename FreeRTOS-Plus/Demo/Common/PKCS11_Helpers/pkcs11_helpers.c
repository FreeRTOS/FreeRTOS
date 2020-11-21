/*
 * FreeRTOS Kernel V10.3.0
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
 */

/**
 * @file pkcs11_helpers.c
 * @brief Implementation of the helper functions for accessing PKCS11 module functionality.
 */

/* Include PKCS11 headers. */
#include "core_pkcs11.h"
#include "pkcs11.h"

/* Include header. */
#include "pkcs11_helpers.h"

/*-----------------------------------------------------------*/

BaseType_t xPkcs11GenerateRandomNumber( uint8_t * pusRandomNumBuffer,
                                        size_t xBufferLength )
{
    BaseType_t xStatus = pdPASS;
    CK_RV xResult = CKR_OK;
    CK_FUNCTION_LIST_PTR pxFunctionList = NULL;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;

    if( ( pusRandomNumBuffer == NULL ) || ( xBufferLength == 0U ) )
    {
        xStatus = pdFAIL;
    }

    if( xStatus == pdPASS )
    {
        /* Get list of functions supported by the PKCS11 port. */
        xResult = C_GetFunctionList( &pxFunctionList );

        if( ( xResult != CKR_OK ) || ( pxFunctionList == NULL ) )
        {
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        /* Initialize PKCS11 module and create a new session. */
        xResult = xInitializePkcs11Session( &xSession );

        if( ( xResult != CKR_OK ) || ( xSession == CK_INVALID_HANDLE ) )
        {
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        if( pxFunctionList->C_GenerateRandom( xSession,
                                              pusRandomNumBuffer,
                                              xBufferLength ) != CKR_OK )
        {
            xStatus = pdFAIL;
        }
    }

    if( xStatus == pdPASS )
    {
        if( pxFunctionList->C_CloseSession( xSession ) != CKR_OK )
        {
            xStatus = pdFAIL;
        }
    }

    return xStatus;
}
