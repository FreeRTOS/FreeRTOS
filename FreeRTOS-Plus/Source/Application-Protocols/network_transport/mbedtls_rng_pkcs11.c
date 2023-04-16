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

#include "logging_levels.h"

#define LIBRARY_LOG_NAME     "MbedTLSRNGP11"
#define LIBRARY_LOG_LEVEL    LOG_ERROR

#include "logging_stack.h"

/**
 * @file mbedtls_rng_pkcs11.c
 * @brief Implements an mbedtls RNG callback using the PKCS#11 API
 */

#include "core_pkcs11_config.h"
#include "core_pkcs11.h"

/*-----------------------------------------------------------*/

int lMbedCryptoRngCallbackPKCS11( void * pvCtx,
                                  unsigned char * pucOutput,
                                  size_t uxLen )
{
    int lRslt;
    CK_FUNCTION_LIST_PTR pxFunctionList = NULL;
    CK_SESSION_HANDLE * pxSessionHandle = ( CK_SESSION_HANDLE * ) pvCtx;

    if( pucOutput == NULL )
    {
        lRslt = -1;
    }
    else if( pvCtx == NULL )
    {
        lRslt = -1;
        LogError( ( "pvCtx must not be NULL." ) );
    }
    else
    {
        lRslt = ( int ) C_GetFunctionList( &pxFunctionList );
    }

    if( ( lRslt != CKR_OK ) ||
        ( pxFunctionList == NULL ) ||
        ( pxFunctionList->C_GenerateRandom == NULL ) )
    {
        lRslt = -1;
    }
    else
    {
        lRslt = ( int ) pxFunctionList->C_GenerateRandom( *pxSessionHandle, pucOutput, uxLen );
    }

    return lRslt;
}

/*-----------------------------------------------------------*/
