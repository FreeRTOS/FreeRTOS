/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#ifndef _DEMO_HELPER_FUNCTIONS_
#define _DEMO_HELPER_FUNCTIONS_

#include "core_pkcs11.h"
#include "threading_alt.h"
#include "mbedtls/pk.h"

/* This function contains standard setup code for PKCS #11. See the
 * "management_and_rng.c" file for the demo code explaining this section
 * of cryptoki.
 */
void vStart( CK_SESSION_HANDLE * pxSession,
             CK_SLOT_ID ** ppxSlotId );
/*-----------------------------------------------------------*/

/* This function contains standard tear down code for PKCS #11. See the
 * "management_and_rng.c" file for the demo code explaining this section
 * of cryptoki.
 */
void vEnd( CK_SESSION_HANDLE xSession,
           CK_SLOT_ID * pxSlotId );
/*-----------------------------------------------------------*/

/* This function is simply a helper function to print the raw hex values
 * of an EC public key. It's explanation is not within the scope of the demos
 * and is sparsely commented. */
void vWriteHexBytesToConsole( char * pcDescription,
                              CK_BYTE * pucData,
                              CK_ULONG ulDataLength );
/*-----------------------------------------------------------*/

/* This function is simply a helper function to export the raw hex values
 * of an EC public key into a buffer. It's explanation is not within the
 * scope of the demos and is sparsely commented. */
CK_RV vExportPublicKey( CK_SESSION_HANDLE xSession,
                        CK_OBJECT_HANDLE xPublicKeyHandle,
                        CK_BYTE ** ppucDerPublicKey,
                        CK_ULONG * pulDerPublicKeyLength );
/*-----------------------------------------------------------*/

/**
 * @brief Implements libc calloc semantics using the FreeRTOS heap
 */
void * pvCalloc( size_t xNumElements,
                 size_t xSize );
/*-----------------------------------------------------------*/

/**
 * @brief Implementation of mbedtls_mutex_init for thread-safety.
 *
 */
void aws_mbedtls_mutex_init( mbedtls_threading_mutex_t * mutex );
/*-----------------------------------------------------------*/

/**
 * @brief Implementation of mbedtls_mutex_free for thread-safety.
 *
 */
void aws_mbedtls_mutex_free( mbedtls_threading_mutex_t * mutex );
/*-----------------------------------------------------------*/

/**
 * @brief Implementation of mbedtls_mutex_lock for thread-safety.
 *
 * @return 0 if successful, MBEDTLS_ERR_THREADING_MUTEX_ERROR if timeout,
 * MBEDTLS_ERR_THREADING_BAD_INPUT_DATA if the mutex is not valid.
 */
int aws_mbedtls_mutex_lock( mbedtls_threading_mutex_t * mutex );
/*-----------------------------------------------------------*/

/**
 * @brief Implementation of mbedtls_mutex_unlock for thread-safety.
 *
 * @return 0 if successful, MBEDTLS_ERR_THREADING_MUTEX_ERROR if timeout,
 * MBEDTLS_ERR_THREADING_BAD_INPUT_DATA if the mutex is not valid.
 */
int aws_mbedtls_mutex_unlock( mbedtls_threading_mutex_t * mutex );

#endif /* _DEMO_HELPER_FUNCTIONS_ */
