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

#ifndef MBEDTLS_PKCS11_H
#define MBEDTLS_PKCS11_H

#include <string.h>
#include "mbedtls/pk.h"
#include "core_pkcs11_config.h"
#include "core_pkcs11.h"

/*-----------------------------------------------------------*/

/**
 * @brief Initialize an mbedtls_pk_context for the given PKCS11 object handle.
 *
 * @param pxMbedtlsPkCtx Pointer to an MbedTLS PK context to initialize.
 * @param xSessionHandle Handle of an initialize PKCS#11 session.
 * @param xPkHandle Handle of a PKCS11 Private Key object.
 * @return CK_RV CKR_OK on success.
 */
CK_RV xPKCS11_initMbedtlsPkContext( mbedtls_pk_context * pxMbedtlsPkCtx,
                                    CK_SESSION_HANDLE xSessionHandle,
                                    CK_OBJECT_HANDLE xPkHandle );

/**
 * @brief Callback to generate random data with the PKCS11 API.
 *
 * @param[in] pvCtx void pointer to a PKCS11 Session handle.
 * @param[in] pucRandom Byte array to fill with random data.
 * @param[in] xRandomLength Length of byte array.
 *
 * @return 0 on success.
 */
int lMbedCryptoRngCallbackPKCS11( void * pvCtx,
                                  unsigned char * pucOutput,
                                  size_t uxLen );

#endif /* MBEDTLS_PKCS11_H */
