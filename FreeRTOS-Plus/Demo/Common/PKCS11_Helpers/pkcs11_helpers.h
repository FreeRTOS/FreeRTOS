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

#ifndef PKCS11_HELPERS_H_
#define PKCS11_HELPERS_H_

/**
 * @file pkcs11_helpers.h
 * @brief Helper functions for accessing PKCS11 module functionality.
 */

/* FreeRTOS include. */
#include "FreeRTOS.h"

/*-----------------------------------------------------------*/

/**
 * @brief Utility function to generate a random number using the
 * PKCS11 module.
 *
 * This is a wrapper function for initiating a PKCS11 session,
 * calling the C_GenerateRandom API function to generate a random
 * number and closing the PKCS11 session.
 *
 * @param[in, out] pusRandomNumBuffer The buffer to store the generated random number.
 * @param[in] xBufferLength The size of the @p pusRandomNumBuffer buffer.
 *
 * @return pdPASS if random number generation was successful; otherwise
 * pdFAIL to indicate failure.
 */
BaseType_t xPkcs11GenerateRandomNumber( uint8_t * pusRandomNumBuffer,
                                        size_t xBufferLength );


#endif /* ifndef PKCS11_HELPERS_H_ */
