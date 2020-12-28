/*
 * FreeRTOS V202012.00
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

#ifndef _PKCS11_DEMOS_h_
#define _PKCS11_DEMOS_h_

/* Prototype for the PKCS #11 "Management" demo. This demo covers the various
 * functions used to manage the internal state of the PKCS #11 stack, and then
 * demonstrates how to generate random numbers using PKCS #11.
 */
void vPKCS11ManagementAndRNGDemo( void );

/* Prototype for the PKCS #11 "Digests" demo. This demo covers how to query
 * slots for supported capabilities, and creating a message digest if the
 * slot supports it.
 */
void vPKCS11MechanismsAndDigestDemo( void );

/* Prototype for the PKCS #11 "Object" demo. This demo covers objects and how
 * they are defined and used within PKCS #11.
 */
void vPKCS11ObjectDemo( void );

/* Prototype for the PKCS #11 "Sign and Verify" demo. This demo covers how 
 * PKCS #11 can be used to sign a message, and verify the integrity of a message
 * using private and public keys.
 *
 * This demo will also cover the "core_pkcs11.h" functions, and how they can be
 * used to make the PKCS #11 flow easier to use.
 *
 * Warning: This demo depends on the objects created in the objects demo.
 */
void vPKCS11SignVerifyDemo( void );

#endif /* _PKCS11_DEMOS_h_ */
