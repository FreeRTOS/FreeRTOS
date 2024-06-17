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

#ifndef _PKCS11_DEMO_CONFIG_
#define _PKCS11_DEMO_CONFIG_

/*
 * @brief this macro defines the stack size for the PKCS #11 demo task.
 */
#define configPKCS11_DEMO_STACK_SIZE                256

/*
 * @brief set this macro to "1" in order to run the PKCS #11 management and
 * random number generator demo.
 */
#define configPKCS11_MANAGEMENT_AND_RNG_DEMO        1

/*
 * @brief set this macro to "1" in order to run the PKCS #11 mechanisms and
 * digest demo.
 */
#define configPKCS11_MECHANISMS_AND_DIGESTS_DEMO    1

/*
 * @brief set this macro to "1" in order to run the PKCS #11 object demo.
 */
#define configPKCS11_OBJECT_DEMO                    1

/*
 * @brief set this macro to "1" in order to run the PKCS #11 sign and verify
 * demo.
 *
 * @warning This demo relies on the objects created in the object demo.
 */
#define configPKCS11_SIGN_AND_VERIFY_DEMO           1

#endif /* ifndef _PKCS11_DEMO_CONFIG_ */
