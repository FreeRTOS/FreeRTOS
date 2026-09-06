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

#ifndef TEST_DEFAULT_SETTING_CONFIG_H
#define TEST_DEFAULT_SETTING_CONFIG_H

#ifndef testNOT_USING_UNITY
    #include "unity.h"
#endif

#ifndef testRUN_TEST_CASE_FUNCTION
    #define testRUN_TEST_CASE_FUNCTION    RUN_TEST
#endif

#ifndef testBEGIN_FUNCTION
    #define testBEGIN_FUNCTION    UNITY_BEGIN
#endif

#ifndef testEND_FUNCTION
    #define testEND_FUNCTION    UNITY_END
#endif

#ifndef testSETUP_FUNCTION_PROTOTYPE
    #define testSETUP_FUNCTION_PROTOTYPE( fxn )    void fxn( void )
#endif

#ifndef testTEARDOWN_FUNCTION_PROTOTYPE
    #define testTEARDOWN_FUNCTION_PROTOTYPE( fxn )    void fxn( void )
#endif

#ifndef testENTRY_FUNCTION_PROTOTYPE
    #define testENTRY_FUNCTION_PROTOTYPE( fxn )    void fxn( void )
#endif

#endif /* TEST_DEFAULT_SETTING_CONFIG_H */
