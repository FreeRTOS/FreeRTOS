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

#ifndef REG_TEST_ASM_H
#define REG_TEST_ASM_H

/**
 * @brief Functions that implement reg tests in assembly.
 *
 * These are called from the FreeRTOS tasks on the non-secure side.
 */
void vRegTest1Asm_NonSecure( void ) __attribute__( ( naked ) );
void vRegTest2Asm_NonSecure( void ) __attribute__( ( naked ) );
void vRegTest3Asm_NonSecure( void ) __attribute__( ( naked ) );
void vRegTest4Asm_NonSecure( void ) __attribute__( ( naked ) );

/**
 * @brief Function that implements reg tests in assembly.
 *
 * This is passed as function pointer to the secure side and called
 * from the secure side.
 */
void vRegTestAsm_NonSecureCallback( void );

#endif /* REG_TEST_ASM_H */
