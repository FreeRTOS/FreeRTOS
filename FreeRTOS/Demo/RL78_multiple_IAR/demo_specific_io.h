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

#ifndef DEMO_SPECIFIC_IO_H
#define DEMO_SPECIFIC_IO_H

    #if !defined(__IASMRL78__) && !defined(__ICCRL78__)
         #error "The demo_specific_io.h header requires IAR Toolchain for RL78."
    #endif

    /* Include register definition header files that match the device in use.
    A symbol definition for the board must be set in in two different places:
    [C/C++ Compiler]/[Preprocessor] as well as in [Assembler]/[Preprocessor].
    NOTE: Use as reference for when adding other boards. */

    #ifdef YRPBRL78G13
        #include <ior5f100le.h>
        #include <ior5f100le_ext.h>
        #define LED_BIT                ( P7_bit.no7 )
        #define LED_INIT()             P7 &= 0x7F; PM7 &= 0x7F
    #endif /* YRPBRL78G13 */

    #ifdef YRPBRL78G14
        #include <ior5f104le.h>
        #include <ior5f104le_ext.h>
        #define LED_BIT                ( P7_bit.no7 )
        #define LED_INIT()             P7 &= 0x7F; PM7 &= 0x7F
    #endif /* YRPBRL78G14 */

    #ifdef YRDKRL78G14
        #include <ior5f104pj.h>
        #include <ior5f104pj_ext.h>
        #define LED_BIT                ( P4_bit.no1 )
        #define LED_INIT()             P4 &= 0xFD; PM4 &= 0xFD
    #endif /* YRDKRL78G14 */

    #ifdef RSKRL78G1C
        #include <ior5f10jgc.h>
        #include <ior5f10jgc_ext.h>
        #define LED_BIT                ( P0_bit.no1 )
        #define LED_INIT()             P0 &= 0xFD; PM0 &= 0xFD
    #endif /* RSKRL78G1C */

    #ifdef RSKRL78L1C
        #include <ior5f110pj.h>
        #include <ior5f110pj_ext.h>
        #define LED_BIT                ( P4_bit.no1 )
        #define LED_INIT()             P4 &= 0xFD; PM4 &= 0xFD
    #endif /* RSKRL78L1C */

    #ifdef RSKRL78L13
        #include <ior5f10wmg.h>
        #include <ior5f10wmg_ext.h>
        #define LED_BIT                ( P4_bit.no1 )
        #define LED_INIT()             P4 &= 0xFD; PM4 &= 0xFD
    #endif /* RSKRL78L13 */

    #ifdef QB_R5F10ELE_TB
        #include <ior5f10ele.h>
        #include <ior5f10ele_ext.h>
        #define LED_BIT                ( P6_bit.no2 )
        #define LED_INIT()             P6 &= 0xFB; PM6 &= 0xFB
    #endif /* QB_R5F10ELE_TB */

    #ifndef LED_BIT
        #error "The hardware platform is not defined."
    #endif

#endif /* DEMO_SPECIFIC_IO_H */
