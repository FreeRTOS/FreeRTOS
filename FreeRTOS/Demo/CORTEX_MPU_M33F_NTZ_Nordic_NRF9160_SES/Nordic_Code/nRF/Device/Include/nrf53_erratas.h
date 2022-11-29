#ifndef NRF53_ERRATAS_H
#define NRF53_ERRATAS_H

/*

Copyright (c) 2010 - 2021, Nordic Semiconductor ASA All rights reserved.

SPDX-License-Identifier: BSD-3-Clause

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this
   list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.

3. Neither the name of Nordic Semiconductor ASA nor the names of its
   contributors may be used to endorse or promote products derived from this
   software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY, AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL NORDIC SEMICONDUCTOR ASA OR CONTRIBUTORS BE
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.

*/

#include <stdint.h>
#include <stdbool.h>
#include "compiler_abstraction.h"

static bool nrf53_errata_1(void) __UNUSED;
static bool nrf53_errata_2(void) __UNUSED;
static bool nrf53_errata_3(void) __UNUSED;
static bool nrf53_errata_4(void) __UNUSED;
static bool nrf53_errata_5(void) __UNUSED;
static bool nrf53_errata_6(void) __UNUSED;
static bool nrf53_errata_7(void) __UNUSED;
static bool nrf53_errata_8(void) __UNUSED;
static bool nrf53_errata_9(void) __UNUSED;
static bool nrf53_errata_10(void) __UNUSED;
static bool nrf53_errata_11(void) __UNUSED;
static bool nrf53_errata_12(void) __UNUSED;
static bool nrf53_errata_13(void) __UNUSED;
static bool nrf53_errata_14(void) __UNUSED;
static bool nrf53_errata_15(void) __UNUSED;
static bool nrf53_errata_16(void) __UNUSED;
static bool nrf53_errata_18(void) __UNUSED;
static bool nrf53_errata_19(void) __UNUSED;
static bool nrf53_errata_20(void) __UNUSED;
static bool nrf53_errata_21(void) __UNUSED;
static bool nrf53_errata_22(void) __UNUSED;
static bool nrf53_errata_23(void) __UNUSED;
static bool nrf53_errata_26(void) __UNUSED;
static bool nrf53_errata_27(void) __UNUSED;
static bool nrf53_errata_28(void) __UNUSED;
static bool nrf53_errata_29(void) __UNUSED;
static bool nrf53_errata_30(void) __UNUSED;
static bool nrf53_errata_31(void) __UNUSED;
static bool nrf53_errata_32(void) __UNUSED;
static bool nrf53_errata_33(void) __UNUSED;
static bool nrf53_errata_34(void) __UNUSED;
static bool nrf53_errata_36(void) __UNUSED;
static bool nrf53_errata_37(void) __UNUSED;
static bool nrf53_errata_42(void) __UNUSED;
static bool nrf53_errata_43(void) __UNUSED;
static bool nrf53_errata_44(void) __UNUSED;
static bool nrf53_errata_45(void) __UNUSED;
static bool nrf53_errata_46(void) __UNUSED;
static bool nrf53_errata_47(void) __UNUSED;
static bool nrf53_errata_49(void) __UNUSED;
static bool nrf53_errata_50(void) __UNUSED;
static bool nrf53_errata_51(void) __UNUSED;
static bool nrf53_errata_52(void) __UNUSED;
static bool nrf53_errata_53(void) __UNUSED;
static bool nrf53_errata_54(void) __UNUSED;
static bool nrf53_errata_55(void) __UNUSED;
static bool nrf53_errata_57(void) __UNUSED;
static bool nrf53_errata_58(void) __UNUSED;
static bool nrf53_errata_59(void) __UNUSED;
static bool nrf53_errata_62(void) __UNUSED;
static bool nrf53_errata_64(void) __UNUSED;
static bool nrf53_errata_65(void) __UNUSED;
static bool nrf53_errata_66(void) __UNUSED;
static bool nrf53_errata_67(void) __UNUSED;
static bool nrf53_errata_69(void) __UNUSED;
static bool nrf53_errata_70(void) __UNUSED;
static bool nrf53_errata_71(void) __UNUSED;
static bool nrf53_errata_72(void) __UNUSED;
static bool nrf53_errata_73(void) __UNUSED;
static bool nrf53_errata_74(void) __UNUSED;
static bool nrf53_errata_75(void) __UNUSED;
static bool nrf53_errata_76(void) __UNUSED;
static bool nrf53_errata_77(void) __UNUSED;
static bool nrf53_errata_79(void) __UNUSED;
static bool nrf53_errata_80(void) __UNUSED;
static bool nrf53_errata_81(void) __UNUSED;
static bool nrf53_errata_82(void) __UNUSED;
static bool nrf53_errata_83(void) __UNUSED;
static bool nrf53_errata_84(void) __UNUSED;
static bool nrf53_errata_85(void) __UNUSED;
static bool nrf53_errata_86(void) __UNUSED;
static bool nrf53_errata_87(void) __UNUSED;
static bool nrf53_errata_90(void) __UNUSED;
static bool nrf53_errata_91(void) __UNUSED;
static bool nrf53_errata_93(void) __UNUSED;
static bool nrf53_errata_95(void) __UNUSED;
static bool nrf53_errata_97(void) __UNUSED;
static bool nrf53_errata_99(void) __UNUSED;
static bool nrf53_errata_103(void) __UNUSED;
static bool nrf53_errata_105(void) __UNUSED;
static bool nrf53_errata_106(void) __UNUSED;
static bool nrf53_errata_107(void) __UNUSED;
static bool nrf53_errata_109(void) __UNUSED;
static bool nrf53_errata_110(void) __UNUSED;
static bool nrf53_errata_112(void) __UNUSED;
static bool nrf53_errata_113(void) __UNUSED;
static bool nrf53_errata_114(void) __UNUSED;
static bool nrf53_errata_115(void) __UNUSED;
static bool nrf53_errata_116(void) __UNUSED;
static bool nrf53_errata_117(void) __UNUSED;
static bool nrf53_errata_119(void) __UNUSED;
static bool nrf53_errata_121(void) __UNUSED;
static bool nrf53_errata_122(void) __UNUSED;
static bool nrf53_errata_134(void) __UNUSED;
static bool nrf53_errata_138(void) __UNUSED;

/* ========= Errata 1 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_1_PRESENT 1
    #else
        #define NRF53_ERRATA_1_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_1_PRESENT 0
#endif

#ifndef NRF53_ERRATA_1_ENABLE_WORKAROUND
    #define NRF53_ERRATA_1_ENABLE_WORKAROUND NRF53_ERRATA_1_PRESENT
#endif

static bool nrf53_errata_1(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 2 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_2_PRESENT 1
    #else
        #define NRF53_ERRATA_2_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_2_PRESENT 0
#endif

#ifndef NRF53_ERRATA_2_ENABLE_WORKAROUND
    #define NRF53_ERRATA_2_ENABLE_WORKAROUND NRF53_ERRATA_2_PRESENT
#endif

static bool nrf53_errata_2(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 3 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_3_PRESENT 1
    #else
        #define NRF53_ERRATA_3_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_3_PRESENT 0
#endif

#ifndef NRF53_ERRATA_3_ENABLE_WORKAROUND
    #define NRF53_ERRATA_3_ENABLE_WORKAROUND NRF53_ERRATA_3_PRESENT
#endif

static bool nrf53_errata_3(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 4 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_4_PRESENT 1
    #else
        #define NRF53_ERRATA_4_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_4_PRESENT 0
#endif

#ifndef NRF53_ERRATA_4_ENABLE_WORKAROUND
    #define NRF53_ERRATA_4_ENABLE_WORKAROUND NRF53_ERRATA_4_PRESENT
#endif

static bool nrf53_errata_4(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 5 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_5_PRESENT 1
    #else
        #define NRF53_ERRATA_5_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_5_PRESENT 0
#endif

#ifndef NRF53_ERRATA_5_ENABLE_WORKAROUND
    #define NRF53_ERRATA_5_ENABLE_WORKAROUND NRF53_ERRATA_5_PRESENT
#endif

static bool nrf53_errata_5(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 6 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_6_PRESENT 1
    #else
        #define NRF53_ERRATA_6_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_6_PRESENT 0
#endif

#ifndef NRF53_ERRATA_6_ENABLE_WORKAROUND
    #define NRF53_ERRATA_6_ENABLE_WORKAROUND NRF53_ERRATA_6_PRESENT
#endif

static bool nrf53_errata_6(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 7 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_7_PRESENT 1
    #else
        #define NRF53_ERRATA_7_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_7_PRESENT 0
#endif

#ifndef NRF53_ERRATA_7_ENABLE_WORKAROUND
    #define NRF53_ERRATA_7_ENABLE_WORKAROUND NRF53_ERRATA_7_PRESENT
#endif

static bool nrf53_errata_7(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 8 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_8_PRESENT 1
    #else
        #define NRF53_ERRATA_8_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_8_PRESENT 0
#endif

#ifndef NRF53_ERRATA_8_ENABLE_WORKAROUND
    #define NRF53_ERRATA_8_ENABLE_WORKAROUND NRF53_ERRATA_8_PRESENT
#endif

static bool nrf53_errata_8(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 9 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_9_PRESENT 1
    #else
        #define NRF53_ERRATA_9_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_9_PRESENT 0
#endif

#ifndef NRF53_ERRATA_9_ENABLE_WORKAROUND
    #define NRF53_ERRATA_9_ENABLE_WORKAROUND NRF53_ERRATA_9_PRESENT
#endif

static bool nrf53_errata_9(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 10 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_10_PRESENT 1
    #else
        #define NRF53_ERRATA_10_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_10_PRESENT 0
#endif

#ifndef NRF53_ERRATA_10_ENABLE_WORKAROUND
    #define NRF53_ERRATA_10_ENABLE_WORKAROUND NRF53_ERRATA_10_PRESENT
#endif

static bool nrf53_errata_10(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 11 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_11_PRESENT 1
    #else
        #define NRF53_ERRATA_11_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_11_PRESENT 0
#endif

#ifndef NRF53_ERRATA_11_ENABLE_WORKAROUND
    #define NRF53_ERRATA_11_ENABLE_WORKAROUND NRF53_ERRATA_11_PRESENT
#endif

static bool nrf53_errata_11(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 12 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_12_PRESENT 1
    #else
        #define NRF53_ERRATA_12_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_12_PRESENT 0
#endif

#ifndef NRF53_ERRATA_12_ENABLE_WORKAROUND
    #define NRF53_ERRATA_12_ENABLE_WORKAROUND NRF53_ERRATA_12_PRESENT
#endif

static bool nrf53_errata_12(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 13 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_13_PRESENT 1
    #else
        #define NRF53_ERRATA_13_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_13_PRESENT 0
#endif

#ifndef NRF53_ERRATA_13_ENABLE_WORKAROUND
    #define NRF53_ERRATA_13_ENABLE_WORKAROUND NRF53_ERRATA_13_PRESENT
#endif

static bool nrf53_errata_13(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 14 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_14_PRESENT 1
    #else
        #define NRF53_ERRATA_14_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_14_PRESENT 0
#endif

#ifndef NRF53_ERRATA_14_ENABLE_WORKAROUND
    #define NRF53_ERRATA_14_ENABLE_WORKAROUND NRF53_ERRATA_14_PRESENT
#endif

static bool nrf53_errata_14(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 15 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_15_PRESENT 1
    #else
        #define NRF53_ERRATA_15_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_15_PRESENT 0
#endif

#ifndef NRF53_ERRATA_15_ENABLE_WORKAROUND
    #define NRF53_ERRATA_15_ENABLE_WORKAROUND NRF53_ERRATA_15_PRESENT
#endif

static bool nrf53_errata_15(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 16 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_16_PRESENT 1
    #else
        #define NRF53_ERRATA_16_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_16_PRESENT 0
#endif

#ifndef NRF53_ERRATA_16_ENABLE_WORKAROUND
    #define NRF53_ERRATA_16_ENABLE_WORKAROUND NRF53_ERRATA_16_PRESENT
#endif

static bool nrf53_errata_16(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 18 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_18_PRESENT 1
    #else
        #define NRF53_ERRATA_18_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_18_PRESENT 0
#endif

#ifndef NRF53_ERRATA_18_ENABLE_WORKAROUND
    #define NRF53_ERRATA_18_ENABLE_WORKAROUND NRF53_ERRATA_18_PRESENT
#endif

static bool nrf53_errata_18(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 19 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_19_PRESENT 1
    #else
        #define NRF53_ERRATA_19_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_19_PRESENT 0
#endif

#ifndef NRF53_ERRATA_19_ENABLE_WORKAROUND
    #define NRF53_ERRATA_19_ENABLE_WORKAROUND NRF53_ERRATA_19_PRESENT
#endif

static bool nrf53_errata_19(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 20 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_20_PRESENT 1
    #else
        #define NRF53_ERRATA_20_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_20_PRESENT 0
#endif

#ifndef NRF53_ERRATA_20_ENABLE_WORKAROUND
    #define NRF53_ERRATA_20_ENABLE_WORKAROUND NRF53_ERRATA_20_PRESENT
#endif

static bool nrf53_errata_20(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 21 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_21_PRESENT 1
    #else
        #define NRF53_ERRATA_21_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_21_PRESENT 0
#endif

#ifndef NRF53_ERRATA_21_ENABLE_WORKAROUND
    #define NRF53_ERRATA_21_ENABLE_WORKAROUND NRF53_ERRATA_21_PRESENT
#endif

static bool nrf53_errata_21(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 22 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_22_PRESENT 1
    #else
        #define NRF53_ERRATA_22_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_22_PRESENT 0
#endif

#ifndef NRF53_ERRATA_22_ENABLE_WORKAROUND
    #define NRF53_ERRATA_22_ENABLE_WORKAROUND NRF53_ERRATA_22_PRESENT
#endif

static bool nrf53_errata_22(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 23 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_23_PRESENT 1
    #else
        #define NRF53_ERRATA_23_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_23_PRESENT 0
#endif

#ifndef NRF53_ERRATA_23_ENABLE_WORKAROUND
    #define NRF53_ERRATA_23_ENABLE_WORKAROUND NRF53_ERRATA_23_PRESENT
#endif

static bool nrf53_errata_23(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 26 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_26_PRESENT 1
    #else
        #define NRF53_ERRATA_26_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_26_PRESENT 0
#endif

#ifndef NRF53_ERRATA_26_ENABLE_WORKAROUND
    #define NRF53_ERRATA_26_ENABLE_WORKAROUND NRF53_ERRATA_26_PRESENT
#endif

static bool nrf53_errata_26(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 27 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_27_PRESENT 1
    #else
        #define NRF53_ERRATA_27_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_27_PRESENT 0
#endif

#ifndef NRF53_ERRATA_27_ENABLE_WORKAROUND
    #define NRF53_ERRATA_27_ENABLE_WORKAROUND NRF53_ERRATA_27_PRESENT
#endif

static bool nrf53_errata_27(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 28 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_28_PRESENT 1
    #else
        #define NRF53_ERRATA_28_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_28_PRESENT 0
#endif

#ifndef NRF53_ERRATA_28_ENABLE_WORKAROUND
    #define NRF53_ERRATA_28_ENABLE_WORKAROUND NRF53_ERRATA_28_PRESENT
#endif

static bool nrf53_errata_28(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 29 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_29_PRESENT 1
    #else
        #define NRF53_ERRATA_29_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_29_PRESENT 0
#endif

#ifndef NRF53_ERRATA_29_ENABLE_WORKAROUND
    #define NRF53_ERRATA_29_ENABLE_WORKAROUND NRF53_ERRATA_29_PRESENT
#endif

static bool nrf53_errata_29(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 30 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_30_PRESENT 1
    #else
        #define NRF53_ERRATA_30_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_30_PRESENT 0
#endif

#ifndef NRF53_ERRATA_30_ENABLE_WORKAROUND
    #define NRF53_ERRATA_30_ENABLE_WORKAROUND NRF53_ERRATA_30_PRESENT
#endif

static bool nrf53_errata_30(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 31 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_31_PRESENT 1
    #else
        #define NRF53_ERRATA_31_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_31_PRESENT 0
#endif

#ifndef NRF53_ERRATA_31_ENABLE_WORKAROUND
    #define NRF53_ERRATA_31_ENABLE_WORKAROUND NRF53_ERRATA_31_PRESENT
#endif

static bool nrf53_errata_31(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 32 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_32_PRESENT 1
    #else
        #define NRF53_ERRATA_32_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_32_PRESENT 0
#endif

#ifndef NRF53_ERRATA_32_ENABLE_WORKAROUND
    #define NRF53_ERRATA_32_ENABLE_WORKAROUND NRF53_ERRATA_32_PRESENT
#endif

static bool nrf53_errata_32(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 33 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_33_PRESENT 1
    #else
        #define NRF53_ERRATA_33_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_33_PRESENT 0
#endif

#ifndef NRF53_ERRATA_33_ENABLE_WORKAROUND
    #define NRF53_ERRATA_33_ENABLE_WORKAROUND NRF53_ERRATA_33_PRESENT
#endif

static bool nrf53_errata_33(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 34 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_34_PRESENT 1
    #else
        #define NRF53_ERRATA_34_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_34_PRESENT 0
#endif

#ifndef NRF53_ERRATA_34_ENABLE_WORKAROUND
    #define NRF53_ERRATA_34_ENABLE_WORKAROUND NRF53_ERRATA_34_PRESENT
#endif

static bool nrf53_errata_34(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 36 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_36_PRESENT 1
    #else
        #define NRF53_ERRATA_36_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_36_PRESENT 0
#endif

#ifndef NRF53_ERRATA_36_ENABLE_WORKAROUND
    #define NRF53_ERRATA_36_ENABLE_WORKAROUND NRF53_ERRATA_36_PRESENT
#endif

static bool nrf53_errata_36(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 37 ========= */
#define NRF53_ERRATA_37_PRESENT 0

#ifndef NRF53_ERRATA_37_ENABLE_WORKAROUND
    #define NRF53_ERRATA_37_ENABLE_WORKAROUND NRF53_ERRATA_37_PRESENT
#endif

static bool nrf53_errata_37(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        return false;
    #endif
}

/* ========= Errata 42 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_42_PRESENT 1
    #else
        #define NRF53_ERRATA_42_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_42_PRESENT 0
#endif

#ifndef NRF53_ERRATA_42_ENABLE_WORKAROUND
    #define NRF53_ERRATA_42_ENABLE_WORKAROUND NRF53_ERRATA_42_PRESENT
#endif

static bool nrf53_errata_42(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 43 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_43_PRESENT 1
    #else
        #define NRF53_ERRATA_43_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_43_PRESENT 0
#endif

#ifndef NRF53_ERRATA_43_ENABLE_WORKAROUND
    #define NRF53_ERRATA_43_ENABLE_WORKAROUND NRF53_ERRATA_43_PRESENT
#endif

static bool nrf53_errata_43(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 44 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_44_PRESENT 1
    #else
        #define NRF53_ERRATA_44_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_44_PRESENT 0
#endif

#ifndef NRF53_ERRATA_44_ENABLE_WORKAROUND
    #define NRF53_ERRATA_44_ENABLE_WORKAROUND NRF53_ERRATA_44_PRESENT
#endif

static bool nrf53_errata_44(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 45 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_45_PRESENT 1
    #else
        #define NRF53_ERRATA_45_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_45_PRESENT 0
#endif

#ifndef NRF53_ERRATA_45_ENABLE_WORKAROUND
    #define NRF53_ERRATA_45_ENABLE_WORKAROUND NRF53_ERRATA_45_PRESENT
#endif

static bool nrf53_errata_45(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 46 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_46_PRESENT 1
    #else
        #define NRF53_ERRATA_46_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_46_PRESENT 0
#endif

#ifndef NRF53_ERRATA_46_ENABLE_WORKAROUND
    #define NRF53_ERRATA_46_ENABLE_WORKAROUND NRF53_ERRATA_46_PRESENT
#endif

static bool nrf53_errata_46(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 47 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_47_PRESENT 1
    #else
        #define NRF53_ERRATA_47_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_47_PRESENT 0
#endif

#ifndef NRF53_ERRATA_47_ENABLE_WORKAROUND
    #define NRF53_ERRATA_47_ENABLE_WORKAROUND NRF53_ERRATA_47_PRESENT
#endif

static bool nrf53_errata_47(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 49 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_49_PRESENT 1
    #else
        #define NRF53_ERRATA_49_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_49_PRESENT 0
#endif

#ifndef NRF53_ERRATA_49_ENABLE_WORKAROUND
    #define NRF53_ERRATA_49_ENABLE_WORKAROUND NRF53_ERRATA_49_PRESENT
#endif

static bool nrf53_errata_49(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 50 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_50_PRESENT 1
    #else
        #define NRF53_ERRATA_50_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_50_PRESENT 0
#endif

#ifndef NRF53_ERRATA_50_ENABLE_WORKAROUND
    #define NRF53_ERRATA_50_ENABLE_WORKAROUND NRF53_ERRATA_50_PRESENT
#endif

static bool nrf53_errata_50(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 51 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_51_PRESENT 1
    #else
        #define NRF53_ERRATA_51_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_51_PRESENT 0
#endif

#ifndef NRF53_ERRATA_51_ENABLE_WORKAROUND
    #define NRF53_ERRATA_51_ENABLE_WORKAROUND NRF53_ERRATA_51_PRESENT
#endif

static bool nrf53_errata_51(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 52 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_52_PRESENT 1
    #else
        #define NRF53_ERRATA_52_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_52_PRESENT 0
#endif

#ifndef NRF53_ERRATA_52_ENABLE_WORKAROUND
    #define NRF53_ERRATA_52_ENABLE_WORKAROUND NRF53_ERRATA_52_PRESENT
#endif

static bool nrf53_errata_52(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 53 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_53_PRESENT 1
    #else
        #define NRF53_ERRATA_53_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_53_PRESENT 0
#endif

#ifndef NRF53_ERRATA_53_ENABLE_WORKAROUND
    #define NRF53_ERRATA_53_ENABLE_WORKAROUND NRF53_ERRATA_53_PRESENT
#endif

static bool nrf53_errata_53(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 54 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_54_PRESENT 1
    #else
        #define NRF53_ERRATA_54_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_54_PRESENT 0
#endif

#ifndef NRF53_ERRATA_54_ENABLE_WORKAROUND
    #define NRF53_ERRATA_54_ENABLE_WORKAROUND NRF53_ERRATA_54_PRESENT
#endif

static bool nrf53_errata_54(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 55 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_55_PRESENT 1
    #else
        #define NRF53_ERRATA_55_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_55_PRESENT 0
#endif

#ifndef NRF53_ERRATA_55_ENABLE_WORKAROUND
    #define NRF53_ERRATA_55_ENABLE_WORKAROUND NRF53_ERRATA_55_PRESENT
#endif

static bool nrf53_errata_55(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 57 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_57_PRESENT 1
    #else
        #define NRF53_ERRATA_57_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_57_PRESENT 0
#endif

#ifndef NRF53_ERRATA_57_ENABLE_WORKAROUND
    #define NRF53_ERRATA_57_ENABLE_WORKAROUND NRF53_ERRATA_57_PRESENT
#endif

static bool nrf53_errata_57(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 58 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_58_PRESENT 1
    #else
        #define NRF53_ERRATA_58_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_58_PRESENT 0
#endif

#ifndef NRF53_ERRATA_58_ENABLE_WORKAROUND
    #define NRF53_ERRATA_58_ENABLE_WORKAROUND NRF53_ERRATA_58_PRESENT
#endif

static bool nrf53_errata_58(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 59 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_59_PRESENT 1
    #else
        #define NRF53_ERRATA_59_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_59_PRESENT 0
#endif

#ifndef NRF53_ERRATA_59_ENABLE_WORKAROUND
    #define NRF53_ERRATA_59_ENABLE_WORKAROUND NRF53_ERRATA_59_PRESENT
#endif

static bool nrf53_errata_59(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 62 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_62_PRESENT 1
    #else
        #define NRF53_ERRATA_62_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_62_PRESENT 0
#endif

#ifndef NRF53_ERRATA_62_ENABLE_WORKAROUND
    #define NRF53_ERRATA_62_ENABLE_WORKAROUND NRF53_ERRATA_62_PRESENT
#endif

static bool nrf53_errata_62(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 64 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_64_PRESENT 1
    #else
        #define NRF53_ERRATA_64_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_64_PRESENT 0
#endif

#ifndef NRF53_ERRATA_64_ENABLE_WORKAROUND
    #define NRF53_ERRATA_64_ENABLE_WORKAROUND NRF53_ERRATA_64_PRESENT
#endif

static bool nrf53_errata_64(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 65 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_65_PRESENT 1
    #else
        #define NRF53_ERRATA_65_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_65_PRESENT 0
#endif

#ifndef NRF53_ERRATA_65_ENABLE_WORKAROUND
    #define NRF53_ERRATA_65_ENABLE_WORKAROUND NRF53_ERRATA_65_PRESENT
#endif

static bool nrf53_errata_65(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 66 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_66_PRESENT 1
    #else
        #define NRF53_ERRATA_66_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_66_PRESENT 0
#endif

#ifndef NRF53_ERRATA_66_ENABLE_WORKAROUND
    #define NRF53_ERRATA_66_ENABLE_WORKAROUND NRF53_ERRATA_66_PRESENT
#endif

static bool nrf53_errata_66(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 67 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_67_PRESENT 1
    #else
        #define NRF53_ERRATA_67_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_67_PRESENT 0
#endif

#ifndef NRF53_ERRATA_67_ENABLE_WORKAROUND
    #define NRF53_ERRATA_67_ENABLE_WORKAROUND NRF53_ERRATA_67_PRESENT
#endif

static bool nrf53_errata_67(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 69 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_69_PRESENT 1
    #else
        #define NRF53_ERRATA_69_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_69_PRESENT 0
#endif

#ifndef NRF53_ERRATA_69_ENABLE_WORKAROUND
    #define NRF53_ERRATA_69_ENABLE_WORKAROUND NRF53_ERRATA_69_PRESENT
#endif

static bool nrf53_errata_69(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 70 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_70_PRESENT 1
    #else
        #define NRF53_ERRATA_70_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_70_PRESENT 0
#endif

#ifndef NRF53_ERRATA_70_ENABLE_WORKAROUND
    #define NRF53_ERRATA_70_ENABLE_WORKAROUND NRF53_ERRATA_70_PRESENT
#endif

static bool nrf53_errata_70(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 71 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_71_PRESENT 1
    #else
        #define NRF53_ERRATA_71_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_71_PRESENT 0
#endif

#ifndef NRF53_ERRATA_71_ENABLE_WORKAROUND
    #define NRF53_ERRATA_71_ENABLE_WORKAROUND NRF53_ERRATA_71_PRESENT
#endif

static bool nrf53_errata_71(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 72 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_72_PRESENT 1
    #else
        #define NRF53_ERRATA_72_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_72_PRESENT 0
#endif

#ifndef NRF53_ERRATA_72_ENABLE_WORKAROUND
    #define NRF53_ERRATA_72_ENABLE_WORKAROUND NRF53_ERRATA_72_PRESENT
#endif

static bool nrf53_errata_72(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 73 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_73_PRESENT 1
    #else
        #define NRF53_ERRATA_73_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_73_PRESENT 0
#endif

#ifndef NRF53_ERRATA_73_ENABLE_WORKAROUND
    #define NRF53_ERRATA_73_ENABLE_WORKAROUND NRF53_ERRATA_73_PRESENT
#endif

static bool nrf53_errata_73(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 74 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_74_PRESENT 1
    #else
        #define NRF53_ERRATA_74_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_74_PRESENT 0
#endif

#ifndef NRF53_ERRATA_74_ENABLE_WORKAROUND
    #define NRF53_ERRATA_74_ENABLE_WORKAROUND NRF53_ERRATA_74_PRESENT
#endif

static bool nrf53_errata_74(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 75 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_75_PRESENT 1
    #else
        #define NRF53_ERRATA_75_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_75_PRESENT 0
#endif

#ifndef NRF53_ERRATA_75_ENABLE_WORKAROUND
    #define NRF53_ERRATA_75_ENABLE_WORKAROUND NRF53_ERRATA_75_PRESENT
#endif

static bool nrf53_errata_75(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 76 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_76_PRESENT 1
    #else
        #define NRF53_ERRATA_76_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_76_PRESENT 0
#endif

#ifndef NRF53_ERRATA_76_ENABLE_WORKAROUND
    #define NRF53_ERRATA_76_ENABLE_WORKAROUND NRF53_ERRATA_76_PRESENT
#endif

static bool nrf53_errata_76(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 77 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_77_PRESENT 1
    #else
        #define NRF53_ERRATA_77_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_77_PRESENT 0
#endif

#ifndef NRF53_ERRATA_77_ENABLE_WORKAROUND
    #define NRF53_ERRATA_77_ENABLE_WORKAROUND NRF53_ERRATA_77_PRESENT
#endif

static bool nrf53_errata_77(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 79 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_79_PRESENT 1
    #else
        #define NRF53_ERRATA_79_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_79_PRESENT 0
#endif

#ifndef NRF53_ERRATA_79_ENABLE_WORKAROUND
    #define NRF53_ERRATA_79_ENABLE_WORKAROUND NRF53_ERRATA_79_PRESENT
#endif

static bool nrf53_errata_79(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 80 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_80_PRESENT 1
    #else
        #define NRF53_ERRATA_80_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_80_PRESENT 0
#endif

#ifndef NRF53_ERRATA_80_ENABLE_WORKAROUND
    #define NRF53_ERRATA_80_ENABLE_WORKAROUND NRF53_ERRATA_80_PRESENT
#endif

static bool nrf53_errata_80(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 81 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_81_PRESENT 1
    #else
        #define NRF53_ERRATA_81_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_81_PRESENT 0
#endif

#ifndef NRF53_ERRATA_81_ENABLE_WORKAROUND
    #define NRF53_ERRATA_81_ENABLE_WORKAROUND NRF53_ERRATA_81_PRESENT
#endif

static bool nrf53_errata_81(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 82 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_82_PRESENT 1
    #else
        #define NRF53_ERRATA_82_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_82_PRESENT 0
#endif

#ifndef NRF53_ERRATA_82_ENABLE_WORKAROUND
    #define NRF53_ERRATA_82_ENABLE_WORKAROUND NRF53_ERRATA_82_PRESENT
#endif

static bool nrf53_errata_82(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 83 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_83_PRESENT 1
    #else
        #define NRF53_ERRATA_83_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_83_PRESENT 0
#endif

#ifndef NRF53_ERRATA_83_ENABLE_WORKAROUND
    #define NRF53_ERRATA_83_ENABLE_WORKAROUND NRF53_ERRATA_83_PRESENT
#endif

static bool nrf53_errata_83(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 84 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_84_PRESENT 1
    #else
        #define NRF53_ERRATA_84_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_84_PRESENT 0
#endif

#ifndef NRF53_ERRATA_84_ENABLE_WORKAROUND
    #define NRF53_ERRATA_84_ENABLE_WORKAROUND NRF53_ERRATA_84_PRESENT
#endif

static bool nrf53_errata_84(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 85 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_85_PRESENT 1
    #else
        #define NRF53_ERRATA_85_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_85_PRESENT 0
#endif

#ifndef NRF53_ERRATA_85_ENABLE_WORKAROUND
    #define NRF53_ERRATA_85_ENABLE_WORKAROUND NRF53_ERRATA_85_PRESENT
#endif

static bool nrf53_errata_85(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 86 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_86_PRESENT 1
    #else
        #define NRF53_ERRATA_86_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_86_PRESENT 0
#endif

#ifndef NRF53_ERRATA_86_ENABLE_WORKAROUND
    #define NRF53_ERRATA_86_ENABLE_WORKAROUND NRF53_ERRATA_86_PRESENT
#endif

static bool nrf53_errata_86(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 87 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_87_PRESENT 1
    #else
        #define NRF53_ERRATA_87_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_87_PRESENT 0
#endif

#ifndef NRF53_ERRATA_87_ENABLE_WORKAROUND
    #define NRF53_ERRATA_87_ENABLE_WORKAROUND NRF53_ERRATA_87_PRESENT
#endif

static bool nrf53_errata_87(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 90 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_90_PRESENT 1
    #else
        #define NRF53_ERRATA_90_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_90_PRESENT 0
#endif

#ifndef NRF53_ERRATA_90_ENABLE_WORKAROUND
    #define NRF53_ERRATA_90_ENABLE_WORKAROUND NRF53_ERRATA_90_PRESENT
#endif

static bool nrf53_errata_90(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 91 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_91_PRESENT 1
    #else
        #define NRF53_ERRATA_91_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_91_PRESENT 0
#endif

#ifndef NRF53_ERRATA_91_ENABLE_WORKAROUND
    #define NRF53_ERRATA_91_ENABLE_WORKAROUND NRF53_ERRATA_91_PRESENT
#endif

static bool nrf53_errata_91(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 93 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_93_PRESENT 1
    #else
        #define NRF53_ERRATA_93_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_93_PRESENT 0
#endif

#ifndef NRF53_ERRATA_93_ENABLE_WORKAROUND
    #define NRF53_ERRATA_93_ENABLE_WORKAROUND NRF53_ERRATA_93_PRESENT
#endif

static bool nrf53_errata_93(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 95 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_95_PRESENT 1
    #else
        #define NRF53_ERRATA_95_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_95_PRESENT 0
#endif

#ifndef NRF53_ERRATA_95_ENABLE_WORKAROUND
    #define NRF53_ERRATA_95_ENABLE_WORKAROUND NRF53_ERRATA_95_PRESENT
#endif

static bool nrf53_errata_95(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 97 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION) || \
        defined(NRF_NETWORK)
        #define NRF53_ERRATA_97_PRESENT 1
    #else
        #define NRF53_ERRATA_97_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_97_PRESENT 0
#endif

#ifndef NRF53_ERRATA_97_ENABLE_WORKAROUND
    #define NRF53_ERRATA_97_ENABLE_WORKAROUND NRF53_ERRATA_97_PRESENT
#endif

static bool nrf53_errata_97(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #elif defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)\
             || defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 99 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_99_PRESENT 1
    #else
        #define NRF53_ERRATA_99_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_99_PRESENT 0
#endif

#ifndef NRF53_ERRATA_99_ENABLE_WORKAROUND
    #define NRF53_ERRATA_99_ENABLE_WORKAROUND NRF53_ERRATA_99_PRESENT
#endif

static bool nrf53_errata_99(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return false;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 103 ========= */
#define NRF53_ERRATA_103_PRESENT 0

#ifndef NRF53_ERRATA_103_ENABLE_WORKAROUND
    #define NRF53_ERRATA_103_ENABLE_WORKAROUND NRF53_ERRATA_103_PRESENT
#endif

static bool nrf53_errata_103(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        return false;
    #endif
}

/* ========= Errata 105 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_105_PRESENT 1
    #else
        #define NRF53_ERRATA_105_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_105_PRESENT 0
#endif

#ifndef NRF53_ERRATA_105_ENABLE_WORKAROUND
    #define NRF53_ERRATA_105_ENABLE_WORKAROUND NRF53_ERRATA_105_PRESENT
#endif

static bool nrf53_errata_105(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 106 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_106_PRESENT 1
    #else
        #define NRF53_ERRATA_106_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_106_PRESENT 0
#endif

#ifndef NRF53_ERRATA_106_ENABLE_WORKAROUND
    #define NRF53_ERRATA_106_ENABLE_WORKAROUND NRF53_ERRATA_106_PRESENT
#endif

static bool nrf53_errata_106(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 107 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_107_PRESENT 1
    #else
        #define NRF53_ERRATA_107_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_107_PRESENT 0
#endif

#ifndef NRF53_ERRATA_107_ENABLE_WORKAROUND
    #define NRF53_ERRATA_107_ENABLE_WORKAROUND NRF53_ERRATA_107_PRESENT
#endif

static bool nrf53_errata_107(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return false;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 109 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_109_PRESENT 1
    #else
        #define NRF53_ERRATA_109_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_109_PRESENT 0
#endif

#ifndef NRF53_ERRATA_109_ENABLE_WORKAROUND
    #define NRF53_ERRATA_109_ENABLE_WORKAROUND NRF53_ERRATA_109_PRESENT
#endif

static bool nrf53_errata_109(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 110 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_110_PRESENT 1
    #else
        #define NRF53_ERRATA_110_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_110_PRESENT 0
#endif

#ifndef NRF53_ERRATA_110_ENABLE_WORKAROUND
    #define NRF53_ERRATA_110_ENABLE_WORKAROUND NRF53_ERRATA_110_PRESENT
#endif

static bool nrf53_errata_110(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 112 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_112_PRESENT 1
    #else
        #define NRF53_ERRATA_112_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_112_PRESENT 0
#endif

#ifndef NRF53_ERRATA_112_ENABLE_WORKAROUND
    #define NRF53_ERRATA_112_ENABLE_WORKAROUND NRF53_ERRATA_112_PRESENT
#endif

static bool nrf53_errata_112(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return false;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 113 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_113_PRESENT 1
    #else
        #define NRF53_ERRATA_113_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_113_PRESENT 0
#endif

#ifndef NRF53_ERRATA_113_ENABLE_WORKAROUND
    #define NRF53_ERRATA_113_ENABLE_WORKAROUND NRF53_ERRATA_113_PRESENT
#endif

static bool nrf53_errata_113(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 114 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_114_PRESENT 1
    #else
        #define NRF53_ERRATA_114_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_114_PRESENT 0
#endif

#ifndef NRF53_ERRATA_114_ENABLE_WORKAROUND
    #define NRF53_ERRATA_114_ENABLE_WORKAROUND NRF53_ERRATA_114_PRESENT
#endif

static bool nrf53_errata_114(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 115 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_115_PRESENT 1
    #else
        #define NRF53_ERRATA_115_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_115_PRESENT 0
#endif

#ifndef NRF53_ERRATA_115_ENABLE_WORKAROUND
    #define NRF53_ERRATA_115_ENABLE_WORKAROUND NRF53_ERRATA_115_PRESENT
#endif

static bool nrf53_errata_115(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 116 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_116_PRESENT 1
    #else
        #define NRF53_ERRATA_116_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_116_PRESENT 0
#endif

#ifndef NRF53_ERRATA_116_ENABLE_WORKAROUND
    #define NRF53_ERRATA_116_ENABLE_WORKAROUND NRF53_ERRATA_116_PRESENT
#endif

static bool nrf53_errata_116(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return false;
                        case 0x05ul:
                            return false;
                        default:
                            return false;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 117 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_117_PRESENT 1
    #else
        #define NRF53_ERRATA_117_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_117_PRESENT 0
#endif

#ifndef NRF53_ERRATA_117_ENABLE_WORKAROUND
    #define NRF53_ERRATA_117_ENABLE_WORKAROUND NRF53_ERRATA_117_PRESENT
#endif

static bool nrf53_errata_117(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 119 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_119_PRESENT 1
    #else
        #define NRF53_ERRATA_119_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_119_PRESENT 0
#endif

#ifndef NRF53_ERRATA_119_ENABLE_WORKAROUND
    #define NRF53_ERRATA_119_ENABLE_WORKAROUND NRF53_ERRATA_119_PRESENT
#endif

static bool nrf53_errata_119(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return true;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 121 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_APPLICATION)
        #define NRF53_ERRATA_121_PRESENT 1
    #else
        #define NRF53_ERRATA_121_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_121_PRESENT 0
#endif

#ifndef NRF53_ERRATA_121_ENABLE_WORKAROUND
    #define NRF53_ERRATA_121_ENABLE_WORKAROUND NRF53_ERRATA_121_PRESENT
#endif

static bool nrf53_errata_121(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_APPLICATION)
                #if defined(NRF_TRUSTZONE_NONSECURE)
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
                #else
                    uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                    uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
                #endif
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_APPLICATION)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return false;
                        case 0x03ul:
                            return true;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 122 ========= */
#if    defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
    #if defined(NRF_NETWORK)
        #define NRF53_ERRATA_122_PRESENT 1
    #else
        #define NRF53_ERRATA_122_PRESENT 0
    #endif
#else
    #define NRF53_ERRATA_122_PRESENT 0
#endif

#ifndef NRF53_ERRATA_122_ENABLE_WORKAROUND
    #define NRF53_ERRATA_122_ENABLE_WORKAROUND NRF53_ERRATA_122_PRESENT
#endif

static bool nrf53_errata_122(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined(NRF_NETWORK)
                uint32_t var1 = *(uint32_t *)0x01FF0130ul;
                uint32_t var2 = *(uint32_t *)0x01FF0134ul;
            #endif
        #endif
        #if defined (NRF5340_XXAA) || defined (DEVELOP_IN_NRF5340)
            #if defined (NRF_NETWORK)
                if (var1 == 0x07)
                {
                    switch(var2)
                    {
                        case 0x02ul:
                            return false;
                        case 0x03ul:
                            return false;
                        case 0x04ul:
                            return true;
                        case 0x05ul:
                            return true;
                        default:
                            return true;
                    }
                }
            #endif
        #endif
        return false;
    #endif
}

/* ========= Errata 134 ========= */
#define NRF53_ERRATA_134_PRESENT 0

#ifndef NRF53_ERRATA_134_ENABLE_WORKAROUND
    #define NRF53_ERRATA_134_ENABLE_WORKAROUND NRF53_ERRATA_134_PRESENT
#endif

static bool nrf53_errata_134(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        return false;
    #endif
}

/* ========= Errata 138 ========= */
#define NRF53_ERRATA_138_PRESENT 0

#ifndef NRF53_ERRATA_138_ENABLE_WORKAROUND
    #define NRF53_ERRATA_138_ENABLE_WORKAROUND NRF53_ERRATA_138_PRESENT
#endif

static bool nrf53_errata_138(void)
{
    #ifndef NRF53_SERIES
        return false;
    #else
        return false;
    #endif
}

#endif /* NRF53_ERRATAS_H */
