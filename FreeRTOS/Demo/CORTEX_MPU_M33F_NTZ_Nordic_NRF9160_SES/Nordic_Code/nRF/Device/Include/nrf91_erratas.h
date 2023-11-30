#ifndef NRF91_ERRATAS_H
#define NRF91_ERRATAS_H

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

static bool nrf91_errata_1(void) __UNUSED;
static bool nrf91_errata_2(void) __UNUSED;
static bool nrf91_errata_4(void) __UNUSED;
static bool nrf91_errata_6(void) __UNUSED;
static bool nrf91_errata_7(void) __UNUSED;
static bool nrf91_errata_8(void) __UNUSED;
static bool nrf91_errata_9(void) __UNUSED;
static bool nrf91_errata_10(void) __UNUSED;
static bool nrf91_errata_12(void) __UNUSED;
static bool nrf91_errata_14(void) __UNUSED;
static bool nrf91_errata_15(void) __UNUSED;
static bool nrf91_errata_16(void) __UNUSED;
static bool nrf91_errata_17(void) __UNUSED;
static bool nrf91_errata_20(void) __UNUSED;
static bool nrf91_errata_21(void) __UNUSED;
static bool nrf91_errata_23(void) __UNUSED;
static bool nrf91_errata_24(void) __UNUSED;
static bool nrf91_errata_26(void) __UNUSED;
static bool nrf91_errata_27(void) __UNUSED;
static bool nrf91_errata_28(void) __UNUSED;
static bool nrf91_errata_29(void) __UNUSED;
static bool nrf91_errata_30(void) __UNUSED;
static bool nrf91_errata_31(void) __UNUSED;
static bool nrf91_errata_32(void) __UNUSED;
static bool nrf91_errata_33(void) __UNUSED;

/* ========= Errata 1 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_1_PRESENT 1
#else
    #define NRF91_ERRATA_1_PRESENT 0
#endif

#ifndef NRF91_ERRATA_1_ENABLE_WORKAROUND
    #define NRF91_ERRATA_1_ENABLE_WORKAROUND NRF91_ERRATA_1_PRESENT
#endif

static bool nrf91_errata_1(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 2 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_2_PRESENT 1
#else
    #define NRF91_ERRATA_2_PRESENT 0
#endif

#ifndef NRF91_ERRATA_2_ENABLE_WORKAROUND
    #define NRF91_ERRATA_2_ENABLE_WORKAROUND NRF91_ERRATA_2_PRESENT
#endif

static bool nrf91_errata_2(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 4 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_4_PRESENT 1
#else
    #define NRF91_ERRATA_4_PRESENT 0
#endif

#ifndef NRF91_ERRATA_4_ENABLE_WORKAROUND
    #define NRF91_ERRATA_4_ENABLE_WORKAROUND NRF91_ERRATA_4_PRESENT
#endif

static bool nrf91_errata_4(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 6 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_6_PRESENT 1
#else
    #define NRF91_ERRATA_6_PRESENT 0
#endif

#ifndef NRF91_ERRATA_6_ENABLE_WORKAROUND
    #define NRF91_ERRATA_6_ENABLE_WORKAROUND NRF91_ERRATA_6_PRESENT
#endif

static bool nrf91_errata_6(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 7 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_7_PRESENT 1
#else
    #define NRF91_ERRATA_7_PRESENT 0
#endif

#ifndef NRF91_ERRATA_7_ENABLE_WORKAROUND
    #define NRF91_ERRATA_7_ENABLE_WORKAROUND NRF91_ERRATA_7_PRESENT
#endif

static bool nrf91_errata_7(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 8 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_8_PRESENT 1
#else
    #define NRF91_ERRATA_8_PRESENT 0
#endif

#ifndef NRF91_ERRATA_8_ENABLE_WORKAROUND
    #define NRF91_ERRATA_8_ENABLE_WORKAROUND NRF91_ERRATA_8_PRESENT
#endif

static bool nrf91_errata_8(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 9 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_9_PRESENT 1
#else
    #define NRF91_ERRATA_9_PRESENT 0
#endif

#ifndef NRF91_ERRATA_9_ENABLE_WORKAROUND
    #define NRF91_ERRATA_9_ENABLE_WORKAROUND NRF91_ERRATA_9_PRESENT
#endif

static bool nrf91_errata_9(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 10 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_10_PRESENT 1
#else
    #define NRF91_ERRATA_10_PRESENT 0
#endif

#ifndef NRF91_ERRATA_10_ENABLE_WORKAROUND
    #define NRF91_ERRATA_10_ENABLE_WORKAROUND NRF91_ERRATA_10_PRESENT
#endif

static bool nrf91_errata_10(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 12 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_12_PRESENT 1
#else
    #define NRF91_ERRATA_12_PRESENT 0
#endif

#ifndef NRF91_ERRATA_12_ENABLE_WORKAROUND
    #define NRF91_ERRATA_12_ENABLE_WORKAROUND NRF91_ERRATA_12_PRESENT
#endif

static bool nrf91_errata_12(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 14 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_14_PRESENT 1
#else
    #define NRF91_ERRATA_14_PRESENT 0
#endif

#ifndef NRF91_ERRATA_14_ENABLE_WORKAROUND
    #define NRF91_ERRATA_14_ENABLE_WORKAROUND NRF91_ERRATA_14_PRESENT
#endif

static bool nrf91_errata_14(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 15 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_15_PRESENT 1
#else
    #define NRF91_ERRATA_15_PRESENT 0
#endif

#ifndef NRF91_ERRATA_15_ENABLE_WORKAROUND
    #define NRF91_ERRATA_15_ENABLE_WORKAROUND NRF91_ERRATA_15_PRESENT
#endif

static bool nrf91_errata_15(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 16 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_16_PRESENT 1
#else
    #define NRF91_ERRATA_16_PRESENT 0
#endif

#ifndef NRF91_ERRATA_16_ENABLE_WORKAROUND
    #define NRF91_ERRATA_16_ENABLE_WORKAROUND NRF91_ERRATA_16_PRESENT
#endif

static bool nrf91_errata_16(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 17 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_17_PRESENT 1
#else
    #define NRF91_ERRATA_17_PRESENT 0
#endif

#ifndef NRF91_ERRATA_17_ENABLE_WORKAROUND
    #define NRF91_ERRATA_17_ENABLE_WORKAROUND NRF91_ERRATA_17_PRESENT
#endif

static bool nrf91_errata_17(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 20 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_20_PRESENT 1
#else
    #define NRF91_ERRATA_20_PRESENT 0
#endif

#ifndef NRF91_ERRATA_20_ENABLE_WORKAROUND
    #define NRF91_ERRATA_20_ENABLE_WORKAROUND NRF91_ERRATA_20_PRESENT
#endif

static bool nrf91_errata_20(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 21 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_21_PRESENT 1
#else
    #define NRF91_ERRATA_21_PRESENT 0
#endif

#ifndef NRF91_ERRATA_21_ENABLE_WORKAROUND
    #define NRF91_ERRATA_21_ENABLE_WORKAROUND NRF91_ERRATA_21_PRESENT
#endif

static bool nrf91_errata_21(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 23 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_23_PRESENT 1
#else
    #define NRF91_ERRATA_23_PRESENT 0
#endif

#ifndef NRF91_ERRATA_23_ENABLE_WORKAROUND
    #define NRF91_ERRATA_23_ENABLE_WORKAROUND NRF91_ERRATA_23_PRESENT
#endif

static bool nrf91_errata_23(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 24 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_24_PRESENT 1
#else
    #define NRF91_ERRATA_24_PRESENT 0
#endif

#ifndef NRF91_ERRATA_24_ENABLE_WORKAROUND
    #define NRF91_ERRATA_24_ENABLE_WORKAROUND NRF91_ERRATA_24_PRESENT
#endif

static bool nrf91_errata_24(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 26 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_26_PRESENT 1
#else
    #define NRF91_ERRATA_26_PRESENT 0
#endif

#ifndef NRF91_ERRATA_26_ENABLE_WORKAROUND
    #define NRF91_ERRATA_26_ENABLE_WORKAROUND NRF91_ERRATA_26_PRESENT
#endif

static bool nrf91_errata_26(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 27 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_27_PRESENT 1
#else
    #define NRF91_ERRATA_27_PRESENT 0
#endif

#ifndef NRF91_ERRATA_27_ENABLE_WORKAROUND
    #define NRF91_ERRATA_27_ENABLE_WORKAROUND NRF91_ERRATA_27_PRESENT
#endif

static bool nrf91_errata_27(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 28 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_28_PRESENT 1
#else
    #define NRF91_ERRATA_28_PRESENT 0
#endif

#ifndef NRF91_ERRATA_28_ENABLE_WORKAROUND
    #define NRF91_ERRATA_28_ENABLE_WORKAROUND NRF91_ERRATA_28_PRESENT
#endif

static bool nrf91_errata_28(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 29 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_29_PRESENT 1
#else
    #define NRF91_ERRATA_29_PRESENT 0
#endif

#ifndef NRF91_ERRATA_29_ENABLE_WORKAROUND
    #define NRF91_ERRATA_29_ENABLE_WORKAROUND NRF91_ERRATA_29_PRESENT
#endif

static bool nrf91_errata_29(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 30 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_30_PRESENT 1
#else
    #define NRF91_ERRATA_30_PRESENT 0
#endif

#ifndef NRF91_ERRATA_30_ENABLE_WORKAROUND
    #define NRF91_ERRATA_30_ENABLE_WORKAROUND NRF91_ERRATA_30_PRESENT
#endif

static bool nrf91_errata_30(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 31 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_31_PRESENT 1
#else
    #define NRF91_ERRATA_31_PRESENT 0
#endif

#ifndef NRF91_ERRATA_31_ENABLE_WORKAROUND
    #define NRF91_ERRATA_31_ENABLE_WORKAROUND NRF91_ERRATA_31_PRESENT
#endif

static bool nrf91_errata_31(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 32 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_32_PRESENT 1
#else
    #define NRF91_ERRATA_32_PRESENT 0
#endif

#ifndef NRF91_ERRATA_32_ENABLE_WORKAROUND
    #define NRF91_ERRATA_32_ENABLE_WORKAROUND NRF91_ERRATA_32_PRESENT
#endif

static bool nrf91_errata_32(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 33 ========= */
#if    defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
    #define NRF91_ERRATA_33_PRESENT 1
#else
    #define NRF91_ERRATA_33_PRESENT 0
#endif

#ifndef NRF91_ERRATA_33_ENABLE_WORKAROUND
    #define NRF91_ERRATA_33_ENABLE_WORKAROUND NRF91_ERRATA_33_PRESENT
#endif

static bool nrf91_errata_33(void)
{
    #ifndef NRF91_SERIES
        return false;
    #else
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            #if defined(NRF_TRUSTZONE_NONSECURE)
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_NS + 0x00000134ul));
            #else
                uint32_t var1 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000130ul));
                uint32_t var2 = *((volatile uint32_t *)((uint32_t)NRF_FICR_S + 0x00000134ul));
            #endif
        #endif
        #if defined (NRF9160_XXAA) || defined (DEVELOP_IN_NRF9160)
            __DSB();
            if (var1 == 0x09)
            {
                switch(var2)
                {
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

#endif /* NRF91_ERRATAS_H */
