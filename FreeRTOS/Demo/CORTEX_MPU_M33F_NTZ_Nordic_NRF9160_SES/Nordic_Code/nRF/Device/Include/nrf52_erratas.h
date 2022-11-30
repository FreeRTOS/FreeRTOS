#ifndef NRF52_ERRATAS_H
#define NRF52_ERRATAS_H

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

static bool nrf52_errata_1(void) __UNUSED;
static bool nrf52_errata_2(void) __UNUSED;
static bool nrf52_errata_3(void) __UNUSED;
static bool nrf52_errata_4(void) __UNUSED;
static bool nrf52_errata_7(void) __UNUSED;
static bool nrf52_errata_8(void) __UNUSED;
static bool nrf52_errata_9(void) __UNUSED;
static bool nrf52_errata_10(void) __UNUSED;
static bool nrf52_errata_11(void) __UNUSED;
static bool nrf52_errata_12(void) __UNUSED;
static bool nrf52_errata_15(void) __UNUSED;
static bool nrf52_errata_16(void) __UNUSED;
static bool nrf52_errata_17(void) __UNUSED;
static bool nrf52_errata_20(void) __UNUSED;
static bool nrf52_errata_23(void) __UNUSED;
static bool nrf52_errata_24(void) __UNUSED;
static bool nrf52_errata_25(void) __UNUSED;
static bool nrf52_errata_26(void) __UNUSED;
static bool nrf52_errata_27(void) __UNUSED;
static bool nrf52_errata_28(void) __UNUSED;
static bool nrf52_errata_29(void) __UNUSED;
static bool nrf52_errata_30(void) __UNUSED;
static bool nrf52_errata_31(void) __UNUSED;
static bool nrf52_errata_32(void) __UNUSED;
static bool nrf52_errata_33(void) __UNUSED;
static bool nrf52_errata_34(void) __UNUSED;
static bool nrf52_errata_35(void) __UNUSED;
static bool nrf52_errata_36(void) __UNUSED;
static bool nrf52_errata_37(void) __UNUSED;
static bool nrf52_errata_38(void) __UNUSED;
static bool nrf52_errata_39(void) __UNUSED;
static bool nrf52_errata_40(void) __UNUSED;
static bool nrf52_errata_41(void) __UNUSED;
static bool nrf52_errata_42(void) __UNUSED;
static bool nrf52_errata_43(void) __UNUSED;
static bool nrf52_errata_44(void) __UNUSED;
static bool nrf52_errata_46(void) __UNUSED;
static bool nrf52_errata_47(void) __UNUSED;
static bool nrf52_errata_48(void) __UNUSED;
static bool nrf52_errata_49(void) __UNUSED;
static bool nrf52_errata_51(void) __UNUSED;
static bool nrf52_errata_54(void) __UNUSED;
static bool nrf52_errata_55(void) __UNUSED;
static bool nrf52_errata_57(void) __UNUSED;
static bool nrf52_errata_58(void) __UNUSED;
static bool nrf52_errata_62(void) __UNUSED;
static bool nrf52_errata_63(void) __UNUSED;
static bool nrf52_errata_64(void) __UNUSED;
static bool nrf52_errata_65(void) __UNUSED;
static bool nrf52_errata_66(void) __UNUSED;
static bool nrf52_errata_67(void) __UNUSED;
static bool nrf52_errata_68(void) __UNUSED;
static bool nrf52_errata_70(void) __UNUSED;
static bool nrf52_errata_71(void) __UNUSED;
static bool nrf52_errata_72(void) __UNUSED;
static bool nrf52_errata_73(void) __UNUSED;
static bool nrf52_errata_74(void) __UNUSED;
static bool nrf52_errata_75(void) __UNUSED;
static bool nrf52_errata_76(void) __UNUSED;
static bool nrf52_errata_77(void) __UNUSED;
static bool nrf52_errata_78(void) __UNUSED;
static bool nrf52_errata_79(void) __UNUSED;
static bool nrf52_errata_81(void) __UNUSED;
static bool nrf52_errata_83(void) __UNUSED;
static bool nrf52_errata_84(void) __UNUSED;
static bool nrf52_errata_86(void) __UNUSED;
static bool nrf52_errata_87(void) __UNUSED;
static bool nrf52_errata_88(void) __UNUSED;
static bool nrf52_errata_89(void) __UNUSED;
static bool nrf52_errata_91(void) __UNUSED;
static bool nrf52_errata_94(void) __UNUSED;
static bool nrf52_errata_96(void) __UNUSED;
static bool nrf52_errata_97(void) __UNUSED;
static bool nrf52_errata_98(void) __UNUSED;
static bool nrf52_errata_101(void) __UNUSED;
static bool nrf52_errata_102(void) __UNUSED;
static bool nrf52_errata_103(void) __UNUSED;
static bool nrf52_errata_104(void) __UNUSED;
static bool nrf52_errata_106(void) __UNUSED;
static bool nrf52_errata_107(void) __UNUSED;
static bool nrf52_errata_108(void) __UNUSED;
static bool nrf52_errata_109(void) __UNUSED;
static bool nrf52_errata_110(void) __UNUSED;
static bool nrf52_errata_111(void) __UNUSED;
static bool nrf52_errata_112(void) __UNUSED;
static bool nrf52_errata_113(void) __UNUSED;
static bool nrf52_errata_115(void) __UNUSED;
static bool nrf52_errata_116(void) __UNUSED;
static bool nrf52_errata_117(void) __UNUSED;
static bool nrf52_errata_118(void) __UNUSED;
static bool nrf52_errata_119(void) __UNUSED;
static bool nrf52_errata_120(void) __UNUSED;
static bool nrf52_errata_121(void) __UNUSED;
static bool nrf52_errata_122(void) __UNUSED;
static bool nrf52_errata_127(void) __UNUSED;
static bool nrf52_errata_128(void) __UNUSED;
static bool nrf52_errata_131(void) __UNUSED;
static bool nrf52_errata_132(void) __UNUSED;
static bool nrf52_errata_133(void) __UNUSED;
static bool nrf52_errata_134(void) __UNUSED;
static bool nrf52_errata_135(void) __UNUSED;
static bool nrf52_errata_136(void) __UNUSED;
static bool nrf52_errata_138(void) __UNUSED;
static bool nrf52_errata_140(void) __UNUSED;
static bool nrf52_errata_141(void) __UNUSED;
static bool nrf52_errata_142(void) __UNUSED;
static bool nrf52_errata_143(void) __UNUSED;
static bool nrf52_errata_144(void) __UNUSED;
static bool nrf52_errata_145(void) __UNUSED;
static bool nrf52_errata_146(void) __UNUSED;
static bool nrf52_errata_147(void) __UNUSED;
static bool nrf52_errata_149(void) __UNUSED;
static bool nrf52_errata_150(void) __UNUSED;
static bool nrf52_errata_151(void) __UNUSED;
static bool nrf52_errata_153(void) __UNUSED;
static bool nrf52_errata_154(void) __UNUSED;
static bool nrf52_errata_155(void) __UNUSED;
static bool nrf52_errata_156(void) __UNUSED;
static bool nrf52_errata_158(void) __UNUSED;
static bool nrf52_errata_160(void) __UNUSED;
static bool nrf52_errata_162(void) __UNUSED;
static bool nrf52_errata_163(void) __UNUSED;
static bool nrf52_errata_164(void) __UNUSED;
static bool nrf52_errata_166(void) __UNUSED;
static bool nrf52_errata_170(void) __UNUSED;
static bool nrf52_errata_171(void) __UNUSED;
static bool nrf52_errata_172(void) __UNUSED;
static bool nrf52_errata_173(void) __UNUSED;
static bool nrf52_errata_174(void) __UNUSED;
static bool nrf52_errata_176(void) __UNUSED;
static bool nrf52_errata_178(void) __UNUSED;
static bool nrf52_errata_179(void) __UNUSED;
static bool nrf52_errata_180(void) __UNUSED;
static bool nrf52_errata_181(void) __UNUSED;
static bool nrf52_errata_182(void) __UNUSED;
static bool nrf52_errata_183(void) __UNUSED;
static bool nrf52_errata_184(void) __UNUSED;
static bool nrf52_errata_186(void) __UNUSED;
static bool nrf52_errata_187(void) __UNUSED;
static bool nrf52_errata_189(void) __UNUSED;
static bool nrf52_errata_190(void) __UNUSED;
static bool nrf52_errata_191(void) __UNUSED;
static bool nrf52_errata_192(void) __UNUSED;
static bool nrf52_errata_193(void) __UNUSED;
static bool nrf52_errata_194(void) __UNUSED;
static bool nrf52_errata_195(void) __UNUSED;
static bool nrf52_errata_196(void) __UNUSED;
static bool nrf52_errata_197(void) __UNUSED;
static bool nrf52_errata_198(void) __UNUSED;
static bool nrf52_errata_199(void) __UNUSED;
static bool nrf52_errata_200(void) __UNUSED;
static bool nrf52_errata_201(void) __UNUSED;
static bool nrf52_errata_202(void) __UNUSED;
static bool nrf52_errata_204(void) __UNUSED;
static bool nrf52_errata_208(void) __UNUSED;
static bool nrf52_errata_209(void) __UNUSED;
static bool nrf52_errata_210(void) __UNUSED;
static bool nrf52_errata_211(void) __UNUSED;
static bool nrf52_errata_212(void) __UNUSED;
static bool nrf52_errata_213(void) __UNUSED;
static bool nrf52_errata_214(void) __UNUSED;
static bool nrf52_errata_215(void) __UNUSED;
static bool nrf52_errata_216(void) __UNUSED;
static bool nrf52_errata_217(void) __UNUSED;
static bool nrf52_errata_218(void) __UNUSED;
static bool nrf52_errata_219(void) __UNUSED;
static bool nrf52_errata_220(void) __UNUSED;
static bool nrf52_errata_223(void) __UNUSED;
static bool nrf52_errata_225(void) __UNUSED;
static bool nrf52_errata_228(void) __UNUSED;
static bool nrf52_errata_230(void) __UNUSED;
static bool nrf52_errata_231(void) __UNUSED;
static bool nrf52_errata_232(void) __UNUSED;
static bool nrf52_errata_233(void) __UNUSED;
static bool nrf52_errata_236(void) __UNUSED;
static bool nrf52_errata_237(void) __UNUSED;
static bool nrf52_errata_242(void) __UNUSED;
static bool nrf52_errata_243(void) __UNUSED;
static bool nrf52_errata_244(void) __UNUSED;
static bool nrf52_errata_245(void) __UNUSED;
static bool nrf52_errata_246(void) __UNUSED;
static bool nrf52_errata_248(void) __UNUSED;
static bool nrf52_configuration_249(void) __UNUSED;
static bool nrf52_errata_250(void) __UNUSED;
static bool nrf52_configuration_254(void) __UNUSED;
static bool nrf52_configuration_255(void) __UNUSED;
static bool nrf52_configuration_256(void) __UNUSED;
static bool nrf52_configuration_257(void) __UNUSED;

/* ========= Errata 1 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_1_PRESENT 1
#else
    #define NRF52_ERRATA_1_PRESENT 0
#endif

#ifndef NRF52_ERRATA_1_ENABLE_WORKAROUND
    #define NRF52_ERRATA_1_ENABLE_WORKAROUND NRF52_ERRATA_1_PRESENT
#endif

static bool nrf52_errata_1(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 2 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_2_PRESENT 1
#else
    #define NRF52_ERRATA_2_PRESENT 0
#endif

#ifndef NRF52_ERRATA_2_ENABLE_WORKAROUND
    #define NRF52_ERRATA_2_ENABLE_WORKAROUND NRF52_ERRATA_2_PRESENT
#endif

static bool nrf52_errata_2(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 3 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_3_PRESENT 1
#else
    #define NRF52_ERRATA_3_PRESENT 0
#endif

#ifndef NRF52_ERRATA_3_ENABLE_WORKAROUND
    #define NRF52_ERRATA_3_ENABLE_WORKAROUND NRF52_ERRATA_3_PRESENT
#endif

static bool nrf52_errata_3(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 4 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_4_PRESENT 1
#else
    #define NRF52_ERRATA_4_PRESENT 0
#endif

#ifndef NRF52_ERRATA_4_ENABLE_WORKAROUND
    #define NRF52_ERRATA_4_ENABLE_WORKAROUND NRF52_ERRATA_4_PRESENT
#endif

static bool nrf52_errata_4(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 7 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_7_PRESENT 1
#else
    #define NRF52_ERRATA_7_PRESENT 0
#endif

#ifndef NRF52_ERRATA_7_ENABLE_WORKAROUND
    #define NRF52_ERRATA_7_ENABLE_WORKAROUND NRF52_ERRATA_7_PRESENT
#endif

static bool nrf52_errata_7(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 8 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_8_PRESENT 1
#else
    #define NRF52_ERRATA_8_PRESENT 0
#endif

#ifndef NRF52_ERRATA_8_ENABLE_WORKAROUND
    #define NRF52_ERRATA_8_ENABLE_WORKAROUND NRF52_ERRATA_8_PRESENT
#endif

static bool nrf52_errata_8(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
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
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_9_PRESENT 1
#else
    #define NRF52_ERRATA_9_PRESENT 0
#endif

#ifndef NRF52_ERRATA_9_ENABLE_WORKAROUND
    #define NRF52_ERRATA_9_ENABLE_WORKAROUND NRF52_ERRATA_9_PRESENT
#endif

static bool nrf52_errata_9(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 10 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_10_PRESENT 1
#else
    #define NRF52_ERRATA_10_PRESENT 0
#endif

#ifndef NRF52_ERRATA_10_ENABLE_WORKAROUND
    #define NRF52_ERRATA_10_ENABLE_WORKAROUND NRF52_ERRATA_10_PRESENT
#endif

static bool nrf52_errata_10(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 11 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_11_PRESENT 1
#else
    #define NRF52_ERRATA_11_PRESENT 0
#endif

#ifndef NRF52_ERRATA_11_ENABLE_WORKAROUND
    #define NRF52_ERRATA_11_ENABLE_WORKAROUND NRF52_ERRATA_11_PRESENT
#endif

static bool nrf52_errata_11(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
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
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_12_PRESENT 1
#else
    #define NRF52_ERRATA_12_PRESENT 0
#endif

#ifndef NRF52_ERRATA_12_ENABLE_WORKAROUND
    #define NRF52_ERRATA_12_ENABLE_WORKAROUND NRF52_ERRATA_12_PRESENT
#endif

static bool nrf52_errata_12(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 15 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_15_PRESENT 1
#else
    #define NRF52_ERRATA_15_PRESENT 0
#endif

#ifndef NRF52_ERRATA_15_ENABLE_WORKAROUND
    #define NRF52_ERRATA_15_ENABLE_WORKAROUND NRF52_ERRATA_15_PRESENT
#endif

static bool nrf52_errata_15(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
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
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_16_PRESENT 1
#else
    #define NRF52_ERRATA_16_PRESENT 0
#endif

#ifndef NRF52_ERRATA_16_ENABLE_WORKAROUND
    #define NRF52_ERRATA_16_ENABLE_WORKAROUND NRF52_ERRATA_16_PRESENT
#endif

static bool nrf52_errata_16(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
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
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_17_PRESENT 1
#else
    #define NRF52_ERRATA_17_PRESENT 0
#endif

#ifndef NRF52_ERRATA_17_ENABLE_WORKAROUND
    #define NRF52_ERRATA_17_ENABLE_WORKAROUND NRF52_ERRATA_17_PRESENT
#endif

static bool nrf52_errata_17(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
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
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_20_PRESENT 1
#else
    #define NRF52_ERRATA_20_PRESENT 0
#endif

#ifndef NRF52_ERRATA_20_ENABLE_WORKAROUND
    #define NRF52_ERRATA_20_ENABLE_WORKAROUND NRF52_ERRATA_20_PRESENT
#endif

static bool nrf52_errata_20(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
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
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_23_PRESENT 1
#else
    #define NRF52_ERRATA_23_PRESENT 0
#endif

#ifndef NRF52_ERRATA_23_ENABLE_WORKAROUND
    #define NRF52_ERRATA_23_ENABLE_WORKAROUND NRF52_ERRATA_23_PRESENT
#endif

static bool nrf52_errata_23(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 24 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_24_PRESENT 1
#else
    #define NRF52_ERRATA_24_PRESENT 0
#endif

#ifndef NRF52_ERRATA_24_ENABLE_WORKAROUND
    #define NRF52_ERRATA_24_ENABLE_WORKAROUND NRF52_ERRATA_24_PRESENT
#endif

static bool nrf52_errata_24(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 25 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_25_PRESENT 1
#else
    #define NRF52_ERRATA_25_PRESENT 0
#endif

#ifndef NRF52_ERRATA_25_ENABLE_WORKAROUND
    #define NRF52_ERRATA_25_ENABLE_WORKAROUND NRF52_ERRATA_25_PRESENT
#endif

static bool nrf52_errata_25(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 26 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_26_PRESENT 1
#else
    #define NRF52_ERRATA_26_PRESENT 0
#endif

#ifndef NRF52_ERRATA_26_ENABLE_WORKAROUND
    #define NRF52_ERRATA_26_ENABLE_WORKAROUND NRF52_ERRATA_26_PRESENT
#endif

static bool nrf52_errata_26(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 27 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_27_PRESENT 1
#else
    #define NRF52_ERRATA_27_PRESENT 0
#endif

#ifndef NRF52_ERRATA_27_ENABLE_WORKAROUND
    #define NRF52_ERRATA_27_ENABLE_WORKAROUND NRF52_ERRATA_27_PRESENT
#endif

static bool nrf52_errata_27(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 28 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_28_PRESENT 1
#else
    #define NRF52_ERRATA_28_PRESENT 0
#endif

#ifndef NRF52_ERRATA_28_ENABLE_WORKAROUND
    #define NRF52_ERRATA_28_ENABLE_WORKAROUND NRF52_ERRATA_28_PRESENT
#endif

static bool nrf52_errata_28(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 29 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_29_PRESENT 1
#else
    #define NRF52_ERRATA_29_PRESENT 0
#endif

#ifndef NRF52_ERRATA_29_ENABLE_WORKAROUND
    #define NRF52_ERRATA_29_ENABLE_WORKAROUND NRF52_ERRATA_29_PRESENT
#endif

static bool nrf52_errata_29(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 30 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_30_PRESENT 1
#else
    #define NRF52_ERRATA_30_PRESENT 0
#endif

#ifndef NRF52_ERRATA_30_ENABLE_WORKAROUND
    #define NRF52_ERRATA_30_ENABLE_WORKAROUND NRF52_ERRATA_30_PRESENT
#endif

static bool nrf52_errata_30(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 31 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_31_PRESENT 1
#else
    #define NRF52_ERRATA_31_PRESENT 0
#endif

#ifndef NRF52_ERRATA_31_ENABLE_WORKAROUND
    #define NRF52_ERRATA_31_ENABLE_WORKAROUND NRF52_ERRATA_31_PRESENT
#endif

static bool nrf52_errata_31(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
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
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_32_PRESENT 1
#else
    #define NRF52_ERRATA_32_PRESENT 0
#endif

#ifndef NRF52_ERRATA_32_ENABLE_WORKAROUND
    #define NRF52_ERRATA_32_ENABLE_WORKAROUND NRF52_ERRATA_32_PRESENT
#endif

static bool nrf52_errata_32(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 33 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_33_PRESENT 1
#else
    #define NRF52_ERRATA_33_PRESENT 0
#endif

#ifndef NRF52_ERRATA_33_ENABLE_WORKAROUND
    #define NRF52_ERRATA_33_ENABLE_WORKAROUND NRF52_ERRATA_33_PRESENT
#endif

static bool nrf52_errata_33(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 34 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_34_PRESENT 1
#else
    #define NRF52_ERRATA_34_PRESENT 0
#endif

#ifndef NRF52_ERRATA_34_ENABLE_WORKAROUND
    #define NRF52_ERRATA_34_ENABLE_WORKAROUND NRF52_ERRATA_34_PRESENT
#endif

static bool nrf52_errata_34(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 35 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_35_PRESENT 1
#else
    #define NRF52_ERRATA_35_PRESENT 0
#endif

#ifndef NRF52_ERRATA_35_ENABLE_WORKAROUND
    #define NRF52_ERRATA_35_ENABLE_WORKAROUND NRF52_ERRATA_35_PRESENT
#endif

static bool nrf52_errata_35(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 36 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_36_PRESENT 1
#else
    #define NRF52_ERRATA_36_PRESENT 0
#endif

#ifndef NRF52_ERRATA_36_ENABLE_WORKAROUND
    #define NRF52_ERRATA_36_ENABLE_WORKAROUND NRF52_ERRATA_36_PRESENT
#endif

static bool nrf52_errata_36(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 37 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_37_PRESENT 1
#else
    #define NRF52_ERRATA_37_PRESENT 0
#endif

#ifndef NRF52_ERRATA_37_ENABLE_WORKAROUND
    #define NRF52_ERRATA_37_ENABLE_WORKAROUND NRF52_ERRATA_37_PRESENT
#endif

static bool nrf52_errata_37(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 38 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_38_PRESENT 1
#else
    #define NRF52_ERRATA_38_PRESENT 0
#endif

#ifndef NRF52_ERRATA_38_ENABLE_WORKAROUND
    #define NRF52_ERRATA_38_ENABLE_WORKAROUND NRF52_ERRATA_38_PRESENT
#endif

static bool nrf52_errata_38(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 39 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_39_PRESENT 1
#else
    #define NRF52_ERRATA_39_PRESENT 0
#endif

#ifndef NRF52_ERRATA_39_ENABLE_WORKAROUND
    #define NRF52_ERRATA_39_ENABLE_WORKAROUND NRF52_ERRATA_39_PRESENT
#endif

static bool nrf52_errata_39(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 40 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_40_PRESENT 1
#else
    #define NRF52_ERRATA_40_PRESENT 0
#endif

#ifndef NRF52_ERRATA_40_ENABLE_WORKAROUND
    #define NRF52_ERRATA_40_ENABLE_WORKAROUND NRF52_ERRATA_40_PRESENT
#endif

static bool nrf52_errata_40(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 41 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_41_PRESENT 1
#else
    #define NRF52_ERRATA_41_PRESENT 0
#endif

#ifndef NRF52_ERRATA_41_ENABLE_WORKAROUND
    #define NRF52_ERRATA_41_ENABLE_WORKAROUND NRF52_ERRATA_41_PRESENT
#endif

static bool nrf52_errata_41(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 42 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_42_PRESENT 1
#else
    #define NRF52_ERRATA_42_PRESENT 0
#endif

#ifndef NRF52_ERRATA_42_ENABLE_WORKAROUND
    #define NRF52_ERRATA_42_ENABLE_WORKAROUND NRF52_ERRATA_42_PRESENT
#endif

static bool nrf52_errata_42(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 43 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_43_PRESENT 1
#else
    #define NRF52_ERRATA_43_PRESENT 0
#endif

#ifndef NRF52_ERRATA_43_ENABLE_WORKAROUND
    #define NRF52_ERRATA_43_ENABLE_WORKAROUND NRF52_ERRATA_43_PRESENT
#endif

static bool nrf52_errata_43(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 44 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_44_PRESENT 1
#else
    #define NRF52_ERRATA_44_PRESENT 0
#endif

#ifndef NRF52_ERRATA_44_ENABLE_WORKAROUND
    #define NRF52_ERRATA_44_ENABLE_WORKAROUND NRF52_ERRATA_44_PRESENT
#endif

static bool nrf52_errata_44(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 46 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_46_PRESENT 1
#else
    #define NRF52_ERRATA_46_PRESENT 0
#endif

#ifndef NRF52_ERRATA_46_ENABLE_WORKAROUND
    #define NRF52_ERRATA_46_ENABLE_WORKAROUND NRF52_ERRATA_46_PRESENT
#endif

static bool nrf52_errata_46(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 47 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_47_PRESENT 1
#else
    #define NRF52_ERRATA_47_PRESENT 0
#endif

#ifndef NRF52_ERRATA_47_ENABLE_WORKAROUND
    #define NRF52_ERRATA_47_ENABLE_WORKAROUND NRF52_ERRATA_47_PRESENT
#endif

static bool nrf52_errata_47(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 48 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_48_PRESENT 1
#else
    #define NRF52_ERRATA_48_PRESENT 0
#endif

#ifndef NRF52_ERRATA_48_ENABLE_WORKAROUND
    #define NRF52_ERRATA_48_ENABLE_WORKAROUND NRF52_ERRATA_48_PRESENT
#endif

static bool nrf52_errata_48(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 49 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_49_PRESENT 1
#else
    #define NRF52_ERRATA_49_PRESENT 0
#endif

#ifndef NRF52_ERRATA_49_ENABLE_WORKAROUND
    #define NRF52_ERRATA_49_ENABLE_WORKAROUND NRF52_ERRATA_49_PRESENT
#endif

static bool nrf52_errata_49(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 51 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_51_PRESENT 1
#else
    #define NRF52_ERRATA_51_PRESENT 0
#endif

#ifndef NRF52_ERRATA_51_ENABLE_WORKAROUND
    #define NRF52_ERRATA_51_ENABLE_WORKAROUND NRF52_ERRATA_51_PRESENT
#endif

static bool nrf52_errata_51(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 54 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_54_PRESENT 1
#else
    #define NRF52_ERRATA_54_PRESENT 0
#endif

#ifndef NRF52_ERRATA_54_ENABLE_WORKAROUND
    #define NRF52_ERRATA_54_ENABLE_WORKAROUND NRF52_ERRATA_54_PRESENT
#endif

static bool nrf52_errata_54(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 55 ========= */
#if    defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_55_PRESENT 1
#else
    #define NRF52_ERRATA_55_PRESENT 0
#endif

#ifndef NRF52_ERRATA_55_ENABLE_WORKAROUND
    #define NRF52_ERRATA_55_ENABLE_WORKAROUND NRF52_ERRATA_55_PRESENT
#endif

static bool nrf52_errata_55(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    case 0x03ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 57 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_57_PRESENT 1
#else
    #define NRF52_ERRATA_57_PRESENT 0
#endif

#ifndef NRF52_ERRATA_57_ENABLE_WORKAROUND
    #define NRF52_ERRATA_57_ENABLE_WORKAROUND NRF52_ERRATA_57_PRESENT
#endif

static bool nrf52_errata_57(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 58 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_58_PRESENT 1
#else
    #define NRF52_ERRATA_58_PRESENT 0
#endif

#ifndef NRF52_ERRATA_58_ENABLE_WORKAROUND
    #define NRF52_ERRATA_58_ENABLE_WORKAROUND NRF52_ERRATA_58_PRESENT
#endif

static bool nrf52_errata_58(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 62 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_62_PRESENT 1
#else
    #define NRF52_ERRATA_62_PRESENT 0
#endif

#ifndef NRF52_ERRATA_62_ENABLE_WORKAROUND
    #define NRF52_ERRATA_62_ENABLE_WORKAROUND NRF52_ERRATA_62_PRESENT
#endif

static bool nrf52_errata_62(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 63 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_63_PRESENT 1
#else
    #define NRF52_ERRATA_63_PRESENT 0
#endif

#ifndef NRF52_ERRATA_63_ENABLE_WORKAROUND
    #define NRF52_ERRATA_63_ENABLE_WORKAROUND NRF52_ERRATA_63_PRESENT
#endif

static bool nrf52_errata_63(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 64 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_64_PRESENT 1
#else
    #define NRF52_ERRATA_64_PRESENT 0
#endif

#ifndef NRF52_ERRATA_64_ENABLE_WORKAROUND
    #define NRF52_ERRATA_64_ENABLE_WORKAROUND NRF52_ERRATA_64_PRESENT
#endif

static bool nrf52_errata_64(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 65 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_65_PRESENT 1
#else
    #define NRF52_ERRATA_65_PRESENT 0
#endif

#ifndef NRF52_ERRATA_65_ENABLE_WORKAROUND
    #define NRF52_ERRATA_65_ENABLE_WORKAROUND NRF52_ERRATA_65_PRESENT
#endif

static bool nrf52_errata_65(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 66 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_66_PRESENT 1
#else
    #define NRF52_ERRATA_66_PRESENT 0
#endif

#ifndef NRF52_ERRATA_66_ENABLE_WORKAROUND
    #define NRF52_ERRATA_66_ENABLE_WORKAROUND NRF52_ERRATA_66_PRESENT
#endif

static bool nrf52_errata_66(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 67 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_67_PRESENT 1
#else
    #define NRF52_ERRATA_67_PRESENT 0
#endif

#ifndef NRF52_ERRATA_67_ENABLE_WORKAROUND
    #define NRF52_ERRATA_67_ENABLE_WORKAROUND NRF52_ERRATA_67_PRESENT
#endif

static bool nrf52_errata_67(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 68 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_68_PRESENT 1
#else
    #define NRF52_ERRATA_68_PRESENT 0
#endif

#ifndef NRF52_ERRATA_68_ENABLE_WORKAROUND
    #define NRF52_ERRATA_68_ENABLE_WORKAROUND NRF52_ERRATA_68_PRESENT
#endif

static bool nrf52_errata_68(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 70 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_70_PRESENT 1
#else
    #define NRF52_ERRATA_70_PRESENT 0
#endif

#ifndef NRF52_ERRATA_70_ENABLE_WORKAROUND
    #define NRF52_ERRATA_70_ENABLE_WORKAROUND NRF52_ERRATA_70_PRESENT
#endif

static bool nrf52_errata_70(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 71 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_71_PRESENT 1
#else
    #define NRF52_ERRATA_71_PRESENT 0
#endif

#ifndef NRF52_ERRATA_71_ENABLE_WORKAROUND
    #define NRF52_ERRATA_71_ENABLE_WORKAROUND NRF52_ERRATA_71_PRESENT
#endif

static bool nrf52_errata_71(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 72 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_72_PRESENT 1
#else
    #define NRF52_ERRATA_72_PRESENT 0
#endif

#ifndef NRF52_ERRATA_72_ENABLE_WORKAROUND
    #define NRF52_ERRATA_72_ENABLE_WORKAROUND NRF52_ERRATA_72_PRESENT
#endif

static bool nrf52_errata_72(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 73 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_73_PRESENT 1
#else
    #define NRF52_ERRATA_73_PRESENT 0
#endif

#ifndef NRF52_ERRATA_73_ENABLE_WORKAROUND
    #define NRF52_ERRATA_73_ENABLE_WORKAROUND NRF52_ERRATA_73_PRESENT
#endif

static bool nrf52_errata_73(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
            uint32_t var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 74 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_74_PRESENT 1
#else
    #define NRF52_ERRATA_74_PRESENT 0
#endif

#ifndef NRF52_ERRATA_74_ENABLE_WORKAROUND
    #define NRF52_ERRATA_74_ENABLE_WORKAROUND NRF52_ERRATA_74_PRESENT
#endif

static bool nrf52_errata_74(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 75 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_75_PRESENT 1
#else
    #define NRF52_ERRATA_75_PRESENT 0
#endif

#ifndef NRF52_ERRATA_75_ENABLE_WORKAROUND
    #define NRF52_ERRATA_75_ENABLE_WORKAROUND NRF52_ERRATA_75_PRESENT
#endif

static bool nrf52_errata_75(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 76 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_76_PRESENT 1
#else
    #define NRF52_ERRATA_76_PRESENT 0
#endif

#ifndef NRF52_ERRATA_76_ENABLE_WORKAROUND
    #define NRF52_ERRATA_76_ENABLE_WORKAROUND NRF52_ERRATA_76_PRESENT
#endif

static bool nrf52_errata_76(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 77 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_77_PRESENT 1
#else
    #define NRF52_ERRATA_77_PRESENT 0
#endif

#ifndef NRF52_ERRATA_77_ENABLE_WORKAROUND
    #define NRF52_ERRATA_77_ENABLE_WORKAROUND NRF52_ERRATA_77_PRESENT
#endif

static bool nrf52_errata_77(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 78 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_78_PRESENT 1
#else
    #define NRF52_ERRATA_78_PRESENT 0
#endif

#ifndef NRF52_ERRATA_78_ENABLE_WORKAROUND
    #define NRF52_ERRATA_78_ENABLE_WORKAROUND NRF52_ERRATA_78_PRESENT
#endif

static bool nrf52_errata_78(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 79 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_79_PRESENT 1
#else
    #define NRF52_ERRATA_79_PRESENT 0
#endif

#ifndef NRF52_ERRATA_79_ENABLE_WORKAROUND
    #define NRF52_ERRATA_79_ENABLE_WORKAROUND NRF52_ERRATA_79_PRESENT
#endif

static bool nrf52_errata_79(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 81 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_81_PRESENT 1
#else
    #define NRF52_ERRATA_81_PRESENT 0
#endif

#ifndef NRF52_ERRATA_81_ENABLE_WORKAROUND
    #define NRF52_ERRATA_81_ENABLE_WORKAROUND NRF52_ERRATA_81_PRESENT
#endif

static bool nrf52_errata_81(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 83 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_83_PRESENT 1
#else
    #define NRF52_ERRATA_83_PRESENT 0
#endif

#ifndef NRF52_ERRATA_83_ENABLE_WORKAROUND
    #define NRF52_ERRATA_83_ENABLE_WORKAROUND NRF52_ERRATA_83_PRESENT
#endif

static bool nrf52_errata_83(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 84 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_84_PRESENT 1
#else
    #define NRF52_ERRATA_84_PRESENT 0
#endif

#ifndef NRF52_ERRATA_84_ENABLE_WORKAROUND
    #define NRF52_ERRATA_84_ENABLE_WORKAROUND NRF52_ERRATA_84_PRESENT
#endif

static bool nrf52_errata_84(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 86 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_86_PRESENT 1
#else
    #define NRF52_ERRATA_86_PRESENT 0
#endif

#ifndef NRF52_ERRATA_86_ENABLE_WORKAROUND
    #define NRF52_ERRATA_86_ENABLE_WORKAROUND NRF52_ERRATA_86_PRESENT
#endif

static bool nrf52_errata_86(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 87 ========= */
#if    defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_87_PRESENT 1
#else
    #define NRF52_ERRATA_87_PRESENT 0
#endif

#ifndef NRF52_ERRATA_87_ENABLE_WORKAROUND
    #define NRF52_ERRATA_87_ENABLE_WORKAROUND NRF52_ERRATA_87_PRESENT
#endif

static bool nrf52_errata_87(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    case 0x03ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 88 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_88_PRESENT 1
#else
    #define NRF52_ERRATA_88_PRESENT 0
#endif

#ifndef NRF52_ERRATA_88_ENABLE_WORKAROUND
    #define NRF52_ERRATA_88_ENABLE_WORKAROUND NRF52_ERRATA_88_PRESENT
#endif

static bool nrf52_errata_88(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 89 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_89_PRESENT 1
#else
    #define NRF52_ERRATA_89_PRESENT 0
#endif

#ifndef NRF52_ERRATA_89_ENABLE_WORKAROUND
    #define NRF52_ERRATA_89_ENABLE_WORKAROUND NRF52_ERRATA_89_PRESENT
#endif

static bool nrf52_errata_89(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 91 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_91_PRESENT 1
#else
    #define NRF52_ERRATA_91_PRESENT 0
#endif

#ifndef NRF52_ERRATA_91_ENABLE_WORKAROUND
    #define NRF52_ERRATA_91_ENABLE_WORKAROUND NRF52_ERRATA_91_PRESENT
#endif

static bool nrf52_errata_91(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 94 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_94_PRESENT 1
#else
    #define NRF52_ERRATA_94_PRESENT 0
#endif

#ifndef NRF52_ERRATA_94_ENABLE_WORKAROUND
    #define NRF52_ERRATA_94_ENABLE_WORKAROUND NRF52_ERRATA_94_PRESENT
#endif

static bool nrf52_errata_94(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 96 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_96_PRESENT 1
#else
    #define NRF52_ERRATA_96_PRESENT 0
#endif

#ifndef NRF52_ERRATA_96_ENABLE_WORKAROUND
    #define NRF52_ERRATA_96_ENABLE_WORKAROUND NRF52_ERRATA_96_PRESENT
#endif

static bool nrf52_errata_96(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 97 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_97_PRESENT 1
#else
    #define NRF52_ERRATA_97_PRESENT 0
#endif

#ifndef NRF52_ERRATA_97_ENABLE_WORKAROUND
    #define NRF52_ERRATA_97_ENABLE_WORKAROUND NRF52_ERRATA_97_PRESENT
#endif

static bool nrf52_errata_97(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 98 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_98_PRESENT 1
#else
    #define NRF52_ERRATA_98_PRESENT 0
#endif

#ifndef NRF52_ERRATA_98_ENABLE_WORKAROUND
    #define NRF52_ERRATA_98_ENABLE_WORKAROUND NRF52_ERRATA_98_PRESENT
#endif

static bool nrf52_errata_98(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 101 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_101_PRESENT 1
#else
    #define NRF52_ERRATA_101_PRESENT 0
#endif

#ifndef NRF52_ERRATA_101_ENABLE_WORKAROUND
    #define NRF52_ERRATA_101_ENABLE_WORKAROUND NRF52_ERRATA_101_PRESENT
#endif

static bool nrf52_errata_101(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 102 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_102_PRESENT 1
#else
    #define NRF52_ERRATA_102_PRESENT 0
#endif

#ifndef NRF52_ERRATA_102_ENABLE_WORKAROUND
    #define NRF52_ERRATA_102_ENABLE_WORKAROUND NRF52_ERRATA_102_PRESENT
#endif

static bool nrf52_errata_102(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 103 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_103_PRESENT 1
#else
    #define NRF52_ERRATA_103_PRESENT 0
#endif

#ifndef NRF52_ERRATA_103_ENABLE_WORKAROUND
    #define NRF52_ERRATA_103_ENABLE_WORKAROUND NRF52_ERRATA_103_PRESENT
#endif

static bool nrf52_errata_103(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 104 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_104_PRESENT 1
#else
    #define NRF52_ERRATA_104_PRESENT 0
#endif

#ifndef NRF52_ERRATA_104_ENABLE_WORKAROUND
    #define NRF52_ERRATA_104_ENABLE_WORKAROUND NRF52_ERRATA_104_PRESENT
#endif

static bool nrf52_errata_104(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 106 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_106_PRESENT 1
#else
    #define NRF52_ERRATA_106_PRESENT 0
#endif

#ifndef NRF52_ERRATA_106_ENABLE_WORKAROUND
    #define NRF52_ERRATA_106_ENABLE_WORKAROUND NRF52_ERRATA_106_PRESENT
#endif

static bool nrf52_errata_106(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 107 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_107_PRESENT 1
#else
    #define NRF52_ERRATA_107_PRESENT 0
#endif

#ifndef NRF52_ERRATA_107_ENABLE_WORKAROUND
    #define NRF52_ERRATA_107_ENABLE_WORKAROUND NRF52_ERRATA_107_PRESENT
#endif

static bool nrf52_errata_107(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 108 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_108_PRESENT 1
#else
    #define NRF52_ERRATA_108_PRESENT 0
#endif

#ifndef NRF52_ERRATA_108_ENABLE_WORKAROUND
    #define NRF52_ERRATA_108_ENABLE_WORKAROUND NRF52_ERRATA_108_PRESENT
#endif

static bool nrf52_errata_108(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 109 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_109_PRESENT 1
#else
    #define NRF52_ERRATA_109_PRESENT 0
#endif

#ifndef NRF52_ERRATA_109_ENABLE_WORKAROUND
    #define NRF52_ERRATA_109_ENABLE_WORKAROUND NRF52_ERRATA_109_PRESENT
#endif

static bool nrf52_errata_109(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 110 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_110_PRESENT 1
#else
    #define NRF52_ERRATA_110_PRESENT 0
#endif

#ifndef NRF52_ERRATA_110_ENABLE_WORKAROUND
    #define NRF52_ERRATA_110_ENABLE_WORKAROUND NRF52_ERRATA_110_PRESENT
#endif

static bool nrf52_errata_110(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 111 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_111_PRESENT 1
#else
    #define NRF52_ERRATA_111_PRESENT 0
#endif

#ifndef NRF52_ERRATA_111_ENABLE_WORKAROUND
    #define NRF52_ERRATA_111_ENABLE_WORKAROUND NRF52_ERRATA_111_PRESENT
#endif

static bool nrf52_errata_111(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 112 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_112_PRESENT 1
#else
    #define NRF52_ERRATA_112_PRESENT 0
#endif

#ifndef NRF52_ERRATA_112_ENABLE_WORKAROUND
    #define NRF52_ERRATA_112_ENABLE_WORKAROUND NRF52_ERRATA_112_PRESENT
#endif

static bool nrf52_errata_112(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 113 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_113_PRESENT 1
#else
    #define NRF52_ERRATA_113_PRESENT 0
#endif

#ifndef NRF52_ERRATA_113_ENABLE_WORKAROUND
    #define NRF52_ERRATA_113_ENABLE_WORKAROUND NRF52_ERRATA_113_PRESENT
#endif

static bool nrf52_errata_113(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 115 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_115_PRESENT 1
#else
    #define NRF52_ERRATA_115_PRESENT 0
#endif

#ifndef NRF52_ERRATA_115_ENABLE_WORKAROUND
    #define NRF52_ERRATA_115_ENABLE_WORKAROUND NRF52_ERRATA_115_PRESENT
#endif

static bool nrf52_errata_115(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 116 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_116_PRESENT 1
#else
    #define NRF52_ERRATA_116_PRESENT 0
#endif

#ifndef NRF52_ERRATA_116_ENABLE_WORKAROUND
    #define NRF52_ERRATA_116_ENABLE_WORKAROUND NRF52_ERRATA_116_PRESENT
#endif

static bool nrf52_errata_116(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 117 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_117_PRESENT 1
#else
    #define NRF52_ERRATA_117_PRESENT 0
#endif

#ifndef NRF52_ERRATA_117_ENABLE_WORKAROUND
    #define NRF52_ERRATA_117_ENABLE_WORKAROUND NRF52_ERRATA_117_PRESENT
#endif

static bool nrf52_errata_117(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 118 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_118_PRESENT 1
#else
    #define NRF52_ERRATA_118_PRESENT 0
#endif

#ifndef NRF52_ERRATA_118_ENABLE_WORKAROUND
    #define NRF52_ERRATA_118_ENABLE_WORKAROUND NRF52_ERRATA_118_PRESENT
#endif

static bool nrf52_errata_118(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 119 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_119_PRESENT 1
#else
    #define NRF52_ERRATA_119_PRESENT 0
#endif

#ifndef NRF52_ERRATA_119_ENABLE_WORKAROUND
    #define NRF52_ERRATA_119_ENABLE_WORKAROUND NRF52_ERRATA_119_PRESENT
#endif

static bool nrf52_errata_119(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 120 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_120_PRESENT 1
#else
    #define NRF52_ERRATA_120_PRESENT 0
#endif

#ifndef NRF52_ERRATA_120_ENABLE_WORKAROUND
    #define NRF52_ERRATA_120_ENABLE_WORKAROUND NRF52_ERRATA_120_PRESENT
#endif

static bool nrf52_errata_120(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 121 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_121_PRESENT 1
#else
    #define NRF52_ERRATA_121_PRESENT 0
#endif

#ifndef NRF52_ERRATA_121_ENABLE_WORKAROUND
    #define NRF52_ERRATA_121_ENABLE_WORKAROUND NRF52_ERRATA_121_PRESENT
#endif

static bool nrf52_errata_121(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 122 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_122_PRESENT 1
#else
    #define NRF52_ERRATA_122_PRESENT 0
#endif

#ifndef NRF52_ERRATA_122_ENABLE_WORKAROUND
    #define NRF52_ERRATA_122_ENABLE_WORKAROUND NRF52_ERRATA_122_PRESENT
#endif

static bool nrf52_errata_122(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        return false;
    #endif
}

/* ========= Errata 127 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_127_PRESENT 1
#else
    #define NRF52_ERRATA_127_PRESENT 0
#endif

#ifndef NRF52_ERRATA_127_ENABLE_WORKAROUND
    #define NRF52_ERRATA_127_ENABLE_WORKAROUND NRF52_ERRATA_127_PRESENT
#endif

static bool nrf52_errata_127(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 128 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_128_PRESENT 1
#else
    #define NRF52_ERRATA_128_PRESENT 0
#endif

#ifndef NRF52_ERRATA_128_ENABLE_WORKAROUND
    #define NRF52_ERRATA_128_ENABLE_WORKAROUND NRF52_ERRATA_128_PRESENT
#endif

static bool nrf52_errata_128(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 131 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_131_PRESENT 1
#else
    #define NRF52_ERRATA_131_PRESENT 0
#endif

#ifndef NRF52_ERRATA_131_ENABLE_WORKAROUND
    #define NRF52_ERRATA_131_ENABLE_WORKAROUND NRF52_ERRATA_131_PRESENT
#endif

static bool nrf52_errata_131(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 132 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_132_PRESENT 1
#else
    #define NRF52_ERRATA_132_PRESENT 0
#endif

#ifndef NRF52_ERRATA_132_ENABLE_WORKAROUND
    #define NRF52_ERRATA_132_ENABLE_WORKAROUND NRF52_ERRATA_132_PRESENT
#endif

static bool nrf52_errata_132(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 133 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_133_PRESENT 1
#else
    #define NRF52_ERRATA_133_PRESENT 0
#endif

#ifndef NRF52_ERRATA_133_ENABLE_WORKAROUND
    #define NRF52_ERRATA_133_ENABLE_WORKAROUND NRF52_ERRATA_133_PRESENT
#endif

static bool nrf52_errata_133(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 134 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_134_PRESENT 1
#else
    #define NRF52_ERRATA_134_PRESENT 0
#endif

#ifndef NRF52_ERRATA_134_ENABLE_WORKAROUND
    #define NRF52_ERRATA_134_ENABLE_WORKAROUND NRF52_ERRATA_134_PRESENT
#endif

static bool nrf52_errata_134(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 135 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_135_PRESENT 1
#else
    #define NRF52_ERRATA_135_PRESENT 0
#endif

#ifndef NRF52_ERRATA_135_ENABLE_WORKAROUND
    #define NRF52_ERRATA_135_ENABLE_WORKAROUND NRF52_ERRATA_135_PRESENT
#endif

static bool nrf52_errata_135(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 136 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_136_PRESENT 1
#else
    #define NRF52_ERRATA_136_PRESENT 0
#endif

#ifndef NRF52_ERRATA_136_ENABLE_WORKAROUND
    #define NRF52_ERRATA_136_ENABLE_WORKAROUND NRF52_ERRATA_136_PRESENT
#endif

static bool nrf52_errata_136(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 138 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_138_PRESENT 1
#else
    #define NRF52_ERRATA_138_PRESENT 0
#endif

#ifndef NRF52_ERRATA_138_ENABLE_WORKAROUND
    #define NRF52_ERRATA_138_ENABLE_WORKAROUND NRF52_ERRATA_138_PRESENT
#endif

static bool nrf52_errata_138(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 140 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_140_PRESENT 1
#else
    #define NRF52_ERRATA_140_PRESENT 0
#endif

#ifndef NRF52_ERRATA_140_ENABLE_WORKAROUND
    #define NRF52_ERRATA_140_ENABLE_WORKAROUND NRF52_ERRATA_140_PRESENT
#endif

static bool nrf52_errata_140(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 141 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_141_PRESENT 1
#else
    #define NRF52_ERRATA_141_PRESENT 0
#endif

#ifndef NRF52_ERRATA_141_ENABLE_WORKAROUND
    #define NRF52_ERRATA_141_ENABLE_WORKAROUND NRF52_ERRATA_141_PRESENT
#endif

static bool nrf52_errata_141(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 142 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_142_PRESENT 1
#else
    #define NRF52_ERRATA_142_PRESENT 0
#endif

#ifndef NRF52_ERRATA_142_ENABLE_WORKAROUND
    #define NRF52_ERRATA_142_ENABLE_WORKAROUND NRF52_ERRATA_142_PRESENT
#endif

static bool nrf52_errata_142(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 143 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_143_PRESENT 1
#else
    #define NRF52_ERRATA_143_PRESENT 0
#endif

#ifndef NRF52_ERRATA_143_ENABLE_WORKAROUND
    #define NRF52_ERRATA_143_ENABLE_WORKAROUND NRF52_ERRATA_143_PRESENT
#endif

static bool nrf52_errata_143(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 144 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_144_PRESENT 1
#else
    #define NRF52_ERRATA_144_PRESENT 0
#endif

#ifndef NRF52_ERRATA_144_ENABLE_WORKAROUND
    #define NRF52_ERRATA_144_ENABLE_WORKAROUND NRF52_ERRATA_144_PRESENT
#endif

static bool nrf52_errata_144(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 145 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_145_PRESENT 1
#else
    #define NRF52_ERRATA_145_PRESENT 0
#endif

#ifndef NRF52_ERRATA_145_ENABLE_WORKAROUND
    #define NRF52_ERRATA_145_ENABLE_WORKAROUND NRF52_ERRATA_145_PRESENT
#endif

static bool nrf52_errata_145(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 146 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_146_PRESENT 1
#else
    #define NRF52_ERRATA_146_PRESENT 0
#endif

#ifndef NRF52_ERRATA_146_ENABLE_WORKAROUND
    #define NRF52_ERRATA_146_ENABLE_WORKAROUND NRF52_ERRATA_146_PRESENT
#endif

static bool nrf52_errata_146(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 147 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_147_PRESENT 1
#else
    #define NRF52_ERRATA_147_PRESENT 0
#endif

#ifndef NRF52_ERRATA_147_ENABLE_WORKAROUND
    #define NRF52_ERRATA_147_ENABLE_WORKAROUND NRF52_ERRATA_147_PRESENT
#endif

static bool nrf52_errata_147(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 149 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_149_PRESENT 1
#else
    #define NRF52_ERRATA_149_PRESENT 0
#endif

#ifndef NRF52_ERRATA_149_ENABLE_WORKAROUND
    #define NRF52_ERRATA_149_ENABLE_WORKAROUND NRF52_ERRATA_149_PRESENT
#endif

static bool nrf52_errata_149(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 150 ========= */
#if    defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_150_PRESENT 1
#else
    #define NRF52_ERRATA_150_PRESENT 0
#endif

#ifndef NRF52_ERRATA_150_ENABLE_WORKAROUND
    #define NRF52_ERRATA_150_ENABLE_WORKAROUND NRF52_ERRATA_150_PRESENT
#endif

static bool nrf52_errata_150(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
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

/* ========= Errata 151 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_151_PRESENT 1
#else
    #define NRF52_ERRATA_151_PRESENT 0
#endif

#ifndef NRF52_ERRATA_151_ENABLE_WORKAROUND
    #define NRF52_ERRATA_151_ENABLE_WORKAROUND NRF52_ERRATA_151_PRESENT
#endif

static bool nrf52_errata_151(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 153 ========= */
#if    defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_153_PRESENT 1
#else
    #define NRF52_ERRATA_153_PRESENT 0
#endif

#ifndef NRF52_ERRATA_153_ENABLE_WORKAROUND
    #define NRF52_ERRATA_153_ENABLE_WORKAROUND NRF52_ERRATA_153_PRESENT
#endif

static bool nrf52_errata_153(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 154 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_154_PRESENT 1
#else
    #define NRF52_ERRATA_154_PRESENT 0
#endif

#ifndef NRF52_ERRATA_154_ENABLE_WORKAROUND
    #define NRF52_ERRATA_154_ENABLE_WORKAROUND NRF52_ERRATA_154_PRESENT
#endif

static bool nrf52_errata_154(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 155 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_155_PRESENT 1
#else
    #define NRF52_ERRATA_155_PRESENT 0
#endif

#ifndef NRF52_ERRATA_155_ENABLE_WORKAROUND
    #define NRF52_ERRATA_155_ENABLE_WORKAROUND NRF52_ERRATA_155_PRESENT
#endif

static bool nrf52_errata_155(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 156 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_156_PRESENT 1
#else
    #define NRF52_ERRATA_156_PRESENT 0
#endif

#ifndef NRF52_ERRATA_156_ENABLE_WORKAROUND
    #define NRF52_ERRATA_156_ENABLE_WORKAROUND NRF52_ERRATA_156_PRESENT
#endif

static bool nrf52_errata_156(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 158 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_158_PRESENT 1
#else
    #define NRF52_ERRATA_158_PRESENT 0
#endif

#ifndef NRF52_ERRATA_158_ENABLE_WORKAROUND
    #define NRF52_ERRATA_158_ENABLE_WORKAROUND NRF52_ERRATA_158_PRESENT
#endif

static bool nrf52_errata_158(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 160 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_160_PRESENT 1
#else
    #define NRF52_ERRATA_160_PRESENT 0
#endif

#ifndef NRF52_ERRATA_160_ENABLE_WORKAROUND
    #define NRF52_ERRATA_160_ENABLE_WORKAROUND NRF52_ERRATA_160_PRESENT
#endif

static bool nrf52_errata_160(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 162 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_162_PRESENT 1
#else
    #define NRF52_ERRATA_162_PRESENT 0
#endif

#ifndef NRF52_ERRATA_162_ENABLE_WORKAROUND
    #define NRF52_ERRATA_162_ENABLE_WORKAROUND NRF52_ERRATA_162_PRESENT
#endif

static bool nrf52_errata_162(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 163 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_163_PRESENT 1
#else
    #define NRF52_ERRATA_163_PRESENT 0
#endif

#ifndef NRF52_ERRATA_163_ENABLE_WORKAROUND
    #define NRF52_ERRATA_163_ENABLE_WORKAROUND NRF52_ERRATA_163_PRESENT
#endif

static bool nrf52_errata_163(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 164 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_164_PRESENT 1
#else
    #define NRF52_ERRATA_164_PRESENT 0
#endif

#ifndef NRF52_ERRATA_164_ENABLE_WORKAROUND
    #define NRF52_ERRATA_164_ENABLE_WORKAROUND NRF52_ERRATA_164_PRESENT
#endif

static bool nrf52_errata_164(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 166 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_166_PRESENT 1
#else
    #define NRF52_ERRATA_166_PRESENT 0
#endif

#ifndef NRF52_ERRATA_166_ENABLE_WORKAROUND
    #define NRF52_ERRATA_166_ENABLE_WORKAROUND NRF52_ERRATA_166_PRESENT
#endif

static bool nrf52_errata_166(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        return false;
    #endif
}

/* ========= Errata 170 ========= */
#if    defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_170_PRESENT 1
#else
    #define NRF52_ERRATA_170_PRESENT 0
#endif

#ifndef NRF52_ERRATA_170_ENABLE_WORKAROUND
    #define NRF52_ERRATA_170_ENABLE_WORKAROUND NRF52_ERRATA_170_PRESENT
#endif

static bool nrf52_errata_170(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    case 0x03ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 171 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_171_PRESENT 1
#else
    #define NRF52_ERRATA_171_PRESENT 0
#endif

#ifndef NRF52_ERRATA_171_ENABLE_WORKAROUND
    #define NRF52_ERRATA_171_ENABLE_WORKAROUND NRF52_ERRATA_171_PRESENT
#endif

static bool nrf52_errata_171(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        return false;
    #endif
}

/* ========= Errata 172 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_172_PRESENT 1
#else
    #define NRF52_ERRATA_172_PRESENT 0
#endif

#ifndef NRF52_ERRATA_172_ENABLE_WORKAROUND
    #define NRF52_ERRATA_172_ENABLE_WORKAROUND NRF52_ERRATA_172_PRESENT
#endif

static bool nrf52_errata_172(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
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
        return false;
    #endif
}

/* ========= Errata 173 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_173_PRESENT 1
#else
    #define NRF52_ERRATA_173_PRESENT 0
#endif

#ifndef NRF52_ERRATA_173_ENABLE_WORKAROUND
    #define NRF52_ERRATA_173_ENABLE_WORKAROUND NRF52_ERRATA_173_PRESENT
#endif

static bool nrf52_errata_173(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 174 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_174_PRESENT 1
#else
    #define NRF52_ERRATA_174_PRESENT 0
#endif

#ifndef NRF52_ERRATA_174_ENABLE_WORKAROUND
    #define NRF52_ERRATA_174_ENABLE_WORKAROUND NRF52_ERRATA_174_PRESENT
#endif

static bool nrf52_errata_174(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
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
        return false;
    #endif
}

/* ========= Errata 176 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_176_PRESENT 1
#else
    #define NRF52_ERRATA_176_PRESENT 0
#endif

#ifndef NRF52_ERRATA_176_ENABLE_WORKAROUND
    #define NRF52_ERRATA_176_ENABLE_WORKAROUND NRF52_ERRATA_176_PRESENT
#endif

static bool nrf52_errata_176(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 178 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_178_PRESENT 1
#else
    #define NRF52_ERRATA_178_PRESENT 0
#endif

#ifndef NRF52_ERRATA_178_ENABLE_WORKAROUND
    #define NRF52_ERRATA_178_ENABLE_WORKAROUND NRF52_ERRATA_178_PRESENT
#endif

static bool nrf52_errata_178(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 179 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_179_PRESENT 1
#else
    #define NRF52_ERRATA_179_PRESENT 0
#endif

#ifndef NRF52_ERRATA_179_ENABLE_WORKAROUND
    #define NRF52_ERRATA_179_ENABLE_WORKAROUND NRF52_ERRATA_179_PRESENT
#endif

static bool nrf52_errata_179(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 180 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_180_PRESENT 1
#else
    #define NRF52_ERRATA_180_PRESENT 0
#endif

#ifndef NRF52_ERRATA_180_ENABLE_WORKAROUND
    #define NRF52_ERRATA_180_ENABLE_WORKAROUND NRF52_ERRATA_180_PRESENT
#endif

static bool nrf52_errata_180(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 181 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_181_PRESENT 1
#else
    #define NRF52_ERRATA_181_PRESENT 0
#endif

#ifndef NRF52_ERRATA_181_ENABLE_WORKAROUND
    #define NRF52_ERRATA_181_ENABLE_WORKAROUND NRF52_ERRATA_181_PRESENT
#endif

static bool nrf52_errata_181(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 182 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_182_PRESENT 1
#else
    #define NRF52_ERRATA_182_PRESENT 0
#endif

#ifndef NRF52_ERRATA_182_ENABLE_WORKAROUND
    #define NRF52_ERRATA_182_ENABLE_WORKAROUND NRF52_ERRATA_182_PRESENT
#endif

static bool nrf52_errata_182(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 183 ========= */
#if    defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_183_PRESENT 1
#else
    #define NRF52_ERRATA_183_PRESENT 0
#endif

#ifndef NRF52_ERRATA_183_ENABLE_WORKAROUND
    #define NRF52_ERRATA_183_ENABLE_WORKAROUND NRF52_ERRATA_183_PRESENT
#endif

static bool nrf52_errata_183(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    case 0x03ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 184 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_184_PRESENT 1
#else
    #define NRF52_ERRATA_184_PRESENT 0
#endif

#ifndef NRF52_ERRATA_184_ENABLE_WORKAROUND
    #define NRF52_ERRATA_184_ENABLE_WORKAROUND NRF52_ERRATA_184_PRESENT
#endif

static bool nrf52_errata_184(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 186 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_186_PRESENT 1
#else
    #define NRF52_ERRATA_186_PRESENT 0
#endif

#ifndef NRF52_ERRATA_186_ENABLE_WORKAROUND
    #define NRF52_ERRATA_186_ENABLE_WORKAROUND NRF52_ERRATA_186_PRESENT
#endif

static bool nrf52_errata_186(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 187 ========= */
#if    defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_187_PRESENT 1
#else
    #define NRF52_ERRATA_187_PRESENT 0
#endif

#ifndef NRF52_ERRATA_187_ENABLE_WORKAROUND
    #define NRF52_ERRATA_187_ENABLE_WORKAROUND NRF52_ERRATA_187_PRESENT
#endif

static bool nrf52_errata_187(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 189 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_189_PRESENT 1
#else
    #define NRF52_ERRATA_189_PRESENT 0
#endif

#ifndef NRF52_ERRATA_189_ENABLE_WORKAROUND
    #define NRF52_ERRATA_189_ENABLE_WORKAROUND NRF52_ERRATA_189_PRESENT
#endif

static bool nrf52_errata_189(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 190 ========= */
#if    defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_190_PRESENT 1
#else
    #define NRF52_ERRATA_190_PRESENT 0
#endif

#ifndef NRF52_ERRATA_190_ENABLE_WORKAROUND
    #define NRF52_ERRATA_190_ENABLE_WORKAROUND NRF52_ERRATA_190_PRESENT
#endif

static bool nrf52_errata_190(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    case 0x03ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 191 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_191_PRESENT 1
#else
    #define NRF52_ERRATA_191_PRESENT 0
#endif

#ifndef NRF52_ERRATA_191_ENABLE_WORKAROUND
    #define NRF52_ERRATA_191_ENABLE_WORKAROUND NRF52_ERRATA_191_PRESENT
#endif

static bool nrf52_errata_191(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
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
        return false;
    #endif
}

/* ========= Errata 192 ========= */
#if    defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_192_PRESENT 1
#else
    #define NRF52_ERRATA_192_PRESENT 0
#endif

#ifndef NRF52_ERRATA_192_ENABLE_WORKAROUND
    #define NRF52_ERRATA_192_ENABLE_WORKAROUND NRF52_ERRATA_192_PRESENT
#endif

static bool nrf52_errata_192(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
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

/* ========= Errata 193 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_193_PRESENT 1
#else
    #define NRF52_ERRATA_193_PRESENT 0
#endif

#ifndef NRF52_ERRATA_193_ENABLE_WORKAROUND
    #define NRF52_ERRATA_193_ENABLE_WORKAROUND NRF52_ERRATA_193_PRESENT
#endif

static bool nrf52_errata_193(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
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
        return false;
    #endif
}

/* ========= Errata 194 ========= */
#if    defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_194_PRESENT 1
#else
    #define NRF52_ERRATA_194_PRESENT 0
#endif

#ifndef NRF52_ERRATA_194_ENABLE_WORKAROUND
    #define NRF52_ERRATA_194_ENABLE_WORKAROUND NRF52_ERRATA_194_PRESENT
#endif

static bool nrf52_errata_194(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    case 0x03ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 195 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_195_PRESENT 1
#else
    #define NRF52_ERRATA_195_PRESENT 0
#endif

#ifndef NRF52_ERRATA_195_ENABLE_WORKAROUND
    #define NRF52_ERRATA_195_ENABLE_WORKAROUND NRF52_ERRATA_195_PRESENT
#endif

static bool nrf52_errata_195(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
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
        return false;
    #endif
}

/* ========= Errata 196 ========= */
#if    defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_196_PRESENT 1
#else
    #define NRF52_ERRATA_196_PRESENT 0
#endif

#ifndef NRF52_ERRATA_196_ENABLE_WORKAROUND
    #define NRF52_ERRATA_196_ENABLE_WORKAROUND NRF52_ERRATA_196_PRESENT
#endif

static bool nrf52_errata_196(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    case 0x03ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 197 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_197_PRESENT 1
#else
    #define NRF52_ERRATA_197_PRESENT 0
#endif

#ifndef NRF52_ERRATA_197_ENABLE_WORKAROUND
    #define NRF52_ERRATA_197_ENABLE_WORKAROUND NRF52_ERRATA_197_PRESENT
#endif

static bool nrf52_errata_197(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 198 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_198_PRESENT 1
#else
    #define NRF52_ERRATA_198_PRESENT 0
#endif

#ifndef NRF52_ERRATA_198_ENABLE_WORKAROUND
    #define NRF52_ERRATA_198_ENABLE_WORKAROUND NRF52_ERRATA_198_PRESENT
#endif

static bool nrf52_errata_198(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
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
        return false;
    #endif
}

/* ========= Errata 199 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_199_PRESENT 1
#else
    #define NRF52_ERRATA_199_PRESENT 0
#endif

#ifndef NRF52_ERRATA_199_ENABLE_WORKAROUND
    #define NRF52_ERRATA_199_ENABLE_WORKAROUND NRF52_ERRATA_199_PRESENT
#endif

static bool nrf52_errata_199(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        return false;
    #endif
}

/* ========= Errata 200 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_200_PRESENT 1
#else
    #define NRF52_ERRATA_200_PRESENT 0
#endif

#ifndef NRF52_ERRATA_200_ENABLE_WORKAROUND
    #define NRF52_ERRATA_200_ENABLE_WORKAROUND NRF52_ERRATA_200_PRESENT
#endif

static bool nrf52_errata_200(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
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
        return false;
    #endif
}

/* ========= Errata 201 ========= */
#if    defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_201_PRESENT 1
#else
    #define NRF52_ERRATA_201_PRESENT 0
#endif

#ifndef NRF52_ERRATA_201_ENABLE_WORKAROUND
    #define NRF52_ERRATA_201_ENABLE_WORKAROUND NRF52_ERRATA_201_PRESENT
#endif

static bool nrf52_errata_201(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
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

/* ========= Errata 202 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_202_PRESENT 1
#else
    #define NRF52_ERRATA_202_PRESENT 0
#endif

#ifndef NRF52_ERRATA_202_ENABLE_WORKAROUND
    #define NRF52_ERRATA_202_ENABLE_WORKAROUND NRF52_ERRATA_202_PRESENT
#endif

static bool nrf52_errata_202(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
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
        return false;
    #endif
}

/* ========= Errata 204 ========= */
#if    defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_204_PRESENT 1
#else
    #define NRF52_ERRATA_204_PRESENT 0
#endif

#ifndef NRF52_ERRATA_204_ENABLE_WORKAROUND
    #define NRF52_ERRATA_204_ENABLE_WORKAROUND NRF52_ERRATA_204_PRESENT
#endif

static bool nrf52_errata_204(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
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

/* ========= Errata 208 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_208_PRESENT 1
#else
    #define NRF52_ERRATA_208_PRESENT 0
#endif

#ifndef NRF52_ERRATA_208_ENABLE_WORKAROUND
    #define NRF52_ERRATA_208_ENABLE_WORKAROUND NRF52_ERRATA_208_PRESENT
#endif

static bool nrf52_errata_208(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        return false;
    #endif
}

/* ========= Errata 209 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_209_PRESENT 1
#else
    #define NRF52_ERRATA_209_PRESENT 0
#endif

#ifndef NRF52_ERRATA_209_ENABLE_WORKAROUND
    #define NRF52_ERRATA_209_ENABLE_WORKAROUND NRF52_ERRATA_209_PRESENT
#endif

static bool nrf52_errata_209(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        return false;
    #endif
}

/* ========= Errata 210 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_210_PRESENT 1
#else
    #define NRF52_ERRATA_210_PRESENT 0
#endif

#ifndef NRF52_ERRATA_210_ENABLE_WORKAROUND
    #define NRF52_ERRATA_210_ENABLE_WORKAROUND NRF52_ERRATA_210_PRESENT
#endif

static bool nrf52_errata_210(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return false;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 211 ========= */
#if    defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_211_PRESENT 1
#else
    #define NRF52_ERRATA_211_PRESENT 0
#endif

#ifndef NRF52_ERRATA_211_ENABLE_WORKAROUND
    #define NRF52_ERRATA_211_ENABLE_WORKAROUND 0
#endif

static bool nrf52_errata_211(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 212 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_212_PRESENT 1
#else
    #define NRF52_ERRATA_212_PRESENT 0
#endif

#ifndef NRF52_ERRATA_212_ENABLE_WORKAROUND
    #define NRF52_ERRATA_212_ENABLE_WORKAROUND NRF52_ERRATA_212_PRESENT
#endif

static bool nrf52_errata_212(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    case 0x03ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 213 ========= */
#if    defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_213_PRESENT 1
#else
    #define NRF52_ERRATA_213_PRESENT 0
#endif

#ifndef NRF52_ERRATA_213_ENABLE_WORKAROUND
    #define NRF52_ERRATA_213_ENABLE_WORKAROUND NRF52_ERRATA_213_PRESENT
#endif

static bool nrf52_errata_213(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 214 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_214_PRESENT 1
#else
    #define NRF52_ERRATA_214_PRESENT 0
#endif

#ifndef NRF52_ERRATA_214_ENABLE_WORKAROUND
    #define NRF52_ERRATA_214_ENABLE_WORKAROUND NRF52_ERRATA_214_PRESENT
#endif

static bool nrf52_errata_214(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        return false;
    #endif
}

/* ========= Errata 215 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_215_PRESENT 1
#else
    #define NRF52_ERRATA_215_PRESENT 0
#endif

#ifndef NRF52_ERRATA_215_ENABLE_WORKAROUND
    #define NRF52_ERRATA_215_ENABLE_WORKAROUND NRF52_ERRATA_215_PRESENT
#endif

static bool nrf52_errata_215(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        return false;
    #endif
}

/* ========= Errata 216 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_216_PRESENT 1
#else
    #define NRF52_ERRATA_216_PRESENT 0
#endif

#ifndef NRF52_ERRATA_216_ENABLE_WORKAROUND
    #define NRF52_ERRATA_216_ENABLE_WORKAROUND NRF52_ERRATA_216_PRESENT
#endif

static bool nrf52_errata_216(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        return false;
    #endif
}

/* ========= Errata 217 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
    #define NRF52_ERRATA_217_PRESENT 1
#else
    #define NRF52_ERRATA_217_PRESENT 0
#endif

#ifndef NRF52_ERRATA_217_ENABLE_WORKAROUND
    #define NRF52_ERRATA_217_ENABLE_WORKAROUND NRF52_ERRATA_217_PRESENT
#endif

static bool nrf52_errata_217(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 218 ========= */
#if    defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_218_PRESENT 1
#else
    #define NRF52_ERRATA_218_PRESENT 0
#endif

#ifndef NRF52_ERRATA_218_ENABLE_WORKAROUND
    #define NRF52_ERRATA_218_ENABLE_WORKAROUND NRF52_ERRATA_218_PRESENT
#endif

static bool nrf52_errata_218(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return false;
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
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    case 0x03ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 219 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_219_PRESENT 1
#else
    #define NRF52_ERRATA_219_PRESENT 0
#endif

#ifndef NRF52_ERRATA_219_ENABLE_WORKAROUND
    #define NRF52_ERRATA_219_ENABLE_WORKAROUND NRF52_ERRATA_219_PRESENT
#endif

static bool nrf52_errata_219(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 220 ========= */
#if    defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
    #define NRF52_ERRATA_220_PRESENT 1
#else
    #define NRF52_ERRATA_220_PRESENT 0
#endif

#ifndef NRF52_ERRATA_220_ENABLE_WORKAROUND
    #define NRF52_ERRATA_220_ENABLE_WORKAROUND NRF52_ERRATA_220_PRESENT
#endif

static bool nrf52_errata_220(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 223 ========= */
#if    defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
    #define NRF52_ERRATA_223_PRESENT 1
#else
    #define NRF52_ERRATA_223_PRESENT 0
#endif

#ifndef NRF52_ERRATA_223_ENABLE_WORKAROUND
    #define NRF52_ERRATA_223_ENABLE_WORKAROUND NRF52_ERRATA_223_PRESENT
#endif

static bool nrf52_errata_223(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 225 ========= */
#if    defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
    #define NRF52_ERRATA_225_PRESENT 1
#else
    #define NRF52_ERRATA_225_PRESENT 0
#endif

#ifndef NRF52_ERRATA_225_ENABLE_WORKAROUND
    #define NRF52_ERRATA_225_ENABLE_WORKAROUND NRF52_ERRATA_225_PRESENT
#endif

static bool nrf52_errata_225(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 228 ========= */
#if    defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_228_PRESENT 1
#else
    #define NRF52_ERRATA_228_PRESENT 0
#endif

#ifndef NRF52_ERRATA_228_ENABLE_WORKAROUND
    #define NRF52_ERRATA_228_ENABLE_WORKAROUND NRF52_ERRATA_228_PRESENT
#endif

static bool nrf52_errata_228(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 230 ========= */
#if    defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
    #define NRF52_ERRATA_230_PRESENT 1
#else
    #define NRF52_ERRATA_230_PRESENT 0
#endif

#ifndef NRF52_ERRATA_230_ENABLE_WORKAROUND
    #define NRF52_ERRATA_230_ENABLE_WORKAROUND NRF52_ERRATA_230_PRESENT
#endif

static bool nrf52_errata_230(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
                    case 0x03ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 231 ========= */
#if    defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
    #define NRF52_ERRATA_231_PRESENT 1
#else
    #define NRF52_ERRATA_231_PRESENT 0
#endif

#ifndef NRF52_ERRATA_231_ENABLE_WORKAROUND
    #define NRF52_ERRATA_231_ENABLE_WORKAROUND NRF52_ERRATA_231_PRESENT
#endif

static bool nrf52_errata_231(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
                    case 0x03ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 232 ========= */
#if    defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
    #define NRF52_ERRATA_232_PRESENT 1
#else
    #define NRF52_ERRATA_232_PRESENT 0
#endif

#ifndef NRF52_ERRATA_232_ENABLE_WORKAROUND
    #define NRF52_ERRATA_232_ENABLE_WORKAROUND NRF52_ERRATA_232_PRESENT
#endif

static bool nrf52_errata_232(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 233 ========= */
#if    defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_233_PRESENT 1
#else
    #define NRF52_ERRATA_233_PRESENT 0
#endif

#ifndef NRF52_ERRATA_233_ENABLE_WORKAROUND
    #define NRF52_ERRATA_233_ENABLE_WORKAROUND NRF52_ERRATA_233_PRESENT
#endif

static bool nrf52_errata_233(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 236 ========= */
#if    defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_236_PRESENT 1
#else
    #define NRF52_ERRATA_236_PRESENT 0
#endif

#ifndef NRF52_ERRATA_236_ENABLE_WORKAROUND
    #define NRF52_ERRATA_236_ENABLE_WORKAROUND NRF52_ERRATA_236_PRESENT
#endif

static bool nrf52_errata_236(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    case 0x03ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 237 ========= */
#if    defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_237_PRESENT 1
#else
    #define NRF52_ERRATA_237_PRESENT 0
#endif

#ifndef NRF52_ERRATA_237_ENABLE_WORKAROUND
    #define NRF52_ERRATA_237_ENABLE_WORKAROUND NRF52_ERRATA_237_PRESENT
#endif

static bool nrf52_errata_237(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    case 0x03ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 242 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_242_PRESENT 1
#else
    #define NRF52_ERRATA_242_PRESENT 0
#endif

#ifndef NRF52_ERRATA_242_ENABLE_WORKAROUND
    #define NRF52_ERRATA_242_ENABLE_WORKAROUND NRF52_ERRATA_242_PRESENT
#endif

static bool nrf52_errata_242(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 243 ========= */
#if    defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_243_PRESENT 1
#else
    #define NRF52_ERRATA_243_PRESENT 0
#endif

#ifndef NRF52_ERRATA_243_ENABLE_WORKAROUND
    #define NRF52_ERRATA_243_ENABLE_WORKAROUND NRF52_ERRATA_243_PRESENT
#endif

static bool nrf52_errata_243(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 244 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_244_PRESENT 1
#else
    #define NRF52_ERRATA_244_PRESENT 0
#endif

#ifndef NRF52_ERRATA_244_ENABLE_WORKAROUND
    #define NRF52_ERRATA_244_ENABLE_WORKAROUND NRF52_ERRATA_244_PRESENT
#endif

static bool nrf52_errata_244(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        return false;
    #endif
}

/* ========= Errata 245 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_245_PRESENT 1
#else
    #define NRF52_ERRATA_245_PRESENT 0
#endif

#ifndef NRF52_ERRATA_245_ENABLE_WORKAROUND
    #define NRF52_ERRATA_245_ENABLE_WORKAROUND 0
#endif

static bool nrf52_errata_245(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            uint32_t var1;
            uint32_t var2;

            if (*(uint32_t *)0x10000130ul == 0xFFFFFFFF)
            {
                var1 = ((*(uint32_t *)0xF0000FE0ul) & 0x000000FFul);
                var2 = ((*(uint32_t *)0xF0000FE8ul) & 0x000000F0ul) >> 4;
            }
            else
            {
                var1 = *(uint32_t *)0x10000130ul;
                var2 = *(uint32_t *)0x10000134ul;
            }
        #elif defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return true;
                    case 0x04ul:
                        return true;
                    case 0x05ul:
                        return true;
                    case 0x06ul:
                        return true;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 246 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_246_PRESENT 1
#else
    #define NRF52_ERRATA_246_PRESENT 0
#endif

#ifndef NRF52_ERRATA_246_ENABLE_WORKAROUND
    #define NRF52_ERRATA_246_ENABLE_WORKAROUND NRF52_ERRATA_246_PRESENT
#endif

static bool nrf52_errata_246(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 248 ========= */
#if    defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_ERRATA_248_PRESENT 1
#else
    #define NRF52_ERRATA_248_PRESENT 0
#endif

#ifndef NRF52_ERRATA_248_ENABLE_WORKAROUND
    #define NRF52_ERRATA_248_ENABLE_WORKAROUND NRF52_ERRATA_248_PRESENT
#endif

static bool nrf52_errata_248(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
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
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return false;
                    default:
                        return false;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 249 ========= */
#if    defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805) \
    || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810) \
    || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811) \
    || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833) \
    || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_CONFIGURATION_249_PRESENT 1
#else
    #define NRF52_CONFIGURATION_249_PRESENT 0
#endif

#ifndef NRF52_CONFIGURATION_249_ENABLE
    #define NRF52_CONFIGURATION_249_ENABLE NRF52_CONFIGURATION_249_PRESENT
#endif

static bool nrf52_configuration_249(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)\
         || defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)\
         || defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)\
         || defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)\
         || defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52832_XXAA) || defined (DEVELOP_IN_NRF52832)\
         || defined (NRF52832_XXAB) || defined (DEVELOP_IN_NRF52832)
            if (var1 == 0x06)
            {
                switch(var2)
                {
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return false;
                    case 0x06ul:
                        return false;
                    case 0x07ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52810_XXAA) || defined (DEVELOP_IN_NRF52810)
            if (var1 == 0x0A)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52805_XXAA) || defined (DEVELOP_IN_NRF52805)
            if (var1 == 0x0F)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 250 ========= */
#if    defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820) \
    || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
    #define NRF52_ERRATA_250_PRESENT 1
#else
    #define NRF52_ERRATA_250_PRESENT 0
#endif

#ifndef NRF52_ERRATA_250_ENABLE_WORKAROUND
    #define NRF52_ERRATA_250_ENABLE_WORKAROUND NRF52_ERRATA_250_PRESENT
#endif

static bool nrf52_errata_250(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)\
         || defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return true;
                    case 0x01ul:
                        return true;
                    case 0x02ul:
                        return true;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 254 ========= */
#if    defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
    #define NRF52_CONFIGURATION_254_PRESENT 1
#else
    #define NRF52_CONFIGURATION_254_PRESENT 0
#endif

#ifndef NRF52_CONFIGURATION_254_ENABLE
    #define NRF52_CONFIGURATION_254_ENABLE NRF52_CONFIGURATION_254_PRESENT
#endif

static bool nrf52_configuration_254(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52840_XXAA) || defined (DEVELOP_IN_NRF52840)
            if (var1 == 0x08)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
                    case 0x03ul:
                        return false;
                    case 0x04ul:
                        return false;
                    case 0x05ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 255 ========= */
#if    defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
    #define NRF52_CONFIGURATION_255_PRESENT 1
#else
    #define NRF52_CONFIGURATION_255_PRESENT 0
#endif

#ifndef NRF52_CONFIGURATION_255_ENABLE
    #define NRF52_CONFIGURATION_255_ENABLE NRF52_CONFIGURATION_255_PRESENT
#endif

static bool nrf52_configuration_255(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52833_XXAA) || defined (DEVELOP_IN_NRF52833)
            if (var1 == 0x0D)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
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

/* ========= Errata 256 ========= */
#if    defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
    #define NRF52_CONFIGURATION_256_PRESENT 1
#else
    #define NRF52_CONFIGURATION_256_PRESENT 0
#endif

#ifndef NRF52_CONFIGURATION_256_ENABLE
    #define NRF52_CONFIGURATION_256_ENABLE NRF52_CONFIGURATION_256_PRESENT
#endif

static bool nrf52_configuration_256(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52820_XXAA) || defined (DEVELOP_IN_NRF52820)
            if (var1 == 0x10)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return false;
                    case 0x02ul:
                        return false;
                    case 0x03ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

/* ========= Errata 257 ========= */
#if    defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
    #define NRF52_CONFIGURATION_257_PRESENT 1
#else
    #define NRF52_CONFIGURATION_257_PRESENT 0
#endif

#ifndef NRF52_CONFIGURATION_257_ENABLE
    #define NRF52_CONFIGURATION_257_ENABLE NRF52_CONFIGURATION_257_PRESENT
#endif

static bool nrf52_configuration_257(void)
{
    #ifndef NRF52_SERIES
        return false;
    #else
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            uint32_t var1 = *(uint32_t *)0x10000130ul;
            uint32_t var2 = *(uint32_t *)0x10000134ul;
        #endif
        #if defined (NRF52811_XXAA) || defined (DEVELOP_IN_NRF52811)
            if (var1 == 0x0E)
            {
                switch(var2)
                {
                    case 0x00ul:
                        return false;
                    case 0x01ul:
                        return true;
                    default:
                        return true;
                }
            }
        #endif
        return false;
    #endif
}

#endif /* NRF52_ERRATAS_H */
