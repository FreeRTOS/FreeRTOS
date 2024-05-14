/** @file het.c
 *   @brief HET Driver Implementation File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 */

/*
 * Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#include "het.h"
#include "sys_vim.h"
/* USER CODE BEGIN (0) */
/* USER CODE END */

/*----------------------------------------------------------------------------*/
/* Global variables                                                           */

static const uint32 s_het1pwmPolarity[ 8U ] = {
    3U, 3U, 3U, 3U, 3U, 3U, 3U, 3U,
};

static const uint32 s_het2pwmPolarity[ 8U ] = {
    3U, 3U, 3U, 3U, 3U, 3U, 3U, 3U,
};

/*----------------------------------------------------------------------------*/
/* Default Program                                                            */

/** @var static const hetINSTRUCTION_t het1PROGRAM[58]
 *   @brief Default Program
 *
 *   Het program running after initialization.
 */

static const hetINSTRUCTION_t het1PROGRAM[ 58U ] = {
    /* CNT: Timebase
     *       - Instruction                  = 0
     *       - Next instruction             = 1
     *       - Conditional next instruction = na
     *       - Interrupt                    = na
     *       - Pin                          = na
     *       - Reg                          = T
     */
    { /* Program */
      0x00002C80U,
      /* Control */
      0x01FFFFFFU,
      /* Data */
      0xFFFFFF80U,
      /* Reserved */
      0x00000000U },

    /* PWCNT: PWM 0 -> Duty Cycle
     *         - Instruction                  = 1
     *         - Next instruction             = 2
     *         - Conditional next instruction = 2
     *         - Interrupt                    = 1
     *         - Pin                          = 8
     */
    { /* Program */
      0x000055C0U,
      /* Control */
      ( 0x00004006U | ( uint32 ) ( ( uint32 ) 8U << 8U )
        | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* DJZ: PWM 0 -> Period
     *         - Instruction                  = 2
     *         - Next instruction             = 3
     *         - Conditional next instruction = 41
     *         - Interrupt                    = 2
     *         - Pin                          = na
     */
    { /* Program */
      0x00007480U,
      /* Control */
      0x00052006U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PWCNT: PWM 1 -> Duty Cycle
     *         - Instruction                  = 3
     *         - Next instruction             = 4
     *         - Conditional next instruction = 4
     *         - Interrupt                    = 3
     *         - Pin                          = 10
     */
    { /* Program */
      0x000095C0U,
      /* Control */
      ( 0x00008006U | ( uint32 ) ( ( uint32 ) 10U << 8U )
        | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* DJZ: PWM 1 -> Period
     *         - Instruction                  = 4
     *         - Next instruction             = 5
     *         - Conditional next instruction = 43
     *         - Interrupt                    = 4
     *         - Pin                          = na
     */
    { /* Program */
      0x0000B480U,
      /* Control */
      0x00056006U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PWCNT: PWM 2 -> Duty Cycle
     *         - Instruction                  = 5
     *         - Next instruction             = 6
     *         - Conditional next instruction = 6
     *         - Interrupt                    = 5
     *         - Pin                          = 12
     */
    { /* Program */
      0x0000D5C0U,
      /* Control */
      ( 0x0000C006U | ( uint32 ) ( ( uint32 ) 12U << 8U )
        | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* DJZ: PWM 2 -> Period
     *         - Instruction                  = 6
     *         - Next instruction             = 7
     *         - Conditional next instruction = 45
     *         - Interrupt                    = 6
     *         - Pin                          = na
     */
    { /* Program */
      0x0000F480U,
      /* Control */
      0x0005A006U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PWCNT: PWM 3 -> Duty Cycle
     *         - Instruction                  = 7
     *         - Next instruction             = 8
     *         - Conditional next instruction = 8
     *         - Interrupt                    = 7
     *         - Pin                          = 14
     */
    { /* Program */
      0x000115C0U,
      /* Control */
      ( 0x00010006U | ( uint32 ) ( ( uint32 ) 14U << 8U )
        | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* DJZ: PWM 3 -> Period
     *         - Instruction                  = 8
     *         - Next instruction             = 9
     *         - Conditional next instruction = 47
     *         - Interrupt                    = 8
     *         - Pin                          = na
     */
    { /* Program */
      0x00013480U,
      /* Control */
      0x0005E006U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PWCNT: PWM 4 -> Duty Cycle
     *         - Instruction                  = 9
     *         - Next instruction             = 10
     *         - Conditional next instruction = 10
     *         - Interrupt                    = 9
     *         - Pin                          = 16
     */
    { /* Program */
      0x000155C0U,
      /* Control */
      ( 0x00014006U | ( uint32 ) ( ( uint32 ) 16U << 8U )
        | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* DJZ: PWM 4 -> Period
     *         - Instruction                  = 10
     *         - Next instruction             = 11
     *         - Conditional next instruction = 49
     *         - Interrupt                    = 10
     *         - Pin                          = na
     */
    { /* Program */
      0x00017480U,
      /* Control */
      0x00062006U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PWCNT: PWM 5 -> Duty Cycle
     *         - Instruction                  = 11
     *         - Next instruction             = 12
     *         - Conditional next instruction = 12
     *         - Interrupt                    = 11
     *         - Pin                          = 17
     */
    { /* Program */
      0x000195C0U,
      /* Control */
      ( 0x00018006U | ( uint32 ) ( ( uint32 ) 17U << 8U )
        | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* DJZ: PWM 5 -> Period
     *         - Instruction                  = 12
     *         - Next instruction             = 13
     *         - Conditional next instruction = 51
     *         - Interrupt                    = 12
     *         - Pin                          = na
     */
    { /* Program */
      0x0001B480U,
      /* Control */
      0x00066006U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PWCNT: PWM 6 -> Duty Cycle
     *         - Instruction                  = 13
     *         - Next instruction             = 14
     *         - Conditional next instruction = 14
     *         - Interrupt                    = 13
     *         - Pin                          = 18
     */
    { /* Program */
      0x0001D5C0U,
      /* Control */
      ( 0x0001C006U | ( uint32 ) ( ( uint32 ) 18U << 8U )
        | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* DJZ: PWM 6 -> Period
     *         - Instruction                  = 14
     *         - Next instruction             = 15
     *         - Conditional next instruction = 53
     *         - Interrupt                    = 14
     *         - Pin                          = na
     */
    { /* Program */
      0x0001F480U,
      /* Control */
      0x0006A006U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PWCNT: PWM 7 -> Duty Cycle
     *         - Instruction                  = 15
     *         - Next instruction             = 16
     *         - Conditional next instruction = 16
     *         - Interrupt                    = 15
     *         - Pin                          = 19
     */
    { /* Program */
      0x000215C0U,
      /* Control */
      ( 0x00020006U | ( uint32 ) ( ( uint32 ) 19U << 8U )
        | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* DJZ: PWM 7 -> Period
     *         - Instruction                  = 16
     *         - Next instruction             = 17
     *         - Conditional next instruction = 55
     *         - Interrupt                    = 16
     *         - Pin                          = na
     */
    { /* Program */
      0x00023480U,
      /* Control */
      0x0006E006U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* ECNT: CCU Edge 0
     *         - Instruction                  = 17
     *         - Next instruction             = 18
     *         - Conditional next instruction = 18
     *         - Interrupt                    = 17
     *         - Pin                          = 9
     */
    { /* Program */
      0x00025440U,
      /* Control */
      ( 0x00024007U | ( uint32 ) ( ( uint32 ) 9U << 8U )
        | ( uint32 ) ( ( uint32 ) 1U << 4U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* ECNT: CCU Edge 1
     *         - Instruction                  = 18
     *         - Next instruction             = 19
     *         - Conditional next instruction = 19
     *         - Interrupt                    = 18
     *         - Pin                          = 11
     */
    { /* Program */
      0x00027440U,
      /* Control */
      ( 0x00026007U | ( uint32 ) ( ( uint32 ) 11U << 8U )
        | ( uint32 ) ( ( uint32 ) 1U << 4U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* ECNT: CCU Edge 2
     *         - Instruction                  = 19
     *         - Next instruction             = 20
     *         - Conditional next instruction = 20
     *         - Interrupt                    = 19
     *         - Pin                          = 13
     */
    { /* Program */
      0x00029440U,
      /* Control */
      ( 0x00028007U | ( uint32 ) ( ( uint32 ) 13U << 8U )
        | ( uint32 ) ( ( uint32 ) 1U << 4U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* ECNT: CCU Edge 3
     *         - Instruction                  = 20
     *         - Next instruction             = 21
     *         - Conditional next instruction = 21
     *         - Interrupt                    = 20
     *         - Pin                          = 15
     */
    { /* Program */
      0x0002B440U,
      /* Control */
      ( 0x0002A007U | ( uint32 ) ( ( uint32 ) 15U << 8U )
        | ( uint32 ) ( ( uint32 ) 1U << 4U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* ECNT: CCU Edge 4
     *         - Instruction                  = 21
     *         - Next instruction             = 22
     *         - Conditional next instruction = 22
     *         - Interrupt                    = 21
     *         - Pin                          = 20
     */
    { /* Program */
      0x0002D440U,
      /* Control */
      ( 0x0002C007U | ( uint32 ) ( ( uint32 ) 20U << 8U )
        | ( uint32 ) ( ( uint32 ) 1U << 4U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* ECNT: CCU Edge 5
     *         - Instruction                  = 22
     *         - Next instruction             = 23
     *         - Conditional next instruction = 23
     *         - Interrupt                    = 22
     *         - Pin                          = 21
     */
    { /* Program */
      0x0002F440U,
      /* Control */
      ( 0x0002E007U | ( uint32 ) ( ( uint32 ) 21U << 8U )
        | ( uint32 ) ( ( uint32 ) 1U << 4U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* ECNT: CCU Edge 6
     *         - Instruction                  = 23
     *         - Next instruction             = 24
     *         - Conditional next instruction = 24
     *         - Interrupt                    = 23
     *         - Pin                          = 22
     */
    { /* Program */
      0x00031440U,
      /* Control */
      ( 0x00030007U | ( uint32 ) ( ( uint32 ) 22U << 8U )
        | ( uint32 ) ( ( uint32 ) 1U << 4U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* ECNT: CCU Edge 7
     *         - Instruction                  = 24
     *         - Next instruction             = 25
     *         - Conditional next instruction = 25
     *         - Interrupt                    = 24
     *         - Pin                          = 23
     */
    { /* Program */
      0x00033440U,
      /* Control */
      ( 0x00032007U | ( uint32 ) ( ( uint32 ) 23U << 8U )
        | ( uint32 ) ( ( uint32 ) 1U << 4U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Duty 0
     *         - Instruction                  = 25
     *         - Next instruction             = 26
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 0
     */
    { /* Program */
      0x00034E00U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( 0U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Period 0
     *         - Instruction                  = 26
     *         - Next instruction             = 27
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 0  + 1
     */
    { /* Program */
      0x00036E80U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( 0U ) + 1U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Duty 1
     *         - Instruction                  = 27
     *         - Next instruction             = 28
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 2
     */
    { /* Program */
      0x00038E00U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( 2U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Period 1
     *         - Instruction                  = 28
     *         - Next instruction             = 29
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 2  + 1
     */
    { /* Program */
      0x0003AE80U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( 2U ) + 1U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Duty 2
     *         - Instruction                  = 29
     *         - Next instruction             = 30
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 4
     */
    { /* Program */
      0x0003CE00U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( 4U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Period 2
     *         - Instruction                  = 30
     *         - Next instruction             = 31
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 4  + 1
     */
    { /* Program */
      0x0003EE80U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( 4U ) + 1U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Duty 3
     *         - Instruction                  = 31
     *         - Next instruction             = 32
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 6
     */
    { /* Program */
      0x00040E00U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( 6U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Period 3
     *         - Instruction                  = 32
     *         - Next instruction             = 33
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 6  + 1
     */
    { /* Program */
      0x00042E80U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( 6U ) + 1U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Duty 4
     *         - Instruction                  = 33
     *         - Next instruction             = 34
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 24
     */
    { /* Program */
      0x00044E00U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( 24U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Period 4
     *         - Instruction                  = 34
     *         - Next instruction             = 35
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 24  + 1
     */
    { /* Program */
      0x00046E80U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( 24U ) + 1U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Duty 5
     *         - Instruction                  = 35
     *         - Next instruction             = 36
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 26
     */
    { /* Program */
      0x00048E00U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( 26U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Period 5
     *         - Instruction                  = 36
     *         - Next instruction             = 37
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 26  + 1
     */
    { /* Program */
      0x0004AE80U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( 26U ) + 1U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Duty 6
     *         - Instruction                  = 37
     *         - Next instruction             = 38
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 28
     */
    { /* Program */
      0x0004CE00U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( 28U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Period 6
     *         - Instruction                  = 38
     *         - Next instruction             = 39
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 28  + 1
     */
    { /* Program */
      0x0004EE80U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( 28U ) + 1U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Duty 7
     *         - Instruction                  = 39
     *         - Next instruction             = 40
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 30
     */
    { /* Program */
      0x00050E00U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( 30U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Period 7
     *         - Instruction                  = 40
     *         - Next instruction             = 57
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 30  + 1
     */
    { /* Program */
      0x00072E80U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( 30U ) + 1U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 0 -> Duty Cycle Update
     *         - Instruction                  = 41
     *         - Next instruction             = 42
     *         - Conditional next instruction = 2
     *         - Interrupt                    = 1
     *         - Pin                          = 8
     */
    { /* Program */
      0x00054201U,
      /* Control */
      ( 0x00004007U | ( uint32 ) ( ( uint32 ) 0U << 22U )
        | ( uint32 ) ( ( uint32 ) 8U << 8U ) | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      55296U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 0 -> Period Update
     *         - Instruction                  = 42
     *         - Next instruction             = 3
     *         - Conditional next instruction = 41
     *         - Interrupt                    = 2
     *         - Pin                          = na
     */
    { /* Program */
      0x00006202U,
      /* Control */
      ( 0x00052007U ),
      /* Data */
      109952U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 1 -> Duty Cycle Update
     *         - Instruction                  = 43
     *         - Next instruction             = 44
     *         - Conditional next instruction = 4
     *         - Interrupt                    = 3
     *         - Pin                          = 10
     */
    { /* Program */
      0x00058203U,
      /* Control */
      ( 0x00008007U | ( uint32 ) ( ( uint32 ) 0U << 22U )
        | ( uint32 ) ( ( uint32 ) 10U << 8U ) | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      55296U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 1 -> Period Update
     *         - Instruction                  = 44
     *         - Next instruction             = 5
     *         - Conditional next instruction = 43
     *         - Interrupt                    = 4
     *         - Pin                          = na
     */
    { /* Program */
      0x0000A204U,
      /* Control */
      ( 0x00056007U ),
      /* Data */
      109952U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 2 -> Duty Cycle Update
     *         - Instruction                  = 45
     *         - Next instruction             = 46
     *         - Conditional next instruction = 6
     *         - Interrupt                    = 5
     *         - Pin                          = 12
     */
    { /* Program */
      0x0005C205U,
      /* Control */
      ( 0x0000C007U | ( uint32 ) ( ( uint32 ) 0U << 22U )
        | ( uint32 ) ( ( uint32 ) 12U << 8U ) | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      55296U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 2 -> Period Update
     *         - Instruction                  = 46
     *         - Next instruction             = 7
     *         - Conditional next instruction = 45
     *         - Interrupt                    = 6
     *         - Pin                          = na
     */
    { /* Program */
      0x0000E206U,
      /* Control */
      ( 0x0005A007U ),
      /* Data */
      109952U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 3 -> Duty Cycle Update
     *         - Instruction                  = 47
     *         - Next instruction             = 48
     *         - Conditional next instruction = 8
     *         - Interrupt                    = 7
     *         - Pin                          = 14
     */
    { /* Program */
      0x00060207U,
      /* Control */
      ( 0x00010007U | ( uint32 ) ( ( uint32 ) 0U << 22U )
        | ( uint32 ) ( ( uint32 ) 14U << 8U ) | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      55296U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 3 -> Period Update
     *         - Instruction                  = 48
     *         - Next instruction             = 9
     *         - Conditional next instruction = 47
     *         - Interrupt                    = 8
     *         - Pin                          = na
     */
    { /* Program */
      0x00012208U,
      /* Control */
      ( 0x0005E007U ),
      /* Data */
      109952U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 4 -> Duty Cycle Update
     *         - Instruction                  = 49
     *         - Next instruction             = 50
     *         - Conditional next instruction = 10
     *         - Interrupt                    = 9
     *         - Pin                          = 16
     */
    { /* Program */
      0x00064209U,
      /* Control */
      ( 0x00014007U | ( uint32 ) ( ( uint32 ) 0U << 22U )
        | ( uint32 ) ( ( uint32 ) 16U << 8U ) | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      55296U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 4 -> Period Update
     *         - Instruction                  = 50
     *         - Next instruction             = 11
     *         - Conditional next instruction = 49
     *         - Interrupt                    = 10
     *         - Pin                          = na
     */
    { /* Program */
      0x0001620AU,
      /* Control */
      ( 0x00062007U ),
      /* Data */
      109952U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 5 -> Duty Cycle Update
     *         - Instruction                  = 51
     *         - Next instruction             = 52
     *         - Conditional next instruction = 12
     *         - Interrupt                    = 11
     *         - Pin                          = 17
     */
    { /* Program */
      0x0006820BU,
      /* Control */
      ( 0x00018007U | ( uint32 ) ( ( uint32 ) 0U << 22U )
        | ( uint32 ) ( ( uint32 ) 17U << 8U ) | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      55296U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 5 -> Period Update
     *         - Instruction                  = 52
     *         - Next instruction             = 13
     *         - Conditional next instruction = 51
     *         - Interrupt                    = 12
     *         - Pin                          = na
     */
    { /* Program */
      0x0001A20CU,
      /* Control */
      ( 0x00066007U ),
      /* Data */
      109952U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 6 -> Duty Cycle Update
     *         - Instruction                  = 53
     *         - Next instruction             = 54
     *         - Conditional next instruction = 14
     *         - Interrupt                    = 13
     *         - Pin                          = 18
     */
    { /* Program */
      0x0006C20DU,
      /* Control */
      ( 0x0001C007U | ( uint32 ) ( ( uint32 ) 0U << 22U )
        | ( uint32 ) ( ( uint32 ) 18U << 8U ) | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      55296U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 6 -> Period Update
     *         - Instruction                  = 54
     *         - Next instruction             = 15
     *         - Conditional next instruction = 53
     *         - Interrupt                    = 14
     *         - Pin                          = na
     */
    { /* Program */
      0x0001E20EU,
      /* Control */
      ( 0x0006A007U ),
      /* Data */
      109952U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 7 -> Duty Cycle Update
     *         - Instruction                  = 55
     *         - Next instruction             = 56
     *         - Conditional next instruction = 16
     *         - Interrupt                    = 15
     *         - Pin                          = 19
     */
    { /* Program */
      0x0007020FU,
      /* Control */
      ( 0x00020007U | ( uint32 ) ( ( uint32 ) 0U << 22U )
        | ( uint32 ) ( ( uint32 ) 19U << 8U ) | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      55296U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 7 -> Period Update
     *         - Instruction                  = 56
     *         - Next instruction             = 17
     *         - Conditional next instruction = 55
     *         - Interrupt                    = 16
     *         - Pin                          = na
     */
    { /* Program */
      0x00022210U,
      /* Control */
      ( 0x0006E007U ),
      /* Data */
      109952U,
      /* Reserved */
      0x00000000U },

    /* WCAP: Capture timestamp
     *         - Instruction                  = 57
     *         - Next instruction             = 0
     *         - Conditional next instruction = 0
     *         - Interrupt                    = na
     *         - Pin                          = na
     *         - Reg                          = T
     */
    { /* Program */
      0x00001600U,
      /* Control */
      ( 0x00000004U ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },
};

/*----------------------------------------------------------------------------*/
/* Default Program                                                            */

/** @var static const hetINSTRUCTION_t het2PROGRAM[58]
 *   @brief Default Program
 *
 *   Het program running after initialization.
 */

static const hetINSTRUCTION_t het2PROGRAM[ 58U ] = {
    /* CNT: Timebase
     *       - Instruction                  = 0
     *       - Next instruction             = 1
     *       - Conditional next instruction = na
     *       - Interrupt                    = na
     *       - Pin                          = na
     *       - Reg                          = T
     */
    { /* Program */
      0x00002C80U,
      /* Control */
      0x01FFFFFFU,
      /* Data */
      0xFFFFFF80U,
      /* Reserved */
      0x00000000U },

    /* PWCNT: PWM 0 -> Duty Cycle
     *         - Instruction                  = 1
     *         - Next instruction             = 2
     *         - Conditional next instruction = 2
     *         - Interrupt                    = 1
     *         - Pin                          = 8
     */
    { /* Program */
      0x000055C0U,
      /* Control */
      ( 0x00004006U | ( uint32 ) ( ( uint32 ) 8U << 8U )
        | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* DJZ: PWM 0 -> Period
     *         - Instruction                  = 2
     *         - Next instruction             = 3
     *         - Conditional next instruction = 41
     *         - Interrupt                    = 2
     *         - Pin                          = na
     */
    { /* Program */
      0x00007480U,
      /* Control */
      0x00052006U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PWCNT: PWM 1 -> Duty Cycle
     *         - Instruction                  = 3
     *         - Next instruction             = 4
     *         - Conditional next instruction = 4
     *         - Interrupt                    = 3
     *         - Pin                          = 10
     */
    { /* Program */
      0x000095C0U,
      /* Control */
      ( 0x00008006U | ( uint32 ) ( ( uint32 ) 10U << 8U )
        | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* DJZ: PWM 1 -> Period
     *         - Instruction                  = 4
     *         - Next instruction             = 5
     *         - Conditional next instruction = 43
     *         - Interrupt                    = 4
     *         - Pin                          = na
     */
    { /* Program */
      0x0000B480U,
      /* Control */
      0x00056006U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PWCNT: PWM 2 -> Duty Cycle
     *         - Instruction                  = 5
     *         - Next instruction             = 6
     *         - Conditional next instruction = 6
     *         - Interrupt                    = 5
     *         - Pin                          = 12
     */
    { /* Program */
      0x0000D5C0U,
      /* Control */
      ( 0x0000C006U | ( uint32 ) ( ( uint32 ) 12U << 8U )
        | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* DJZ: PWM 2 -> Period
     *         - Instruction                  = 6
     *         - Next instruction             = 7
     *         - Conditional next instruction = 45
     *         - Interrupt                    = 6
     *         - Pin                          = na
     */
    { /* Program */
      0x0000F480U,
      /* Control */
      0x0005A006U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PWCNT: PWM 3 -> Duty Cycle
     *         - Instruction                  = 7
     *         - Next instruction             = 8
     *         - Conditional next instruction = 8
     *         - Interrupt                    = 7
     *         - Pin                          = 14
     */
    { /* Program */
      0x000115C0U,
      /* Control */
      ( 0x00010006U | ( uint32 ) ( ( uint32 ) 14U << 8U )
        | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* DJZ: PWM 3 -> Period
     *         - Instruction                  = 8
     *         - Next instruction             = 9
     *         - Conditional next instruction = 47
     *         - Interrupt                    = 8
     *         - Pin                          = na
     */
    { /* Program */
      0x00013480U,
      /* Control */
      0x0005E006U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PWCNT: PWM 4 -> Duty Cycle
     *         - Instruction                  = 9
     *         - Next instruction             = 10
     *         - Conditional next instruction = 10
     *         - Interrupt                    = 9
     *         - Pin                          = 16
     */
    { /* Program */
      0x000155C0U,
      /* Control */
      ( 0x00014006U | ( uint32 ) ( ( uint32 ) 16U << 8U )
        | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* DJZ: PWM 4 -> Period
     *         - Instruction                  = 10
     *         - Next instruction             = 11
     *         - Conditional next instruction = 49
     *         - Interrupt                    = 10
     *         - Pin                          = na
     */
    { /* Program */
      0x00017480U,
      /* Control */
      0x00062006U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PWCNT: PWM 5 -> Duty Cycle
     *         - Instruction                  = 11
     *         - Next instruction             = 12
     *         - Conditional next instruction = 12
     *         - Interrupt                    = 11
     *         - Pin                          = 17
     */
    { /* Program */
      0x000195C0U,
      /* Control */
      ( 0x00018006U | ( uint32 ) ( ( uint32 ) 17U << 8U )
        | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* DJZ: PWM 5 -> Period
     *         - Instruction                  = 12
     *         - Next instruction             = 13
     *         - Conditional next instruction = 51
     *         - Interrupt                    = 12
     *         - Pin                          = na
     */
    { /* Program */
      0x0001B480U,
      /* Control */
      0x00066006U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PWCNT: PWM 6 -> Duty Cycle
     *         - Instruction                  = 13
     *         - Next instruction             = 14
     *         - Conditional next instruction = 14
     *         - Interrupt                    = 13
     *         - Pin                          = 18
     */
    { /* Program */
      0x0001D5C0U,
      /* Control */
      ( 0x0001C006U | ( uint32 ) ( ( uint32 ) 18U << 8U )
        | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* DJZ: PWM 6 -> Period
     *         - Instruction                  = 14
     *         - Next instruction             = 15
     *         - Conditional next instruction = 53
     *         - Interrupt                    = 14
     *         - Pin                          = na
     */
    { /* Program */
      0x0001F480U,
      /* Control */
      0x0006A006U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PWCNT: PWM 7 -> Duty Cycle
     *         - Instruction                  = 15
     *         - Next instruction             = 16
     *         - Conditional next instruction = 16
     *         - Interrupt                    = 15
     *         - Pin                          = 19
     */
    { /* Program */
      0x000215C0U,
      /* Control */
      ( 0x00020006U | ( uint32 ) ( ( uint32 ) 19U << 8U )
        | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* DJZ: PWM 7 -> Period
     *         - Instruction                  = 16
     *         - Next instruction             = 17
     *         - Conditional next instruction = 55
     *         - Interrupt                    = 16
     *         - Pin                          = na
     */
    { /* Program */
      0x00023480U,
      /* Control */
      0x0006E006U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* ECNT: CCU Edge 0
     *         - Instruction                  = 17
     *         - Next instruction             = 18
     *         - Conditional next instruction = 18
     *         - Interrupt                    = 17
     *         - Pin                          = 9
     */
    { /* Program */
      0x00025440U,
      /* Control */
      ( 0x00024007U | ( uint32 ) ( ( uint32 ) 9U << 8U )
        | ( uint32 ) ( ( uint32 ) 1U << 4U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* ECNT: CCU Edge 1
     *         - Instruction                  = 18
     *         - Next instruction             = 19
     *         - Conditional next instruction = 19
     *         - Interrupt                    = 18
     *         - Pin                          = 11
     */
    { /* Program */
      0x00027440U,
      /* Control */
      ( 0x00026007U | ( uint32 ) ( ( uint32 ) 11U << 8U )
        | ( uint32 ) ( ( uint32 ) 1U << 4U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* ECNT: CCU Edge 2
     *         - Instruction                  = 19
     *         - Next instruction             = 20
     *         - Conditional next instruction = 20
     *         - Interrupt                    = 19
     *         - Pin                          = 13
     */
    { /* Program */
      0x00029440U,
      /* Control */
      ( 0x00028007U | ( uint32 ) ( ( uint32 ) 13U << 8U )
        | ( uint32 ) ( ( uint32 ) 1U << 4U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* ECNT: CCU Edge 3
     *         - Instruction                  = 20
     *         - Next instruction             = 21
     *         - Conditional next instruction = 21
     *         - Interrupt                    = 20
     *         - Pin                          = 15
     */
    { /* Program */
      0x0002B440U,
      /* Control */
      ( 0x0002A007U | ( uint32 ) ( ( uint32 ) 15U << 8U )
        | ( uint32 ) ( ( uint32 ) 1U << 4U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* ECNT: CCU Edge 4
     *         - Instruction                  = 21
     *         - Next instruction             = 22
     *         - Conditional next instruction = 22
     *         - Interrupt                    = 21
     *         - Pin                          = 20
     */
    { /* Program */
      0x0002D440U,
      /* Control */
      ( 0x0002C007U | ( uint32 ) ( ( uint32 ) 20U << 8U )
        | ( uint32 ) ( ( uint32 ) 1U << 4U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* ECNT: CCU Edge 5
     *         - Instruction                  = 22
     *         - Next instruction             = 23
     *         - Conditional next instruction = 23
     *         - Interrupt                    = 22
     *         - Pin                          = 21
     */
    { /* Program */
      0x0002F440U,
      /* Control */
      ( 0x0002E007U | ( uint32 ) ( ( uint32 ) 21U << 8U )
        | ( uint32 ) ( ( uint32 ) 1U << 4U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* ECNT: CCU Edge 6
     *         - Instruction                  = 23
     *         - Next instruction             = 24
     *         - Conditional next instruction = 24
     *         - Interrupt                    = 23
     *         - Pin                          = 22
     */
    { /* Program */
      0x00031440U,
      /* Control */
      ( 0x00030007U | ( uint32 ) ( ( uint32 ) 22U << 8U )
        | ( uint32 ) ( ( uint32 ) 1U << 4U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* ECNT: CCU Edge 7
     *         - Instruction                  = 24
     *         - Next instruction             = 25
     *         - Conditional next instruction = 25
     *         - Interrupt                    = 24
     *         - Pin                          = 23
     */
    { /* Program */
      0x00033440U,
      /* Control */
      ( 0x00032007U | ( uint32 ) ( ( uint32 ) 23U << 8U )
        | ( uint32 ) ( ( uint32 ) 1U << 4U ) ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Duty 0
     *         - Instruction                  = 25
     *         - Next instruction             = 26
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 0
     */
    { /* Program */
      0x00034E00U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( 0U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Period 0
     *         - Instruction                  = 26
     *         - Next instruction             = 27
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 0  + 1
     */
    { /* Program */
      0x00036E80U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( 0U ) + 1U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Duty 1
     *         - Instruction                  = 27
     *         - Next instruction             = 28
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 2
     */
    { /* Program */
      0x00038E00U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( 2U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Period 1
     *         - Instruction                  = 28
     *         - Next instruction             = 29
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 2  + 1
     */
    { /* Program */
      0x0003AE80U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( 2U ) + 1U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Duty 2
     *         - Instruction                  = 29
     *         - Next instruction             = 30
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 4
     */
    { /* Program */
      0x0003CE00U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( 4U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Period 2
     *         - Instruction                  = 30
     *         - Next instruction             = 31
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 4  + 1
     */
    { /* Program */
      0x0003EE80U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( 4U ) + 1U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Duty 3
     *         - Instruction                  = 31
     *         - Next instruction             = 32
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 6
     */
    { /* Program */
      0x00040E00U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( 6U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Period 3
     *         - Instruction                  = 32
     *         - Next instruction             = 33
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 6  + 1
     */
    { /* Program */
      0x00042E80U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( 6U ) + 1U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Duty 4
     *         - Instruction                  = 33
     *         - Next instruction             = 34
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 0
     */
    { /* Program */
      0x00044E00U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( 0U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Period 4
     *         - Instruction                  = 34
     *         - Next instruction             = 35
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 0  + 1
     */
    { /* Program */
      0x00046E80U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( 0U ) + 1U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Duty 5
     *         - Instruction                  = 35
     *         - Next instruction             = 36
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 2
     */
    { /* Program */
      0x00048E00U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( 2U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Period 5
     *         - Instruction                  = 36
     *         - Next instruction             = 37
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 2  + 1
     */
    { /* Program */
      0x0004AE80U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( 2U ) + 1U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Duty 6
     *         - Instruction                  = 37
     *         - Next instruction             = 38
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 4
     */
    { /* Program */
      0x0004CE00U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( 4U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Period 6
     *         - Instruction                  = 38
     *         - Next instruction             = 39
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 4  + 1
     */
    { /* Program */
      0x0004EE80U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( 4U ) + 1U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Duty 7
     *         - Instruction                  = 39
     *         - Next instruction             = 40
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 6
     */
    { /* Program */
      0x00050E00U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( 6U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* PCNT: Capture Period 7
     *         - Instruction                  = 40
     *         - Next instruction             = 57
     *         - Conditional next instruction = na
     *         - Interrupt                    = na
     *         - Pin                          = 6  + 1
     */
    { /* Program */
      0x00072E80U | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( 6U ) + 1U ),
      /* Control */
      0x00000000U,
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 0 -> Duty Cycle Update
     *         - Instruction                  = 41
     *         - Next instruction             = 42
     *         - Conditional next instruction = 2
     *         - Interrupt                    = 1
     *         - Pin                          = 8
     */
    { /* Program */
      0x00054201U,
      /* Control */
      ( 0x00004007U | ( uint32 ) ( ( uint32 ) 0U << 22U )
        | ( uint32 ) ( ( uint32 ) 8U << 8U ) | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      55296U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 0 -> Period Update
     *         - Instruction                  = 42
     *         - Next instruction             = 3
     *         - Conditional next instruction = 41
     *         - Interrupt                    = 2
     *         - Pin                          = na
     */
    { /* Program */
      0x00006202U,
      /* Control */
      ( 0x00052007U ),
      /* Data */
      109952U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 1 -> Duty Cycle Update
     *         - Instruction                  = 43
     *         - Next instruction             = 44
     *         - Conditional next instruction = 4
     *         - Interrupt                    = 3
     *         - Pin                          = 10
     */
    { /* Program */
      0x00058203U,
      /* Control */
      ( 0x00008007U | ( uint32 ) ( ( uint32 ) 0U << 22U )
        | ( uint32 ) ( ( uint32 ) 10U << 8U ) | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      55296U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 1 -> Period Update
     *         - Instruction                  = 44
     *         - Next instruction             = 5
     *         - Conditional next instruction = 43
     *         - Interrupt                    = 4
     *         - Pin                          = na
     */
    { /* Program */
      0x0000A204U,
      /* Control */
      ( 0x00056007U ),
      /* Data */
      109952U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 2 -> Duty Cycle Update
     *         - Instruction                  = 45
     *         - Next instruction             = 46
     *         - Conditional next instruction = 6
     *         - Interrupt                    = 5
     *         - Pin                          = 12
     */
    { /* Program */
      0x0005C205U,
      /* Control */
      ( 0x0000C007U | ( uint32 ) ( ( uint32 ) 0U << 22U )
        | ( uint32 ) ( ( uint32 ) 12U << 8U ) | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      55296U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 2 -> Period Update
     *         - Instruction                  = 46
     *         - Next instruction             = 7
     *         - Conditional next instruction = 45
     *         - Interrupt                    = 6
     *         - Pin                          = na
     */
    { /* Program */
      0x0000E206U,
      /* Control */
      ( 0x0005A007U ),
      /* Data */
      109952U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 3 -> Duty Cycle Update
     *         - Instruction                  = 47
     *         - Next instruction             = 48
     *         - Conditional next instruction = 8
     *         - Interrupt                    = 7
     *         - Pin                          = 14
     */
    { /* Program */
      0x00060207U,
      /* Control */
      ( 0x00010007U | ( uint32 ) ( ( uint32 ) 0U << 22U )
        | ( uint32 ) ( ( uint32 ) 14U << 8U ) | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      55296U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 3 -> Period Update
     *         - Instruction                  = 48
     *         - Next instruction             = 9
     *         - Conditional next instruction = 47
     *         - Interrupt                    = 8
     *         - Pin                          = na
     */
    { /* Program */
      0x00012208U,
      /* Control */
      ( 0x0005E007U ),
      /* Data */
      109952U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 4 -> Duty Cycle Update
     *         - Instruction                  = 49
     *         - Next instruction             = 50
     *         - Conditional next instruction = 10
     *         - Interrupt                    = 9
     *         - Pin                          = 16
     */
    { /* Program */
      0x00064209U,
      /* Control */
      ( 0x00014007U | ( uint32 ) ( ( uint32 ) 0U << 22U )
        | ( uint32 ) ( ( uint32 ) 16U << 8U ) | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      55296U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 4 -> Period Update
     *         - Instruction                  = 50
     *         - Next instruction             = 11
     *         - Conditional next instruction = 49
     *         - Interrupt                    = 10
     *         - Pin                          = na
     */
    { /* Program */
      0x0001620AU,
      /* Control */
      ( 0x00062007U ),
      /* Data */
      109952U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 5 -> Duty Cycle Update
     *         - Instruction                  = 51
     *         - Next instruction             = 52
     *         - Conditional next instruction = 12
     *         - Interrupt                    = 11
     *         - Pin                          = 17
     */
    { /* Program */
      0x0006820BU,
      /* Control */
      ( 0x00018007U | ( uint32 ) ( ( uint32 ) 0U << 22U )
        | ( uint32 ) ( ( uint32 ) 17U << 8U ) | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      55296U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 5 -> Period Update
     *         - Instruction                  = 52
     *         - Next instruction             = 13
     *         - Conditional next instruction = 51
     *         - Interrupt                    = 12
     *         - Pin                          = na
     */
    { /* Program */
      0x0001A20CU,
      /* Control */
      ( 0x00066007U ),
      /* Data */
      109952U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 6 -> Duty Cycle Update
     *         - Instruction                  = 53
     *         - Next instruction             = 54
     *         - Conditional next instruction = 14
     *         - Interrupt                    = 13
     *         - Pin                          = 18
     */
    { /* Program */
      0x0006C20DU,
      /* Control */
      ( 0x0001C007U | ( uint32 ) ( ( uint32 ) 0U << 22U )
        | ( uint32 ) ( ( uint32 ) 18U << 8U ) | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      55296U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 6 -> Period Update
     *         - Instruction                  = 54
     *         - Next instruction             = 15
     *         - Conditional next instruction = 53
     *         - Interrupt                    = 14
     *         - Pin                          = na
     */
    { /* Program */
      0x0001E20EU,
      /* Control */
      ( 0x0006A007U ),
      /* Data */
      109952U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 7 -> Duty Cycle Update
     *         - Instruction                  = 55
     *         - Next instruction             = 56
     *         - Conditional next instruction = 16
     *         - Interrupt                    = 15
     *         - Pin                          = 19
     */
    { /* Program */
      0x0007020FU,
      /* Control */
      ( 0x00020007U | ( uint32 ) ( ( uint32 ) 0U << 22U )
        | ( uint32 ) ( ( uint32 ) 19U << 8U ) | ( uint32 ) ( ( uint32 ) 3U << 3U ) ),
      /* Data */
      55296U,
      /* Reserved */
      0x00000000U },

    /* MOV64: PWM 7 -> Period Update
     *         - Instruction                  = 56
     *         - Next instruction             = 17
     *         - Conditional next instruction = 55
     *         - Interrupt                    = 16
     *         - Pin                          = na
     */
    { /* Program */
      0x00022210U,
      /* Control */
      ( 0x0006E007U ),
      /* Data */
      109952U,
      /* Reserved */
      0x00000000U },

    /* WCAP: Capture timestamp
     *         - Instruction                  = 57
     *         - Next instruction             = 0
     *         - Conditional next instruction = 0
     *         - Interrupt                    = na
     *         - Pin                          = na
     *         - Reg                          = T
     */
    { /* Program */
      0x00001600U,
      /* Control */
      ( 0x00000004U ),
      /* Data */
      0x00000000U,
      /* Reserved */
      0x00000000U },
};

/** @fn void hetInit(void)
 *   @brief Initializes the het Driver
 *
 *   This function initializes the het 1 module.
 */
/* SourceId : HET_SourceId_001 */
/* DesignId : HET_DesignId_001 */
/* Requirements : HL_SR363 */
void hetInit( void )
{
    /** @b initialize @b HET */

    /** - Set HET pins default output value */
    hetREG1
        ->DOUT = ( uint32 ) ( ( uint32 ) 0U << 31U ) | ( uint32 ) ( ( uint32 ) 0U << 30U )
               | ( uint32 ) ( ( uint32 ) 0U << 29U ) | ( uint32 ) ( ( uint32 ) 0U << 28U )
               | ( uint32 ) ( ( uint32 ) 0U << 27U ) | ( uint32 ) ( ( uint32 ) 0U << 26U )
               | ( uint32 ) ( ( uint32 ) 0U << 25U ) | ( uint32 ) ( ( uint32 ) 0U << 24U )
               | ( uint32 ) ( ( uint32 ) 0U << 23U ) | ( uint32 ) ( ( uint32 ) 0U << 22U )
               | ( uint32 ) ( ( uint32 ) 0U << 21U ) | ( uint32 ) ( ( uint32 ) 0U << 20U )
               | ( uint32 ) ( ( uint32 ) 0U << 19U ) | ( uint32 ) ( ( uint32 ) 0U << 18U )
               | ( uint32 ) ( ( uint32 ) 0U << 17U ) | ( uint32 ) ( ( uint32 ) 0U << 16U )
               | ( uint32 ) ( ( uint32 ) 0U << 15U ) | ( uint32 ) ( ( uint32 ) 0U << 14U )
               | ( uint32 ) ( ( uint32 ) 0U << 13U ) | ( uint32 ) ( ( uint32 ) 0U << 12U )
               | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 10U )
               | ( uint32 ) ( ( uint32 ) 0U << 9U ) | ( uint32 ) ( ( uint32 ) 0U << 8U )
               | ( uint32 ) ( ( uint32 ) 0U << 7U ) | ( uint32 ) ( ( uint32 ) 0U << 6U )
               | ( uint32 ) ( ( uint32 ) 0U << 5U ) | ( uint32 ) ( ( uint32 ) 0U << 4U )
               | ( uint32 ) ( ( uint32 ) 0U << 3U ) | ( uint32 ) ( ( uint32 ) 0U << 2U )
               | ( uint32 ) ( ( uint32 ) 0U << 1U ) | ( uint32 ) ( ( uint32 ) 0U << 0U );

    /** - Set HET pins direction */
    hetREG1->DIR = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    /** - Set HET pins open drain enable */
    hetREG1->PDR = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    /** - Set HET pins pullup/down enable */
    hetREG1->PULDIS = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    /** - Set HET pins pullup/down select */
    hetREG1->PSL = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    /** - Set HET pins high resolution share */
    hetREG1->HRSH = ( uint32 ) 0x00008000U | ( uint32 ) 0x00004000U
                  | ( uint32 ) 0x00002000U | ( uint32 ) 0x00001000U
                  | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                  | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                  | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                  | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                  | ( uint32 ) 0x00000008U | ( uint32 ) 0x00000004U
                  | ( uint32 ) 0x00000002U | ( uint32 ) 0x00000001U;

    /** - Set HET pins AND share */
    hetREG1->AND = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    /** - Set HET pins XOR share */
    hetREG1->XOR = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    /* USER CODE BEGIN (1) */
    /* USER CODE END */

    /** - Setup prescaler values
     *     - Loop resolution prescaler
     *     - High resolution prescaler
     */
    hetREG1->PFR = ( uint32 ) ( ( uint32 ) 7U << 8U ) | ( ( uint32 ) 0U );

    /** - Parity control register
     *     - Enable/Disable Parity check
     */
    hetREG1->PCR = ( uint32 ) 0x00000005U;

    /** - Fill HET RAM with opcodes and Data */
    /*SAFETYMCUSW 94 S MR:11.1,11.2,11.4 <APPROVED> "HET RAM Fill from the table - Allowed
     * as per MISRA rule 11.2" */
    /*SAFETYMCUSW 94 S MR:11.1,11.2,11.4 <APPROVED> "HET RAM Fill from the table - Allowed
     * as per MISRA rule 11.2" */
    /*SAFETYMCUSW 95 S MR:11.1,11.4 <APPROVED> "HET RAM Fill from the table - Allowed as
     * per MISRA rule 11.2" */
    /*SAFETYMCUSW 95 S MR:11.1,11.4 <APPROVED> "HET RAM Fill from the table - Allowed as
     * per MISRA rule 11.2" */
    ( void ) memcpy( ( void * ) hetRAM1,
                     ( const void * ) het1PROGRAM,
                     sizeof( het1PROGRAM ) );

    /** - Setup interrupt priority level
     *     - PWM 0 end of duty  level
     *     - PWM 0 end of period level
     *     - PWM 1 end of duty  level
     *     - PWM 1 end of period level
     *     - PWM 2 end of duty  level
     *     - PWM 2 end of period level
     *     - PWM 3 end of duty  level
     *     - PWM 3 end of period level
     *     - PWM 4 end of duty  level
     *     - PWM 4 end of period level
     *     - PWM 5 end of duty  level
     *     - PWM 5 end of period level
     *     - PWM 6 end of duty  level
     *     - PWM 6 end of period level
     *     - PWM 7 end of duty  level
     *     - PWM 7 end of period level
     *
     *     - CCU Edge Detection 0 level
     *     - CCU Edge Detection 1 level
     *     - CCU Edge Detection 2 level
     *     - CCU Edge Detection 3 level
     *     - CCU Edge Detection 4 level
     *     - CCU Edge Detection 5 level
     *     - CCU Edge Detection 6 level
     *     - CCU Edge Detection 7 level
     */
    hetREG1->PRY = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    /** - Enable interrupts
     *     - PWM 0 end of duty
     *     - PWM 0 end of period
     *     - PWM 1 end of duty
     *     - PWM 1 end of period
     *     - PWM 2 end of duty
     *     - PWM 2 end of period
     *     - PWM 3 end of duty
     *     - PWM 3 end of period
     *     - PWM 4 end of duty
     *     - PWM 4 end of period
     *     - PWM 5 end of duty
     *     - PWM 5 end of period
     *     - PWM 6 end of duty
     *     - PWM 6 end of period
     *     - PWM 7 end of duty
     *     - PWM 7 end of period
     *     - CCU Edge Detection 0
     *     - CCU Edge Detection 1
     *     - CCU Edge Detection 2
     *     - CCU Edge Detection 3
     *     - CCU Edge Detection 4
     *     - CCU Edge Detection 5
     *     - CCU Edge Detection 6
     *     - CCU Edge Detection 7
     */
    hetREG1->INTENAC = 0xFFFFFFFFU;
    hetREG1->INTENAS = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    /** - Setup control register
     *     - Enable output buffers
     *     - Ignore software breakpoints
     *     - Master or Slave Clock Mode
     *     - Enable HET
     */
    hetREG1->GCR = ( 0x00000001U | ( uint32 ) ( ( uint32 ) 0U << 24U )
                     | ( uint32 ) ( ( uint32 ) 1U << 16U ) | ( 0x00020000U ) );

    /** @b initialize @b HET 2 */

    /** - Set HET pins default output value */
    hetREG2
        ->DOUT = ( uint32 ) ( ( uint32 ) 0U << 18U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )
               | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 0U << 15U )
               | ( uint32 ) ( ( uint32 ) 0U << 14U ) | ( uint32 ) ( ( uint32 ) 0U << 13U )
               | ( uint32 ) ( ( uint32 ) 0U << 12U ) | ( uint32 ) ( ( uint32 ) 0U << 11U )
               | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )
               | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 7U )
               | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 5U )
               | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )
               | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )
               | ( uint32 ) ( ( uint32 ) 0U << 0U );

    /** - Set HET pins direction */
    hetREG2->DIR = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U;

    /** - Set HET pins open drain enable */
    hetREG2->PDR = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U;

    /** - Set HET pins pullup/down enable */
    hetREG2->PULDIS = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                    | ( uint32 ) 0x00000000U;

    /** - Set HET pins pullup/down select */
    hetREG2->PSL = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U;

    /** - Set HET pins high resolution share */
    hetREG2->HRSH = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                  | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                  | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000008U
                  | ( uint32 ) 0x00000004U | ( uint32 ) 0x00000002U
                  | ( uint32 ) 0x00000001U;

    /** - Set HET pins AND share */
    hetREG2->AND = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U;

    /** - Set HET pins XOR share */
    hetREG2->XOR = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U;

    /* USER CODE BEGIN (2) */
    /* USER CODE END */

    /** - Setup prescaler values
     *     - Loop resolution prescaler
     *     - High resolution prescaler
     */
    hetREG2->PFR = ( uint32 ) ( ( uint32 ) 7U << 8U ) | ( ( uint32 ) 0U );

    /** - Parity control register
     *     - Enable/Disable Parity check
     */
    hetREG2->PCR = ( uint32 ) 0x00000005U;

    /** - Fill HET RAM with opcodes and Data */

    /* USER CODE BEGIN (3) */
    /* USER CODE END */

    /** - Release from reset */
    /*SAFETYMCUSW 94 S MR:11.1,11.2,11.4 <APPROVED> "HET RAM Fill from the table - Allowed
     * as per MISRA rule 11.2" */
    /*SAFETYMCUSW 94 S MR:11.1,11.2,11.4 <APPROVED> "HET RAM Fill from the table - Allowed
     * as per MISRA rule 11.2" */
    /*SAFETYMCUSW 95 S MR:11.1,11.4 <APPROVED> "HET RAM Fill from the table - Allowed as
     * per MISRA rule 11.2" */
    /*SAFETYMCUSW 95 S MR:11.1,11.4 <APPROVED> "HET RAM Fill from the table - Allowed as
     * per MISRA rule 11.2" */
    ( void ) memcpy( ( void * ) hetRAM2,
                     ( const void * ) het2PROGRAM,
                     sizeof( het2PROGRAM ) );

    /** - Setup prescaler values
     *     - Loop resolution prescaler
     *     - High resolution prescaler
     */
    hetREG2->PFR = ( uint32 ) ( ( uint32 ) 7U << 8U ) | ( ( uint32 ) 0U );

    /** - Setup interrupt priority level
     *     - PWM 0 end of duty  level
     *     - PWM 0 end of period level
     *     - PWM 1 end of duty  level
     *     - PWM 1 end of period level
     *     - PWM 2 end of duty  level
     *     - PWM 2 end of period level
     *     - PWM 3 end of duty  level
     *     - PWM 3 end of period level
     *     - PWM 4 end of duty  level
     *     - PWM 4 end of period level
     *     - PWM 5 end of duty  level
     *     - PWM 5 end of period level
     *     - PWM 6 end of duty  level
     *     - PWM 6 end of period level
     *     - PWM 7 end of duty  level
     *     - PWM 7 end of period level
     *
     *     - CCU Edge Detection 0 level
     *     - CCU Edge Detection 1 level
     *     - CCU Edge Detection 2 level
     *     - CCU Edge Detection 3 level
     *     - CCU Edge Detection 4 level
     *     - CCU Edge Detection 5 level
     *     - CCU Edge Detection 6 level
     *     - CCU Edge Detection 7 level
     */
    hetREG2->PRY = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                 | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    /** - Enable interrupts
     *     - PWM 0 end of duty
     *     - PWM 0 end of period
     *     - PWM 1 end of duty
     *     - PWM 1 end of period
     *     - PWM 2 end of duty
     *     - PWM 2 end of period
     *     - PWM 3 end of duty
     *     - PWM 3 end of period
     *     - PWM 4 end of duty
     *     - PWM 4 end of period
     *     - PWM 5 end of duty
     *     - PWM 5 end of period
     *     - PWM 6 end of duty
     *     - PWM 6 end of period
     *     - PWM 7 end of duty
     *     - PWM 7 end of period
     *     - CCU Edge Detection 0
     *     - CCU Edge Detection 1
     *     - CCU Edge Detection 2
     *     - CCU Edge Detection 3
     *     - CCU Edge Detection 4
     *     - CCU Edge Detection 5
     *     - CCU Edge Detection 6
     *     - CCU Edge Detection 7
     */
    hetREG2->INTENAC = 0xFFFFFFFFU;
    hetREG2->INTENAS = ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U
                     | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    /** - Setup control register
     *     - Enable output buffers
     *     - Ignore software breakpoints
     *     - Master or Slave Clock Mode
     *     - Enable HET
     */
    hetREG2->GCR = ( 0x00000001U | ( uint32 ) ( ( uint32 ) 0U << 24U )
                     | ( uint32 ) ( ( uint32 ) 1U << 16U ) | ( 0x00020000U ) );

    /**   @note This function has to be called before the driver can be used.\n
     *           This function has to be executed in privileged mode.\n
     */
}

/** @fn void pwmStart( hetRAMBASE_t * hetRAM, uint32 pwm)
 *   @brief Start pwm signal
 *   @param[in] hetRAM Pointer to HET RAM:
 *              - hetRAM1: HET1 RAM pointer
 *              - hetRAM2: HET2 RAM pointer
 *   @param[in] pwm Pwm signal:
 *              - pwm0: Pwm 0
 *              - pwm1: Pwm 1
 *              - pwm2: Pwm 2
 *              - pwm3: Pwm 3
 *              - pwm4: Pwm 4
 *              - pwm5: Pwm 5
 *              - pwm6: Pwm 6
 *              - pwm7: Pwm 7
 *
 *   Start the given pwm signal
 */
/* SourceId : HET_SourceId_002 */
/* DesignId : HET_DesignId_002 */
/* Requirements : HL_SR364 */
void pwmStart( hetRAMBASE_t * hetRAM, uint32 pwm )
{
    hetRAM->Instruction[ ( pwm << 1U ) + 41U ].Control |= 0x00400000U;
}

/** @fn void pwmStop( hetRAMBASE_t * hetRAM, uint32 pwm)
 *   @brief Stop pwm signal
 *   @param[in] hetRAM Pointer to HET RAM:
 *              - hetRAM1: HET1 RAM pointer
 *              - hetRAM2: HET2 RAM pointer
 *   @param[in] pwm Pwm signal:
 *              - pwm0: Pwm 0
 *              - pwm1: Pwm 1
 *              - pwm2: Pwm 2
 *              - pwm3: Pwm 3
 *              - pwm4: Pwm 4
 *              - pwm5: Pwm 5
 *              - pwm6: Pwm 6
 *              - pwm7: Pwm 7
 *
 *   Stop the given pwm signal
 */
/* SourceId : HET_SourceId_003 */
/* DesignId : HET_DesignId_003 */
/* Requirements : HL_SR365 */
void pwmStop( hetRAMBASE_t * hetRAM, uint32 pwm )
{
    hetRAM->Instruction[ ( pwm << 1U ) + 41U ].Control &= ~( uint32 ) 0x00400000U;
}

/** @fn void pwmSetDuty(hetRAMBASE_t * hetRAM, uint32 pwm, uint32 pwmDuty)
 *   @brief Set duty cycle
 *   @param[in] hetRAM Pointer to HET RAM:
 *              - hetRAM1: HET1 RAM pointer
 *              - hetRAM2: HET2 RAM pointer
 *   @param[in] pwm Pwm signal:
 *              - pwm0: Pwm 0
 *              - pwm1: Pwm 1
 *              - pwm2: Pwm 2
 *              - pwm3: Pwm 3
 *              - pwm4: Pwm 4
 *              - pwm5: Pwm 5
 *              - pwm6: Pwm 6
 *              - pwm7: Pwm 7
 *   @param[in] pwmDuty duty cycle in %.
 *
 *   Sets a new duty cycle on the given pwm signal
 */
/* SourceId : HET_SourceId_004 */
/* DesignId : HET_DesignId_004 */
/* Requirements : HL_SR366 */
void pwmSetDuty( hetRAMBASE_t * hetRAM, uint32 pwm, uint32 pwmDuty )
{
    uint32 action;
    uint32 pwmPolarity = 0U;
    uint32 pwmPeriod = hetRAM->Instruction[ ( pwm << 1U ) + 42U ].Data + 128U;

    pwmPeriod = pwmPeriod >> 7U;

    if( hetRAM == hetRAM1 )
    {
        pwmPolarity = s_het1pwmPolarity[ pwm ];
    }
    else
    {
        pwmPolarity = s_het2pwmPolarity[ pwm ];
    }

    if( pwmDuty == 0U )
    {
        action = ( pwmPolarity == 3U ) ? 0U : 2U;
    }
    else if( pwmDuty >= 100U )
    {
        action = ( pwmPolarity == 3U ) ? 2U : 0U;
    }
    else
    {
        action = pwmPolarity;
    }

    hetRAM->Instruction[ ( pwm << 1U ) + 41U ]
        .Control = ( ( hetRAM->Instruction[ ( pwm << 1U ) + 41U ].Control )
                     & ( ~( uint32 ) ( 0x00000018U ) ) )
                 | ( action << 3U );
    hetRAM->Instruction[ ( pwm << 1U ) + 41U ].Data = ( ( ( pwmPeriod * pwmDuty ) / 100U )
                                                        << 7U )
                                                    + 128U;
}

/** @fn void pwmSetSignal(hetRAMBASE_t * hetRAM, uint32 pwm, hetSIGNAL_t signal)
 *   @brief Set period
 *   @param[in] hetRAM Pointer to HET RAM:
 *              - hetRAM1: HET1 RAM pointer
 *              - hetRAM2: HET2 RAM pointer
 *   @param[in] pwm Pwm signal:
 *              - pwm0: Pwm 0
 *              - pwm1: Pwm 1
 *              - pwm2: Pwm 2
 *              - pwm3: Pwm 3
 *              - pwm4: Pwm 4
 *              - pwm5: Pwm 5
 *              - pwm6: Pwm 6
 *              - pwm7: Pwm 7
 *   @param[in] signal signal
 *             - duty cycle in %.
 *              - period period in us.
 *
 *   Sets a new pwm signal
 */
/* SourceId : HET_SourceId_005 */
/* DesignId : HET_DesignId_005 */
/* Requirements : HL_SR367 */
void pwmSetSignal( hetRAMBASE_t * hetRAM, uint32 pwm, hetSIGNAL_t signal )
{
    uint32 action;
    uint32 pwmPolarity = 0U;
    float64 pwmPeriod = 0.0F;

    if( hetRAM == hetRAM1 )
    {
        pwmPeriod = ( signal.period * 1000.0F ) / 1163.636F;
        pwmPolarity = s_het1pwmPolarity[ pwm ];
    }
    else
    {
        pwmPeriod = ( signal.period * 1000.0F ) / 1163.636F;
        pwmPolarity = s_het2pwmPolarity[ pwm ];
    }

    if( signal.duty == 0U )
    {
        action = ( pwmPolarity == 3U ) ? 0U : 2U;
    }
    else if( signal.duty >= 100U )
    {
        action = ( pwmPolarity == 3U ) ? 2U : 0U;
    }
    else
    {
        action = pwmPolarity;
    }

    hetRAM->Instruction[ ( pwm << 1U ) + 41U ]
        .Control = ( ( hetRAM->Instruction[ ( pwm << 1U ) + 41U ].Control )
                     & ( ~( uint32 ) ( 0x00000018U ) ) )
                 | ( action << 3U );
    hetRAM->Instruction[ ( pwm << 1U ) + 41U ]
        .Data = ( ( ( ( uint32 ) pwmPeriod * signal.duty ) / 100U ) << 7U ) + 128U;
    hetRAM->Instruction[ ( pwm << 1U ) + 42U ].Data = ( ( uint32 ) pwmPeriod << 7U )
                                                    - 128U;
}

/** @fn void pwmGetSignal(hetRAMBASE_t * hetRAM, uint32 pwm, hetSIGNAL_t signal)
 *   @brief Get duty cycle
 *   @param[in] hetRAM Pointer to HET RAM:
 *              - hetRAM1: HET1 RAM pointer
 *              - hetRAM2: HET2 RAM pointer
 *   @param[in] pwm Pwm signal:
 *              - pwm0: Pwm 0
 *              - pwm1: Pwm 1
 *              - pwm2: Pwm 2
 *              - pwm3: Pwm 3
 *              - pwm4: Pwm 4
 *              - pwm5: Pwm 5
 *              - pwm6: Pwm 6
 *              - pwm7: Pwm 7
 *   @param[in] signal signal
 *              - duty cycle in %.
 *              - period period in us.
 *
 *   Gets current signal of the given pwm signal.
 */
/* SourceId : HET_SourceId_006 */
/* DesignId : HET_DesignId_006 */
/* Requirements : HL_SR368 */
void pwmGetSignal( hetRAMBASE_t * hetRAM, uint32 pwm, hetSIGNAL_t * signal )
{
    uint32 pwmDuty = ( hetRAM->Instruction[ ( pwm << 1U ) + 41U ].Data - 128U ) >> 7U;
    uint32 pwmPeriod = ( hetRAM->Instruction[ ( pwm << 1U ) + 42U ].Data + 128U ) >> 7U;

    signal->duty = ( pwmDuty * 100U ) / pwmPeriod;

    if( hetRAM == hetRAM1 )
    {
        signal->period = ( ( float64 ) pwmPeriod * 1163.636F ) / 1000.0F;
    }
    else
    {
        signal->period = ( ( float64 ) pwmPeriod * 1163.636F ) / 1000.0F;
    }
}

/** @fn void pwmEnableNotification(hetBASE_t * hetREG, uint32 pwm, uint32 notification)
 *   @brief Enable pwm notification
 *   @param[in] hetREG Pointer to HET Module:
 *              - hetREG1: HET1 Module pointer
 *              - hetREG2: HET2 Module pointer
 *   @param[in] pwm Pwm signal:
 *              - pwm0: Pwm 0
 *              - pwm1: Pwm 1
 *              - pwm2: Pwm 2
 *              - pwm3: Pwm 3
 *              - pwm4: Pwm 4
 *              - pwm5: Pwm 5
 *              - pwm6: Pwm 6
 *              - pwm7: Pwm 7
 *   @param[in] notification Pwm notification:
 *              - pwmEND_OF_DUTY:   Notification on end of duty
 *              - pwmEND_OF_PERIOD: Notification on end of end period
 *              - pwmEND_OF_BOTH:   Notification on end of both duty and period
 */
/* SourceId : HET_SourceId_007 */
/* DesignId : HET_DesignId_007 */
/* Requirements : HL_SR369 */
void pwmEnableNotification( hetBASE_t * hetREG, uint32 pwm, uint32 notification )
{
    hetREG->FLG = notification << ( pwm << 1U );
    hetREG->INTENAS = notification << ( pwm << 1U );
}

/** @fn void pwmDisableNotification(hetBASE_t * hetREG, uint32 pwm, uint32 notification)
 *   @brief Enable pwm notification
 *   @param[in] hetREG Pointer to HET Module:
 *              - hetREG1: HET1 Module pointer
 *              - hetREG2: HET2 Module pointer
 *   @param[in] pwm Pwm signal:
 *              - pwm0: Pwm 0
 *              - pwm1: Pwm 1
 *              - pwm2: Pwm 2
 *              - pwm3: Pwm 3
 *              - pwm4: Pwm 4
 *              - pwm5: Pwm 5
 *              - pwm6: Pwm 6
 *              - pwm7: Pwm 7
 *   @param[in] notification Pwm notification:
 *              - pwmEND_OF_DUTY:   Notification on end of duty
 *              - pwmEND_OF_PERIOD: Notification on end of end period
 *              - pwmEND_OF_BOTH:   Notification on end of both duty and period
 */
/* SourceId : HET_SourceId_008 */
/* DesignId : HET_DesignId_008 */
/* Requirements : HL_SR370 */
void pwmDisableNotification( hetBASE_t * hetREG, uint32 pwm, uint32 notification )
{
    hetREG->INTENAC = notification << ( pwm << 1U );
}

/** @fn void edgeResetCounter(hetRAMBASE_t * hetRAM, uint32 edge)
 *   @brief Resets edge counter to 0
 *   @param[in] hetRAM Pointer to HET RAM:
 *              - hetRAM1: HET1 RAM pointer
 *              - hetRAM2: HET2 RAM pointer
 *   @param[in] edge Edge signal:
 *              - edge0: Edge 0
 *              - edge1: Edge 1
 *              - edge2: Edge 2
 *              - edge3: Edge 3
 *              - edge4: Edge 4
 *              - edge5: Edge 5
 *              - edge6: Edge 6
 *              - edge7: Edge 7
 *
 *   Reset edge counter to 0.
 */
/* SourceId : HET_SourceId_009 */
/* DesignId : HET_DesignId_009 */
/* Requirements : HL_SR372 */
void edgeResetCounter( hetRAMBASE_t * hetRAM, uint32 edge )
{
    hetRAM->Instruction[ edge + 17U ].Data = 0U;
}

/** @fn uint32 edgeGetCounter(hetRAMBASE_t * hetRAM, uint32 edge)
 *   @brief Get current edge counter value
 *   @param[in] hetRAM Pointer to HET RAM:
 *              - hetRAM1: HET1 RAM pointer
 *              - hetRAM2: HET2 RAM pointer
 *   @param[in] edge Edge signal:
 *              - edge0: Edge 0
 *              - edge1: Edge 1
 *              - edge2: Edge 2
 *              - edge3: Edge 3
 *              - edge4: Edge 4
 *              - edge5: Edge 5
 *              - edge6: Edge 6
 *              - edge7: Edge 7
 *
 *   Gets current edge counter value.
 */
/* SourceId : HET_SourceId_010 */
/* DesignId : HET_DesignId_010 */
/* Requirements : HL_SR373 */
uint32 edgeGetCounter( hetRAMBASE_t * hetRAM, uint32 edge )
{
    return hetRAM->Instruction[ edge + 17U ].Data >> 7U;
}

/** @fn void edgeEnableNotification(hetBASE_t * hetREG, uint32 edge)
 *   @brief Enable edge notification
 *   @param[in] hetREG Pointer to HET Module:
 *              - hetREG1: HET1 Module pointer
 *              - hetREG2: HET2 Module pointer
 *   @param[in] edge Edge signal:
 *              - edge0: Edge 0
 *              - edge1: Edge 1
 *              - edge2: Edge 2
 *              - edge3: Edge 3
 *              - edge4: Edge 4
 *              - edge5: Edge 5
 *              - edge6: Edge 6
 *              - edge7: Edge 7
 */
/* SourceId : HET_SourceId_011 */
/* DesignId : HET_DesignId_011 */
/* Requirements : HL_SR374 */
void edgeEnableNotification( hetBASE_t * hetREG, uint32 edge )
{
    hetREG->FLG = ( uint32 ) 0x20000U << edge;
    hetREG->INTENAS = ( uint32 ) 0x20000U << edge;
}

/** @fn void edgeDisableNotification(hetBASE_t * hetREG, uint32 edge)
 *   @brief Enable edge notification
 *   @param[in] hetREG Pointer to HET Module:
 *              - hetREG1: HET1 Module pointer
 *              - hetREG2: HET2 Module pointer
 *   @param[in] edge Edge signal:
 *              - edge0: Edge 0
 *              - edge1: Edge 1
 *              - edge2: Edge 2
 *              - edge3: Edge 3
 *              - edge4: Edge 4
 *              - edge5: Edge 5
 *              - edge6: Edge 6
 *              - edge7: Edge 7
 */
/* SourceId : HET_SourceId_012 */
/* DesignId : HET_DesignId_012 */
/* Requirements : HL_SR375 */
void edgeDisableNotification( hetBASE_t * hetREG, uint32 edge )
{
    hetREG->INTENAC = ( uint32 ) 0x20000U << edge;
}

/** @fn void capGetSignal(hetRAMBASE_t * hetRAM, uint32 cap, hetSIGNAL_t signal)
 *   @brief Get capture signal
 *   @param[in] hetRAM Pointer to HET RAM:
 *              - hetRAM1: HET1 RAM pointer
 *              - hetRAM2: HET2 RAM pointer
 *   @param[in] cap captured signal:
 *              - cap0: Captured signal 0
 *              - cap1: Captured signal 1
 *              - cap2: Captured signal 2
 *              - cap3: Captured signal 3
 *              - cap4: Captured signal 4
 *              - cap5: Captured signal 5
 *              - cap6: Captured signal 6
 *              - cap7: Captured signal 7
 *   @param[in] signal signal
 *              - duty cycle in %.
 *              - period period in us.
 *
 *   Gets current signal of the given capture signal.
 */
/* SourceId : HET_SourceId_013 */
/* DesignId : HET_DesignId_013 */
/* Requirements : HL_SR377 */
void capGetSignal( hetRAMBASE_t * hetRAM, uint32 cap, hetSIGNAL_t * signal )
{
    uint32 pwmDuty = ( hetRAM->Instruction[ ( cap << 1U ) + 25U ].Data ) >> 7U;
    uint32 pwmPeriod = ( hetRAM->Instruction[ ( cap << 1U ) + 26U ].Data ) >> 7U;

    signal->duty = ( pwmDuty * 100U ) / pwmPeriod;

    if( hetRAM == hetRAM1 )
    {
        signal->period = ( ( float64 ) pwmPeriod * 1163.636F ) / 1000.0F;
    }
    else
    {
        signal->period = ( ( float64 ) pwmPeriod * 1163.636F ) / 1000.0F;
    }
}

/** @fn void hetResetTimestamp(hetRAMBASE_t *hetRAM)
 *   @brief Resets timestamp
 *   @param[in] hetRAM Pointer to HET RAM:
 *              - hetRAM1: HET1 RAM pointer
 *              - hetRAM2: HET2 RAM pointer
 *
 *   Resets loop count based timestamp.
 */
/* SourceId : HET_SourceId_014 */
/* DesignId : HET_DesignId_014 */
/* Requirements : HL_SR378 */
void hetResetTimestamp( hetRAMBASE_t * hetRAM )
{
    hetRAM->Instruction[ 0U ].Data = 0U;
}

/** @fn uint32 hetGetTimestamp(hetRAMBASE_t *hetRAM)
 *   @brief Returns timestamp
 *
 *   Returns loop count based timestamp.
 */
/* SourceId : HET_SourceId_015 */
/* DesignId : HET_DesignId_015 */
/* Requirements : HL_SR379 */
uint32 hetGetTimestamp( hetRAMBASE_t * hetRAM )
{
    return hetRAM->Instruction[ 57U ].Data;
}

/* USER CODE BEGIN (4) */
/* USER CODE END */

/** @fn void het1GetConfigValue(het_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the HET1 configuration registers
 *
 *   @param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *   @param[in] type:    whether initial or current value of the configuration registers
 * need to be stored
 *                       - InitialValue: initial value of the configuration registers will
 * be stored in the struct pointed by config_reg
 *                       - CurrentValue: initial value of the configuration registers will
 * be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 * 'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : HET_SourceId_016 */
/* DesignId : HET_DesignId_016 */
/* Requirements : HL_SR379 */
void het1GetConfigValue( het_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_GCR = HET1_GCR_CONFIGVALUE;
        config_reg->CONFIG_PFR = HET1_PFR_CONFIGVALUE;
        config_reg->CONFIG_INTENAS = HET1_INTENAS_CONFIGVALUE;
        config_reg->CONFIG_INTENAC = HET1_INTENAC_CONFIGVALUE;
        config_reg->CONFIG_PRY = HET1_PRY_CONFIGVALUE;
        config_reg->CONFIG_AND = HET1_AND_CONFIGVALUE;
        config_reg->CONFIG_HRSH = HET1_HRSH_CONFIGVALUE;
        config_reg->CONFIG_XOR = HET1_XOR_CONFIGVALUE;
        config_reg->CONFIG_DIR = HET1_DIR_CONFIGVALUE;
        config_reg->CONFIG_PDR = HET1_PDR_CONFIGVALUE;
        config_reg->CONFIG_PULDIS = HET1_PULDIS_CONFIGVALUE;
        config_reg->CONFIG_PSL = HET1_PSL_CONFIGVALUE;
        config_reg->CONFIG_PCR = HET1_PCR_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_GCR = hetREG1->GCR;
        config_reg->CONFIG_PFR = hetREG1->PFR;
        config_reg->CONFIG_INTENAS = hetREG1->INTENAS;
        config_reg->CONFIG_INTENAC = hetREG1->INTENAC;
        config_reg->CONFIG_PRY = hetREG1->PRY;
        config_reg->CONFIG_AND = hetREG1->AND;
        config_reg->CONFIG_HRSH = hetREG1->HRSH;
        config_reg->CONFIG_XOR = hetREG1->XOR;
        config_reg->CONFIG_DIR = hetREG1->DIR;
        config_reg->CONFIG_PDR = hetREG1->PDR;
        config_reg->CONFIG_PULDIS = hetREG1->PULDIS;
        config_reg->CONFIG_PSL = hetREG1->PSL;
        config_reg->CONFIG_PCR = hetREG1->PCR;
    }
}

/** @fn void het2GetConfigValue(het_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the HET2 configuration registers
 *
 *   @param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *   @param[in] type:    whether initial or current value of the configuration registers
 * need to be stored
 *                       - InitialValue: initial value of the configuration registers will
 * be stored in the struct pointed by config_reg
 *                       - CurrentValue: initial value of the configuration registers will
 * be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 * 'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : HET_SourceId_017 */
/* DesignId : HET_DesignId_016 */
/* Requirements : HL_SR379 */
void het2GetConfigValue( het_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_GCR = HET2_GCR_CONFIGVALUE;
        config_reg->CONFIG_PFR = HET2_PFR_CONFIGVALUE;
        config_reg->CONFIG_INTENAS = HET2_INTENAS_CONFIGVALUE;
        config_reg->CONFIG_INTENAC = HET2_INTENAC_CONFIGVALUE;
        config_reg->CONFIG_PRY = HET2_PRY_CONFIGVALUE;
        config_reg->CONFIG_AND = HET2_AND_CONFIGVALUE;
        config_reg->CONFIG_HRSH = HET2_HRSH_CONFIGVALUE;
        config_reg->CONFIG_XOR = HET2_XOR_CONFIGVALUE;
        config_reg->CONFIG_DIR = HET2_DIR_CONFIGVALUE;
        config_reg->CONFIG_PDR = HET2_PDR_CONFIGVALUE;
        config_reg->CONFIG_PULDIS = HET2_PULDIS_CONFIGVALUE;
        config_reg->CONFIG_PSL = HET2_PSL_CONFIGVALUE;
        config_reg->CONFIG_PCR = HET2_PCR_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_GCR = hetREG2->GCR;
        config_reg->CONFIG_PFR = hetREG2->PFR;
        config_reg->CONFIG_INTENAS = hetREG2->INTENAS;
        config_reg->CONFIG_INTENAC = hetREG2->INTENAC;
        config_reg->CONFIG_PRY = hetREG2->PRY;
        config_reg->CONFIG_AND = hetREG2->AND;
        config_reg->CONFIG_HRSH = hetREG2->HRSH;
        config_reg->CONFIG_XOR = hetREG2->XOR;
        config_reg->CONFIG_DIR = hetREG2->DIR;
        config_reg->CONFIG_PDR = hetREG2->PDR;
        config_reg->CONFIG_PULDIS = hetREG2->PULDIS;
        config_reg->CONFIG_PSL = hetREG2->PSL;
        config_reg->CONFIG_PCR = hetREG2->PCR;
    }
}
