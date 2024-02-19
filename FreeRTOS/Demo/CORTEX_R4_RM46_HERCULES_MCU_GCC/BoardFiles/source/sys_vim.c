/** @file sys_vim.c
 *   @brief VIM Driver Implementation File
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

#include "sys_vim.h"
#include "system.h"
#include "esm.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Vim Ram Definition */

/** @struct vimRam
 *   @brief Vim Ram Definition
 *
 *   This type is used to access the Vim Ram.
 */

/** @typedef vimRAM_t
 *   @brief Vim Ram Type Definition
 *
 *   This type is used to access the Vim Ram.
 */
typedef volatile struct vimRam
{
    t_isrFuncPTR ISR[ VIM_CHANNELS ];
} vimRAM_t;

#define vimRAM ( ( vimRAM_t * ) 0xFFF82000U )

static const t_isrFuncPTR s_vim_init[ 128U ] = {
    &phantomInterrupt,     &esmHighInterrupt, /* Channel 0 */
    &phantomInterrupt,                        /* Channel 1 */
    &FreeRTOS_IRQ_Handler,                    /* Channel 2 */
    &phantomInterrupt,                        /* Channel 3 */
    &phantomInterrupt,                        /* Channel 4 */
    &phantomInterrupt,                        /* Channel 5 */
    &phantomInterrupt,                        /* Channel 6 */
    &phantomInterrupt,                        /* Channel 7 */
    &phantomInterrupt,                        /* Channel 8 */
    &phantomInterrupt,                        /* Channel 9 */
    &phantomInterrupt,                        /* Channel 10 */
    &phantomInterrupt,                        /* Channel 11 */
    &phantomInterrupt,                        /* Channel 12 */
    &phantomInterrupt,                        /* Channel 13 */
    &phantomInterrupt,                        /* Channel 14 */
    &phantomInterrupt,                        /* Channel 15 */
    &phantomInterrupt,                        /* Channel 16 */
    &phantomInterrupt,                        /* Channel 17 */
    &phantomInterrupt,                        /* Channel 18 */
    &phantomInterrupt,                        /* Channel 19 */
    &phantomInterrupt,                        /* Channel 20 */
    &FreeRTOS_IRQ_Handler,                    /* Channel 21 */
    &phantomInterrupt,                        /* Channel 22 */
    &phantomInterrupt,                        /* Channel 23 */
    &phantomInterrupt,                        /* Channel 24 */
    &phantomInterrupt,                        /* Channel 25 */
    &phantomInterrupt,                        /* Channel 26 */
    &phantomInterrupt,                        /* Channel 27 */
    &phantomInterrupt,                        /* Channel 28 */
    &phantomInterrupt,                        /* Channel 29 */
    &phantomInterrupt,                        /* Channel 30 */
    &phantomInterrupt,                        /* Channel 31 */
    &phantomInterrupt,                        /* Channel 32 */
    &phantomInterrupt,                        /* Channel 33 */
    &phantomInterrupt,                        /* Channel 34 */
    &phantomInterrupt,                        /* Channel 35 */
    &phantomInterrupt,                        /* Channel 36 */
    &phantomInterrupt,                        /* Channel 37 */
    &phantomInterrupt,                        /* Channel 38 */
    &phantomInterrupt,                        /* Channel 39 */
    &phantomInterrupt,                        /* Channel 40 */
    &phantomInterrupt,                        /* Channel 41 */
    &phantomInterrupt,                        /* Channel 42 */
    &phantomInterrupt,                        /* Channel 43 */
    &phantomInterrupt,                        /* Channel 44 */
    &phantomInterrupt,                        /* Channel 45 */
    &phantomInterrupt,                        /* Channel 46 */
    &phantomInterrupt,                        /* Channel 47 */
    &phantomInterrupt,                        /* Channel 48 */
    &phantomInterrupt,                        /* Channel 49 */
    &phantomInterrupt,                        /* Channel 50 */
    &phantomInterrupt,                        /* Channel 51 */
    &phantomInterrupt,                        /* Channel 52 */
    &phantomInterrupt,                        /* Channel 53 */
    &phantomInterrupt,                        /* Channel 54 */
    &phantomInterrupt,                        /* Channel 55 */
    &phantomInterrupt,                        /* Channel 56 */
    &phantomInterrupt,                        /* Channel 57 */
    &phantomInterrupt,                        /* Channel 58 */
    &phantomInterrupt,                        /* Channel 59 */
    &phantomInterrupt,                        /* Channel 60 */
    &phantomInterrupt,                        /* Channel 61 */
    &phantomInterrupt,                        /* Channel 62 */
    &phantomInterrupt,                        /* Channel 63 */
    &phantomInterrupt,                        /* Channel 64 */
    &phantomInterrupt,                        /* Channel 65 */
    &phantomInterrupt,                        /* Channel 66 */
    &phantomInterrupt,                        /* Channel 67 */
    &phantomInterrupt,                        /* Channel 68 */
    &phantomInterrupt,                        /* Channel 69 */
    &phantomInterrupt,                        /* Channel 70 */
    &phantomInterrupt,                        /* Channel 71 */
    &phantomInterrupt,                        /* Channel 72 */
    &phantomInterrupt,                        /* Channel 73 */
    &phantomInterrupt,                        /* Channel 74 */
    &phantomInterrupt,                        /* Channel 75 */
    &phantomInterrupt,                        /* Channel 76 */
    &phantomInterrupt,                        /* Channel 77 */
    &phantomInterrupt,                        /* Channel 78 */
    &phantomInterrupt,                        /* Channel 79 */
    &phantomInterrupt,                        /* Channel 80 */
    &phantomInterrupt,                        /* Channel 81 */
    &phantomInterrupt,                        /* Channel 82 */
    &phantomInterrupt,                        /* Channel 83 */
    &phantomInterrupt,                        /* Channel 84 */
    &phantomInterrupt,                        /* Channel 85 */
    &phantomInterrupt,                        /* Channel 86 */
    &phantomInterrupt,                        /* Channel 87 */
    &phantomInterrupt,                        /* Channel 88 */
    &phantomInterrupt,                        /* Channel 89 */
    &phantomInterrupt,                        /* Channel 90 */
    &phantomInterrupt,                        /* Channel 91 */
    &phantomInterrupt,                        /* Channel 92 */
    &phantomInterrupt,                        /* Channel 93 */
    &phantomInterrupt,                        /* Channel 94 */
    &phantomInterrupt,                        /* Channel 95 */
    &phantomInterrupt,                        /* Channel 96 */
    &phantomInterrupt,                        /* Channel 97 */
    &phantomInterrupt,                        /* Channel 98 */
    &phantomInterrupt,                        /* Channel 99 */
    &phantomInterrupt,                        /* Channel 100 */
    &phantomInterrupt,                        /* Channel 101 */
    &phantomInterrupt,                        /* Channel 102 */
    &phantomInterrupt,                        /* Channel 103 */
    &phantomInterrupt,                        /* Channel 104 */
    &phantomInterrupt,                        /* Channel 105 */
    &phantomInterrupt,                        /* Channel 106 */
    &phantomInterrupt,                        /* Channel 107 */
    &phantomInterrupt,                        /* Channel 108 */
    &phantomInterrupt,                        /* Channel 109 */
    &phantomInterrupt,                        /* Channel 110 */
    &phantomInterrupt,                        /* Channel 111 */
    &phantomInterrupt,                        /* Channel 112 */
    &phantomInterrupt,                        /* Channel 113 */
    &phantomInterrupt,                        /* Channel 114 */
    &phantomInterrupt,                        /* Channel 115 */
    &phantomInterrupt,                        /* Channel 116 */
    &phantomInterrupt,                        /* Channel 117 */
    &phantomInterrupt,                        /* Channel 118 */
    &phantomInterrupt,                        /* Channel 119 */
    &phantomInterrupt,                        /* Channel 120 */
    &phantomInterrupt,                        /* Channel 121 */
    &phantomInterrupt,                        /* Channel 122 */
    &phantomInterrupt,                        /* Channel 123 */
    &phantomInterrupt,                        /* Channel 124 */
    &phantomInterrupt,                        /* Channel 125 */
    &phantomInterrupt,                        /* Channel 126 */
};
void vimParityErrorHandler( void );

/** @fn void vimInit(void)
 *   @brief Initializes VIM module
 *
 *   This function initializes VIM RAM and registers
 */
/* SourceId : VIM_SourceId_001 */
/* DesignId : VIM_DesignId_001 */
/* Requirements : HL_SR100 */
void vimInit( void )
{
    /* VIM RAM Parity Enable */
    VIM_PARCTL = 0xAU;

    /* Initialize VIM table */
    {
        uint32 i;

        for( i = 0U; i < VIM_CHANNELS; i++ )
        {
            vimRAM->ISR[ i ] = s_vim_init[ i ];
        }
    }

    /* Set Fall-Back Address Parity Error Register */
    /*SAFETYMCUSW 439 S MR:11.3 <APPROVED> " Need to store the address of a function in a
     * 32 bit register - Advisory as per MISRA" */
    VIM_FBPARERR = ( uint32 ) &vimParityErrorHandler;

    /* set IRQ/FIQ priorities */
    vimREG->FIRQPR0 = ( uint32 ) ( ( uint32 ) SYS_FIQ << 0U )
                    | ( uint32 ) ( ( uint32 ) SYS_FIQ << 1U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 2U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 3U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 4U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 5U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 6U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 7U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 8U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 9U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 10U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 11U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 12U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 13U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 14U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 15U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 16U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 17U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 18U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 19U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 20U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 21U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 22U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 23U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 24U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 25U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 26U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 27U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 28U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 29U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 30U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 31U );

    vimREG->FIRQPR1 = ( uint32 ) ( ( uint32 ) SYS_IRQ << 0U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 1U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 2U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 3U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 4U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 5U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 6U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 7U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 8U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 9U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 10U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 11U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 12U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 13U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 14U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 15U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 16U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 17U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 18U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 19U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 20U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 21U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 22U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 23U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 24U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 25U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 26U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 27U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 28U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 29U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 30U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 31U );

    vimREG->FIRQPR2 = ( uint32 ) ( ( uint32 ) SYS_IRQ << 0U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 1U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 2U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 3U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 4U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 5U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 6U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 7U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 8U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 9U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 10U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 11U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 12U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 13U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 14U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 15U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 16U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 17U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 18U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 19U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 20U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 21U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 22U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 23U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 24U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 25U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 26U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 27U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 28U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 29U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 30U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 31U );

    vimREG->FIRQPR3 = ( uint32 ) ( ( uint32 ) SYS_IRQ << 0U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 1U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 2U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 3U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 4U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 5U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 6U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 7U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 8U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 9U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 10U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 11U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 12U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 13U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 14U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 15U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 16U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 17U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 18U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 19U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 20U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 21U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 22U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 23U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 24U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 25U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 26U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 27U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 28U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 29U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 30U )
                    | ( uint32 ) ( ( uint32 ) SYS_IRQ << 31U );

    /* enable interrupts */
    vimREG->REQMASKSET0 = ( uint32 ) ( ( uint32 ) 1U << 0U )
                        | ( uint32 ) ( ( uint32 ) 0U << 1U )
                        | ( uint32 ) ( ( uint32 ) 1U << 2U )
                        | ( uint32 ) ( ( uint32 ) 0U << 3U )
                        | ( uint32 ) ( ( uint32 ) 0U << 4U )
                        | ( uint32 ) ( ( uint32 ) 0U << 5U )
                        | ( uint32 ) ( ( uint32 ) 0U << 6U )
                        | ( uint32 ) ( ( uint32 ) 0U << 7U )
                        | ( uint32 ) ( ( uint32 ) 0U << 8U )
                        | ( uint32 ) ( ( uint32 ) 0U << 9U )
                        | ( uint32 ) ( ( uint32 ) 0U << 10U )
                        | ( uint32 ) ( ( uint32 ) 0U << 11U )
                        | ( uint32 ) ( ( uint32 ) 0U << 12U )
                        | ( uint32 ) ( ( uint32 ) 0U << 13U )
                        | ( uint32 ) ( ( uint32 ) 0U << 14U )
                        | ( uint32 ) ( ( uint32 ) 0U << 15U )
                        | ( uint32 ) ( ( uint32 ) 0U << 16U )
                        | ( uint32 ) ( ( uint32 ) 0U << 17U )
                        | ( uint32 ) ( ( uint32 ) 0U << 18U )
                        | ( uint32 ) ( ( uint32 ) 0U << 19U )
                        | ( uint32 ) ( ( uint32 ) 0U << 20U )
                        | ( uint32 ) ( ( uint32 ) 1U << 21U )
                        | ( uint32 ) ( ( uint32 ) 0U << 22U )
                        | ( uint32 ) ( ( uint32 ) 0U << 23U )
                        | ( uint32 ) ( ( uint32 ) 0U << 24U )
                        | ( uint32 ) ( ( uint32 ) 0U << 25U )
                        | ( uint32 ) ( ( uint32 ) 0U << 26U )
                        | ( uint32 ) ( ( uint32 ) 0U << 27U )
                        | ( uint32 ) ( ( uint32 ) 0U << 28U )
                        | ( uint32 ) ( ( uint32 ) 0U << 29U )
                        | ( uint32 ) ( ( uint32 ) 0U << 30U )
                        | ( uint32 ) ( ( uint32 ) 0U << 31U );

    vimREG->REQMASKSET1 = ( uint32 ) ( ( uint32 ) 0U << 0U )
                        | ( uint32 ) ( ( uint32 ) 0U << 1U )
                        | ( uint32 ) ( ( uint32 ) 0U << 2U )
                        | ( uint32 ) ( ( uint32 ) 0U << 3U )
                        | ( uint32 ) ( ( uint32 ) 0U << 4U )
                        | ( uint32 ) ( ( uint32 ) 0U << 5U )
                        | ( uint32 ) ( ( uint32 ) 0U << 6U )
                        | ( uint32 ) ( ( uint32 ) 0U << 7U )
                        | ( uint32 ) ( ( uint32 ) 0U << 8U )
                        | ( uint32 ) ( ( uint32 ) 0U << 9U )
                        | ( uint32 ) ( ( uint32 ) 0U << 10U )
                        | ( uint32 ) ( ( uint32 ) 0U << 11U )
                        | ( uint32 ) ( ( uint32 ) 0U << 12U )
                        | ( uint32 ) ( ( uint32 ) 0U << 13U )
                        | ( uint32 ) ( ( uint32 ) 0U << 14U )
                        | ( uint32 ) ( ( uint32 ) 0U << 15U )
                        | ( uint32 ) ( ( uint32 ) 0U << 16U )
                        | ( uint32 ) ( ( uint32 ) 0U << 17U )
                        | ( uint32 ) ( ( uint32 ) 0U << 18U )
                        | ( uint32 ) ( ( uint32 ) 0U << 19U )
                        | ( uint32 ) ( ( uint32 ) 0U << 20U )
                        | ( uint32 ) ( ( uint32 ) 0U << 21U )
                        | ( uint32 ) ( ( uint32 ) 0U << 22U )
                        | ( uint32 ) ( ( uint32 ) 0U << 23U )
                        | ( uint32 ) ( ( uint32 ) 0U << 24U )
                        | ( uint32 ) ( ( uint32 ) 0U << 25U )
                        | ( uint32 ) ( ( uint32 ) 0U << 26U )
                        | ( uint32 ) ( ( uint32 ) 0U << 27U )
                        | ( uint32 ) ( ( uint32 ) 0U << 28U )
                        | ( uint32 ) ( ( uint32 ) 0U << 29U )
                        | ( uint32 ) ( ( uint32 ) 0U << 30U )
                        | ( uint32 ) ( ( uint32 ) 0U << 31U );

    vimREG->REQMASKSET2 = ( uint32 ) ( ( uint32 ) 0U << 0U )
                        | ( uint32 ) ( ( uint32 ) 0U << 1U )
                        | ( uint32 ) ( ( uint32 ) 0U << 2U )
                        | ( uint32 ) ( ( uint32 ) 0U << 3U )
                        | ( uint32 ) ( ( uint32 ) 0U << 4U )
                        | ( uint32 ) ( ( uint32 ) 0U << 5U )
                        | ( uint32 ) ( ( uint32 ) 0U << 6U )
                        | ( uint32 ) ( ( uint32 ) 0U << 7U )
                        | ( uint32 ) ( ( uint32 ) 0U << 8U )
                        | ( uint32 ) ( ( uint32 ) 0U << 9U )
                        | ( uint32 ) ( ( uint32 ) 0U << 10U )
                        | ( uint32 ) ( ( uint32 ) 0U << 11U )
                        | ( uint32 ) ( ( uint32 ) 0U << 12U )
                        | ( uint32 ) ( ( uint32 ) 0U << 13U )
                        | ( uint32 ) ( ( uint32 ) 0U << 14U )
                        | ( uint32 ) ( ( uint32 ) 0U << 15U )
                        | ( uint32 ) ( ( uint32 ) 0U << 16U )
                        | ( uint32 ) ( ( uint32 ) 0U << 17U )
                        | ( uint32 ) ( ( uint32 ) 0U << 18U )
                        | ( uint32 ) ( ( uint32 ) 0U << 19U )
                        | ( uint32 ) ( ( uint32 ) 0U << 20U )
                        | ( uint32 ) ( ( uint32 ) 0U << 21U )
                        | ( uint32 ) ( ( uint32 ) 0U << 22U )
                        | ( uint32 ) ( ( uint32 ) 0U << 23U )
                        | ( uint32 ) ( ( uint32 ) 0U << 24U )
                        | ( uint32 ) ( ( uint32 ) 0U << 25U )
                        | ( uint32 ) ( ( uint32 ) 0U << 26U )
                        | ( uint32 ) ( ( uint32 ) 0U << 27U )
                        | ( uint32 ) ( ( uint32 ) 0U << 28U )
                        | ( uint32 ) ( ( uint32 ) 0U << 29U )
                        | ( uint32 ) ( ( uint32 ) 0U << 30U )
                        | ( uint32 ) ( ( uint32 ) 0U << 31U );

    vimREG->REQMASKSET3 = ( uint32 ) ( ( uint32 ) 0U << 0U )
                        | ( uint32 ) ( ( uint32 ) 0U << 1U )
                        | ( uint32 ) ( ( uint32 ) 0U << 2U )
                        | ( uint32 ) ( ( uint32 ) 0U << 3U )
                        | ( uint32 ) ( ( uint32 ) 0U << 4U )
                        | ( uint32 ) ( ( uint32 ) 0U << 5U )
                        | ( uint32 ) ( ( uint32 ) 0U << 6U )
                        | ( uint32 ) ( ( uint32 ) 0U << 7U )
                        | ( uint32 ) ( ( uint32 ) 0U << 8U )
                        | ( uint32 ) ( ( uint32 ) 0U << 9U )
                        | ( uint32 ) ( ( uint32 ) 0U << 10U )
                        | ( uint32 ) ( ( uint32 ) 0U << 11U )
                        | ( uint32 ) ( ( uint32 ) 0U << 12U )
                        | ( uint32 ) ( ( uint32 ) 0U << 13U )
                        | ( uint32 ) ( ( uint32 ) 0U << 14U )
                        | ( uint32 ) ( ( uint32 ) 0U << 15U )
                        | ( uint32 ) ( ( uint32 ) 0U << 16U )
                        | ( uint32 ) ( ( uint32 ) 0U << 17U )
                        | ( uint32 ) ( ( uint32 ) 0U << 18U )
                        | ( uint32 ) ( ( uint32 ) 0U << 19U )
                        | ( uint32 ) ( ( uint32 ) 0U << 20U )
                        | ( uint32 ) ( ( uint32 ) 0U << 21U )
                        | ( uint32 ) ( ( uint32 ) 0U << 22U )
                        | ( uint32 ) ( ( uint32 ) 0U << 23U )
                        | ( uint32 ) ( ( uint32 ) 0U << 24U )
                        | ( uint32 ) ( ( uint32 ) 0U << 25U )
                        | ( uint32 ) ( ( uint32 ) 0U << 26U )
                        | ( uint32 ) ( ( uint32 ) 0U << 27U )
                        | ( uint32 ) ( ( uint32 ) 0U << 28U )
                        | ( uint32 ) ( ( uint32 ) 0U << 29U )
                        | ( uint32 ) ( ( uint32 ) 0U << 30U )
                        | ( uint32 ) ( ( uint32 ) 0U << 31U );

    /* Set Capture event sources */
    vimREG->CAPEVT = ( ( uint32 ) ( ( uint32 ) 0U << 0U )
                       | ( uint32 ) ( ( uint32 ) 0U << 16U ) );
}

/** @fn void vimChannelMap(uint32 request, uint32 channel, t_isrFuncPTR handler)
 *   @brief Map selected interrupt request to the selected channel
 *
 *    @param[in] request: Interrupt request number 2..127
 *    @param[in] channel: VIM Channel number 2..127
 *    @param[in] handler: Address of the interrupt handler
 *
 *   This function will map selected interrupt request to the selected channel.
 *
 */
/* SourceId : VIM_SourceId_002 */
/* DesignId : VIM_DesignId_002 */
/* Requirements : HL_SR101 */
void vimChannelMap( uint32 request, uint32 channel, t_isrFuncPTR handler )
{
    uint32 i, j;

    i = channel >> 2U;         /* Find the register to configure */
    j = channel - ( i << 2U ); /* Find the offset of the type    */
    j = 3U - j;                /* reverse the byte order         */
    j = j << 3U;               /* find the bit location          */

    /*Mapping the required interrupt request to the required channel*/
    vimREG->CHANCTRL[ i ] &= ~( uint32 ) ( ( uint32 ) 0xFFU << j );
    vimREG->CHANCTRL[ i ] |= ( request << j );

    /*Updating VIMRAM*/
    vimRAM->ISR[ channel + 1U ] = handler;
}

/** @fn void vimEnableInterrupt(uint32 channel, boolean inttype)
 *   @brief Enable interrupt for the the selected channel
 *
 *    @param[in] channel: VIM Channel number 2..127
 *    @param[in] inttype: Interrupt type
 *                        - SYS_IRQ: Selected channel will be enabled as IRQ
 *                        - SYS_FIQ: Selected channel will be enabled as FIQ
 *
 *   This function will enable interrupt for the selected channel.
 *
 */
/* SourceId : VIM_SourceId_003 */
/* DesignId : VIM_DesignId_003 */
/* Requirements : HL_SR102 */
void vimEnableInterrupt( uint32 channel, systemInterrupt_t inttype )
{
    if( channel >= 96U )
    {
        if( inttype == SYS_IRQ )
        {
            vimREG->FIRQPR3 &= ~( uint32 ) ( ( uint32 ) 1U << ( channel - 96U ) );
        }
        else
        {
            vimREG->FIRQPR3 |= ( ( uint32 ) 1U << ( channel - 96U ) );
        }

        vimREG->REQMASKSET3 = ( uint32 ) 1U << ( channel - 96U );
    }
    else if( channel >= 64U )
    {
        if( inttype == SYS_IRQ )
        {
            vimREG->FIRQPR2 &= ~( uint32 ) ( ( uint32 ) 1U << ( channel - 64U ) );
        }
        else
        {
            vimREG->FIRQPR2 |= ( ( uint32 ) 1U << ( channel - 64U ) );
        }

        vimREG->REQMASKSET2 = ( uint32 ) 1U << ( channel - 64U );
    }
    else if( channel >= 32U )
    {
        if( inttype == SYS_IRQ )
        {
            vimREG->FIRQPR1 &= ~( uint32 ) ( ( uint32 ) 1U << ( channel - 32U ) );
        }
        else
        {
            vimREG->FIRQPR1 |= ( ( uint32 ) 1U << ( channel - 32U ) );
        }

        vimREG->REQMASKSET1 = ( uint32 ) 1U << ( channel - 32U );
    }
    else if( channel >= 2U )
    {
        if( inttype == SYS_IRQ )
        {
            vimREG->FIRQPR0 &= ~( uint32 ) ( ( uint32 ) 1U << channel );
        }
        else
        {
            vimREG->FIRQPR0 |= ( ( uint32 ) 1U << channel );
        }

        vimREG->REQMASKSET0 = ( uint32 ) 1U << channel;
    }
    else
    {
        /* Empty */
    }
}

/** @fn void vimDisableInterrupt(uint32 channel)
 *   @brief Disable interrupt for the the selected channel
 *
 *    @param[in] channel: VIM Channel number 2..127
 *
 *   This function will disable interrupt for the selected channel.
 *
 */
/* SourceId : VIM_SourceId_004 */
/* DesignId : VIM_DesignId_004 */
/* Requirements : HL_SR103 */
void vimDisableInterrupt( uint32 channel )
{
    if( channel >= 96U )
    {
        vimREG->REQMASKCLR3 = ( uint32 ) 1U << ( channel - 96U );
    }
    else if( channel >= 64U )
    {
        vimREG->REQMASKCLR2 = ( uint32 ) 1U << ( channel - 64U );
    }
    else if( channel >= 32U )
    {
        vimREG->REQMASKCLR1 = ( uint32 ) 1U << ( channel - 32U );
    }
    else if( channel >= 2U )
    {
        vimREG->REQMASKCLR0 = ( uint32 ) 1U << channel;
    }
    else
    {
        /* Empty */
    }
}

/* USER CODE BEGIN (1) */
/* USER CODE END */

/** @fn void vimGetConfigValue(vim_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *    @param[in] *config_reg: pointer to the struct to which the initial or current value
 * of the configuration registers need to be stored
 *    @param[in] type:     whether initial or current value of the configuration registers
 * need to be stored
 *                        - InitialValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg
 *                        - CurrentValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 * 'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : VIM_SourceId_005 */
/* DesignId : VIM_DesignId_005 */
/* Requirements : HL_SR104 */
void vimGetConfigValue( vim_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_FIRQPR0 = VIM_FIRQPR0_CONFIGVALUE;
        config_reg->CONFIG_FIRQPR1 = VIM_FIRQPR1_CONFIGVALUE;
        config_reg->CONFIG_FIRQPR2 = VIM_FIRQPR2_CONFIGVALUE;
        config_reg->CONFIG_FIRQPR3 = VIM_FIRQPR3_CONFIGVALUE;
        config_reg->CONFIG_REQMASKSET0 = VIM_REQMASKSET0_CONFIGVALUE;
        config_reg->CONFIG_REQMASKSET1 = VIM_REQMASKSET1_CONFIGVALUE;
        config_reg->CONFIG_REQMASKSET2 = VIM_REQMASKSET2_CONFIGVALUE;
        config_reg->CONFIG_REQMASKSET3 = VIM_REQMASKSET3_CONFIGVALUE;
        config_reg->CONFIG_WAKEMASKSET0 = VIM_WAKEMASKSET0_CONFIGVALUE;
        config_reg->CONFIG_WAKEMASKSET1 = VIM_WAKEMASKSET1_CONFIGVALUE;
        config_reg->CONFIG_WAKEMASKSET2 = VIM_WAKEMASKSET2_CONFIGVALUE;
        config_reg->CONFIG_WAKEMASKSET3 = VIM_WAKEMASKSET3_CONFIGVALUE;
        config_reg->CONFIG_CAPEVT = VIM_CAPEVT_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 0U ] = VIM_CHANCTRL0_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 1U ] = VIM_CHANCTRL1_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 2U ] = VIM_CHANCTRL2_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 3U ] = VIM_CHANCTRL3_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 4U ] = VIM_CHANCTRL4_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 5U ] = VIM_CHANCTRL5_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 6U ] = VIM_CHANCTRL6_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 7U ] = VIM_CHANCTRL7_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 8U ] = VIM_CHANCTRL8_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 9U ] = VIM_CHANCTRL9_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 10U ] = VIM_CHANCTRL10_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 11U ] = VIM_CHANCTRL11_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 12U ] = VIM_CHANCTRL12_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 13U ] = VIM_CHANCTRL13_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 14U ] = VIM_CHANCTRL14_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 15U ] = VIM_CHANCTRL15_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 16U ] = VIM_CHANCTRL16_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 17U ] = VIM_CHANCTRL17_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 18U ] = VIM_CHANCTRL18_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 19U ] = VIM_CHANCTRL19_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 20U ] = VIM_CHANCTRL20_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 21U ] = VIM_CHANCTRL21_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 22U ] = VIM_CHANCTRL22_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 23U ] = VIM_CHANCTRL23_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 24U ] = VIM_CHANCTRL24_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 25U ] = VIM_CHANCTRL25_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 26U ] = VIM_CHANCTRL26_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 27U ] = VIM_CHANCTRL27_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 28U ] = VIM_CHANCTRL28_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 29U ] = VIM_CHANCTRL29_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 30U ] = VIM_CHANCTRL30_CONFIGVALUE;
        config_reg->CONFIG_CHANCTRL[ 31U ] = VIM_CHANCTRL31_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_FIRQPR0 = vimREG->FIRQPR0;
        config_reg->CONFIG_FIRQPR1 = vimREG->FIRQPR1;
        config_reg->CONFIG_FIRQPR2 = vimREG->FIRQPR2;
        config_reg->CONFIG_FIRQPR3 = vimREG->FIRQPR3;
        config_reg->CONFIG_REQMASKSET0 = vimREG->REQMASKSET0;
        config_reg->CONFIG_REQMASKSET1 = vimREG->REQMASKSET1;
        config_reg->CONFIG_REQMASKSET2 = vimREG->REQMASKSET2;
        config_reg->CONFIG_REQMASKSET3 = vimREG->REQMASKSET3;
        config_reg->CONFIG_WAKEMASKSET0 = vimREG->WAKEMASKSET0;
        config_reg->CONFIG_WAKEMASKSET1 = vimREG->WAKEMASKSET1;
        config_reg->CONFIG_WAKEMASKSET2 = vimREG->WAKEMASKSET2;
        config_reg->CONFIG_WAKEMASKSET3 = vimREG->WAKEMASKSET3;
        config_reg->CONFIG_CAPEVT = vimREG->CAPEVT;
        config_reg->CONFIG_CHANCTRL[ 0U ] = vimREG->CHANCTRL[ 0U ];
        config_reg->CONFIG_CHANCTRL[ 1U ] = vimREG->CHANCTRL[ 1U ];
        config_reg->CONFIG_CHANCTRL[ 2U ] = vimREG->CHANCTRL[ 2U ];
        config_reg->CONFIG_CHANCTRL[ 3U ] = vimREG->CHANCTRL[ 3U ];
        config_reg->CONFIG_CHANCTRL[ 4U ] = vimREG->CHANCTRL[ 4U ];
        config_reg->CONFIG_CHANCTRL[ 5U ] = vimREG->CHANCTRL[ 5U ];
        config_reg->CONFIG_CHANCTRL[ 6U ] = vimREG->CHANCTRL[ 6U ];
        config_reg->CONFIG_CHANCTRL[ 7U ] = vimREG->CHANCTRL[ 7U ];
        config_reg->CONFIG_CHANCTRL[ 8U ] = vimREG->CHANCTRL[ 8U ];
        config_reg->CONFIG_CHANCTRL[ 9U ] = vimREG->CHANCTRL[ 9U ];
        config_reg->CONFIG_CHANCTRL[ 10U ] = vimREG->CHANCTRL[ 10U ];
        config_reg->CONFIG_CHANCTRL[ 11U ] = vimREG->CHANCTRL[ 11U ];
        config_reg->CONFIG_CHANCTRL[ 12U ] = vimREG->CHANCTRL[ 12U ];
        config_reg->CONFIG_CHANCTRL[ 13U ] = vimREG->CHANCTRL[ 13U ];
        config_reg->CONFIG_CHANCTRL[ 14U ] = vimREG->CHANCTRL[ 14U ];
        config_reg->CONFIG_CHANCTRL[ 15U ] = vimREG->CHANCTRL[ 15U ];
        config_reg->CONFIG_CHANCTRL[ 16U ] = vimREG->CHANCTRL[ 16U ];
        config_reg->CONFIG_CHANCTRL[ 17U ] = vimREG->CHANCTRL[ 17U ];
        config_reg->CONFIG_CHANCTRL[ 18U ] = vimREG->CHANCTRL[ 18U ];
        config_reg->CONFIG_CHANCTRL[ 19U ] = vimREG->CHANCTRL[ 19U ];
        config_reg->CONFIG_CHANCTRL[ 20U ] = vimREG->CHANCTRL[ 20U ];
        config_reg->CONFIG_CHANCTRL[ 21U ] = vimREG->CHANCTRL[ 21U ];
        config_reg->CONFIG_CHANCTRL[ 22U ] = vimREG->CHANCTRL[ 22U ];
        config_reg->CONFIG_CHANCTRL[ 23U ] = vimREG->CHANCTRL[ 23U ];
        config_reg->CONFIG_CHANCTRL[ 24U ] = vimREG->CHANCTRL[ 24U ];
        config_reg->CONFIG_CHANCTRL[ 25U ] = vimREG->CHANCTRL[ 25U ];
        config_reg->CONFIG_CHANCTRL[ 26U ] = vimREG->CHANCTRL[ 26U ];
        config_reg->CONFIG_CHANCTRL[ 27U ] = vimREG->CHANCTRL[ 27U ];
        config_reg->CONFIG_CHANCTRL[ 28U ] = vimREG->CHANCTRL[ 28U ];
        config_reg->CONFIG_CHANCTRL[ 29U ] = vimREG->CHANCTRL[ 29U ];
        config_reg->CONFIG_CHANCTRL[ 30U ] = vimREG->CHANCTRL[ 30U ];
        config_reg->CONFIG_CHANCTRL[ 31U ] = vimREG->CHANCTRL[ 31U ];
    }
}

/* SourceId : VIM_SourceId_006 */
/* DesignId : VIM_DesignId_006 */
/* Requirements : HL_SR105 */
void vimParityErrorHandler( void )
{
    uint32 vec;

    /* Identify the corrupted address */
    uint32 error_addr = VIM_ADDERR;

    /* Identify the channel number */
    uint32 error_channel = ( ( error_addr & 0x1FFU ) >> 2U );

    /* Correct the corrupted location */
    vimRAM->ISR[ error_channel ] = s_vim_init[ error_channel ];

    /* Clear Parity Error Flag */
    VIM_PARFLG = 1U;

    /* Disable and enable the highest priority pending channel */
    if( vimREG->FIQINDEX != 0U )
    {
        vec = vimREG->FIQINDEX - 1U;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Read 32 bit volatile register" */
        vec = vimREG->IRQINDEX - 1U;
    }

    if( vec == 0U )
    {
        vimREG->INTREQ0 = 1U;
        vec = esmREG->IOFFHR - 1U;

        if( vec < 32U )
        {
            esmREG->SR1[ 0U ] = ( uint32 ) 1U << vec;
            esmGroup1Notification( vec );
        }
        else if( vec < 64U )
        {
            esmREG->SR1[ 1U ] = ( uint32 ) 1U << ( vec - 32U );
            esmGroup2Notification( vec - 32U );
        }
        else if( vec < 96U )
        {
            esmREG->SR4[ 0U ] = ( uint32 ) 1U << ( vec - 64U );
            esmGroup1Notification( vec - 32U );
        }
        else
        {
            esmREG->SR4[ 1U ] = ( uint32 ) 1U << ( vec - 96U );
            esmGroup2Notification( vec - 64U );
        }
    }
    else if( vec < 32U )
    {
        vimREG->REQMASKCLR0 = ( uint32 ) 1U << vec;
        vimREG->REQMASKSET0 = ( uint32 ) 1U << vec;
    }
    else if( vec < 64U )
    {
        vimREG->REQMASKCLR1 = ( uint32 ) 1U << ( vec - 32U );
        vimREG->REQMASKSET1 = ( uint32 ) 1U << ( vec - 32U );
    }
    else if( vec < 96U )
    {
        vimREG->REQMASKCLR2 = ( uint32 ) 1U << ( vec - 64U );
        vimREG->REQMASKSET2 = ( uint32 ) 1U << ( vec - 64U );
    }
    else
    {
        vimREG->REQMASKCLR3 = ( uint32 ) 1U << ( vec - 96U );
        vimREG->REQMASKSET3 = ( uint32 ) 1U << ( vec - 96U );
    }
}
