/** @file sys_startup.c
 *   @brief Startup Source File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Include Files
 *   - Type Definitions
 *   - External Functions
 *   - VIM RAM Setup
 *   - Startup Routine
 *   .
 *   which are relevant for the Startup.
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

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Include Files */

#include "sys_common.h"
#include "system.h"
#include "sys_vim.h"
#include "sys_core.h"
#include "sys_selftest.h"
#include "esm.h"
#include "mibspi.h"

#include "errata_SSWF021_45.h"
/* USER CODE BEGIN (1) */
/* USER CODE END */

/* USER CODE BEGIN (2) */
/* USER CODE END */

/* External Functions */
/*SAFETYMCUSW 354 S MR:NA <APPROVED> " Startup code(main should be declared by the user)"
 */
extern void main( void );
/*SAFETYMCUSW 122 S MR:20.11 <APPROVED> "Startup code(exit and abort need to be present)"
 */
/*SAFETYMCUSW 354 S MR:NA <APPROVED> " Startup code(Extern declaration present in the
 * library)" */
extern void exit( int _status );

/* USER CODE BEGIN (3) */
/* USER CODE END */
void handlePLLLockFail( void );
/* Startup Routine */
void _c_int00( void ) __attribute__( ( noreturn ) );
#define PLL_RETRIES 5U
/* USER CODE BEGIN (4) */
/* USER CODE END */

__attribute__( ( naked ) )

/* SourceId : STARTUP_SourceId_001 */
/* DesignId : STARTUP_DesignId_001 */
/* Requirements : HL_SR508 */
void _c_int00( void )
{
    /* USER CODE BEGIN (5) */
    /* USER CODE END */

    /* Initialize Core Registers to avoid CCM Error */
    _coreInitRegisters_();

    /* USER CODE BEGIN (6) */
    /* USER CODE END */

    /* Initialize Stack Pointers */
    _coreInitStackPointer_();

    /* USER CODE BEGIN (7) */
    /* USER CODE END */

    /* Enable CPU Event Export */

    /* This allows the CPU to signal any single-bit or double-bit errors detected
     * by its ECC logic for accesses to program flash or data RAM.
     */
    _coreEnableEventBusExport_();

    /* USER CODE BEGIN (11) */
    /* USER CODE END */

    /* Workaround for Errata CORTEXR4 66 */
    _errata_CORTEXR4_66_();

    /* Workaround for Errata CORTEXR4 57 */
    _errata_CORTEXR4_57_();

    /* Reset handler: the following instructions read from the system exception status
     * register to identify the cause of the CPU reset.
     */

    /* check for power-on reset condition */
    /*SAFETYMCUSW 139 S MR:13.7 <APPROVED> "Hardware status bit read check" */
    if( ( SYS_EXCEPTION & POWERON_RESET ) != 0U )
    {
        /* USER CODE BEGIN (12) */
        /* USER CODE END */
        /* Add condition to check whether PLL can be started successfully */
        if( _errata_SSWF021_45_both_plls( PLL_RETRIES ) != 0U )
        {
            /* Put system in a safe state */
            handlePLLLockFail();
        }

        /* clear all reset status flags */
        SYS_EXCEPTION = 0xFFFFU;

        /* USER CODE BEGIN (13) */
        /* USER CODE END */
        /* USER CODE BEGIN (14) */
        /* USER CODE END */
        /* USER CODE BEGIN (15) */
        /* USER CODE END */
        /* continue with normal start-up sequence */
    }
    /*SAFETYMCUSW 139 S MR:13.7 <APPROVED> "Hardware status bit read check" */
    else if( ( SYS_EXCEPTION & OSC_FAILURE_RESET ) != 0U )
    {
        /* Reset caused due to oscillator failure.
         * Add user code here to handle oscillator failure */

        /* USER CODE BEGIN (16) */
        /* USER CODE END */
    }
    /*SAFETYMCUSW 139 S MR:13.7 <APPROVED> "Hardware status bit read check" */
    else if( ( SYS_EXCEPTION & WATCHDOG_RESET ) != 0U )
    {
        /* Reset caused due
         *  1) windowed watchdog violation - Add user code here to handle watchdog
         * violation. 2) ICEPICK Reset - After loading code via CCS / System Reset through
         * CCS
         */
        /* Check the WatchDog Status register */
        if( WATCHDOG_STATUS != 0U )
        {
            /* Add user code here to handle watchdog violation. */
            /* USER CODE BEGIN (17) */
            /* USER CODE END */

            /* Clear the Watchdog reset flag in Exception Status register */
            SYS_EXCEPTION = WATCHDOG_RESET;

            /* USER CODE BEGIN (18) */
            /* USER CODE END */
        }
        else
        {
            /* Clear the ICEPICK reset flag in Exception Status register */
            SYS_EXCEPTION = ICEPICK_RESET;
            /* USER CODE BEGIN (19) */
            /* USER CODE END */
        }
    }
    /*SAFETYMCUSW 139 S MR:13.7 <APPROVED> "Hardware status bit read check" */
    else if( ( SYS_EXCEPTION & CPU_RESET ) != 0U )
    {
        /* Reset caused due to CPU reset.
         * CPU reset can be caused by CPU self-test completion, or
         * by toggling the "CPU RESET" bit of the CPU Reset Control Register. */

        /* USER CODE BEGIN (20) */
        /* USER CODE END */

        /* clear all reset status flags */
        SYS_EXCEPTION = CPU_RESET;

        /* USER CODE BEGIN (21) */
        /* USER CODE END */
    }
    /*SAFETYMCUSW 139 S MR:13.7 <APPROVED> "Hardware status bit read check" */
    else if( ( SYS_EXCEPTION & SW_RESET ) != 0U )
    {
        /* Reset caused due to software reset.
         * Add user code to handle software reset. */

        /* USER CODE BEGIN (22) */
        /* USER CODE END */
    }
    else
    {
        /* Reset caused by nRST being driven low externally.
         * Add user code to handle external reset. */

        /* USER CODE BEGIN (23) */
        /* USER CODE END */
    }

    /* Check if there were ESM group3 errors during power-up.
     * These could occur during eFuse auto-load or during reads from flash OTP
     * during power-up. Device operation is not reliable and not recommended
     * in this case.
     * An ESM group3 error only drives the nERROR pin low. An external circuit
     * that monitors the nERROR pin must take the appropriate action to ensure that
     * the system is placed in a safe state, as determined by the application.
     */
    if( ( esmREG->SR1[ 2 ] ) != 0U )
    {
        /* USER CODE BEGIN (24) */
        /* USER CODE END */
        /*SAFETYMCUSW 5 C MR:NA <APPROVED> "for(;;) can be removed by adding "# if 0" and
         * "# endif" in the user codes above and below" */
        /*SAFETYMCUSW 26 S MR:NA <APPROVED> "for(;;) can be removed by adding "# if 0" and
         * "# endif" in the user codes above and below" */
        /*SAFETYMCUSW 28 D MR:NA <APPROVED> "for(;;) can be removed by adding "# if 0" and
         * "# endif" in the user codes above and below" */
        for( ;; )
        {
        } /* Wait */

        /* USER CODE BEGIN (25) */
        /* USER CODE END */
    }

    /* USER CODE BEGIN (26) */
    /* USER CODE END */

    /* Initialize System - Clock, Flash settings with Efuse self check */
    systemInit();

    /* Run PBIST on STC ROM */
    pbistRun( ( uint32 ) STC_ROM_PBIST_RAM_GROUP,
              ( ( uint32 ) PBIST_TripleReadSlow | ( uint32 ) PBIST_TripleReadFast ) );

    /* Wait for PBIST for STC ROM to be completed */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( pbistIsTestCompleted() != TRUE )
    {
    } /* Wait */

    /* Check if PBIST on STC ROM passed the self-test */
    if( pbistIsTestPassed() != TRUE )
    {
        /* PBIST and STC ROM failed the self-test.
         * Need custom handler to check the memory failure
         * and to take the appropriate next step.
         */

        pbistFail();
    }

    /* Disable PBIST clocks and disable memory self-test mode */
    pbistStop();

    /* Run PBIST on PBIST ROM */
    pbistRun( ( uint32 ) PBIST_ROM_PBIST_RAM_GROUP,
              ( ( uint32 ) PBIST_TripleReadSlow | ( uint32 ) PBIST_TripleReadFast ) );

    /* Wait for PBIST for PBIST ROM to be completed */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( pbistIsTestCompleted() != TRUE )
    {
    } /* Wait */

    /* Check if PBIST ROM passed the self-test */
    if( pbistIsTestPassed() != TRUE )
    {
        /* PBIST and STC ROM failed the self-test.
         * Need custom handler to check the memory failure
         * and to take the appropriate next step.
         */

        pbistFail();
    }

    /* Disable PBIST clocks and disable memory self-test mode */
    pbistStop();
    /* USER CODE BEGIN (29) */
    /* USER CODE END */

    /* USER CODE BEGIN (31) */
    /* USER CODE END */

    /* USER CODE BEGIN (37) */
    /* USER CODE END */

    /* Initialize CPU RAM.
     * This function uses the system module's hardware for auto-initialization of memories
     * and their associated protection schemes. The CPU RAM is initialized by setting bit
     * 0 of the MSIENA register. Hence the value 0x1 passed to the function. This function
     * will initialize the entire CPU RAM and the corresponding ECC locations.
     */
    memoryInit( 0x1U );

    /* USER CODE BEGIN (38) */
    /* USER CODE END */

    /* Enable ECC checking for TCRAM accesses.
     * This function enables the CPU's ECC logic for accesses to B0TCM and B1TCM.
     */
    _coreEnableRamEcc_();

    /* USER CODE BEGIN (39) */
    /* USER CODE END */

    /* USER CODE BEGIN (55) */
    /* USER CODE END */

    /* USER CODE BEGIN (68) */
    /* USER CODE END */

    /* USER CODE BEGIN (72) */
    /* USER CODE END */

    /* Enable IRQ offset via Vic controller */
    _coreEnableIrqVicOffset_();

    /* USER CODE BEGIN (73) */
    /* USER CODE END */

    /* Initialize VIM table */
    vimInit();

    /* USER CODE BEGIN (74) */
    /* USER CODE END */

    /* Configure system response to error conditions signaled to the ESM group1 */
    /* This function can be configured from the ESM tab of HALCoGen */
    esmInit();
    {
        extern uint32 _sidata, _sdata, _edata;
        extern uint32 _siPrivData, __privileged_data_start__, __privileged_data_end__;
        uint32 *src, *dst;

        src = &_sidata;
        dst = &_sdata;

        while( dst < &_edata )
        {
            *dst++ = *src++;
        }

        src = &_siPrivData;
        dst = &__privileged_data_start__;

        while( dst < &__privileged_data_end__ )
        {
            *dst++ = *src++;
        }
    }
    /* USER CODE BEGIN (75) */
    /* USER CODE END */

    /* call the application */
    /*SAFETYMCUSW 296 S MR:8.6 <APPROVED> "Startup code(library functions at block scope)"
     */
    /*SAFETYMCUSW 326 S MR:8.2 <APPROVED> "Startup code(Declaration for main in library)"
     */
    /*SAFETYMCUSW 60 D MR:8.8 <APPROVED> "Startup code(Declaration for main in
     * library;Only doing an extern for the same)" */
    main();

    /*SAFETYMCUSW 122 S MR:20.11 <APPROVED> "Startup code(exit and abort need to be
     * present)" */
    exit( 0 );
    /* USER CODE BEGIN (77) */
    /* USER CODE END */
}

/* USER CODE BEGIN (78) */
/* USER CODE END */

/** @fn void handlePLLLockFail(void)
 *   @brief This function handles PLL lock fail.
 */
void handlePLLLockFail( void )
{
    /* USER CODE BEGIN (79) */
    /* USER CODE END */
    while( 1 )
    {
    }

    /* USER CODE BEGIN (80) */
    /* USER CODE END */
}
/* USER CODE BEGIN (81) */
/* USER CODE END */
