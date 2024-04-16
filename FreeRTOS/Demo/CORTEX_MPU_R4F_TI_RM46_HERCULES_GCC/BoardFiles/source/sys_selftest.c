/** @file sys_selftest.c
 *   @brief Selftest Source File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Selftest API's
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

#include "sys_selftest.h"
#include "sys_core.h"
#include "sys_pmu.h"

/** @fn void selftestFailNotification(uint32 flag)
 *   @brief Self test fail service routine
 *
 *    This function is called if there is a self test fail with appropriate flag
 */
void selftestFailNotification( uint32 flag )
{
    /* USER CODE BEGIN (1) */
    /* USER CODE END */
}

/* USER CODE BEGIN (2) */
/* USER CODE END */

/** @fn void ccmSelfCheck(void)
 *   @brief CCM module self check Driver
 *
 *   This function self checks the CCM module.
 */
/* SourceId : SELFTEST_SourceId_001 */
/* DesignId : SELFTEST_DesignId_001 */
/* Requirements : HL_SR395 */
void ccmSelfCheck( void )
{
    /* USER CODE BEGIN (3) */
    /* USER CODE END */

    /* Run a diagnostic check on the CCM-R4F module */
    /* This step ensures that the CCM-R4F can actually indicate an error */

    /* Configure CCM in self-test mode */
    CCMKEYR = 0x6U;

    /* Wait for CCM self-test to complete */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( CCMSR & 0x100U ) != 0x100U )
    {
    } /* Wait */

    /* USER CODE BEGIN (4) */
    /* USER CODE END */

    /* Check if there was an error during the self-test */
    if( ( CCMSR & 0x1U ) == 0x1U )
    {
        /* STE is set */
        selftestFailNotification( CCMSELFCHECK_FAIL1 );
    }
    else
    {
        /* Check CCM-R4 self-test error flag by itself (without compare error) */
        if( ( esmREG->SR1[ 0U ] & 0x80000000U ) == 0x80000000U )
        {
            /* ESM flag is not set */
            selftestFailNotification( CCMSELFCHECK_FAIL2 );
        }
        else
        {
            /* Configure CCM in error-forcing mode */
            CCMKEYR = 0x9U;

            /* Wait till error-forcing is completed. */
            /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
            while( CCMKEYR != 0U )
            {
            } /* Wait */

            /* check if compare error flag is set */
            if( ( esmREG->SR1[ 1U ] & 0x4U ) != 0x4U )
            {
                /* ESM flag is not set */
                selftestFailNotification( CCMSELFCHECK_FAIL3 );
            }
            else
            {
                /* Check FIQIVEC to ESM High Interrupt flag is set */
                if( ( vimREG->FIQINDEX & 0x000000FFU ) != 1U )
                {
                    /* ESM High Interrupt flag is not set in VIM*/
                    selftestFailNotification( CCMSELFCHECK_FAIL4 );
                }

                /* clear ESM group2 channel 2 flag */
                esmREG->SR1[ 1U ] = 0x4U;

                /* clear ESM group2 shadow status flag */
                esmREG->SSR2 = 0x4U;

                /* ESM self-test error needs to also be cleared */
                esmREG->SR1[ 0U ] = 0x80000000U;

                /* The nERROR pin will become inactive once the LTC counter expires */
                esmREG->EKR = 0x5U;

                /* Configure CCM in selftest error-forcing mode */
                CCMKEYR = 0xFU;

                /* Wait till selftest error-forcing is completed. */
                /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
                while( CCMKEYR != 0U )
                {
                } /* Wait */

                if( ( esmREG->SR1[ 0U ] & 0x80000000U ) != 0x80000000U )
                {
                    /* ESM flag not set */
                    selftestFailNotification( CCMSELFCHECK_FAIL2 );
                }
                else
                {
                    /* clear ESM flag */
                    esmREG->SR1[ 0U ] = 0x80000000U;
                }
            }
        }
    }
}

/* USER CODE BEGIN (5) */
/* USER CODE END */

/** @fn void memoryInit(uint32 ram)
 *   @brief Memory Initialization Driver
 *
 *   This function is called to perform Memory initialization of selected RAM's.
 */
/* SourceId : SELFTEST_SourceId_002 */
/* DesignId : SELFTEST_DesignId_004 */
/* Requirements : HL_SR396 */
void memoryInit( uint32 ram )
{
    /* USER CODE BEGIN (6) */
    /* USER CODE END */

    /* Enable Memory Hardware Initialization */
    systemREG1->MINITGCR = 0xAU;

    /* Enable Memory Hardware Initialization for selected RAM's */
    systemREG1->MSINENA = ram;

    /* Wait until Memory Hardware Initialization complete */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( systemREG1->MSTCGSTAT & 0x00000100U ) != 0x00000100U )
    {
    } /* Wait */

    /* Disable Memory Hardware Initialization */
    systemREG1->MINITGCR = 0x5U;

    /* USER CODE BEGIN (7) */
    /* USER CODE END */
}

/** @fn void stcSelfCheck(void)
 *   @brief STC module self check Driver
 *
 *   This function is called to perform STC module self check.
 */
/* SourceId : SELFTEST_SourceId_003 */
/* DesignId : SELFTEST_DesignId_002 */
/* Requirements : HL_SR397 */
void stcSelfCheck( void )
{
    /* USER CODE BEGIN (8) */
    /* USER CODE END */
    volatile uint32 i = 0U;

    /* Run a diagnostic check on the CPU self-test controller */
    /* First set up the STC clock divider as STC is only supported up to 90MHz */

    /* STC clock is now normal mode CPU clock frequency/2 = 180MHz/2 */
    systemREG2->STCCLKDIV = 0x01000000U;

    /* Select one test interval, restart self-test next time, 0x00010001 */
    stcREG->STCGCR0 = 0x00010001U;

    /* Enable comparator self-check and stuck-at-0 fault insertion in CPU, 0x1A */
    stcREG->STCSCSCR = 0x1AU;

    /* Maximum time-out period */
    stcREG->STCTPR = 0xFFFFFFFFU;

    /* wait for 16 VBUS clock cycles at least, based on HCLK to VCLK ratio */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Wait for few clock cycles (Value of i not
     * used)" */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Wait for few clock cycles (Value of i not
     * used)" */
    for( i = 0U; i < ( 16U + ( 16U * 1U ) ); i++ )
    { /* Wait */
    }

    /* Enable self-test */
    stcREG->STCGCR1 = 0xAU;

    /* USER CODE BEGIN (9) */
    /* USER CODE END */

    /* Idle the CPU so that the self-test can start */
    _gotoCPUIdle_();

    /* USER CODE BEGIN (10) */
    /* USER CODE END */
}

/** @fn void cpuSelfTest(uint32 no_of_intervals, uint32 max_timeout, boolean restart_test)
 *   @brief CPU self test Driver
 *   @param[in] no_of_intervals - Number of Test Intervals to be
 *   @param[in] max_timeout     - Maximum Timeout to complete selected test Intervals
 *   @param[in] restart_test    - Restart the test from Interval 0 or Continue from where
 * it stopped.
 *
 *   This function is called to perform CPU self test using STC module.
 */
/* SourceId : SELFTEST_SourceId_004 */
/* DesignId : SELFTEST_DesignId_003 */
/* Requirements : HL_SR398 */
void cpuSelfTest( uint32 no_of_intervals, uint32 max_timeout, boolean restart_test )
{
    volatile uint32 i = 0U;

    /* USER CODE BEGIN (11) */
    /* USER CODE END */

    /* Run specified no of test intervals starting from interval 0 */
    /* Start test from interval 0 or continue the test. */
    stcREG->STCGCR0 = no_of_intervals << 16U;

    if( restart_test )
    {
        stcREG->STCGCR0 |= 0x00000001U;
    }

    /* Configure Maximum time-out period */
    stcREG->STCTPR = max_timeout;

    /* wait for 16 VBUS clock cycles at least, based on HCLK to VCLK ratio */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Wait for few clock cycles (Value of i not
     * used)" */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Wait for few clock cycles (Value of i not
     * used)" */
    for( i = 0U; i < ( 16U + ( 16U * 1U ) ); i++ )
    { /* Wait */
    }

    /* Enable self-test */
    stcREG->STCGCR1 = 0xAU;

    /* USER CODE BEGIN (12) */
    /* USER CODE END */
    /* Idle the CPU so that the self-test can start */

    _gotoCPUIdle_();
}

/** @fn void pbistSelfCheck(void)
 *   @brief PBIST self test Driver
 *
 *   This function is called to perform PBIST self test.
 *
 *   @note This Function uses register's which are not exposed to users through
 *   TRM , to run custom algorithm to make PBIST Fail. Users can use this function as
 * Black box.
 *
 */
/* SourceId : SELFTEST_SourceId_005 */
/* DesignId : SELFTEST_DesignId_005 */
/* Requirements : HL_SR399 */
void pbistSelfCheck( void )
{
    volatile uint32 i = 0U;
    uint32 PBIST_wait_done_loop = 0U;

    /* USER CODE BEGIN (13) */
    /* USER CODE END */
    /* Run a diagnostic check on the memory self-test controller */
    /* First set up the PBIST ROM clock as this clock frequency is limited to 90MHz */

    /* Disable PBIST clocks and ROM clock */
    pbistREG->PACT = 0x0U;

    /* PBIST ROM clock frequency = HCLK frequency /2 */
    /* Disable memory self controller */
    systemREG1->MSTGCR = 0x00000105U;

    /* Disable Memory Initialization controller */
    systemREG1->MINITGCR = 0x5U;

    /* Enable memory self controller */
    systemREG1->MSTGCR = 0x0000010AU;

    /* Clear PBIST Done */
    systemREG1->MSTCGSTAT = 0x1U;

    /* Enable PBIST controller */
    systemREG1->MSINENA = 0x1U;

    /* wait for 32 VBUS clock cycles at least, based on HCLK to VCLK ratio */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Wait for few clock cycles (Value of i not
     * used)" */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Wait for few clock cycles (Value of i not
     * used)" */
    for( i = 0U; i < ( 32U + ( 32U * 1U ) ); i++ )
    { /* Wait */
    }

    /* USER CODE BEGIN (14) */
    /* USER CODE END */

    /* Enable PBIST clocks and ROM clock */
    pbistREG->PACT = 0x3U;

    /* CPU control of PBIST */
    pbistREG->DLR = 0x10U;

    /* Custom always fail algo, this will not use the ROM and just set a fail */
    pbistREG->RAMT = 0x00002000U;
    *( volatile uint32 * ) 0xFFFFE400U = 0x4C000001U;
    *( volatile uint32 * ) 0xFFFFE440U = 0x00000075U;
    *( volatile uint32 * ) 0xFFFFE404U = 0x4C000002U;
    *( volatile uint32 * ) 0xFFFFE444U = 0x00000075U;
    *( volatile uint32 * ) 0xFFFFE408U = 0x4C000003U;
    *( volatile uint32 * ) 0xFFFFE448U = 0x00000075U;
    *( volatile uint32 * ) 0xFFFFE40CU = 0x4C000004U;
    *( volatile uint32 * ) 0xFFFFE44CU = 0x00000075U;
    *( volatile uint32 * ) 0xFFFFE410U = 0x4C000005U;
    *( volatile uint32 * ) 0xFFFFE450U = 0x00000075U;
    *( volatile uint32 * ) 0xFFFFE414U = 0x4C000006U;
    *( volatile uint32 * ) 0xFFFFE454U = 0x00000075U;
    *( volatile uint32 * ) 0xFFFFE418U = 0x00000000U;
    *( volatile uint32 * ) 0xFFFFE458U = 0x00000001U;

    /* PBIST_RUN */
    pbistREG->rsvd1[ 1U ] = 1U;

    /* wait until memory self-test done is indicated */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( systemREG1->MSTCGSTAT & 0x1U ) != 0x1U )
    {
        PBIST_wait_done_loop++;
    } /* Wait */

    /* Check for the failure */
    if( ( pbistREG->FSRF0 & 0x1U ) != 0x1U )
    {
        /* No failure was indicated even if the always fail algorithm was run*/
        selftestFailNotification( PBISTSELFCHECK_FAIL1 );

        /* USER CODE BEGIN (15) */
        /* USER CODE END */
    }
    else
    {
        /* Check that the algorithm executed in the expected amount of time. */
        /* This time is dependent on the ROMCLKDIV selected above            */
        if( PBIST_wait_done_loop >= 2U )
        {
            selftestFailNotification( PBISTSELFCHECK_FAIL2 );
        }

        /* Disable PBIST clocks and ROM clock */
        pbistREG->PACT = 0x0U;

        /* Disable PBIST */
        systemREG1->MSTGCR &= 0xFFFFFFF0U;
        systemREG1->MSTGCR |= 0x5U;

        /* USER CODE BEGIN (16) */
        /* USER CODE END */
    }
}

/** @fn void pbistRun(uint32 raminfoL, uint32 algomask)
 *   @brief CPU self test Driver
 *   @param[in] raminfoL   - Select the list of RAM to be tested.
 *   @param[in] algomask   - Select the list of Algorithm to be run.
 *
 *   This function performs Memory Built-in Self test using PBIST module.
 */
/* SourceId : SELFTEST_SourceId_006 */
/* DesignId : SELFTEST_DesignId_006 */
/* Requirements : HL_SR400 */
void pbistRun( uint32 raminfoL, uint32 algomask )
{
    volatile uint32 i = 0U;

    /* USER CODE BEGIN (17) */
    /* USER CODE END */

    /* PBIST ROM clock frequency = HCLK frequency /2 */
    /* Disable memory self controller */
    systemREG1->MSTGCR = 0x00000105U;

    /* Disable Memory Initialization controller */
    systemREG1->MINITGCR = 0x5U;

    /* Enable PBIST controller */
    systemREG1->MSINENA = 0x1U;

    /* Enable memory self controller */
    systemREG1->MSTGCR = 0x0000010AU;

    /* wait for 32 VBUS clock cycles at least, based on HCLK to VCLK ratio */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Wait for few clock cycles (Value of i not
     * used)" */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Wait for few clock cycles (Value of i not
     * used)" */
    for( i = 0U; i < ( 32U + ( 32U * 1U ) ); i++ )
    { /* Wait */
    }

    /* USER CODE BEGIN (18) */
    /* USER CODE END */

    /* Enable PBIST clocks and ROM clock */
    pbistREG->PACT = 0x3U;

    /* Select all algorithms to be tested */
    pbistREG->ALGO = algomask;

    /* Select RAM groups */
    pbistREG->RINFOL = raminfoL;

    /* Select all RAM groups */
    pbistREG->RINFOU = 0x00000000U;

    /* ROM contents will not override RINFOx settings */
    pbistREG->OVER = 0x0U;

    /* Algorithm code is loaded from ROM */
    pbistREG->ROM = 0x3U;

    /* Start PBIST */
    pbistREG->DLR = 0x14U;

    /* USER CODE BEGIN (19) */
    /* USER CODE END */
}

/** @fn void pbistStop(void)
 *   @brief Routine to stop PBIST test enabled.
 *
 *   This function is called to stop PBIST after test is performed.
 */
/* SourceId : SELFTEST_SourceId_007 */
/* DesignId : SELFTEST_DesignId_007 */
/* Requirements : HL_SR523 */
void pbistStop( void )
{
    /* USER CODE BEGIN (20) */
    /* USER CODE END */
    /* disable pbist clocks and ROM clock */
    pbistREG->PACT = 0x0U;
    systemREG1->MSTGCR &= 0xFFFFFFF0U;
    systemREG1->MSTGCR |= 0x5U;
    /* USER CODE BEGIN (21) */
    /* USER CODE END */
}

/** @fn boolean pbistIsTestCompleted(void)
 *   @brief Checks to see if the PBIST test is completed.
 *   @return 1 if PBIST test completed, otherwise 0.
 *
 *   Checks to see if the PBIST test is completed.
 */
/* SourceId : SELFTEST_SourceId_008 */
/* DesignId : SELFTEST_DesignId_008 */
/* Requirements : HL_SR401 */
boolean pbistIsTestCompleted( void )
{
    /* USER CODE BEGIN (22) */
    /* USER CODE END */

    return ( ( systemREG1->MSTCGSTAT & 0x1U ) != 0U );
    /* USER CODE BEGIN (23) */
    /* USER CODE END */
}

/** @fn boolean pbistIsTestPassed(void)
 *   @brief Checks to see if the PBIST test is completed successfully.
 *   @return 1 if PBIST test passed, otherwise 0.
 *
 *   Checks to see if the PBIST test is completed successfully.
 */
/* SourceId : SELFTEST_SourceId_009 */
/* DesignId : SELFTEST_DesignId_009 */
/* Requirements : HL_SR401 */
boolean pbistIsTestPassed( void )
{
    /* USER CODE BEGIN (24) */
    /* USER CODE END */
    boolean status;

    if( pbistREG->FSRF0 == 0U )
    {
        status = TRUE;
    }
    else
    {
        status = FALSE;
    }

    /* USER CODE BEGIN (25) */
    /* USER CODE END */
    return status;
}

/** @fn boolean pbistPortTestStatus(uint32 port)
 *   @brief Checks to see if the PBIST Port test is completed successfully.
 *   @param[in] port   - Select the port to get the status.
 *   @return 1 if PBIST Port test completed successfully, otherwise 0.
 *
 *   Checks to see if the selected PBIST Port test is completed successfully.
 */
/* SourceId : SELFTEST_SourceId_010 */
/* DesignId : SELFTEST_DesignId_010 */
/* Requirements : HL_SR401 */
boolean pbistPortTestStatus( uint32 port )
{
    boolean status;

    /* USER CODE BEGIN (26) */
    /* USER CODE END */

    if( port == ( uint32 ) PBIST_PORT0 )
    {
        status = ( pbistREG->FSRF0 == 0U );
    }
    else
    {
        /* Invalid Input */
        status = FALSE;
    }

    return status;
}

/** @fn uint32 efcCheck(void)
 *   @brief EFUSE module self check Driver
 *   @return Returns 0 if no error was detected during autoload and Stuck At Zero Test
 * passed 1 if no error was detected during autoload but Stuck At Zero Test failed 2 if
 * there was a single-bit error detected during autoload 3 if some other error occurred
 * during autoload
 *
 *   This function self checks the EFUSE module.
 */
/* SourceId : SELFTEST_SourceId_011 */
/* DesignId : SELFTEST_DesignId_012 */
/* Requirements : HL_SR402 */
uint32 efcCheck( void )
{
    uint32 efcStatus = 0U;
    uint32 status;

    /* USER CODE BEGIN (27) */
    /* USER CODE END */

    /* read the EFC Error Status Register */
    efcStatus = efcREG->ERROR;

    /* USER CODE BEGIN (28) */
    /* USER CODE END */

    if( efcStatus == 0x0U )
    {
        /* run stuck-at-zero test and check if it passed */
        if( efcStuckZeroTest() == TRUE )
        {
            /* start EFC ECC logic self-test */
            efcSelfTest();
            status = 0U;
        }
        else
        {
            /* EFC output is stuck-at-zero, device operation unreliable */
            selftestFailNotification( EFCCHECK_FAIL1 );
            status = 1U;
        }
    }
    /* EFC Error Register is not zero */
    else
    {
        /* one-bit error detected during autoload */
        if( efcStatus == 0x15U )
        {
            /* start EFC ECC logic self-test */
            efcSelfTest();
            status = 2U;
        }
        else
        {
            /* Some other EFC error was detected */
            selftestFailNotification( EFCCHECK_FAIL1 );
            status = 3U;
        }
    }

    return status;
}

/** @fn boolean efcStuckZeroTest(void)
 *   @brief Checks to see if the EFUSE Stuck at zero test is completed successfully.
 *   @return 1 if EFUSE Stuck at zero test completed, otherwise 0.
 *
 *   Checks to see if the EFUSE Stuck at zero test is completed successfully.
 */
/* SourceId : SELFTEST_SourceId_012 */
/* DesignId : SELFTEST_DesignId_014 */
/* Requirements : HL_SR402 */
boolean efcStuckZeroTest( void )
{
    /* USER CODE BEGIN (29) */
    /* USER CODE END */

    uint32 ESM_ESTATUS4, ESM_ESTATUS1;

    boolean result = FALSE;
    uint32 error_checks = EFC_INSTRUCTION_INFO_EN | EFC_INSTRUCTION_ERROR_EN
                        | EFC_AUTOLOAD_ERROR_EN | EFC_SELF_TEST_ERROR_EN;

    /* configure the output enable for auto load error , instruction info,
     *   instruction error, and self test error using boundary register
     *   and drive values one across all the errors */
    efcREG->BOUNDARY = ( ( uint32 ) OUTPUT_ENABLE | error_checks );

    /* Read from the pin register. This register holds the current values
     *   of above errors. This value should be 0x5c00.If not at least one of
     *   the above errors is stuck at 0. */
    if( ( efcREG->PINS & 0x5C00U ) == 0x5C00U )
    {
        ESM_ESTATUS4 = esmREG->SR4[ 0U ];
        ESM_ESTATUS1 = esmREG->SR1[ 2U ];

        /* check if the ESM group1 channel 41 is set and group3 channel 1 is set */
        if( ( ( ESM_ESTATUS4 & 0x200U ) == 0x200U )
            && ( ( ESM_ESTATUS1 & 0x2U ) == 0x2U ) )
        {
            /* stuck-at-zero test passed */
            result = TRUE;
        }
    }

    /* put the pins back low */
    efcREG->BOUNDARY = OUTPUT_ENABLE;

    /* clear group1 flag */
    esmREG->SR4[ 0U ] = 0x200U;

    /* clear group3 flag */
    esmREG->SR1[ 2U ] = 0x2U;

    /* The nERROR pin will become inactive once the LTC counter expires */
    esmREG->EKR = 0x5U;

    return result;
}

/** @fn void efcSelfTest(void)
 *   @brief EFUSE module self check Driver
 *
 *   This function self checks the EFSUE module.
 */
/* SourceId : SELFTEST_SourceId_013 */
/* DesignId : SELFTEST_DesignId_013 */
/* Requirements : HL_SR402 */
void efcSelfTest( void )
{
    /* USER CODE BEGIN (30) */
    /* USER CODE END */
    /* configure self-test cycles */
    efcREG->SELF_TEST_CYCLES = 0x258U;

    /* configure self-test signature */
    efcREG->SELF_TEST_SIGN = 0x5362F97FU;

    /* configure boundary register to start ECC self-test */
    efcREG->BOUNDARY = 0x0000200FU;
}

/** @fn boolean checkefcSelfTest(void)
 *   @brief EFUSE module self check Driver
 *   @return Returns TRUE if EFC Selftest was a PASS, else FALSE
 *
 *   This function returns the status of efcSelfTest.
 *   Note: This function can be called only after calling efcSelfTest
 */
/* SourceId : SELFTEST_SourceId_014 */
/* DesignId : SELFTEST_DesignId_015 */
/* Requirements : HL_SR403 */
boolean checkefcSelfTest( void )
{
    /* USER CODE BEGIN (31) */
    /* USER CODE END */
    boolean result = FALSE;

    uint32 EFC_PINS, EFC_ERROR;
    uint32 esmCh40Stat, esmCh41Stat = 0U;

    /* wait until EFC self-test is done */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( efcREG->PINS & EFC_SELF_TEST_DONE ) == 0U )
    {
    } /* Wait */

    /* check if EFC self-test error occurred */
    EFC_PINS = efcREG->PINS;
    EFC_ERROR = efcREG->ERROR;

    if( ( ( EFC_PINS & EFC_SELF_TEST_ERROR ) == 0U ) && ( ( EFC_ERROR & 0x1FU ) == 0U ) )
    {
        /* check if EFC self-test error is set */
        esmCh40Stat = esmREG->SR4[ 0U ] & 0x100U;
        esmCh41Stat = esmREG->SR4[ 0U ] & 0x200U;

        if( ( esmCh40Stat == 0U ) && ( esmCh41Stat == 0U ) )
        {
            result = TRUE;
        }
    }

    return result;
}

/** @fn void fmcBus2Check(void)
 *   @brief Self Check Flash Bus2 Interface
 *
 *   This function self checks Flash Bus2 Interface
 */
/* SourceId : SELFTEST_SourceId_015 */
/* DesignId : SELFTEST_DesignId_016 */
/* Requirements : HL_SR404, HL_SR405 */
void fmcBus2Check( void )
{
    /* USER CODE BEGIN (32) */
    /* USER CODE END */
    /* enable ECC logic inside FMC */
    flashWREG->FEDACCTRL1 = 0x000A060AU;

    if( ( esmREG->SR1[ 0U ] & 0x40U ) == 0x40U )
    {
        /* a 1-bit error was detected during flash OTP read by flash module
         * run a self-check on ECC logic inside FMC */

        /* clear ESM group1 channel 6 flag */
        esmREG->SR1[ 0U ] = 0x40U;

        fmcECCcheck();
    }

    /* no 2-bit or 1-bit error detected during power-up */
    else
    {
        fmcECCcheck();
    }

    /* USER CODE BEGIN (33) */
    /* USER CODE END */
}

/** @fn void fmcECCcheck(void)
 *   @brief Check Flash ECC Single Bit and multi Bit errors detection logic.
 *
 *   This function Checks Flash ECC Single Bit and multi Bit errors detection logic.
 */
/* SourceId : SELFTEST_SourceId_016 */
/* DesignId : SELFTEST_DesignId_017 */
/* Requirements : HL_SR404, HL_SR405 */
void fmcECCcheck( void )
{
    volatile uint32 otpread;
    volatile uint32 temp;

    /* USER CODE BEGIN (34) */
    /* USER CODE END */

    /* read location with deliberate 1-bit error */
    otpread = flash1bitError;
    ( void ) otpread;

    if( ( esmREG->SR1[ 0U ] & 0x40U ) == 0x40U )
    {
        /* 1-bit failure was indicated and corrected */
        flashWREG->FEDACSTATUS = 0x00010006U;

        /* clear ESM group1 channel 6 flag */
        esmREG->SR1[ 0U ] = 0x40U;

        /* read location with deliberate 2-bit error */
        otpread = flash2bitError;
        ( void ) otpread;

        if( ( esmREG->SR1[ 2U ] & 0x80U ) == 0x80U )
        {
            /* 2-bit failure was detected correctly */
            temp = flashWREG->FUNCERRADD;
            ( void ) temp;
            flashWREG->FEDACSTATUS = 0x00020100U;

            /* clear ESM group3 channel 7 */
            esmREG->SR1[ 2U ] = 0x80U;

            /* The nERROR pin will become inactive once the LTC counter expires */
            esmREG->EKR = 0x5U;
        }
        else
        {
            /* ECC logic inside FMC cannot detect 2-bit error */
            selftestFailNotification( FMCECCCHECK_FAIL1 );
        }
    }
    else
    {
        /* ECC logic inside FMC cannot detect 1-bit error */
        selftestFailNotification( FMCECCCHECK_FAIL1 );
    }

    /* USER CODE BEGIN (35) */
    /* USER CODE END */
}

/** @fn void checkB0RAMECC(void)
 *   @brief Check TCRAM1 ECC error detection logic.
 *
 *   This function checks TCRAM1 ECC error detection logic.
 */
/* SourceId : SELFTEST_SourceId_017 */
/* DesignId : SELFTEST_DesignId_019 */
/* Requirements : HL_SR408 */
void checkB0RAMECC( void )
{
    volatile uint64 ramread = 0U;
    volatile uint32 regread = 0U;
    uint32 tcram1ErrStat, tcram2ErrStat = 0U;

    uint64 tcramA1_bk = tcramA1bit;
    uint64 tcramA2_bk = tcramA2bit;
    volatile uint32 i;

    /* USER CODE BEGIN (36) */
    /* USER CODE END */

    /* enable writes to ECC RAM, enable ECC error response */
    tcram1REG->RAMCTRL = 0x0005010AU;
    tcram2REG->RAMCTRL = 0x0005010AU;

    /* the first 1-bit error will cause an error response */
    tcram1REG->RAMTHRESHOLD = 0x1U;
    tcram2REG->RAMTHRESHOLD = 0x1U;

    /* allow SERR to be reported to ESM */
    tcram1REG->RAMINTCTRL = 0x1U;
    tcram2REG->RAMINTCTRL = 0x1U;

    /* cause a 1-bit ECC error */
    _coreDisableRamEcc_();
    tcramA1bitError ^= 0x1U;
    _coreEnableRamEcc_();

    /* disable writes to ECC RAM */
    tcram1REG->RAMCTRL = 0x0005000AU;
    tcram2REG->RAMCTRL = 0x0005000AU;

    /* read from location with 1-bit ECC error */
    ramread = tcramA1bit;
    ( void ) ramread;

    /* Check for error status */
    tcram1ErrStat = tcram1REG->RAMERRSTATUS & 0x1U;
    tcram2ErrStat = tcram2REG->RAMERRSTATUS & 0x1U;

    /*SAFETYMCUSW 139 S MR:13.7  <APPROVED> "LDRA Tool issue" */
    /*SAFETYMCUSW 139 S MR:13.7  <APPROVED> "LDRA Tool issue" */
    if( ( tcram1ErrStat == 0U ) && ( tcram2ErrStat == 0U ) )
    {
        /* TCRAM module does not reflect 1-bit error reported by CPU */
        selftestFailNotification( CHECKB0RAMECC_FAIL1 );
    }
    else
    {
        /* clear SERR flag */
        tcram1REG->RAMERRSTATUS = 0x1U;
        tcram2REG->RAMERRSTATUS = 0x1U;

        /* clear status flags for ESM group1 channels 26 and 28 */
        esmREG->SR1[ 0U ] = 0x14000000U;
    }

    /* enable writes to ECC RAM, enable ECC error response */
    tcram1REG->RAMCTRL = 0x0005010AU;
    tcram2REG->RAMCTRL = 0x0005010AU;

    /* cause a 2-bit ECC error */
    _coreDisableRamEcc_();
    tcramA2bitError ^= 0x3U;
    _coreEnableRamEcc_();

    /* read from location with 2-bit ECC error this will cause a data abort to be
     * generated */
    ramread = tcramA2bit;

    /* delay before restoring the ram value */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Wait for few clock cycles (Value of i not
     * used)" */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Wait for few clock cycles (Value of i not
     * used)" */
    for( i = 0U; i < 10U; i++ )
    {
    } /* Wait */

    regread = tcram1REG->RAMUERRADDR;
    ( void ) regread;
    regread = tcram2REG->RAMUERRADDR;
    ( void ) regread;

    /* disable writes to ECC RAM */
    tcram1REG->RAMCTRL = 0x0005000AU;
    tcram2REG->RAMCTRL = 0x0005000AU;

    /* Compute correct ECC */
    tcramA1bit = tcramA1_bk;
    tcramA2bit = tcramA2_bk;

    /* USER CODE BEGIN (37) */
    /* USER CODE END */
}

/** @fn void checkB1RAMECC(void)
 *   @brief Check TCRAM2 ECC error detection logic.
 *
 *   This function checks TCRAM2 ECC error detection logic.
 */
/* SourceId : SELFTEST_SourceId_018 */
/* DesignId : SELFTEST_DesignId_019 */
/* Requirements : HL_SR408 */
void checkB1RAMECC( void )
{
    volatile uint64 ramread = 0U;
    volatile uint32 regread = 0U;
    uint32 tcram1ErrStat, tcram2ErrStat = 0U;

    uint64 tcramB1_bk = tcramB1bit;
    uint64 tcramB2_bk = tcramB2bit;
    volatile uint32 i;

    /* USER CODE BEGIN (38) */
    /* USER CODE END */

    /* enable writes to ECC RAM, enable ECC error response */
    tcram1REG->RAMCTRL = 0x0005010AU;
    tcram2REG->RAMCTRL = 0x0005010AU;

    /* the first 1-bit error will cause an error response */
    tcram1REG->RAMTHRESHOLD = 0x1U;
    tcram2REG->RAMTHRESHOLD = 0x1U;

    /* allow SERR to be reported to ESM */
    tcram1REG->RAMINTCTRL = 0x1U;
    tcram2REG->RAMINTCTRL = 0x1U;

    /* cause a 1-bit ECC error */
    _coreDisableRamEcc_();
    tcramB1bitError ^= 0x1U;
    _coreEnableRamEcc_();

    /* disable writes to ECC RAM */
    tcram1REG->RAMCTRL = 0x0005000AU;
    tcram2REG->RAMCTRL = 0x0005000AU;

    /* read from location with 1-bit ECC error */
    ramread = tcramB1bit;
    ( void ) ramread;

    /* Check for error status */
    tcram1ErrStat = tcram1REG->RAMERRSTATUS & 0x1U;
    tcram2ErrStat = tcram2REG->RAMERRSTATUS & 0x1U;

    /*SAFETYMCUSW 139 S MR:13.7  <APPROVED> "LDRA Tool issue" */
    /*SAFETYMCUSW 139 S MR:13.7  <APPROVED> "LDRA Tool issue" */
    if( ( tcram1ErrStat == 0U ) && ( tcram2ErrStat == 0U ) )
    {
        /* TCRAM module does not reflect 1-bit error reported by CPU */
        selftestFailNotification( CHECKB1RAMECC_FAIL1 );
    }
    else
    {
        /* clear SERR flag */
        tcram1REG->RAMERRSTATUS = 0x1U;
        tcram2REG->RAMERRSTATUS = 0x1U;

        /* clear status flags for ESM group1 channels 26 and 28 */
        esmREG->SR1[ 0U ] = 0x14000000U;
    }

    /* enable writes to ECC RAM, enable ECC error response */
    tcram1REG->RAMCTRL = 0x0005010AU;
    tcram2REG->RAMCTRL = 0x0005010AU;

    /* cause a 2-bit ECC error */
    _coreDisableRamEcc_();
    tcramB2bitError ^= 0x3U;
    _coreEnableRamEcc_();

    /* read from location with 2-bit ECC error this will cause a data abort to be
     * generated */
    ramread = tcramB2bit;

    /* delay before restoring the ram value */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Wait for few clock cycles (Value of i not
     * used)" */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Wait for few clock cycles (Value of i not
     * used)" */
    for( i = 0U; i < 10U; i++ )
    {
    } /* Wait */

    regread = tcram1REG->RAMUERRADDR;
    ( void ) regread;
    regread = tcram2REG->RAMUERRADDR;
    ( void ) regread;

    /* disable writes to ECC RAM */
    tcram1REG->RAMCTRL = 0x0005000AU;
    tcram2REG->RAMCTRL = 0x0005000AU;

    /* Compute correct ECC */
    tcramB1bit = tcramB1_bk;
    tcramB2bit = tcramB2_bk;

    /* USER CODE BEGIN (39) */
    /* USER CODE END */
}

/** @fn void checkFlashECC(void)
 *   @brief Check Flash ECC error detection logic.
 *
 *   This function checks Flash ECC error detection logic.
 */
/* SourceId : SELFTEST_SourceId_019 */
/* DesignId : SELFTEST_DesignId_020 */
/* Requirements : HL_SR405 */
void checkFlashECC( void )
{
    /* Routine to check operation of ECC logic inside CPU for accesses to program flash */
    volatile uint32 flashread = 0U;

    /* USER CODE BEGIN (40) */
    /* USER CODE END */

    /* Flash Module ECC Response enabled */
    flashWREG->FEDACCTRL1 = 0x000A060AU;

    /* Enable diagnostic mode and select diag mode 7 */
    flashWREG->FDIAGCTRL = 0x00050007U;

    /* Select ECC diagnostic mode, single-bit to be corrupted */
    flashWREG->FPAROVR = 0x00005A01U;

    /* Set the trigger for the diagnostic mode */
    flashWREG->FDIAGCTRL |= 0x01000000U;

    /* read a flash location from the mirrored memory map */
    flashread = flashBadECC1;
    ( void ) flashread;

    /* disable diagnostic mode */
    flashWREG->FDIAGCTRL = 0x000A0007U;

    /* this will have caused a single-bit error to be generated and corrected by CPU */
    /* single-bit error not captured in flash module */
    /*SAFETYMCUSW 139 S MR:13.7 <APPROVED> "Hardware status bit read check" */
    if( ( flashWREG->FEDACSTATUS & 0x2U ) == 0U )
    {
        selftestFailNotification( CHECKFLASHECC_FAIL1 );
    }
    else
    {
        /* clear single-bit error flag */
        flashWREG->FEDACSTATUS = 0x2U;

        /* clear ESM flag */
        esmREG->SR1[ 0U ] = 0x40U;

        /* Enable diagnostic mode and select diag mode 7 */
        flashWREG->FDIAGCTRL = 0x00050007U;

        /* Select ECC diagnostic mode, two bits of ECC to be corrupted */
        flashWREG->FPAROVR = 0x00005A03U;

        /* Set the trigger for the diagnostic mode */
        flashWREG->FDIAGCTRL |= 0x01000000U;

        /* read from flash location from mirrored memory map this will cause a data abort
         */
        flashread = flashBadECC2;

        /* Read FUNCERRADD register */
        flashread = flashWREG->FUNCERRADD;

        /* disable diagnostic mode */
        flashWREG->FDIAGCTRL = 0x000A0007U;
    }

    /* USER CODE BEGIN (41) */
    /* USER CODE END */
}

/** @fn void custom_dabort(void)
 *   @brief Custom Data abort routine for the application.
 *
 *   Custom Data abort routine for the application.
 */
void custom_dabort( void )
{
    /* Need custom data abort handler here.
     * This data abort is not caused due to diagnostic checks of flash and TCRAM ECC
     * logic.
     */
    /* USER CODE BEGIN (42) */
    /* USER CODE END */
}

/** @fn void stcSelfCheckFail(void)
 *   @brief STC Self test check fail service routine
 *
 *   This function is called if STC Self test check fail.
 */
void stcSelfCheckFail( void )
{
    /* USER CODE BEGIN (43) */
    /* USER CODE END */

    /* CPU self-test controller's own self-test failed.
     * It is not possible to verify that STC is capable of indicating a CPU self-test
     * error. It is not recommended to continue operation.
     */

    /* User can add small piece of code to take system to Safe state using user code
     * section. Note: Just removing the for(;;) will take the system to unknown state
     * under ST failure, since it is not handled by HALCoGen driver */
    /* USER CODE BEGIN (44) */
    /* USER CODE END */
    /*SAFETYMCUSW 5 C MR:NA <APPROVED> "for(;;) can be removed by adding "# if 0" and "#
     * endif" in the user codes above and below" */
    /*SAFETYMCUSW 26 S MR:NA <APPROVED> "for(;;) can be removed by adding "# if 0" and "#
     * endif" in the user codes above and below" */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "for(;;) can be removed by adding "# if 0" and "#
     * endif" in the user codes above and below" */
    for( ;; )
    {
    } /* Wait */

    /* USER CODE BEGIN (45) */
    /* USER CODE END */
}

/** @fn void cpuSelfTestFail(void)
 *   @brief CPU Self test check fail service routine
 *
 *   This function is called if CPU Self test check fail.
 */
void cpuSelfTestFail( void )
{
    /* USER CODE BEGIN (46) */
    /* USER CODE END */

    /* CPU self-test has failed.
     * CPU operation is not reliable.
     */
    /* USER CODE BEGIN (47) */
    /* USER CODE END */
    /*SAFETYMCUSW 5 C MR:NA <APPROVED> "for(;;) can be removed by adding "# if 0" and "#
     * endif" in the user codes above and below" */
    /*SAFETYMCUSW 26 S MR:NA <APPROVED> "for(;;) can be removed by adding "# if 0" and "#
     * endif" in the user codes above and below" */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "for(;;) can be removed by adding "# if 0" and "#
     * endif" in the user codes above and below" */
    for( ;; )
    {
    } /* Wait */

    /* USER CODE BEGIN (48) */
    /* USER CODE END */
}

/** @fn void vimParityCheck(void)
 *   @brief Routine to check VIM RAM parity error detection and signaling mechanism
 *
 *   Routine to check VIM RAM parity error detection and signaling mechanism
 */
/* SourceId : SELFTEST_SourceId_020 */
/* DesignId : SELFTEST_DesignId_021 */
/* Requirements : HL_SR385 */
void vimParityCheck( void )
{
    volatile uint32 vimramread = 0U;
    uint32 vimparctl_bk = VIM_PARCTL;

    /* USER CODE BEGIN (49) */
    /* USER CODE END */

    /* Enable parity checking and parity test mode */
    VIM_PARCTL = 0x0000010AU;

    /* flip a bit in the VIM RAM parity location */
    VIMRAMPARLOC ^= 0x1U;

    /* disable parity test mode */
    VIM_PARCTL = 0x0000000AU;

    /* cause parity error */
    vimramread = VIMRAMLOC;
    ( void ) vimramread;

    /* check if ESM group1 channel 15 is flagged */
    if( ( esmREG->SR1[ 0U ] & 0x8000U ) == 0U )
    {
        /* VIM RAM parity error was not flagged to ESM. */
        selftestFailNotification( VIMPARITYCHECK_FAIL1 );
    }
    else
    {
        /* clear VIM RAM parity error flag in VIM */
        VIM_PARFLG = 0x1U;

        /* clear ESM group1 channel 15 flag */
        esmREG->SR1[ 0U ] = 0x8000U;

        /* Enable parity checking and parity test mode */
        VIM_PARCTL = 0x0000010AU;

        /* Revert back to correct data, flip bit 0 of the parity location */
        VIMRAMPARLOC ^= 0x1U;
    }

    /* Restore Parity Control register */
    VIM_PARCTL = vimparctl_bk;

    /* USER CODE BEGIN (50) */
    /* USER CODE END */
}

/** @fn void dmaParityCheck(void)
 *   @brief Routine to check DMA control packet RAM parity error detection and signaling
 * mechanism
 *
 *   Routine to check DMA control packet RAM parity error detection and signaling
 * mechanism
 */
/* SourceId : SELFTEST_SourceId_021 */
/* DesignId : SELFTEST_DesignId_022 */
/* Requirements : HL_SR388 */
void dmaParityCheck( void )
{
    volatile uint32 dmaread = 0U;
    uint32 dmaparcr_bk = DMA_PARCR;

    /* USER CODE BEGIN (51) */
    /* USER CODE END */

    /* Enable parity checking and parity test mode */
    DMA_PARCR = 0x0000010AU;

    /* Flip a bit in DMA RAM parity location */
    DMARAMPARLOC ^= 0x1U;

    /* Disable parity test mode */
    DMA_PARCR = 0x0000000AU;

    /* Cause parity error */
    dmaread = DMARAMLOC;
    ( void ) dmaread;

    /* Check if ESM group1 channel 3 is flagged */
    if( ( esmREG->SR1[ 0U ] & 0x8U ) == 0U )
    {
        /* DMA RAM parity error was not flagged to ESM. */
        selftestFailNotification( DMAPARITYCHECK_FAIL1 );
    }
    else
    {
        /* clear DMA parity error flag in DMA */
        DMA_PARADDR = 0x01000000U;

        /* clear ESM group1 channel 3 flag */
        esmREG->SR1[ 0U ] = 0x8U;

        /* Enable parity checking and parity test mode */
        DMA_PARCR = 0x0000010AU;

        /* Revert back to correct data, flip bit 0 of the parity location */
        DMARAMPARLOC ^= 0x1U;
    }

    /* Restrore Parity Control register */
    DMA_PARCR = dmaparcr_bk;

    /* USER CODE BEGIN (52) */
    /* USER CODE END */
}

/** @fn void het1ParityCheck(void)
 *   @brief Routine to check HET1 RAM parity error detection and signaling mechanism
 *
 *   Routine to check HET1 RAM parity error detection and signaling mechanism
 */
/* SourceId : SELFTEST_SourceId_022 */
/* DesignId : SELFTEST_DesignId_024 */
/* Requirements : HL_SR389 */
void het1ParityCheck( void )
{
    volatile uint32 nhetread = 0U;
    uint32 hetpcr_bk = hetREG1->PCR;

    /* USER CODE BEGIN (53) */
    /* USER CODE END */

    /* Set TEST mode and enable parity checking */
    hetREG1->PCR = 0x0000010AU;

    /* flip parity bit */
    NHET1RAMPARLOC ^= 0x1U;

    /* Disable TEST mode */
    hetREG1->PCR = 0x0000000AU;

    /* read to cause parity error */
    nhetread = NHET1RAMLOC;
    ( void ) nhetread;

    /* check if ESM group1 channel 7 is flagged */
    if( ( esmREG->SR1[ 0U ] & 0x80U ) == 0U )
    {
        /* NHET1 RAM parity error was not flagged to ESM. */
        selftestFailNotification( HET1PARITYCHECK_FAIL1 );
    }
    else
    {
        /* clear ESM group1 channel 7 flag */
        esmREG->SR1[ 0U ] = 0x80U;

        /* Set TEST mode and enable parity checking */
        hetREG1->PCR = 0x0000010AU;

        /* Revert back to correct data, flip bit 0 of the parity location */
        NHET1RAMPARLOC ^= 0x1U;
    }

    /* Restore Parity comtrol register */
    hetREG1->PCR = hetpcr_bk;

    /* USER CODE BEGIN (54) */
    /* USER CODE END */
}

/** @fn void htu1ParityCheck(void)
 *   @brief Routine to check HTU1 RAM parity error detection and signaling mechanism
 *
 *   Routine to check HTU1 RAM parity error detection and signaling mechanism
 */
/* SourceId : SELFTEST_SourceId_023 */
/* DesignId : SELFTEST_DesignId_025 */
/* Requirements : HL_SR390 */
void htu1ParityCheck( void )
{
    volatile uint32 hturead = 0U;
    uint32 htupcr_bk = htuREG1->PCR;

    /* USER CODE BEGIN (55) */
    /* USER CODE END */

    /* Enable parity and TEST mode */
    htuREG1->PCR = 0x0000010AU;

    /* flip parity bit */
    HTU1PARLOC ^= 0x1U;

    /* Disable parity RAM test mode */
    htuREG1->PCR = 0x0000000AU;

    /* read to cause parity error */
    hturead = HTU1RAMLOC;
    ( void ) hturead;

    /* check if ESM group1 channel 8 is flagged */
    if( ( esmREG->SR1[ 0U ] & 0x100U ) == 0U )
    {
        /* HTU1 RAM parity error was not flagged to ESM. */
        selftestFailNotification( HTU1PARITYCHECK_FAIL1 );
    }
    else
    {
        /* Clear HTU parity error flag */
        htuREG1->PAR = 0x00010000U;
        esmREG->SR1[ 0U ] = 0x100U;

        /* Enable parity and TEST mode */
        htuREG1->PCR = 0x0000010AU;

        /* Revert back to correct data, flip bit 0 of the parity location */
        HTU1PARLOC ^= 0x1U;
    }

    /* Restore Parity control register */
    htuREG1->PCR = htupcr_bk;

    /* USER CODE BEGIN (56) */
    /* USER CODE END */
}

/** @fn void het2ParityCheck(void)
 *   @brief Routine to check HET2 RAM parity error detection and signaling mechanism
 *
 *   Routine to check HET2 RAM parity error detection and signaling mechanism
 */
/* SourceId : SELFTEST_SourceId_024 */
/* DesignId : SELFTEST_DesignId_024 */
/* Requirements : HL_SR389 */
void het2ParityCheck( void )
{
    volatile uint32 nhetread = 0U;
    uint32 hetpcr_bk = hetREG2->PCR;
    uint32 esmCh7Stat, esmCh34Stat = 0U;

    /* USER CODE BEGIN (57) */
    /* USER CODE END */

    /* Set TEST mode and enable parity checking */
    hetREG2->PCR = 0x0000010AU;

    /* flip parity bit */
    NHET2RAMPARLOC ^= 0x1U;

    /* Disable TEST mode */
    hetREG2->PCR = 0x0000000AU;

    /* read to cause parity error */
    nhetread = NHET2RAMLOC;
    ( void ) nhetread;

    /* check if ESM group1 channel 7 or 34 (If not reserved) is flagged */
    esmCh7Stat = esmREG->SR1[ 0U ] & 0x80U;
    esmCh34Stat = esmREG->SR4[ 0U ] & 0x4U;

    if( ( esmCh7Stat == 0U ) && ( esmCh34Stat == 0U ) )
    {
        /* NHET2 RAM parity error was not flagged to ESM. */
        selftestFailNotification( HET2PARITYCHECK_FAIL1 );
    }
    else
    {
        /* clear ESM group1 channel 7 flag */
        esmREG->SR1[ 0U ] = 0x80U;

        /* clear ESM group1 channel 34 flag */
        esmREG->SR4[ 0U ] = 0x4U;

        /* Set TEST mode and enable parity checking */
        hetREG2->PCR = 0x0000010AU;

        /* Revert back to correct data, flip bit 0 of the parity location */
        NHET2RAMPARLOC ^= 0x1U;
    }

    /* Restore parity control register */
    hetREG2->PCR = hetpcr_bk;

    /* USER CODE BEGIN (58) */
    /* USER CODE END */
}

/** @fn void htu2ParityCheck(void)
 *   @brief Routine to check HTU2 RAM parity error detection and signaling mechanism
 *
 *   Routine to check HTU2 RAM parity error detection and signaling mechanism
 */
/* SourceId : SELFTEST_SourceId_025 */
/* DesignId : SELFTEST_DesignId_025 */
/* Requirements : HL_SR390 */
void htu2ParityCheck( void )
{
    volatile uint32 hturead = 0U;
    uint32 htupcr_bk = htuREG2->PCR;

    /* USER CODE BEGIN (59) */
    /* USER CODE END */

    /* Enable parity and TEST mode */
    htuREG2->PCR = 0x0000010AU;

    /* flip parity bit */
    HTU2PARLOC ^= 0x1U;

    /* Disable parity RAM test mode */
    htuREG2->PCR = 0x0000000AU;

    /* read to cause parity error */
    hturead = HTU2RAMLOC;
    ( void ) hturead;

    /* check if ESM group1 channel 8 is flagged */
    if( ( esmREG->SR1[ 0U ] & 0x100U ) == 0U )
    {
        /* HTU2 RAM parity error was not flagged to ESM. */
        selftestFailNotification( HTU2PARITYCHECK_FAIL1 );
    }
    else
    {
        /* Clear HTU parity error flag */
        htuREG2->PAR = 0x00010000U;
        esmREG->SR1[ 0U ] = 0x100U;

        /* Enable parity and TEST mode */
        htuREG2->PCR = 0x0000010AU;

        /* Revert back to correct data, flip bit 0 of the parity location */
        HTU2PARLOC ^= 0x1U;
    }

    /* Restore parity control register*/
    htuREG2->PCR = htupcr_bk;

    /* USER CODE BEGIN (60) */
    /* USER CODE END */
}

/** @fn void adc1ParityCheck(void)
 *   @brief Routine to check ADC1 RAM parity error detection and signaling mechanism
 *
 *   Routine to check ADC1 RAM parity error detection and signaling mechanism
 */
/* SourceId : SELFTEST_SourceId_026 */
/* DesignId : SELFTEST_DesignId_023 */
/* Requirements : HL_SR387 */
void adc1ParityCheck( void )
{
    volatile uint32 adcramread = 0U;
    uint32 adcparcr_bk = adcREG1->PARCR;

    /* USER CODE BEGIN (61) */
    /* USER CODE END */

    /* Set the TEST bit in the PARCR and enable parity checking */
    adcREG1->PARCR = 0x10AU;

    /* Invert the parity bits inside the ADC1 RAM's first location */
    adcPARRAM1 = ~( adcPARRAM1 );

    /* clear the TEST bit */
    adcREG1->PARCR = 0x00AU;

    /* This read is expected to trigger a parity error */
    adcramread = adcRAM1;
    ( void ) adcramread;

    /* Check for ESM group1 channel 19 to be flagged */
    if( ( esmREG->SR1[ 0U ] & 0x80000U ) == 0U )
    {
        /* no ADC1 RAM parity error was flagged to ESM */
        selftestFailNotification( ADC1PARITYCHECK_FAIL1 );
    }
    else
    {
        /* clear ADC1 RAM parity error flag */
        esmREG->SR1[ 0U ] = 0x80000U;

        /* Set the TEST bit in the PARCR and enable parity checking */
        adcREG1->PARCR = 0x10AU;

        /* Revert back the parity bits to correct data */
        adcPARRAM1 = ~( adcPARRAM1 );
    }

    /* Restore parity control register */
    adcREG1->PARCR = adcparcr_bk;

    /* USER CODE BEGIN (62) */
    /* USER CODE END */
}

/** @fn void adc2ParityCheck(void)
 *   @brief Routine to check ADC2 RAM parity error detection and signaling mechanism
 *
 *   Routine to check ADC2 RAM parity error detection and signaling mechanism
 */
/* SourceId : SELFTEST_SourceId_027 */
/* DesignId : SELFTEST_DesignId_023 */
/* Requirements : HL_SR387 */
void adc2ParityCheck( void )
{
    volatile uint32 adcramread = 0U;
    uint32 adcparcr_bk = adcREG2->PARCR;

    /* USER CODE BEGIN (63) */
    /* USER CODE END */

    /* Set the TEST bit in the PARCR and enable parity checking */
    adcREG2->PARCR = 0x10AU;

    /* Invert the parity bits inside the ADC2 RAM's first location */
    adcPARRAM2 = ~( adcPARRAM2 );

    /* clear the TEST bit */
    adcREG2->PARCR = 0x00AU;

    /* This read is expected to trigger a parity error */
    adcramread = adcRAM2;
    ( void ) adcramread;

    /* Check for ESM group1 channel 1 to be flagged */
    if( ( esmREG->SR1[ 0U ] & 0x2U ) == 0U )
    {
        /* no ADC2 RAM parity error was flagged to ESM */
        selftestFailNotification( ADC2PARITYCHECK_FAIL1 );
    }
    else
    {
        /* clear ADC2 RAM parity error flag */
        esmREG->SR1[ 0U ] = 0x2U;

        /* Set the TEST bit in the PARCR and enable parity checking */
        adcREG2->PARCR = 0x10AU;

        /* Revert back the parity bits to correct data */
        adcPARRAM2 = ~( adcPARRAM2 );
    }

    /* Restore parity control register*/
    adcREG2->PARCR = adcparcr_bk;

    /* USER CODE BEGIN (64) */
    /* USER CODE END */
}

/** @fn void checkRAMECC(void)
 *   @brief Check TCRAM ECC error detection logic.
 *
 *   This function checks TCRAM ECC error detection logic.
 */
/* SourceId : SELFTEST_SourceId_034 */
/* DesignId : SELFTEST_DesignId_019 */
/* Requirements : HL_SR408 */
void checkRAMECC( void )
{
    volatile uint64 ramread = 0U;
    volatile uint32 regread = 0U;
    uint32 tcram1ErrStat, tcram2ErrStat = 0U;

    uint64 tcramA1_bk = tcramA1bit;
    uint64 tcramB1_bk = tcramB1bit;
    uint64 tcramA2_bk = tcramA2bit;
    uint64 tcramB2_bk = tcramB2bit;

    /* Clear RAMOCUUR before setting RAMTHRESHOLD register */
    tcram1REG->RAMOCCUR = 0U;
    tcram2REG->RAMOCCUR = 0U;

    /* Set Single-bit Error Threshold Count as 1 */
    tcram1REG->RAMTHRESHOLD = 1U;
    tcram2REG->RAMTHRESHOLD = 1U;

    /* Enable single bit error generation */
    tcram1REG->RAMINTCTRL = 1U;
    tcram2REG->RAMINTCTRL = 1U;

    /* Enable writes to ECC RAM, enable ECC error response */
    tcram1REG->RAMCTRL = 0x0005010AU;
    tcram2REG->RAMCTRL = 0x0005010AU;

    /* Force a single bit error in both the banks */
    _coreDisableRamEcc_();
    tcramA1bitError ^= 1U;
    tcramB1bitError ^= 1U;
    _coreEnableRamEcc_();

    /* Read the corrupted data to generate single bit error */
    ramread = tcramA1bit;
    ( void ) ramread;
    ramread = tcramB1bit;
    ( void ) ramread;

    /* Check for error status */
    tcram1ErrStat = tcram1REG->RAMERRSTATUS & 0x1U;
    tcram2ErrStat = tcram2REG->RAMERRSTATUS & 0x1U;

    /*SAFETYMCUSW 139 S MR:13.7  <APPROVED> "LDRA Tool issue" */
    /*SAFETYMCUSW 139 S MR:13.7  <APPROVED> "LDRA Tool issue" */
    if( ( tcram1ErrStat == 0U ) || ( tcram2ErrStat == 0U ) )
    {
        /* TCRAM module does not reflect 1-bit error reported by CPU */
        selftestFailNotification( CHECKRAMECC_FAIL1 );
    }
    else
    {
        if( ( esmREG->SR1[ 0U ] & 0x14000000U ) != 0x14000000U )
        {
            /* TCRAM 1-bit error not flagged in ESM */
            selftestFailNotification( CHECKRAMECC_FAIL2 );
        }
        else
        {
            /* Clear single bit error flag in TCRAM module */
            tcram1REG->RAMERRSTATUS = 0x1U;
            tcram2REG->RAMERRSTATUS = 0x1U;

            /* Clear ESM status */
            esmREG->SR1[ 0U ] = 0x14000000U;
        }
    }

    /* Force a double bit error in both the banks */
    _coreDisableRamEcc_();
    tcramA2bitError ^= 3U;
    tcramB2bitError ^= 3U;
    _coreEnableRamEcc_();

    /* Read the corrupted data to generate double bit error */
    ramread = tcramA2bit;
    ( void ) ramread;
    ramread = tcramB2bit;
    ( void ) ramread;

    regread = tcram1REG->RAMUERRADDR;
    ( void ) regread;
    regread = tcram2REG->RAMUERRADDR;
    ( void ) regread;

    /* disable writes to ECC RAM */
    tcram1REG->RAMCTRL = 0x0005000AU;
    tcram2REG->RAMCTRL = 0x0005000AU;

    /* Compute correct ECC */
    tcramA1bit = tcramA1_bk;
    tcramB1bit = tcramB1_bk;
    tcramA2bit = tcramA2_bk;
    tcramB2bit = tcramB2_bk;
}

/** @fn void checkClockMonitor(void)
 *   @brief Check clock monitor failure detection logic.
 *
 *   This function checks clock monitor failure detection logic.
 */
/* SourceId : SELFTEST_SourceId_035 */
/* DesignId : SELFTEST_DesignId_028 */
/* Requirements : HL_SR394 */
void checkClockMonitor( void )
{
    uint32 ghvsrc_bk;

    /* Enable clock monitor range detection circuitry */
    systemREG1->CLKTEST |= 0x03000000U;

    /* Backup register GHVSRC */
    ghvsrc_bk = systemREG1->GHVSRC;

    /* Switch all clock domains to HF LPO */
    systemREG1->GHVSRC = 0x05050005U;

    /* Disable oscillator to cause a oscillator fail */
    systemREG1->CSDISSET = 0x1U;

    /* Wait till oscillator fail flag is set */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( systemREG1->GBLSTAT & 0x1U ) == 0U )
    {
    } /* Wait */

    if( ( esmREG->SR1[ 0U ] & 0x800U ) != 0x800U )
    {
        selftestFailNotification( CHECKCLOCKMONITOR_FAIL1 );
    }
    else
    {
        /* Clear ESM flag */
        esmREG->SR1[ 0U ] = 0x800U;

        /* Disable clock monitor range detection circuitry */
        systemREG1->CLKTEST &= ~( 0x03000000U );

        /* Enable oscillator */
        systemREG1->CSDISCLR = 0x1U;

        /* Wait until oscillator is enabled */
        /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
        while( ( systemREG1->CSVSTAT & 0x3U ) == 0U )
        {
        } /* Wait */

        /* Clear oscillator fail flag and PLL slip flag if any*/
        systemREG1->GBLSTAT = 0x301U;

        /* Switch back all clock domains */
        systemREG1->GHVSRC = ghvsrc_bk;
    }
}

/** @fn void checkFlashEEPROMECC(void)
 *   @brief Check Flash EEPROM ECC error detection logic.
 *
 *   This function checks Flash EEPROM ECC error detection logic.
 */
/* SourceId : SELFTEST_SourceId_036 */
/* DesignId : SELFTEST_DesignId_029 */
/* Requirements : HL_SR406 */
void checkFlashEEPROMECC( void )
{
    uint32 ecc;
    volatile uint32 regread;

    /* Set Single Error Correction Threshold as 1 */
    flashWREG->EECTRL2 |= 1U;

    /* Enable EEPROM Emulation Error Profiling */
    flashWREG->EECTRL1 |= 0x00000100U;

    /* Load FEMU_XX regs in order to generate ECC */
    flashWREG->FEMUADDR = 0xF0200000U;
    flashWREG->FEMUDMSW = 0U;
    flashWREG->FEMUDLSW = 0U;

    /* ECC for the correct data*/
    ecc = flashWREG->FEMUECC;

    /* Load data with 1 bit error */
    flashWREG->FEMUDMSW = 0U;
    flashWREG->FEMUDLSW = 1U;

    /* Enable Diagnostic ECC data correction mode and select FEE SECDED for diagnostic
     * testing */
    flashWREG->FDIAGCTRL = 0x00055001U;

    flashWREG->FEMUECC = ecc;

    /* Diagnostic trigger */
    flashWREG->FDIAGCTRL |= 0x01000000U;

    /*SAFETYMCUSW 139 S MR:13.7 <APPROVED> "Hardware status bit read check" */
    if( ( flashWREG->EESTATUS & 0x1U ) != 0x1U )
    {
        /* No single bit error was detected */
        selftestFailNotification( CHECKFLASHEEPROMECC_FAIL1 );
    }
    else
    {
        if( ( esmREG->SR4[ 0U ] & 0x8U ) != 0x8U )
        {
            /* EEPROM single bit error not captured in ESM */
            selftestFailNotification( CHECKFLASHEEPROMECC_FAIL2 );
        }
        else
        {
            /* Clear single bit error flag in flash wrapper */
            flashWREG->EESTATUS = 0xFU;

            /* Clear ESM flag */
            esmREG->SR4[ 0U ] = 0x8U;
        }
    }

    /* Load data with 2 bit error */
    flashWREG->FEMUDMSW = 0U;
    flashWREG->FEMUDLSW = 3U;

    /* Enable Diagnostic ECC data correction mode and select FEE SECDED for diagnostic
     * testing */
    flashWREG->FDIAGCTRL = 0x00055001U;

    flashWREG->FEMUECC = ecc;

    /* Diagnostic trigger */
    flashWREG->FDIAGCTRL |= 0x01000000U;

    /*SAFETYMCUSW 139 S MR:13.7 <APPROVED> "Hardware status bit read check" */
    if( ( flashWREG->EESTATUS & 0x100U ) != 0x100U )
    {
        /* No double bit error was detected */
        selftestFailNotification( CHECKFLASHEEPROMECC_FAIL3 );
    }
    else
    {
        if( ( esmREG->SR4[ 0U ] & 0x10U ) != 0x10U )
        {
            /* EEPROM double bit error not captured in ESM */
            selftestFailNotification( CHECKFLASHEEPROMECC_FAIL4 );
        }
        else
        {
            /* Clear uncorrectable error flag in flash wrapper */
            flashWREG->EESTATUS = 0x1100U;

            /* Read EEUNCERRADD register */
            regread = flashWREG->EEUNCERRADD;
            ( void ) regread;

            /* Clear ESM flag */
            esmREG->SR4[ 0U ] = 0x10U;
        }
    }
}

/** @fn void checkPLL1Slip(void)
 *   @brief Check PLL1 Slip detection logic.
 *
 *   This function checks PLL1 Slip detection logic.
 */
/* SourceId : SELFTEST_SourceId_037 */
/* DesignId : SELFTEST_DesignId_030 */
/* Requirements : HL_SR384 */
void checkPLL1Slip( void )
{
    uint32 ghvsrc_bk, pllctl1_bk;

    /* Back up the the registers GHVSRC and PLLCTRL1 */
    ghvsrc_bk = systemREG1->GHVSRC;
    pllctl1_bk = systemREG1->PLLCTL1;

    /* Switch all clock domains to oscillator */
    systemREG1->GHVSRC = 0x00000000U;

    /* Disable Reset on PLL Slip and enable Bypass on PLL slip */
    systemREG1->PLLCTL1 &= 0x1FFFFFFFU;

    /* Force a PLL Slip */
    systemREG1->PLLCTL1 ^= 0x8000U;

    /* Wait till PLL slip flag is set */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( systemREG1->GBLSTAT & 0x300U ) == 0U )
    {
    } /* Wait */

    if( ( esmREG->SR1[ 0U ] & 0x400U ) != 0x400U )
    {
        /* ESM flag not set */
        selftestFailNotification( CHECKPLL1SLIP_FAIL1 );
    }
    else
    {
        /* Disable PLL1 */
        systemREG1->CSDISSET = 0x2U;

        /* Wait till PLL1 is disabled */
        /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
        while( ( systemREG1->CSDIS & 0x2U ) == 0U )
        {
        } /* Wait */

        /* Restore the PLL multiplier value */
        systemREG1->PLLCTL1 ^= 0x8000U;

        /* Enable PLL1 */
        systemREG1->CSDISCLR = 0x2U;

        /* Wait till PLL1 is disabled */
        /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
        while( ( systemREG1->CSDIS & 0x2U ) != 0U )
        {
        } /* Wait */

        /* Switch back to the initial clock source */
        systemREG1->GHVSRC = ghvsrc_bk;

        /* Clear PLL slip flag */
        systemREG1->GBLSTAT = 0x300U;

        /* Clear ESM flag */
        esmREG->SR1[ 0U ] = 0x400U;

        /* Restore the PLLCTL1 register */
        systemREG1->PLLCTL1 = pllctl1_bk;
    }
}

/** @fn void checkPLL2Slip(void)
 *   @brief Check PLL2 Slip detection logic.
 *
 *   This function checks PLL2 Slip detection logic.
 */
/* SourceId : SELFTEST_SourceId_038 */
/* DesignId : SELFTEST_DesignId_031 */
/* Requirements : HL_SR384 */
void checkPLL2Slip( void )
{
    uint32 ghvsrc_bk;

    /* Back up the the register GHVSRC */
    ghvsrc_bk = systemREG1->GHVSRC;

    /* Switch all clock domains to oscillator */
    systemREG1->GHVSRC = 0x00000000U;

    /* Force a PLL2 Slip */
    systemREG2->PLLCTL3 ^= 0x8000U;

    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( esmREG->SR4[ 0U ] & 0x400U ) != 0x400U )
    {
        /* Wait till ESM flag is set */
    }

    /* Disable PLL2 */
    systemREG1->CSDISSET = 0x40U;

    /* Wait till PLL2 is disabled */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( systemREG1->CSDIS & 0x40U ) == 0U )
    {
    } /* Wait */

    /* Restore the PLL 2 multiplier value */
    systemREG2->PLLCTL3 ^= 0x8000U;

    /* Enable PLL2 */
    systemREG1->CSDISCLR = 0x40U;

    /* Wait till PLL2 is disabled */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( systemREG1->CSDIS & 0x40U ) != 0U )
    {
    } /* Wait */

    /* Switch back to the initial clock source */
    systemREG1->GHVSRC = ghvsrc_bk;

    /* Clear PLL slip flag */
    systemREG1->GBLSTAT = 0x300U;

    /* Clear ESM flag */
    esmREG->SR4[ 0U ] = 0x400U;
}

/** @fn void checkRAMAddrParity(void)
 *   @brief Check TCRAM Address parity error detection and signaling mechanism.
 *
 *   This function TCRAM Address parity error detection and signaling mechanism.
 */
/* SourceId : SELFTEST_SourceId_039 */
/* DesignId : SELFTEST_DesignId_032 */
/* Requirements : HL_SR409 */
void checkRAMAddrParity( void )
{
    register uint64 ramread;
    volatile uint32 regread;
    uint32 tcram1ErrStat, tcram2ErrStat;

    /* Invert Address parity scheme */
    tcram1REG->RAMCTRL = 0x0D05000AU;
    tcram2REG->RAMCTRL = 0x0D05000AU;

    /* Read from both RAM banks */
    ramread = tcramA1bit;
    ramread = ramread | tcramB1bit; /* XOR-ing with ramread to avoid warnings */

    /* Switch back to Address parity scheme */
    tcram1REG->RAMCTRL = 0x0005000AU;
    tcram2REG->RAMCTRL = 0x0005000AU;

    /* Check for error status */
    tcram1ErrStat = tcram1REG->RAMERRSTATUS & 0x100U;
    tcram2ErrStat = tcram2REG->RAMERRSTATUS & 0x100U;

    /*SAFETYMCUSW 139 S MR:13.7  <APPROVED> "LDRA Tool issue" */
    /*SAFETYMCUSW 139 S MR:13.7  <APPROVED> "LDRA Tool issue" */
    if( ( tcram1ErrStat == 0U ) || ( tcram2ErrStat == 0U ) )
    {
        /* No Address parity error detected */
        selftestFailNotification( CHECKRAMADDRPARITY_FAIL1 );
    }
    else
    {
        if( ( esmREG->SR1[ 1U ] & 0x1400U ) != 0x1400U )
        {
            /* Address parity error not reported to ESM */
            selftestFailNotification( CHECKRAMADDRPARITY_FAIL2 );
        }
        else
        {
            /* Clear Address parity error flag */
            tcram1REG->RAMERRSTATUS = 0x300U;
            tcram2REG->RAMERRSTATUS = 0x300U;

            /* Clear ESM flag */
            esmREG->SR1[ 1U ] = 0x1400U;

            /* The nERROR pin will become inactive once the LTC counter expires */
            esmREG->EKR = 0x5U;

            regread = tcram1REG->RAMPERADDR;
            ( void ) regread;
            regread = tcram2REG->RAMPERADDR;
            ( void ) regread;
        }
    }
}

/** @fn void checkRAMUERRTest(void)
 *   @brief Run RAM test
 *
 *   This function runs RAM test to test the redundant address decode and compare logic.
 */
/* SourceId : SELFTEST_SourceId_040 */
/* DesignId : SELFTEST_DesignId_033 */
/* Requirements : HL_SR410 */
void checkRAMUERRTest( void )
{
    uint32 tcram1ErrStat, tcram2ErrStat = 0U;

    /* Trigger equality check */
    tcram1REG->RAMTEST = 0x018AU;
    tcram2REG->RAMTEST = 0x018AU;

    /* Wait till test is completed */
    while( tcram1REG->RAMTEST != 0x008AU )
    {
    } /* Wait */

    while( tcram2REG->RAMTEST != 0x008AU )
    {
    } /* Wait */

    /* Check for error status */
    tcram1ErrStat = tcram1REG->RAMERRSTATUS & 0x10U;
    tcram2ErrStat = tcram2REG->RAMERRSTATUS & 0x10U;

    if( ( tcram1ErrStat == 0x10U ) || ( tcram2ErrStat == 0x10U ) )
    {
        /* test failed */
        selftestFailNotification( CHECKRAMUERRTEST_FAIL1 );
    }

    /* Trigger inequality check */
    tcram1REG->RAMTEST = 0x014AU;
    tcram2REG->RAMTEST = 0x014AU;

    /* Wait till test is completed */
    while( tcram1REG->RAMTEST != 0x004AU )
    {
    } /* Wait */

    while( tcram2REG->RAMTEST != 0x004AU )
    {
    } /* Wait */

    tcram1ErrStat = tcram1REG->RAMERRSTATUS & 0x10U;
    tcram2ErrStat = tcram2REG->RAMERRSTATUS & 0x10U;

    if( ( tcram1ErrStat == 0x10U ) || ( tcram2ErrStat == 0x10U ) )
    {
        /* test failed */
        selftestFailNotification( CHECKRAMUERRTEST_FAIL2 );
    }
    else
    {
        tcram1REG->RAMERRSTATUS = 0x4U;
        tcram2REG->RAMERRSTATUS = 0x4U;

        /* Clear ESM flag */
        esmREG->SR1[ 1U ] = 0x140U;
        esmREG->SSR2 = 0x140U;
        esmREG->EKR = 0x5U;
    }

    /* Disable RAM test mode */
    tcram1REG->RAMTEST = 0x5U;
    tcram2REG->RAMTEST = 0x5U;
}

/* SourceId : SELFTEST_SourceId_041 */
/* DesignId : SELFTEST_DesignId_018 */
/* Requirements : HL_SR407 */
void fmcBus1ParityCheck( void )
{
    uint32 regBkupFparOvr, regBckupFdiagctrl;
    volatile uint32 flashread = 0U;

    /* Backup registers */
    regBkupFparOvr = flashWREG->FPAROVR;
    regBckupFdiagctrl = flashWREG->FDIAGCTRL;

    /* Read to unfreeze the error address registers */
    flashread = flashWREG->FUNCERRADD;
    ( void ) flashread;

    /* clear status register */
    flashWREG->FEDACSTATUS = 0x400U;

    /* Enable Parity Error */
    flashWREG->FPAROVR = ( uint32 ) ( ( uint32 ) 0x5U << 9U )
                       | ( uint32 ) ( ( uint32 ) 0x5U << 12U );

    /* set Diag test mode */
    flashWREG->FDIAGCTRL = 0x00050000U | 0x00000007U;

    /* Add parity */
    flashWREG->FPAROVR |= 0x00000100U;

    /* Start Test */
    flashWREG->FDIAGCTRL |= 0x1000000U;

    /* Wait until test done */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    /*SAFETYMCUSW 139 S MR:13.7 <APPROVED> "Hardware status bit read check" */
    while( ( flashWREG->FDIAGCTRL & 0x1000000U ) == 0x1000000U )
    {
    } /* Wait */

    /* Check address Error */
    /*SAFETYMCUSW 139 S MR:13.7 <APPROVED> "Hardware status bit read check" */
    if( ( flashWREG->FEDACSTATUS & 0x400U ) != 0x400U )
    {
        selftestFailNotification( FMCBUS1PARITYCHECK_FAIL1 );
    }
    else
    {
        /* clear status register */
        flashWREG->FEDACSTATUS = 0x400U;

        /* check if ESM is flagged */
        /*SAFETYMCUSW 139 S MR:13.7 <APPROVED> "Hardware status bit read check" */
        if( ( esmREG->SR1[ 1U ] & 0x0000010U ) == 0U )
        {
            selftestFailNotification( FMCBUS1PARITYCHECK_FAIL2 );
        }
        else
        {
            /* clear ESM flag */
            esmREG->SR1[ 1U ] |= 0x0000010U;
            esmREG->SSR2 |= 0x0000010U;
            esmREG->EKR = 0x5U;

            /* Stop Diag test mode */
            flashWREG->FDIAGCTRL = regBckupFdiagctrl;
            flashWREG->FPAROVR = regBkupFparOvr;
        }
    }

    /* Read to unfreeze the error address registers */
    flashread = flashWREG->FUNCERRADD;
}

/* SourceId : SELFTEST_SourceId_042 */
/* DesignId : SELFTEST_DesignId_011 */
/* Requirements : HL_SR401 */
void pbistFail( void )
{
    uint32 PBIST_RAMT, PBIST_FSRA0, PBIST_FSRDL0;

    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
    PBIST_RAMT = pbistREG->RAMT;
    PBIST_FSRA0 = pbistREG->FSRA0;
    PBIST_FSRDL0 = pbistREG->FSRDL0;

    if( pbistPortTestStatus( ( uint32 ) PBIST_PORT0 ) != TRUE )
    {
        memoryPort0TestFailNotification( ( uint32 ) ( ( PBIST_RAMT & 0xFF000000U )
                                                      >> 24U ),
                                         ( uint32 ) ( ( PBIST_RAMT & 0x00FF0000U )
                                                      >> 16U ),
                                         ( uint32 ) PBIST_FSRA0,
                                         ( uint32 ) PBIST_FSRDL0 );
    }
    else
    {
        /* USER CODE BEGIN (77) */
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

        /* USER CODE BEGIN (78) */
        /* USER CODE END */
    }
}

/** @fn void pbistGetConfigValue(pbist_config_reg_t *config_reg, config_value_type_t type)
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
/* SourceId : SELFTEST_SourceId_043 */
/* DesignId : SELFTEST_DesignId_034 */
/* Requirements : HL_SR506 */
void pbistGetConfigValue( pbist_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_RAMT = PBIST_RAMT_CONFIGVALUE;
        config_reg->CONFIG_DLR = PBIST_DLR_CONFIGVALUE;
        config_reg->CONFIG_PACT = PBIST_PACT_CONFIGVALUE;
        config_reg->CONFIG_PBISTID = PBIST_PBISTID_CONFIGVALUE;
        config_reg->CONFIG_OVER = PBIST_OVER_CONFIGVALUE;
        config_reg->CONFIG_FSRDL1 = PBIST_FSRDL1_CONFIGVALUE;
        config_reg->CONFIG_ROM = PBIST_ROM_CONFIGVALUE;
        config_reg->CONFIG_ALGO = PBIST_ALGO_CONFIGVALUE;
        config_reg->CONFIG_RINFOL = PBIST_RINFOL_CONFIGVALUE;
        config_reg->CONFIG_RINFOU = PBIST_RINFOU_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_RAMT = pbistREG->RAMT;
        config_reg->CONFIG_DLR = pbistREG->DLR;
        config_reg->CONFIG_PACT = pbistREG->PACT;
        config_reg->CONFIG_PBISTID = pbistREG->PBISTID;
        config_reg->CONFIG_OVER = pbistREG->OVER;
        config_reg->CONFIG_FSRDL1 = pbistREG->FSRDL1;
        config_reg->CONFIG_ROM = pbistREG->ROM;
        config_reg->CONFIG_ALGO = pbistREG->ALGO;
        config_reg->CONFIG_RINFOL = pbistREG->RINFOL;
        config_reg->CONFIG_RINFOU = pbistREG->RINFOU;
    }
}

/** @fn void stcGetConfigValue(stc_config_reg_t *config_reg, config_value_type_t type)
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
/* SourceId : SELFTEST_SourceId_044 */
/* DesignId : SELFTEST_DesignId_035 */
/* Requirements : HL_SR506 */
void stcGetConfigValue( stc_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_STCGCR0 = STC_STCGCR0_CONFIGVALUE;
        config_reg->CONFIG_STCGCR1 = STC_STCGCR1_CONFIGVALUE;
        config_reg->CONFIG_STCTPR = STC_STCTPR_CONFIGVALUE;
        config_reg->CONFIG_STCSCSCR = STC_STCSCSCR_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_STCGCR0 = stcREG->STCGCR0;
        config_reg->CONFIG_STCGCR1 = stcREG->STCGCR1;
        config_reg->CONFIG_STCTPR = stcREG->STCTPR;
        config_reg->CONFIG_STCSCSCR = stcREG->STCSCSCR;
    }
}

/** @fn void efcGetConfigValue(efc_config_reg_t *config_reg, config_value_type_t type)
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
/* SourceId : SELFTEST_SourceId_045 */
/* DesignId : SELFTEST_DesignId_036 */
/* Requirements : HL_SR506 */
void efcGetConfigValue( efc_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_BOUNDARY = EFC_BOUNDARY_CONFIGVALUE;
        config_reg->CONFIG_PINS = EFC_PINS_CONFIGVALUE;
        config_reg->CONFIG_SELFTESTCYCLES = EFC_SELFTESTCYCLES_CONFIGVALUE;
        config_reg->CONFIG_SELFTESTSIGN = EFC_SELFTESTSIGN_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_BOUNDARY = efcREG->BOUNDARY;
        config_reg->CONFIG_PINS = efcREG->PINS;
        config_reg->CONFIG_SELFTESTCYCLES = efcREG->SELF_TEST_CYCLES;
        config_reg->CONFIG_SELFTESTSIGN = efcREG->SELF_TEST_SIGN;
    }
}

/** @fn void ccmr4GetConfigValue(ccmr4_config_reg_t *config_reg, config_value_type_t type)
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
/* SourceId : SELFTEST_SourceId_046 */
/* DesignId : SELFTEST_DesignId_037 */
/* Requirements : HL_SR506 */
void ccmr4GetConfigValue( ccmr4_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_CCMKEYR = CCMR4_CCMKEYR_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_CCMKEYR = CCMKEYR;
    }
}

/** @fn void errata_PBIST_4(void)
 *   @brief Workaround for the Errata PBIST#4.
 *
 *   This function is workaround for Errata PBIST#4.
 *   This function is designed to initialize the ROMs using the PBIST controller.
 *   The CPU will configure the PBIST controller to test the PBIST ROM and STC ROM.
 *   This function should be called at startup after system init before using the ROMs.
 *
 *   @note : This Function uses register's which are not exposed to users through
 *   TRM , to run custom algorithm. User can use this function as Black box.
 *
 */
void errata_PBIST_4( void )
{
    volatile uint32 i = 0U;
    uint8 ROM_count;
    sint32 PBIST_wait_done_loop;
    uint32 pmuCalibration, pmuCount;

    /* PMU calibration */
    _pmuEnableCountersGlobal_();
    _pmuResetCounters_();
    _pmuStartCounters_( pmuCYCLE_COUNTER );
    _pmuStopCounters_( pmuCYCLE_COUNTER );
    pmuCalibration = _pmuGetCycleCount_();

    /* ROM_init Setup using special reserved registers as part of errata fix */
    /* (Only to be used in this function) */
    *( volatile uint32 * ) 0xFFFF0400U = 0x0000000AU;
    *( volatile uint32 * ) 0xFFFF040CU = 0x0000EE0AU;

    /* Loop for Executing PBIST ROM and STC ROM */
    for( ROM_count = 0U; ROM_count < 2U; ROM_count++ )
    {
        PBIST_wait_done_loop = 0;

        /* Disable PBIST clocks and ROM clock */
        pbistREG->PACT = 0x0U;

        /* PBIST Clocks did not disable */
        if( pbistREG->PACT != 0x0U )
        {
            selftestFailNotification( PBISTSELFCHECK_FAIL3 );
        }
        else
        {
            /* PBIST ROM clock frequency = HCLK frequency /2 */
            /* Disable memory self controller */
            systemREG1->MSTGCR = 0x00000105U;

            /* Disable Memory Initialization controller */
            systemREG1->MINITGCR = 0x5U;

            /* Enable memory self controller */
            systemREG1->MSTGCR = 0x0000010AU;

            /* Clear PBIST Done */
            systemREG1->MSTCGSTAT = 0x1U;

            /* Enable PBIST controller */
            systemREG1->MSINENA = 0x1U;

            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Wait for few clock cycles (Value of i
             * not used)" */
            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Wait for few clock cycles (Value of i
             * not used)" */
            /* wait for 32 VBUS clock cycles at least, based on HCLK to VCLK ratio */
            for( i = 0U; i < ( 32U + ( 32U * 1U ) ); i++ )
            { /* Wait */
            }

            /* Enable PBIST clocks and ROM clock */
            pbistREG->PACT = 0x3U;

            /* CPU control of PBIST */
            pbistREG->DLR = 0x10U;

            /* Load PBIST ALGO to initialize the ROMs */
            *( volatile uint32 * ) 0xFFFFE400U = 0x00000001U;
            *( volatile uint32 * ) 0xFFFFE440U = 0x00000025U;
            *( volatile uint32 * ) 0xFFFFE404U = 0x62400001U;
            *( volatile uint32 * ) 0xFFFFE444U = 0x00000004U;
            *( volatile uint32 * ) 0xFFFFE408U = 0x00068003U;
            *( volatile uint32 * ) 0xFFFFE448U = 0x00000000U;
            *( volatile uint32 * ) 0xFFFFE40CU = 0x00000004U;
            *( volatile uint32 * ) 0xFFFFE44CU = 0x00006860U;
            *( volatile uint32 * ) 0xFFFFE410U = 0x00000000U;
            *( volatile uint32 * ) 0xFFFFE450U = 0x00000001U;
            *( volatile uint32 * ) 0xFFFFE540U = 0x000003E8U;
            *( volatile uint32 * ) 0xFFFFE550U = 0x00000001U;
            *( volatile uint32 * ) 0xFFFFE530U = 0x00000000U;

            /* SELECT ROM */
            if( ROM_count == 1U )
            {
                /* SELECT PBIST ROM */
                *( volatile uint32 * ) 0xFFFFE520U = 0x00000002U;
                *( volatile uint32 * ) 0xFFFFE524U = 0x00000000U;
                pbistREG->RAMT = 0x01002008U;
            }
            else
            {
                /* SELECT STC ROM */
                *( volatile uint32 * ) 0xFFFFE520U = 0xFFF0007CU;
                *( volatile uint32 * ) 0xFFFFE524U = 0x0A63FFFFU;
                pbistREG->RAMT = 0x02002008U;
            }

            /*  Setup using special reserved registers as part of errata fix */
            /*      (Only to be used in this function) */
            pbistREG->rsvd1[ 4U ] = 1U;
            pbistREG->rsvd1[ 0U ] = 3U;

            /* Start PMU counter */
            _pmuResetCounters_();
            _pmuStartCounters_( pmuCYCLE_COUNTER );

            /* PBIST_RUN */
            pbistREG->rsvd1[ 1U ] = 1U;

            /* wait until memory self-test done is indicated */
            /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
            while( ( systemREG1->MSTCGSTAT & 0x1U ) != 0x1U )
            {
            } /* Wait */

            /* Stop PMU counter */
            _pmuStopCounters_( pmuCYCLE_COUNTER );

            /* Get CPU cycle count */
            pmuCount = _pmuGetCycleCount_();

            /* Calculate PBIST test complete time in ROM Clock */
            /* 2 - Divide value ( Default is 2 in HALCoGen) */
            /* 1000 = 0x3E8 - Test Loop count in ROM Algorithm */
            pmuCount = pmuCount - pmuCalibration;
            PBIST_wait_done_loop = ( ( sint32 ) pmuCount / 2 ) - 1000;

            /* Check PBIST status results (Address, Status, Count, etc...) */
            if( ( pbistREG->FSRA0 | pbistREG->FSRA1 | pbistREG->FSRDL0 | pbistREG->rsvd3
                  | pbistREG->FSRDL1 | pbistREG->rsvd4[ 0U ] | pbistREG->rsvd4[ 1U ] )
                != 0U )
            {
                /* PBIST Failure for the Algorithm chosen above */
                selftestFailNotification( PBISTSELFCHECK_FAIL1 );
            }

            /* Check that the algorithm executed in the expected amount of time. */
            /* This time is dependent on the ROMCLKDIV selected */
            if( ( PBIST_wait_done_loop <= 20 ) || ( PBIST_wait_done_loop >= 200 ) )
            {
                selftestFailNotification( PBISTSELFCHECK_FAIL2 );
            }

            /* Disable PBIST clocks and ROM clock */
            pbistREG->PACT = 0x0U;

            /* Disable PBIST */
            systemREG1->MSTGCR &= 0xFFFFFFF0U;
            systemREG1->MSTGCR |= 0x5U;
        }
    } /* ROM Loop */

    /* ROM restore default setup */
    /* (must be completed before continuing) */
    *( volatile uint32 * ) 0xFFFF040CU = 0x0000AA0AU;
    *( volatile uint32 * ) 0xFFFF040CU = 0x0000AA05U;
    *( volatile uint32 * ) 0xFFFF0400U = 0x00000005U;

    _pmuDisableCountersGlobal_();
}

/** @fn void enableParity(void)
 *   @brief Enable peripheral RAM parity
 *
 *   This function enables RAM parity for all peripherals for which RAM parity check is
 * enabled. This function is called before memoryInit in the startup
 *
 */
void enableParity( void )
{
}

/** @fn void disableParity(void)
 *   @brief Disable peripheral RAM parity
 *
 *   This function disables RAM parity for all peripherals for which RAM parity check is
 * enabled. This function is called after memoryInit in the startup
 *
 */
void disableParity( void )
{
}
