/** @file errata.c
 *   @brief Errata workaround Source File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Errata workaround API's
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

#include "errata.h"
#include "sys_core.h"
#include "sys_pmu.h"

/** @fn void errataFailNotification(uint32 flag)
 *   @brief Errata fail service routine
 *
 *    This function is called if there is a errata workaround fail with appropriate flag
 */
void errataFailNotification( uint32 flag )
{
    /* USER CODE BEGIN (1) */
    /* USER CODE END */
}

/* USER CODE BEGIN (2) */
/* USER CODE END */
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

    /* USER CODE BEGIN (3) */
    /* USER CODE END */

    /* PMU calibration */
    _pmuInit_();
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
    for( ROM_count = 0U; ROM_count < 4U; ROM_count++ )
    {
        PBIST_wait_done_loop = 0;

        /* Disable PBIST clocks and ROM clock */
        pbistREG->PACT = 0x0U;

        /* PBIST Clocks did not disable */
        if( pbistREG->PACT != 0x0U )
        {
            errataFailNotification( PBISTERRATA_FAIL3 );
        }
        else
        {
            /* PBIST ROM clock frequency = GCLK frequency /4 */
            /* Disable memory self controller */
            systemREG1->MSTGCR = 0x00000205U;

            /* Disable Memory Initialization controller */
            systemREG1->MINITGCR = 0x5U;

            /* Enable memory self controller */
            systemREG1->MSTGCR = 0x0000020AU;

            /* Clear PBIST Done */
            systemREG1->MSTCGSTAT = 0x1U;

            /* Enable PBIST controller */
            systemREG1->MSINENA = 0x1U;

            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Wait for few clock cycles (Value of i
             * not used)" */
            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Wait for few clock cycles (Value of i
             * not used)" */
            /* wait for 64 VBUS clock cycles at least, based on HCLK to VCLK ratio */
            for( i = 0U; i < ( 64U + ( 64U * 1U ) ); i++ )
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
            if( ROM_count == 0U )
            {
                /* SELECT STC1 ROM1 */
                *( volatile uint32 * ) 0xFFFFE520U = 0xFFF0007CU;
                *( volatile uint32 * ) 0xFFFFE524U = 0x07B3FFFFU;
                pbistREG->RAMT = 0x0E01200CU;
                /*  Setup using special reserved registers as part of errata fix */
                /*      (Only to be used in this function) */
                pbistREG->rsvd1[ 4U ] = 1U; /* CSR */
            }
            else if( ROM_count == 1U )
            {
                /* SELECT STC1 ROM2 */
                *( volatile uint32 * ) 0xFFFFE520U = 0xA88FA473U;
                *( volatile uint32 * ) 0xFFFFE524U = 0x00BD719DU;
                pbistREG->RAMT = 0x0E02200CU;
                /*  Setup using special reserved registers as part of errata fix */
                /*      (Only to be used in this function) */
                pbistREG->rsvd1[ 4U ] = 2U; /* CSR */
            }
            else if( ROM_count == 2U )
            {
                /* SELECT STC2 ROM */
                *( volatile uint32 * ) 0xFFFFE520U = 0xFFF0007CU;
                *( volatile uint32 * ) 0xFFFFE524U = 0x06E3FFFFU;
                pbistREG->RAMT = 0x0F01200CU;
                /*  Setup using special reserved registers as part of errata fix */
                /*      (Only to be used in this function) */
                pbistREG->rsvd1[ 4U ] = 1U; /* CSR */
            }
            else if( ROM_count == 3U )
            {
                /* SELECT PBIST ROM */
                *( volatile uint32 * ) 0xFFFFE520U = 0x00000002U;
                *( volatile uint32 * ) 0xFFFFE524U = 0x00000000U;
                pbistREG->RAMT = 0x0101200CU;
                /*  Setup using special reserved registers as part of errata fix */
                /*      (Only to be used in this function) */
                pbistREG->rsvd1[ 4U ] = 1U; /* CSR */
            }
            else
            {
                /* Empty */
            }

            /*  Setup using special reserved registers as part of errata fix */
            /*      (Only to be used in this function) */
            pbistREG->rsvd1[ 0U ] = 8U; /* CMS */

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
            /* 4 - Divide value ( Default is 4 in HALCoGen) */
            /* 1000 = 0x3E8 - Test Loop count in ROM Algorithm */
            pmuCount = pmuCount - pmuCalibration;
            PBIST_wait_done_loop = ( ( sint32 ) pmuCount / 4 ) - 1000;

            /* Check PBIST status results (Address, Status, Count, etc...) */
            if( ( pbistREG->FSRA0 | pbistREG->FSRA1 | pbistREG->FSRDL0 | pbistREG->rsvd3
                  | pbistREG->FSRDL1 | pbistREG->rsvd4[ 0U ] | pbistREG->rsvd4[ 1U ] )
                != 0U )
            {
                /* PBIST Failure for the Algorithm chosen above */
                errataFailNotification( PBISTERRATA_FAIL1 );
            }

            /* Check that the algorithm executed in the expected amount of time. */
            /* This time is dependent on the ROMCLKDIV selected */
            if( ( PBIST_wait_done_loop <= 20 ) || ( PBIST_wait_done_loop >= 200 ) )
            {
                errataFailNotification( PBISTERRATA_FAIL2 );
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

    /* USER CODE BEGIN (4) */
    /* USER CODE END */
}

/* USER CODE BEGIN (5) */
/* USER CODE END */
