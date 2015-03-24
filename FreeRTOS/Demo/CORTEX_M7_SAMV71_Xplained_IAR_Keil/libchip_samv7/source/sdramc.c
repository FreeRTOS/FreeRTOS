/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2010, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 * \file
 *
 * Implementation of memories configuration on board.
 *
 */
/*----------------------------------------------------------------------------
*        Headers
*----------------------------------------------------------------------------*/
#include "chip.h"

/*----------------------------------------------------------------------------
*        Local functions
*----------------------------------------------------------------------------*/
/**
 * \brief Calculate the sdram controller config register value.
 * \param pMemory  Pointer to the sdram structure.
 * \return Configure register value.
 */
static uint32_t SDRAMC_compute_CR_value( SSdramc_Memory* pMemory )
{
    uint32_t dw=0 ;

    dw |= pMemory->cfg.dwColumnBits ;
    dw |= pMemory->cfg.dwRowBits ;
    dw |= pMemory->cfg.dwBanks ;  //NB, number of banks
    dw |= pMemory->cfg.dwCAS ;  //CAS, CAS latency
    dw |= pMemory->cfg.dwDataBusWidth ;  //DBW, data bus width
    dw |= SDRAMC_CR_TWR( pMemory->cfg.dwWriteRecoveryDelay ) ;  //TWR, Write Recovery Delay
    dw |= SDRAMC_CR_TRC_TRFC( pMemory->cfg.dwRowCycleDelay_RowRefreshCycle ) ;  //TRC_TRFC,Row Cycle Delay and Row Refresh Cycle
    dw |= SDRAMC_CR_TRP( pMemory->cfg.dwRowPrechargeDelay ) ;  //TRP, Row Precharge Delay
    dw |= SDRAMC_CR_TRCD( pMemory->cfg.dwRowColumnDelay ) ;  //TRCD, Row to Column Delay
    dw |= SDRAMC_CR_TRAS( pMemory->cfg.dwActivePrechargeDelay ) ;  //TRAS, Active to Precharge Delay
    dw |= SDRAMC_CR_TXSR( pMemory->cfg.dwExitSelfRefreshActiveDelay ) ;  //TXSR, Exit Self Refresh to Active Delay

    return dw ;
}

/*----------------------------------------------------------------------------
*        Exported functions
*----------------------------------------------------------------------------*/
/**
 * \brief Configure and initialize the SDRAM controller.
 * \param pMemory  Pointer to the sdram structure.
 * \param dwClockFrequency  SDRAM clock frequency.
 */
extern void SDRAMC_Configure( SSdramc_Memory* pMemory, uint32_t dwClockFrequency )
{
    volatile uint32_t dw ;

    /* SDRAM hardware init */
    /* Enable peripheral clock */
    PMC_EnablePeripheral( ID_SMC ) ;

    /* SDRAM device configure */
    /* Step 1. */
    /* Program the features of SDRAM device into the Configuration Register.*/
    SDRAMC->SDRAMC_CR = SDRAMC_compute_CR_value( pMemory ) ;

    /* Step 2. */
    /* For low-power SDRAM, temperature-compensated self refresh (TCSR),
    drive strength (DS) and partial array self refresh (PASR) must be set
    in the Low-power Register.*/
    SDRAMC->SDRAMC_LPR = 0;

    /* Step 3. */
    /* Program the memory device type into the Memory Device Register */
    SDRAMC->SDRAMC_MDR = SDRAMC_MDR_MD_SDRAM;

    /* Step 4 */
    /* A minimum pause of 200 ¦Ìs is provided to precede any signal toggle.
    (6 core cycles per iteration) */
    for ( dw = 0; dw < ((dwClockFrequency/1000000)*200/6) ; dw++ )
    {
        ;
    }

    /* Step 5. */
    /* A NOP command is issued to the SDR-SDRAM. Program NOP command into
    Mode Register, the application must set Mode to 1 in the Mode Register.
    Perform a write access to any SDR-SDRAM address to acknowledge this command.
    Now the clock which drives SDR-SDRAM device is enabled.*/
    SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_NOP;
    *(uint16_t *)(EBI_SDRAMC_ADDR) = 0;

    /* Step 6. */
    /* An all banks precharge command is issued to the SDR-SDRAM. Program all
    banks precharge command into Mode Register, the application must set Mode to
    2 in the Mode Register . Perform a write access to any SDRSDRAM address to
    acknowledge this command. */
    SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_ALLBANKS_PRECHARGE;
    *(uint16_t *)(EBI_SDRAMC_ADDR) = 0x0;

    /* add some delays after precharge */
    for ( dw = 0; dw < ((dwClockFrequency/1000000)*200/6) ; dw++ )
    {
        ;
    }

    /* Step 7. */
    /* Eight auto-refresh (CBR) cycles are provided. Program the auto refresh
    command (CBR) into Mode Register, the application must set Mode to 4 in
    the Mode Register. Once in the idle state, eight AUTO REFRESH cycles must
    be performed. */
    SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_AUTO_REFRESH;
    *(uint16_t *)(EBI_SDRAMC_ADDR + 0 ) = 0x1;

    SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_AUTO_REFRESH;
    *(uint16_t *)(EBI_SDRAMC_ADDR + 0) = 0x2;

    SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_AUTO_REFRESH;
    *(uint16_t *)(EBI_SDRAMC_ADDR + 0 ) = 0x3;

    SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_AUTO_REFRESH;
    *(uint16_t *)(EBI_SDRAMC_ADDR + 0) = 0x4;

    SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_AUTO_REFRESH;
    *(uint16_t *)(EBI_SDRAMC_ADDR + 0 ) = 0x5;

    SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_AUTO_REFRESH;
    *(uint16_t *)(EBI_SDRAMC_ADDR + 0) = 0x6;

    SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_AUTO_REFRESH;
    *(uint16_t *)(EBI_SDRAMC_ADDR + 0 ) = 0x7;

    SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_AUTO_REFRESH;
    *(uint16_t *)(EBI_SDRAMC_ADDR + 0) = 0x8;

    /* Step 8. */
    /* A Mode Register set (MRS) cycle is issued to program the parameters of
    the SDRAM devices, in particular CAS latency and burst length. */
    SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_LOAD_MODEREG;
    *(uint16_t *)(EBI_SDRAMC_ADDR + 0x22) = 0xcafe;

    /* Step 9. */
    /* For low-power SDR-SDRAM initialization, an Extended Mode Register set
    (EMRS) cycle is issued to program the SDR-SDRAM parameters (TCSR, PASR, DS).
    The write address must be chosen so that BA[1] is set to 1 and BA[0] is set
    to 0 */
    SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_EXT_LOAD_MODEREG;
    *((uint16_t *)(EBI_SDRAMC_ADDR + (1 << pMemory->cfg.dwBK1))) = 0;

    /* Step 10. */
    /* The application must go into Normal Mode, setting Mode to 0 in the Mode
    Register and perform a write access at any location in the SDRAM to
    acknowledge this command. */
    SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_NORMAL;
    *(uint16_t *)(EBI_SDRAMC_ADDR ) = 0x0;

    /* Step 11. */
    /* Write the refresh rate into the count field in the SDRAMC Refresh
     Timer register. Set Refresh timer 15.625 us*/
    dw=dwClockFrequency/1000u ;
    dw*=15625u ;
    dw/=1000000u ;
    SDRAMC->SDRAMC_TR = SDRAMC_TR_COUNT( dw ) ;
}

