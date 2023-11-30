/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
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
#include "board.h"

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Configures the EBI for NandFlash access.
 */
extern void BOARD_ConfigureNandFlash( Smc* pSmc )
{
    /* Enable peripheral clock */
    PMC_EnablePeripheral( ID_SMC ) ;

    /* NCS0 is assigned to a NAND Flash (NANDOE and NANWE used for NCS0) */
    // MATRIX->MATRIX_SFR[5] = 1;

    pSmc->SMC_CS_NUMBER[0].SMC_SETUP = 
          SMC_SETUP_NWE_SETUP(0)
        | SMC_SETUP_NCS_WR_SETUP(1)
        | SMC_SETUP_NRD_SETUP(0)
        | SMC_SETUP_NCS_RD_SETUP(1);

    pSmc->SMC_CS_NUMBER[0].SMC_PULSE = 
          SMC_PULSE_NWE_PULSE(2)
        | SMC_PULSE_NCS_WR_PULSE(3)
        | SMC_PULSE_NRD_PULSE(4)
        | SMC_PULSE_NCS_RD_PULSE(4);

    pSmc->SMC_CS_NUMBER[0].SMC_CYCLE = 
          SMC_CYCLE_NWE_CYCLE(4)
        | SMC_CYCLE_NRD_CYCLE(7);

    pSmc->SMC_CS_NUMBER[0].SMC_MODE = 
          SMC_MODE_READ_MODE
        | SMC_MODE_WRITE_MODE;
}

/**
 * \brief Configures the EBI for %NorFlash access.
 */
extern void BOARD_ConfigureNorFlash( Smc* pSmc )
{
    /* Enable peripheral clock */
    PMC_EnablePeripheral( ID_SMC ) ;

    /* Configure SMC, NCS0 is assigned to a norflash */
    pSmc->SMC_CS_NUMBER[0].SMC_SETUP = 
          SMC_SETUP_NWE_SETUP(2)
        | SMC_SETUP_NCS_WR_SETUP(0)
        | SMC_SETUP_NRD_SETUP(0)
        | SMC_SETUP_NCS_RD_SETUP(0);

    pSmc->SMC_CS_NUMBER[0].SMC_PULSE = 
          SMC_PULSE_NWE_PULSE(6)
        | SMC_PULSE_NCS_WR_PULSE(0xA)
        | SMC_PULSE_NRD_PULSE(0xA)
        | SMC_PULSE_NCS_RD_PULSE(0xA);

    pSmc->SMC_CS_NUMBER[0].SMC_CYCLE = 
          SMC_CYCLE_NWE_CYCLE(0xA)
        | SMC_CYCLE_NRD_CYCLE(0xA);

    pSmc->SMC_CS_NUMBER[0].SMC_MODE  = 
          SMC_MODE_READ_MODE
        | SMC_MODE_WRITE_MODE
        | SMC_MODE_EXNW_MODE_DISABLED
        | SMC_MODE_TDF_CYCLES(0x1);
}

/**
 * \brief An accurate one-to-one comparison is necessary between PSRAM and SMC waveforms for
 *   a complete SMC configuration.
 *  \note The system is running at 48 MHz for the EBI Bus.
 *        Please refer to the "AC Characteristics" section of the customer product datasheet.
 */
extern void BOARD_ConfigurePSRAM( Smc* pSmc )
{
    uint32_t dwTmp ;

    /* Enable peripheral clock */
    PMC_EnablePeripheral( ID_SMC ) ;

    /* Configure SMC, NCS1 is assigned to a external PSRAM */
    /**
     * PSRAM IS66WV51216BLL
     * 55 ns Access time
     * tdoe = 25 ns max
     * SMC1 (timing SAM3S read mode SMC) = 21 ns of setup
     * 21 + 55 = 76 ns => at least 5 cycles at 64 MHz
     * Write pulse width minimum = 45 ns (PSRAM)
     */
    pSmc->SMC_CS_NUMBER[1].SMC_SETUP = 
          SMC_SETUP_NWE_SETUP( 1 )
        | SMC_SETUP_NCS_WR_SETUP( 0 )
        | SMC_SETUP_NRD_SETUP( 2 )
        | SMC_SETUP_NCS_RD_SETUP( 0 ) ;

    pSmc->SMC_CS_NUMBER[1].SMC_PULSE = 
          SMC_PULSE_NWE_PULSE( 3 )
        | SMC_PULSE_NCS_WR_PULSE( 4 )
        | SMC_PULSE_NRD_PULSE( 3 )
        | SMC_PULSE_NCS_RD_PULSE( 5 ) ;

    /* NWE_CYCLE:     The total duration of the write cycle.
       NWE_CYCLE = NWE_SETUP + NWE_PULSE + NWE_HOLD
       = NCS_WR_SETUP + NCS_WR_PULSE + NCS_WR_HOLD
       (tWC) Write Cycle Time min. 70ns
NRD_CYCLE:     The total duration of the read cycle.
NRD_CYCLE = NRD_SETUP + NRD_PULSE + NRD_HOLD
= NCS_RD_SETUP + NCS_RD_PULSE + NCS_RD_HOLD
(tRC) Read Cycle Time min. 70ns. */
    pSmc->SMC_CS_NUMBER[1].SMC_CYCLE = 
          SMC_CYCLE_NWE_CYCLE( 4 )
        | SMC_CYCLE_NRD_CYCLE( 5 ) ;

    dwTmp = SMC->SMC_CS_NUMBER[0].SMC_MODE;
    pSmc->SMC_CS_NUMBER[1].SMC_MODE  = dwTmp
        | SMC_MODE_READ_MODE
        | SMC_MODE_WRITE_MODE;
}


uint32_t ExtRAM_Validation(uint32_t baseAddr, uint32_t size)
{
    uint32_t i;
    uint32_t *ptr = (uint32_t *) baseAddr;

    for (i = 0; i < size << 2; ++i) {

        if (i & 1) {
            ptr[i] = 0x55AA55AA | (1 << i);
        }
        else {
            ptr[i] = 0xAA55AA55 | (1 << i);
        }
    }

    for (i = 0; i <  size << 2; ++i) {
        if (i & 1) {
            if (ptr[i] != (0x55AA55AA | (1 << i))) {
                return 0;
            }
        }
        else {
            if (ptr[i] != (0xAA55AA55 | (1 << i))) {
                return 0;
            }
        }
    }
    return 1;
}


#define SDRAM_BA0 (1 << 20)
#define SDRAM_BA1 (1 << 21)

/**
 * \brief Configures the EBI for Sdram (IS42S16100E-7B) access.
 */


void BOARD_ConfigureSdram( void )
{
    const Pin pinsSdram[] = {BOARD_SDRAM_PINS};
    volatile uint32_t i;
    volatile uint8_t *pSdram = (uint8_t *) SDRAM_CS_ADDR;

    /* Configure PIO */
    PIO_Configure(pinsSdram, PIO_LISTSIZE(pinsSdram));
    PMC_EnablePeripheral(ID_SDRAMC);
    *((uint32_t *)0x40088124) = 0x10;

    /* 1. SDRAM features must be set in the configuration register: asynchronous timings (TRC, TRAS, etc.), number
       of columns, rows, CAS latency, and the data bus width. */
    SDRAMC->SDRAMC_CR = 
          SDRAMC_CR_NC_COL8    // 8 column bits 
        | SDRAMC_CR_NR_ROW11   // 12 row bits (4K)
        | SDRAMC_CR_CAS_LATENCY3              // CAS Latency 2
        | SDRAMC_CR_NB_BANK2                  // 2 banks
        | SDRAMC_CR_DBW                       // 16 bit
        | SDRAMC_CR_TWR(2)
        | SDRAMC_CR_TRC_TRFC(9) // 63ns   min
        | SDRAMC_CR_TRP(3) // Command period (PRE to ACT) 21 ns min
        | SDRAMC_CR_TRCD(3) // Active Command to read/Write Command delay time 21ns min 
        | SDRAMC_CR_TRAS(6) // Command period (ACT to PRE)  42ns min 
        | SDRAMC_CR_TXSR(10U); //Exit self-refresh to active time  70ns Min

    /* 2. For mobile SDRAM, temperature-compensated self refresh (TCSR), drive strength (DS) and partial array
       self refresh (PASR) must be set in the Low Power Register. */

    /* 3. The SDRAM memory type must be set in the Memory Device Register.*/
    SDRAMC->SDRAMC_MDR = SDRAMC_MDR_MD_SDRAM;

    /* 4. A minimum pause of 200 ¦Ìs is provided to precede any signal toggle.*/
    for (i = 0; i < 100000; i++);

    /* 5. (1)A NOP command is issued to the SDRAM devices. The application must set Mode to 1 in the Mode
       Register and perform a write access to any SDRAM address.*/
    SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_NOP;
    *pSdram = 0;
    for (i = 0; i < 100000; i++);
    /* 6. An All Banks Precharge command is issued to the SDRAM devices. The application must set Mode to 2 in
       the Mode Register and perform a write access to any SDRAM address. */
    SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_ALLBANKS_PRECHARGE;
    *pSdram = 0;
    for (i = 0; i < 100000; i++);
    /* 7. Eight auto-refresh (CBR) cycles are provided. The application must set the Mode to 4 in the Mode Register
       and perform a write access to any SDRAM location eight times.*/
    for (i = 0 ; i< 8; i++) {
        SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_AUTO_REFRESH;
        *pSdram = 0;
    }
    for (i = 0; i < 100000; i++);
    /*8. A Mode Register set (MRS) cycle is issued to program the parameters of the SDRAM devices, in particular
      CAS latency and burst length. The application must set Mode to 3 in the Mode Register and perform a write
      access to the SDRAM. The write address must be chosen so that BA[1:0] are set to 0. For example, with a
      16-bit 128 MB SDRAM (12 rows, 9 columns, 4 banks) bank address, the SDRAM write access should be
      done at the address 0x70000000.*/
    SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_LOAD_MODEREG;
    *pSdram = 0;

    for (i = 0; i < 100000; i++);
    /*9. For mobile SDRAM initialization, an Extended Mode Register set (EMRS) cycle is issued to program the
      SDRAM parameters (TCSR, PASR, DS). The application must set Mode to 5 in the Mode Register and
      perform a write access to the SDRAM. The write address must be chosen so that BA[1] or BA[0] are set to 1.
      For example, with a 16-bit 128 MB SDRAM, (12 rows, 9 columns, 4 banks) bank address the SDRAM write
      access should be done at the address 0x70800000 or 0x70400000. */
    //SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_EXT_LOAD_MODEREG;
    // *((uint8_t *)(pSdram + SDRAM_BA0)) = 0;

    /* 10. The application must go into Normal Mode, setting Mode to 0 in the Mode Register and performing a write
       access at any location in the SDRAM. */
    SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_NORMAL;
    *pSdram = 0;
    for (i = 0; i < 100000; i++);
    /* 11. Write the refresh rate into the count field in the SDRAMC Refresh Timer register. (Refresh rate = delay
       between refresh cycles). The SDRAM device requires a refresh every 15.625 ¦Ìs or 7.81 ¦Ìs. With a 100 MHz
       frequency, the Refresh Timer Counter Register must be set with the value 1562(15.625 ¦Ìs x 100 MHz) or
       781(7.81 ¦Ìs x 100 MHz). */
    // For IS42S16100E, 2048 refresh cycle every 32ms, every 15.625 ¦Ìs
    SDRAMC->SDRAMC_TR = 2011; //1562;
    SDRAMC->SDRAMC_CR1 |= 1<<8;
    /* After initialization, the SDRAM devices are fully functional. */
}
