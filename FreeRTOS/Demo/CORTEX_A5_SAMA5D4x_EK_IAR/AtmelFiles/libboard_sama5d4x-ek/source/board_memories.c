/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 20143, Atmel Corporation
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

/** \addtogroup ddrd_module
 *
 * The DDR/SDR SDRAM Controller (DDRSDRC) is a multiport memory controller. It comprises
 * four slave AHB interfaces. All simultaneous accesses (four independent AHB ports) are interleaved
 * to maximize memory bandwidth and minimize transaction latency due to SDRAM protocol.
 *
 * \section ddr2 Configures DDR2
 *
 * The DDR2-SDRAM devices are initialized by the following sequence:
 * <ul>
 * <li> EBI Chip Select 1 is assigned to the DDR2SDR Controller, Enable DDR2 clock x2 in PMC.</li>
 * <li> Step 1: Program the memory device type</li>
 * <li> Step 2:
 *  -# Program the features of DDR2-SDRAM device into the Configuration Register.
 *  -# Program the features of DDR2-SDRAM device into the Timing Register HDDRSDRC2_T0PR.
 *  -# Program the features of DDR2-SDRAM device into the Timing Register HDDRSDRC2_T1PR.
 *  -# Program the features of DDR2-SDRAM device into the Timing Register HDDRSDRC2_T2PR. </li>
 * <li> Step 3: An NOP command is issued to the DDR2-SDRAM to enable clock. </li>
 * <li> Step 4:  An NOP command is issued to the DDR2-SDRAM </li>
 * <li> Step 5: An all banks precharge command is issued to the DDR2-SDRAM. </li>
 * <li> Step 6: An Extended Mode Register set (EMRS2) cycle is  issued to chose between commercialor high  temperature operations.</li>
 * <li> Step 7: An Extended Mode Register set (EMRS3) cycle is issued to set all registers to 0. </li>
 * <li> Step 8:  An Extended Mode Register set (EMRS1) cycle is issued to enable DLL.</li>
 * <li> Step 9:  Program DLL field into the Configuration Register.</li>
 * <li> Step 10: A Mode Register set (MRS) cycle is issued to reset DLL.</li>
 * <li> Step 11: An all banks precharge command is issued to the DDR2-SDRAM.</li>
 * <li> Step 12: Two auto-refresh (CBR) cycles are provided. Program the auto refresh command (CBR) into the Mode Register.</li>
 * <li> Step 13: Program DLL field into the Configuration Register to low(Disable DLL reset).</li>
 * <li> Step 14: A Mode Register set (MRS) cycle is issued to program the parameters of the DDR2-SDRAM devices.</li>
 * <li> Step 15: Program OCD field into the Configuration Register to high (OCD calibration default). </li>
 * <li> Step 16: An Extended Mode Register set (EMRS1) cycle is issued to OCD default value.</li>
 * <li> Step 17: Program OCD field into the Configuration Register to low (OCD calibration mode exit).</li>
 * <li> Step 18: An Extended Mode Register set (EMRS1) cycle is issued to enable OCD exit.</li>
 * <li> Step 19,20: A mode Normal command is provided. Program the Normal mode into Mode Register.</li>
 * <li> Step 21: Write the refresh rate into the count field in the Refresh Timer register. The DDR2-SDRAM device requires a refresh every 15.625 or 7.81. </li>
 * </ul>
*/
/*@{*/
/*@}*/

/** \addtogroup sdram_module
 *
 * \section sdram Configures SDRAM
 *
 * The SDR-SDRAM devices are initialized by the following sequence:
 * <ul>
 * <li> EBI Chip Select 1 is assigned to the DDR2SDR Controller, Enable DDR2 clock x2 in PMC.</li>
 * <li> Step 1. Program the memory device type into the Memory Device Register</li>
 * <li> Step 2. Program the features of the SDR-SDRAM device into the Timing Register and into the Configuration Register.</li>
 * <li> Step 3. For low-power SDRAM, temperature-compensated self refresh (TCSR), drive strength (DS) and partial array self refresh (PASR) must be set in the Low-power Register.</li>
 * <li> Step 4. A NOP command is issued to the SDR-SDRAM. Program NOP command into Mode Register, the application must
 * set Mode to 1 in the Mode Register. Perform a write access to any SDR-SDRAM address to acknowledge this command.
 * Now the clock which drives SDR-SDRAM device is enabled.</li>
 * <li> Step 5. An all banks precharge command is issued to the SDR-SDRAM. Program all banks precharge command into Mode Register, the application must set Mode to 2 in the
 * Mode Register . Perform a write access to any SDRSDRAM address to acknowledge this command.</li>
 * <li> Step 6. Eight auto-refresh (CBR) cycles are provided. Program the auto refresh command (CBR) into Mode Register, the application must set Mode to 4 in the Mode Register.
 * Once in the idle state, two AUTO REFRESH cycles must be performed.</li>
 * <li> Step 7. A Mode Register set (MRS) cycle is issued to program the parameters of the SDRSDRAM
 * devices, in particular CAS latency and burst length. </li>
 * <li> Step 8. For low-power SDR-SDRAM initialization, an Extended Mode Register set (EMRS) cycle is issued to program the SDR-SDRAM parameters (TCSR, PASR, DS). The write
 * address must be chosen so that BA[1] is set to 1 and BA[0] is set to 0 </li>
 * <li> Step 9. The application must go into Normal Mode, setting Mode to 0 in the Mode Register and perform a write access at any location in the SDRAM to acknowledge this command.</li>
 * <li> Step 10. Write the refresh rate into the count field in the DDRSDRC Refresh Timer register </li>
* </ul>
*/
/*@{*/
/*@}*/



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
 * \brief Changes the mapping of the chip so that the remap area mirrors the
 * internal ROM or the EBI CS0.
 */
void BOARD_RemapRom( void )
{
    AXIMX->AXIMX_REMAP = 0;
}

/**
 * \brief Changes the mapping of the chip so that the remap area mirrors the
 * internal RAM.
 */

void BOARD_RemapRam( void )
{
    AXIMX->AXIMX_REMAP = AXIMX_REMAP_REMAP0;
}

/**
 * \brief Initialize Vdd EBI drive
 * \param 0: 1.8V 1: 3.3V
 */
void BOARD_ConfigureVddMemSel( uint8_t VddMemSel )
{
	( void ) VddMemSel;
}

#define DDR2_BA0(r) (1 << (26 + r))
#define DDR2_BA1(r) (1 << (27 + r))

#define H64MX_DDR_SLAVE_PORT0   3

static void matrix_configure_slave_ddr(void)
{
     int ddr_port;

     /* Disable write protection */
     MATRIX0->MATRIX_WPMR = MPDDRC_WPMR_WPKEY_PASSWD;

     /* Partition internal SRAM */
     MATRIX0->MATRIX_SSR[11]   = 0;
     MATRIX0->MATRIX_SRTSR[11] = 0x05;
     MATRIX0->MATRIX_SASSR[11] = 0x04;

     ddr_port = 1;

     /* Partition external DDR */
     /* DDR port 0 not used from NWd */
     for (ddr_port = 1 ; ddr_port < 8 ; ddr_port++) {
           MATRIX0->MATRIX_SSR[H64MX_DDR_SLAVE_PORT0 + ddr_port]   = 0x00FFFFFF;
           MATRIX0->MATRIX_SRTSR[H64MX_DDR_SLAVE_PORT0 + ddr_port] = 0x0000000F;
           MATRIX0->MATRIX_SASSR[H64MX_DDR_SLAVE_PORT0 + ddr_port] = 0x0000FFFF;
     }
}

#define MATRIX_KEY_VAL (0x4D4154u)

static void matrix_configure_slave_nand(void)
{
    /* Disable write protection */
    MATRIX0->MATRIX_WPMR = MATRIX_WPMR_WPKEY(MATRIX_KEY_VAL);
    MATRIX1->MATRIX_WPMR = MATRIX_WPMR_WPKEY(MATRIX_KEY_VAL);

    /* Partition internal SRAM */
    MATRIX0->MATRIX_SSR[11]   = 0x00010101;
    MATRIX0->MATRIX_SRTSR[11] = 0x05;
    MATRIX0->MATRIX_SASSR[11] = 0x05;

    MATRIX1->MATRIX_SRTSR[3] = 0xBBBBBBBB;
    MATRIX1->MATRIX_SSR[3]   = 0x00FFFFFF;
    MATRIX1->MATRIX_SASSR[3] = 0xBBBBBBBB;

    MATRIX1->MATRIX_SRTSR[4] = 0x01;
    MATRIX1->MATRIX_SSR[4]   = 0x00FFFFFF;
    MATRIX1->MATRIX_SASSR[4] = 0x01;
    MATRIX1->MATRIX_MEIER = 0x3FF;
}

/**
 * \brief Configures DDR2 (MT47H128M16RT 128MB/ MT47H64M16HR)
 MT47H64M16HR : 8 Meg x 16 x 8 banks
 Refresh count: 8K
 Row address: A[12:0] (8K)
 Column address A[9:0] (1K)
 Bank address BA[2:0] a(24,25) (8)
 */
void BOARD_ConfigureDdram( void )
{
    volatile uint8_t *pDdr = (uint8_t *) DDR_CS_ADDR;
    volatile uint32_t i;

    volatile uint32_t dummy_value;

    matrix_configure_slave_ddr();

    /* Enable DDR2 clock x2 in PMC */
    PMC->PMC_PCER0 = (1 << (ID_MPDDRC));
    PMC->PMC_SCER  |= PMC_SCER_DDRCK;

    /* MPDDRC I/O Calibration Register */
    dummy_value  =  MPDDRC->MPDDRC_IO_CALIBR;
    dummy_value &= ~MPDDRC_IO_CALIBR_RDIV_Msk;
    dummy_value &= ~MPDDRC_IO_CALIBR_TZQIO_Msk;
    dummy_value |= MPDDRC_IO_CALIBR_CALCODEP(7);
    dummy_value |= MPDDRC_IO_CALIBR_CALCODEN(8);
    dummy_value |= MPDDRC_IO_CALIBR_RDIV_RZQ_60_RZQ_50;
    dummy_value |= MPDDRC_IO_CALIBR_TZQIO(5);
    dummy_value |= MPDDRC_IO_CALIBR_EN_CALIB_ENABLE_CALIBRATION;
    MPDDRC->MPDDRC_IO_CALIBR = dummy_value;

    /* Step 1: Program the memory device type */
    /* DBW = 0 (32 bits bus wide); Memory Device = 6 = DDR2-SDRAM = 0x00000006*/

    MPDDRC->MPDDRC_MD   =  MPDDRC_MD_MD_DDR2_SDRAM | MPDDRC_MD_DBW_DBW_32_BITS;

    MPDDRC->MPDDRC_RD_DATA_PATH = MPDDRC_RD_DATA_PATH_SHIFT_SAMPLING_SHIFT_ONE_CYCLE;

    /* Step 2: Program the features of DDR2-SDRAM device into the Timing Register.*/
    MPDDRC->MPDDRC_CR    = MPDDRC_CR_NR_14_ROW_BITS     |
                           MPDDRC_CR_NC_10_COL_BITS     |
                           MPDDRC_CR_CAS_DDR_CAS3       |
                           MPDDRC_CR_DLL_RESET_DISABLED |
                           MPDDRC_CR_DQMS_NOT_SHARED    |
                           MPDDRC_CR_ENRDM_OFF          |
                           MPDDRC_CR_NB_8_BANKS         |
                           MPDDRC_CR_NDQS_DISABLED      |
                           MPDDRC_CR_UNAL_SUPPORTED     |
                           MPDDRC_CR_OCD_DDR2_EXITCALIB;

    MPDDRC->MPDDRC_TPR0 = MPDDRC_TPR0_TRAS(8)    //  40 ns
                        | MPDDRC_TPR0_TRCD(3)    //  12.5 ns
                        | MPDDRC_TPR0_TWR(3)     //  15 ns
                        | MPDDRC_TPR0_TRC(10)    //  55 ns
                        | MPDDRC_TPR0_TRP(3)     //  12.5 ns
                        | MPDDRC_TPR0_TRRD(2)    //  8 ns
                        | MPDDRC_TPR0_TWTR(2)    //  2 clock cycle
                        | MPDDRC_TPR0_TMRD(2);   //  2 clock cycles


    MPDDRC->MPDDRC_TPR1 = MPDDRC_TPR1_TRFC(23)
                        | MPDDRC_TPR1_TXSNR(25)
                        | MPDDRC_TPR1_TXSRD(200)
                        | MPDDRC_TPR1_TXP(2);

    MPDDRC->MPDDRC_TPR2 = MPDDRC_TPR2_TXARD(8)
                          | MPDDRC_TPR2_TXARDS(2)
                          | MPDDRC_TPR2_TRPA(3)
                          | MPDDRC_TPR2_TRTP(2)
                          | MPDDRC_TPR2_TFAW(7);

    /* DDRSDRC Low-power Register */
    for (i = 0; i < 13300; i++) {
        asm("nop");
    }

/* Step 3: An NOP command is issued to the DDR2-SDRAM. Program the NOP command into
    the Mode Register, the application must set MODE to 1 in the Mode Register. */
    MPDDRC->MPDDRC_MR = MPDDRC_MR_MODE_NOP_CMD;
    /* Perform a write access to any DDR2-SDRAM address to acknowledge this command */
    *pDdr = 0;  /* Now clocks which drive DDR2-SDRAM device are enabled.*/

    /* A minimum pause of 200 ¦Ìs is provided to precede any signal toggle. (6 core cycles per iteration, core is at 396MHz: min 13200 loops) */
    for (i = 0; i < 13300; i++) {
        asm("nop");
    }

/* Step 4:  An NOP command is issued to the DDR2-SDRAM */
    MPDDRC->MPDDRC_MR = MPDDRC_MR_MODE_NOP_CMD;
    /* Perform a write access to any DDR2-SDRAM address to acknowledge this command.*/
    *pDdr = 0; /* Now CKE is driven high.*/
    /* wait 400 ns min */
    for (i = 0; i < 100; i++) {
        asm("nop");
    }

/* Step 5: An all banks precharge command is issued to the DDR2-SDRAM. */
    MPDDRC->MPDDRC_MR = MPDDRC_MR_MODE_PRCGALL_CMD;
    /* Perform a write access to any DDR2-SDRAM address to acknowledge this command.*/
    *pDdr = 0;
    /* wait 400 ns min */
    for (i = 0; i < 100; i++) {
        asm("nop");
    }

/* Step 6: An Extended Mode Register set (EMRS2) cycle is  issued to chose between commercialor high  temperature operations. */
    MPDDRC->MPDDRC_MR = MPDDRC_MR_MODE_EXT_LMR_CMD;
    *((uint8_t *)(pDdr + DDR2_BA1(0))) = 0; /* The write address must be chosen so that BA[1] is set to 1 and BA[0] is set to 0. */
    /* wait 2 cycles min */
    for (i = 0; i < 100; i++) {
        asm("nop");
    }

/* Step 7: An Extended Mode Register set (EMRS3) cycle is issued to set all registers to 0. */
    MPDDRC->MPDDRC_MR = MPDDRC_MR_MODE_EXT_LMR_CMD;
    *((uint8_t *)(pDdr + DDR2_BA1(0) + DDR2_BA0(0))) = 0;  /* The write address must be chosen so that BA[1] is set to 1 and BA[0] is set to 1.*/
    /* wait 2 cycles min */
    for (i = 0; i < 100; i++) {
        asm("nop");
    }

 /* Step 8:  An Extended Mode Register set (EMRS1) cycle is issued to enable DLL. */
    MPDDRC->MPDDRC_MR = MPDDRC_MR_MODE_EXT_LMR_CMD;
    *((uint8_t *)(pDdr + DDR2_BA0(0))) = 0;  /* The write address must be chosen so that BA[1] is set to 0 and BA[0] is set to 1. */
    /* An additional 200 cycles of clock are required for locking DLL */
    for (i = 0; i < 10000; i++) {
        asm("nop");
    }

/* Step 9:  Program DLL field into the Configuration Register.*/
    MPDDRC->MPDDRC_CR |= MPDDRC_CR_DLL_RESET_ENABLED;

/* Step 10: A Mode Register set (MRS) cycle is issued to reset DLL. */
    MPDDRC->MPDDRC_MR = MPDDRC_MR_MODE_LMR_CMD;
    *(pDdr) = 0;  /* The write address must be chosen so that BA[1:0] bits are set to 0. */
    /* wait 2 cycles min */
    for (i = 0; i < 100; i++) {
        asm("nop");
    }

/* Step 11: An all banks precharge command is issued to the DDR2-SDRAM. */
    MPDDRC->MPDDRC_MR = MPDDRC_MR_MODE_PRCGALL_CMD;
    *(pDdr) = 0;  /* Perform a write access to any DDR2-SDRAM address to acknowledge this command */
    /* wait 2 cycles min */
    for (i = 0; i < 100; i++) {
        asm("nop");
    }

/* Step 12: Two auto-refresh (CBR) cycles are provided. Program the auto refresh command (CBR) into the Mode Register. */
    MPDDRC->MPDDRC_MR = MPDDRC_MR_MODE_RFSH_CMD;
    *(pDdr) = 0;  /* Perform a write access to any DDR2-SDRAM address to acknowledge this command */
    /* wait 2 cycles min */
    for (i = 0; i < 100; i++) {
        asm("nop");
    }
    /* Configure 2nd CBR. */
    MPDDRC->MPDDRC_MR = MPDDRC_MR_MODE_RFSH_CMD;
    *(pDdr) = 0;  /* Perform a write access to any DDR2-SDRAM address to acknowledge this command */
    /* wait 2 cycles min */
    for (i = 0; i < 100; i++) {
        asm("nop");
    }

/* Step 13: Program DLL field into the Configuration Register to low(Disable DLL reset). */
    MPDDRC->MPDDRC_CR   &= ~MPDDRC_CR_DLL_RESET_ENABLED;

/* Step 14: A Mode Register set (MRS) cycle is issued to program the parameters of the DDR2-SDRAM devices. */
    MPDDRC->MPDDRC_MR = MPDDRC_MR_MODE_LMR_CMD;
    *(pDdr) = 0;  /* The write address must be chosen so that BA[1:0] are set to 0. */
    /* wait 2 cycles min */
    for (i = 0; i < 100; i++) {
        asm("nop");
    }

/* Step 15: Program OCD field into the Configuration Register to high (OCD calibration default). */
    MPDDRC->MPDDRC_CR   |= MPDDRC_CR_OCD_DDR2_DEFAULT_CALIB;

/* Step 16: An Extended Mode Register set (EMRS1) cycle is issued to OCD default value. */
    MPDDRC->MPDDRC_MR = MPDDRC_MR_MODE_EXT_LMR_CMD;
    *((uint8_t *)(pDdr + DDR2_BA0(0))) = 0;  /* The write address must be chosen so that BA[1] is set to 0 and BA[0] is set to 1.*/
    /* wait 2 cycles min */
    for (i = 0; i < 100; i++) {
        asm("nop");
    }

/* Step 17: Program OCD field into the Configuration Register to low (OCD calibration mode exit). */
   MPDDRC->MPDDRC_CR   &= ~(MPDDRC_CR_OCD_DDR2_DEFAULT_CALIB);

/* Step 18: An Extended Mode Register set (EMRS1) cycle is issued to enable OCD exit.*/
    MPDDRC->MPDDRC_MR = MPDDRC_MR_MODE_EXT_LMR_CMD;
    *((uint8_t *)(pDdr + DDR2_BA0(0))) = 0;  /* The write address must be chosen so that BA[1] is set to 0 and BA[0] is set to 1.*/
    /* wait 2 cycles min */
    for (i = 0; i < 100; i++) {
        asm("nop");
    }

/* Step 19,20: A mode Normal command is provided. Program the Normal mode into Mode Register. */
    MPDDRC->MPDDRC_MR = MPDDRC_MR_MODE_NORMAL_CMD;
    *(pDdr) = 0;

/* Step 21: Write the refresh rate into the count field in the Refresh Timer register. The DDR2-SDRAM device requires a refresh every 15.625 ¦Ìs or 7.81 ¦Ìs.
   With a 100MHz frequency, the refresh timer count register must to be set with (15.625 /100 MHz) = 1562 i.e. 0x061A or (7.81 /100MHz) = 781 i.e. 0x030d. */
    /* For MT47H64M16HR, The refresh period is 64ms (commercial), This equates to an average
       refresh rate of 7.8125¦Ìs (commercial), To ensure all rows of all banks are properly
       refreshed, 8192 REFRESH commands must be issued every 64ms (commercial) */
    /* ((64 x 10(^-3))/8192) x133 x (10^6) */
    MPDDRC->MPDDRC_RTR = MPDDRC_RTR_COUNT(0x2b0); /* Set Refresh timer 7.8125 us*/
    /* OK now we are ready to work on the DDRSDR */
    /* wait for end of calibration */
    for (i = 0; i < 500; i++) {
        asm("    nop");
    }
}

/**
 * \brief Configures the EBI for Sdram (LPSDR Micron MT48H8M16) access.
 */
void BOARD_ConfigureSdram( void )
{
}

/** \brief Configures the EBI for NandFlash access at 133Mhz.
 */
void BOARD_ConfigureNandFlash( uint8_t busWidth )
{
    PMC_EnablePeripheral(ID_HSMC);
    matrix_configure_slave_nand();

   HSMC->HSMC_CS_NUMBER[3].HSMC_SETUP = 0
                    | HSMC_SETUP_NWE_SETUP(2)
                    | HSMC_SETUP_NCS_WR_SETUP(2)
                    | HSMC_SETUP_NRD_SETUP(2)
                    | HSMC_SETUP_NCS_RD_SETUP(2);

    HSMC->HSMC_CS_NUMBER[3].HSMC_PULSE = 0
                    | HSMC_PULSE_NWE_PULSE(7)
                    | HSMC_PULSE_NCS_WR_PULSE(7)
                    | HSMC_PULSE_NRD_PULSE(7)
                    | HSMC_PULSE_NCS_RD_PULSE(7);

    HSMC->HSMC_CS_NUMBER[3].HSMC_CYCLE = 0
                    | HSMC_CYCLE_NWE_CYCLE(13)
                    | HSMC_CYCLE_NRD_CYCLE(13);

    HSMC->HSMC_CS_NUMBER[3].HSMC_TIMINGS = HSMC_TIMINGS_TCLR(3)
                                       | HSMC_TIMINGS_TADL(27)
                                       | HSMC_TIMINGS_TAR(3)
                                       | HSMC_TIMINGS_TRR(6)
                                       | HSMC_TIMINGS_TWB(5)
                                       | HSMC_TIMINGS_RBNSEL(3)
                                       |(HSMC_TIMINGS_NFSEL);
    HSMC->HSMC_CS_NUMBER[3].HSMC_MODE = HSMC_MODE_READ_MODE |
                                     HSMC_MODE_WRITE_MODE |
                                     ((busWidth == 8 )? HSMC_MODE_DBW_BIT_8 :HSMC_MODE_DBW_BIT_16) |
                                      HSMC_MODE_TDF_CYCLES(1);
}


void BOARD_ConfigureNorFlash( uint8_t busWidth )
{
    uint32_t dbw;
    PMC_EnablePeripheral(ID_HSMC);
    if (busWidth == 8)
    {
        dbw = HSMC_MODE_DBW_BIT_8;
    }
    else {
        dbw = HSMC_MODE_DBW_BIT_16;
    }
    /* Configure SMC, NCS0 is assigned to a norflash */
    HSMC->HSMC_CS_NUMBER[0].HSMC_SETUP = 0x00020001;
    HSMC->HSMC_CS_NUMBER[0].HSMC_PULSE = 0x0B0B0A0A;
    HSMC->HSMC_CS_NUMBER[0].HSMC_CYCLE = 0x000E000B;
    HSMC->HSMC_CS_NUMBER[0].HSMC_TIMINGS = 0x00000000;
    HSMC->HSMC_CS_NUMBER[0].HSMC_MODE  = HSMC_MODE_WRITE_MODE
                                    | HSMC_MODE_READ_MODE
                                    | dbw
                                    | HSMC_MODE_EXNW_MODE_DISABLED
                                    | HSMC_MODE_TDF_CYCLES(1);

}
