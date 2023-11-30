/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
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

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include <board.h>
#include <pio/pio.h>

//------------------------------------------------------------------------------
//         Local macros
//------------------------------------------------------------------------------

/// Reads a register value. Useful to add trace information to read  accesses.
#define READ(peripheral, register)          (peripheral->register)
/// Writes data in a register. Useful to add trace information to write accesses.
#define WRITE(peripheral, register, value)  (peripheral->register = value)

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Changes the mapping of the chip so that the remap area mirrors the
/// internal ROM or the EBI CS0 (depending on the BMS input).
//------------------------------------------------------------------------------
void BOARD_RemapRom(void)
{
    WRITE(AT91C_BASE_MATRIX, MATRIX_MRCR, 0);
}

//------------------------------------------------------------------------------
/// Changes the mapping of the chip so that the remap area mirrors the
/// internal RAM.
//------------------------------------------------------------------------------
void BOARD_RemapRam(void)
{
    WRITE(AT91C_BASE_MATRIX,
          MATRIX_MRCR,
          (AT91C_MATRIX_RCA926I | AT91C_MATRIX_RCA926D));
}

//------------------------------------------------------------------------------
/// Initialize and configure the external SDRAM.
//------------------------------------------------------------------------------
void BOARD_ConfigureSdram(void)
{
	volatile unsigned int i;
	static const Pin pinsSdram = PINS_SDRAM;
	volatile unsigned int *pSdram = (unsigned int *) AT91C_EBI_SDRAM;
	
	// Enable corresponding PIOs
    PIO_Configure(&pinsSdram, 1);
    
	// Enable EBI chip select for the SDRAM
	WRITE(AT91C_BASE_MATRIX, MATRIX_EBI, AT91C_MATRIX_CS1A_SDRAMC);
	

	// CFG Control Register
	WRITE(AT91C_BASE_SDRAMC, SDRAMC_CR, AT91C_SDRAMC_NC_9
                        				| AT91C_SDRAMC_NR_13 
                        				| AT91C_SDRAMC_CAS_2 
                        				| AT91C_SDRAMC_NB_4_BANKS
                        				| AT91C_SDRAMC_DBW_32_BITS
                        				| AT91C_SDRAMC_TWR_2
                        				| AT91C_SDRAMC_TRC_7
                        				| AT91C_SDRAMC_TRP_2
                        				| AT91C_SDRAMC_TRCD_2
                        				| AT91C_SDRAMC_TRAS_5
                        				| AT91C_SDRAMC_TXSR_8);

	for (i = 0; i < 1000; i++);

	WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_NOP_CMD);	// Perform NOP
	pSdram[0] = 0x00000000;

	WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_PRCGALL_CMD);	// Set PRCHG AL
	pSdram[0] = 0x00000000;						// Perform PRCHG

	for (i = 0; i < 10000; i++);

	WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_RFSH_CMD);	// Set 1st CBR
	pSdram[1] = 0x00000001;						// Perform CBR

	WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_RFSH_CMD);	// Set 2 CBR
	pSdram[2] = 0x00000002;						// Perform CBR

	WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_RFSH_CMD);	// Set 3 CBR
	pSdram[3] = 0x00000003;					   // Perform CBR

	WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_RFSH_CMD);	// Set 4 CBR
	pSdram[4] = 0x00000004;					  // Perform CBR

	WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_RFSH_CMD);	// Set 5 CBR
	pSdram[5] = 0x00000005;					  // Perform CBR

	WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_RFSH_CMD);	// Set 6 CBR
	pSdram[6] = 0x00000006;					// Perform CBR

	WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_RFSH_CMD);	// Set 7 CBR
	pSdram[7] = 0x00000007;					// Perform CBR

	WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_RFSH_CMD);	// Set 8 CBR
	pSdram[8] = 0x00000008;					// Perform CBR

	WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_LMR_CMD);		// Set LMR operation
	pSdram[9] = 0xcafedede;					// Perform LMR burst=1, lat=2

	WRITE(AT91C_BASE_SDRAMC, SDRAMC_TR, (BOARD_MCK * 7) / 1000000);		// Set Refresh Timer

	WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_NORMAL_CMD);	// Set Normal mode
	pSdram[0] = 0x00000000;						// Perform Normal mode
}

//------------------------------------------------------------------------------
/// Initialize and configure the SDRAM for a 48 MHz MCK (ROM code clock settings).
//------------------------------------------------------------------------------
void BOARD_ConfigureSdram48MHz(void)
{
    volatile unsigned int i;
    static const Pin pinsSdram = PINS_SDRAM;
    volatile unsigned int *pSdram = (unsigned int *) AT91C_EBI_SDRAM;
    
    // Enable corresponding PIOs
    PIO_Configure(&pinsSdram, 1);
    
    // Enable EBI chip select for the SDRAM
    WRITE(AT91C_BASE_MATRIX, MATRIX_EBI, AT91C_MATRIX_CS1A_SDRAMC);
    

    // CFG Control Register
    WRITE(AT91C_BASE_SDRAMC, SDRAMC_CR, AT91C_SDRAMC_NC_9
                                        | AT91C_SDRAMC_NR_13 
                                        | AT91C_SDRAMC_CAS_2 
                                        | AT91C_SDRAMC_NB_4_BANKS
                                        | AT91C_SDRAMC_DBW_32_BITS
                                        | AT91C_SDRAMC_TWR_1
                                        | AT91C_SDRAMC_TRC_4
                                        | AT91C_SDRAMC_TRP_1
                                        | AT91C_SDRAMC_TRCD_1
                                        | AT91C_SDRAMC_TRAS_2
                                        | AT91C_SDRAMC_TXSR_3);

    for (i = 0; i < 1000; i++);

    WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_NOP_CMD); // Perform NOP
    pSdram[0] = 0x00000000;

    WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_PRCGALL_CMD); // Set PRCHG AL
    pSdram[0] = 0x00000000;                     // Perform PRCHG

    for (i = 0; i < 10000; i++);

    WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_RFSH_CMD);    // Set 1st CBR
    pSdram[1] = 0x00000001;                     // Perform CBR

    WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_RFSH_CMD);    // Set 2 CBR
    pSdram[2] = 0x00000002;                     // Perform CBR

    WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_RFSH_CMD);    // Set 3 CBR
    pSdram[3] = 0x00000003;                    // Perform CBR

    WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_RFSH_CMD);    // Set 4 CBR
    pSdram[4] = 0x00000004;                   // Perform CBR

    WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_RFSH_CMD);    // Set 5 CBR
    pSdram[5] = 0x00000005;                   // Perform CBR

    WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_RFSH_CMD);    // Set 6 CBR
    pSdram[6] = 0x00000006;                 // Perform CBR

    WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_RFSH_CMD);    // Set 7 CBR
    pSdram[7] = 0x00000007;                 // Perform CBR

    WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_RFSH_CMD);    // Set 8 CBR
    pSdram[8] = 0x00000008;                 // Perform CBR

    WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_LMR_CMD);     // Set LMR operation
    pSdram[9] = 0xcafedede;                 // Perform LMR burst=1, lat=2

    WRITE(AT91C_BASE_SDRAMC, SDRAMC_TR, (48000000 * 7) / 1000000);      // Set Refresh Timer

    WRITE(AT91C_BASE_SDRAMC, SDRAMC_MR, AT91C_SDRAMC_MODE_NORMAL_CMD);  // Set Normal mode
    pSdram[0] = 0x00000000;                     // Perform Normal mode
}

//------------------------------------------------------------------------------
/// Configures the EBI for NandFlash access. Pins must be configured after or
/// before calling this function.
//------------------------------------------------------------------------------
void BOARD_ConfigureNandFlash(unsigned char busWidth)
{
    // Configure EBI
    AT91C_BASE_MATRIX->MATRIX_EBI |= AT91C_MATRIX_CS3A_SM;

    // Configure SMC
    AT91C_BASE_SMC->SMC_SETUP3 = 0x00000000;
    AT91C_BASE_SMC->SMC_PULSE3 = 0x00030003;
    AT91C_BASE_SMC->SMC_CYCLE3 = 0x00050005;
    AT91C_BASE_SMC->SMC_CTRL3  = 0x00002003;

    if (busWidth == 8) {

        AT91C_BASE_SMC->SMC_CTRL3 |= AT91C_SMC_DBW_WIDTH_EIGTH_BITS;
    }
    else if (busWidth == 16) {
 
        AT91C_BASE_SMC->SMC_CTRL3 |= AT91C_SMC_DBW_WIDTH_SIXTEEN_BITS;
    }
}

//------------------------------------------------------------------------------
/// Configures the EBI for NandFlash access at 48MHz. Pins must be configured
/// after or before calling this function.
//------------------------------------------------------------------------------
void BOARD_ConfigureNandFlash48MHz(unsigned char busWidth)
{
    // Configure EBI
    AT91C_BASE_CCFG->CCFG_EBICSA |= AT91C_EBI_CS3A_SM;

    // Configure SMC
    AT91C_BASE_SMC->SMC_SETUP3 = 0x00010001;
    AT91C_BASE_SMC->SMC_PULSE3 = 0x04030302;
    AT91C_BASE_SMC->SMC_CYCLE3 = 0x00070004;
    AT91C_BASE_SMC->SMC_CTRL3  = (AT91C_SMC_READMODE
                                 | AT91C_SMC_WRITEMODE
                                 | AT91C_SMC_NWAITM_NWAIT_DISABLE
                                 | ((0x1 << 16) & AT91C_SMC_TDF));
    
    if (busWidth == 8) {

        AT91C_BASE_SMC->SMC_CTRL3 |= AT91C_SMC_DBW_WIDTH_EIGTH_BITS;
    }
    else if (busWidth == 16) {
 
        AT91C_BASE_SMC->SMC_CTRL3 |= AT91C_SMC_DBW_WIDTH_SIXTEEN_BITS;
    }
}

//------------------------------------------------------------------------------
/// Configures the EBI for NorFlash access at 48MHz.
/// \Param busWidth Bus width 
//------------------------------------------------------------------------------
void BOARD_ConfigureNorFlash48MHz(unsigned char busWidth)
{
    // Configure SMC
    AT91C_BASE_SMC->SMC_SETUP0 = 0x00000001;
    AT91C_BASE_SMC->SMC_PULSE0 = 0x07070703;
    AT91C_BASE_SMC->SMC_CYCLE0 = 0x00070007;
    AT91C_BASE_SMC->SMC_CTRL0  = (AT91C_SMC_READMODE
                                  | AT91C_SMC_WRITEMODE
                                  | AT91C_SMC_NWAITM_NWAIT_DISABLE
                                  | ((0x1 << 16) & AT91C_SMC_TDF));
                           
    if (busWidth == 8) {

        AT91C_BASE_SMC->SMC_CTRL0 |= AT91C_SMC_DBW_WIDTH_EIGTH_BITS;
    }
    else if (busWidth == 16) {
 
        AT91C_BASE_SMC->SMC_CTRL0 |= AT91C_SMC_DBW_WIDTH_SIXTEEN_BITS;
    }
    else if (busWidth == 32) {
 
        AT91C_BASE_SMC->SMC_CTRL0 |= AT91C_SMC_DBW_WIDTH_THIRTY_TWO_BITS;
    }
}

//------------------------------------------------------------------------------
/// Set flash wait states in the EFC for 48MHz
//------------------------------------------------------------------------------
void BOARD_ConfigureFlash48MHz(void)
{
    // Set flash wait states
    //----------------------
    AT91C_BASE_EFC->EFC_FMR = 6 << 8;
}
