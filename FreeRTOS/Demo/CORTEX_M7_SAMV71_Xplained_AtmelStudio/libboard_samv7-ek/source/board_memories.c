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

#define SDRAM_BA0 (1 << 20)
#define SDRAM_BA1 (1 << 21)


uint32_t BOARD_SdramValidation(uint32_t baseAddr, uint32_t size)
{
	uint32_t i;
	uint32_t ret = 1;
	uint32_t *ptr32 = (uint32_t *) baseAddr;
	uint16_t *ptr16 = (uint16_t *) baseAddr;
	uint8_t *ptr8 = (uint8_t *) baseAddr;
	/* Test for 55AA55AA/AA55AA55 pattern */
	printf(" Test for 55AA55AA/AA55AA55 pattern ... \n\r");
	for (i = 0; i < size ; i ++) {
		if (i & 1) {
			ptr32[i] = 0x55AA55AA ;
		} else {
			ptr32[i] = 0xAA55AA55 ;
		}
		memory_barrier() 
	}
	for (i = 0; i <  size ; i++) {
		if (i & 1) {
			if (ptr32[i] != 0x55AA55AA ) {
				printf("-E- Expected:%x, read %x @ %x \n\r" ,
					0xAA55AA55, (unsigned)ptr32[i], (unsigned)(baseAddr + i));
				ret = 0;
				
			}
		} else {
			if (ptr32[i] != 0xAA55AA55 ) {
				printf("-E- Expected:%x, read %x @ %x \n\r" ,
						0xAA55AA55 , (unsigned)ptr32[i], (unsigned)(baseAddr + i));
				ret = 0;
			}
		}
	}
	if (!ret) return ret;
	printf(" Test for BYTE accessing... \n\r");
	/* Test for BYTE accessing */
	for (i = 0; i < size ; i ++) {
		ptr8[i] = (uint8_t)( i & 0xFF) ;
	}
	
	for (i = 0; i <  size ; i++) {
		if (ptr8[i] != (uint8_t)(i & 0xFF))  {
			printf("-E- Expected:%x, read %x @ %x \n\r" ,
				(unsigned)(i & 0xFF), ptr8[i],(unsigned)(baseAddr + i));
			ret = 0;
		}
	}
	if (!ret) return ret;
	
	printf(" Test for WORD accessing... \n\r");
	/* Test for WORD accessing */
	for (i = 0; i < size / 2 ; i ++) {
		ptr16[i] = (uint16_t)( i & 0xFFFF) ;
	}
	
	for (i = 0; i <  size / 2 ; i++) {
		if (ptr16[i] != (uint16_t)(i & 0xFFFF))  {
			printf("-E- Expected:%x, read %x @ %x \n\r" ,
				(unsigned)(i & 0xFFFF), ptr16[i],(unsigned)(baseAddr + i));
			ret = 0;
		}
	}
	if (!ret) return ret;
	printf(" Test for DWORD accessing... \n\r");
	/* Test for DWORD accessing */
	for (i = 0; i < size / 4 ; i ++) {
		ptr32[i] = (uint32_t)( i & 0xFFFFFFFF) ;
		memory_barrier() 
	}
	
	for (i = 0; i <  size / 4 ; i++) {
		if (ptr32[i] != (uint32_t)(i & 0xFFFFFFFF))  {
			printf("-E- Expected:%x, read %x @ %x \n\r" ,
				(unsigned)(i & 0xFFFFFFFF), (unsigned)ptr32[i], (unsigned)(baseAddr + i));
			ret = 0;
		}
	}
	return ret;
}


/**
 * \brief Configures the EBI for SDRAM (IS42S16100E-7B) access.
 */


void BOARD_ConfigureSdram( void )
{
	const Pin pinsSdram[] = {BOARD_SDRAM_PINS};
	volatile uint32_t i;
	volatile uint8_t *pSdram = (uint8_t *) SDRAM_CS_ADDR;

	/* Configure PIO */
	PIO_Configure(pinsSdram, PIO_LISTSIZE(pinsSdram));
	PMC_EnablePeripheral(ID_SDRAMC);
	MATRIX->CCFG_SMCNFCS = CCFG_SMCNFCS_SDRAMEN;

	/* 1. SDRAM features must be set in the configuration register: 
	asynchronous timings (TRC, TRAS, etc.), number of columns, rows, 
	CAS latency, and the data bus width. */
	SDRAMC->SDRAMC_CR = 
		  SDRAMC_CR_NC_COL8      // 8 column bits 
		| SDRAMC_CR_NR_ROW11     // 12 row bits (4K)
		| SDRAMC_CR_CAS_LATENCY3 // CAS Latency 3
		| SDRAMC_CR_NB_BANK2     // 2 banks
		| SDRAMC_CR_DBW          // 16 bit
		| SDRAMC_CR_TWR(4)
		| SDRAMC_CR_TRC_TRFC(11) // 63ns   min
		| SDRAMC_CR_TRP(5)       // Command period (PRE to ACT) 21 ns min
		| SDRAMC_CR_TRCD(5)      // Active Command to read/Write Command delay time 21ns min 
		| SDRAMC_CR_TRAS(8)      // Command period (ACT to PRE)  42ns min 
		| SDRAMC_CR_TXSR(13U);   // Exit self-refresh to active time  70ns Min

	/* 2. For mobile SDRAM, temperature-compensated self refresh (TCSR), drive
	strength (DS) and partial array self refresh (PASR) must be set in the
	Low Power Register. */

	/* 3. The SDRAM memory type must be set in the Memory Device Register.*/
	SDRAMC->SDRAMC_MDR = SDRAMC_MDR_MD_SDRAM;

	/* 4. A minimum pause of 200 ¦Ìs is provided to precede any signal toggle.*/
	for (i = 0; i < 100000; i++);

	/* 5. (1)A NOP command is issued to the SDRAM devices. The application must
	set Mode to 1 in the Mode Register and perform a write access to
	any SDRAM address.*/
	SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_NOP;
	*pSdram = 0;
	for (i = 0; i < 100000; i++);
	/* 6. An All Banks Precharge command is issued to the SDRAM devices.
	The application must set Mode to 2 in the Mode Register and perform a write
	access to any SDRAM address. */
	SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_ALLBANKS_PRECHARGE;
	*pSdram = 0;
	for (i = 0; i < 100000; i++);
	/* 7. Eight auto-refresh (CBR) cycles are provided. The application must
	set the Mode to 4 in the Mode Register and perform a write access to any
	SDRAM location eight times.*/
	for (i = 0 ; i< 8; i++) {
		SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_AUTO_REFRESH;
		*pSdram = 0;
	}
	for (i = 0; i < 100000; i++);
	/*8. A Mode Register set (MRS) cycle is issued to program the parameters of
	the SDRAM devices, in particular CAS latency and burst length. The 
	application must set Mode to 3 in the Mode Register and perform a write
	access to the SDRAM. The write address must be chosen so that BA[1:0] 
	are set to 0. For example, with a 16-bit 128 MB SDRAM (12 rows, 9 columns,
	4 banks) bank address, the SDRAM write access should be done at the address
	0x70000000.*/
	SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_LOAD_MODEREG;
	*pSdram = 0;

	for (i = 0; i < 100000; i++);
	/*9. For mobile SDRAM initialization, an Extended Mode Register set (EMRS) 
	cycle is issued to program the SDRAM parameters (TCSR, PASR, DS). The 
	application must set Mode to 5 in the Mode Register and perform a write 
	access to the SDRAM. The write address must be chosen so that BA[1] or BA[0]
	are set to 1.
	For example, with a 16-bit 128 MB SDRAM, (12 rows, 9 columns, 4 banks) bank
	address the SDRAM write access should be done at the address 0x70800000 or 
	0x70400000. */
	//SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_EXT_LOAD_MODEREG;
	// *((uint8_t *)(pSdram + SDRAM_BA0)) = 0;

	/* 10. The application must go into Normal Mode, setting Mode to 0 in the
	Mode Register and performing a write access at any location in the SDRAM. */
	SDRAMC->SDRAMC_MR = SDRAMC_MR_MODE_NORMAL;
	*pSdram = 0;
	for (i = 0; i < 100000; i++);
	/* 11. Write the refresh rate into the count field in the SDRAMC Refresh
	Timer register. (Refresh rate = delay between refresh cycles). 
	The SDRAM device requires a refresh every 15.625 ¦Ìs or 7.81 ¦Ìs.
	With a 100 MHz frequency, the Refresh Timer Counter Register must be set
	with the value 1562(15.625 ¦Ìs x 100 MHz) or 781(7.81 ¦Ìs x 100 MHz). */
	// For IS42S16100E, 2048 refresh cycle every 32ms, every 15.625 ¦Ìs
	/* ((32 x 10(^-3))/2048) x150 x (10^6) */
	SDRAMC->SDRAMC_TR = 2343; ;
	SDRAMC->SDRAMC_CFR1 |= SDRAMC_CFR1_UNAL;
	/* After initialization, the SDRAM devices are fully functional. */
}
