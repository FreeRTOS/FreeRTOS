/**********************************************************************
* $Id: lpc18xx_emc.c 8765 2011-12-08 00:51:21Z nxp21346 $		lpc18xx_emc.c		2011-12-07
*//**
* @file		lpc18xx_emc.c
* @brief	Contains all functions support for Clock Generation and Control
* 			firmware library on lpc18xx
* @version	1.0
* @date		07. December. 2011
* @author	NXP MCU SW Application Team
*
* Copyright(C) 2011, NXP Semiconductor
* All rights reserved.
*
***********************************************************************
* Software that is described herein is for illustrative purposes only
* which provides customers with programming information regarding the
* products. This software is supplied "AS IS" without any warranties.
* NXP Semiconductors assumes no responsibility or liability for the
* use of the software, conveys no license or title under any patent,
* copyright, or mask work right to the product. NXP Semiconductors
* reserves the right to make changes in the software without
* notification. NXP Semiconductors also make no representation or
* warranty that such application will be suitable for the specified
* use without further testing or modification.
**********************************************************************/

#include "LPC18xx.h"
#include "lpc18xx_emc.h"
#include "lpc18xx_scu.h"

#define M32(x)	*((uint32_t *)x)
#define DELAYCYCLES(ns) (ns / ((1.0 / __EMCHZ) * 1E9))

void emc_WaitUS(volatile uint32_t us)
{
	us *= (SystemCoreClock / 1000000) / 3;
	while(us--);
}

void emc_WaitMS(uint32_t ms)
{
	emc_WaitUS(ms * 1000);
}

void MemoryPinInit(void)
{
  /* select correct functions on the GPIOs */

#if 1
  /* DATA LINES 0..31 > D0..D31 */
  	/* P1_7 - EXTBUS_D0 — External memory data line 0 */
    scu_pinmux(0x1,  7,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* P1_7: D0 (function 0) errata */
    scu_pinmux(0x1,  8,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* P1_8: D1 (function 0) errata */
    scu_pinmux(0x1,  9,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* P1_9: D2 (function 0) errata */
    scu_pinmux(0x1,  10, (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* P1_10: D3 (function 0) errata */
    scu_pinmux(0x1,  11, (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* P1_11: D4 (function 0) errata */
    scu_pinmux(0x1,  12, (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* P1_12: D5 (function 0) errata */
    scu_pinmux(0x1,  13, (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* P1_13: D6 (function 0) errata */
    scu_pinmux(0x1,  14, (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* P1_14: D7 (function 0) errata */
    scu_pinmux(0x5,  4,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);  /* P5_4: D8 (function 0) errata */
    scu_pinmux(0x5,  5,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);  /* P5_5: D9 (function 0) errata */
    scu_pinmux(0x5,  6,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);  /* P5_6: D10 (function 0) errata */
    scu_pinmux(0x5,  7,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);  /* P5_7: D11 (function 0) errata */
    scu_pinmux(0x5,  0,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);  /* P5_0: D12 (function 0) errata */
    scu_pinmux(0x5,  1,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);  /* P5_1: D13 (function 0) errata */
    scu_pinmux(0x5,  2,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);  /* P5_2: D14 (function 0) errata */
    scu_pinmux(0x5,  3,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);  /* P5_3: D15 (function 0) errata */
#if 0
    scu_pinmux(0xD,  2,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);  /* PD_2: D16 (function 0) errata */
    scu_pinmux(0xD,  3,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);  /* PD_3: D17 (function 0) errata */
    scu_pinmux(0xD,  4,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);  /* PD_4: D18 (function 0) errata */
    scu_pinmux(0xD,  5,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);  /* PD_5: D19 (function 0) errata */
    scu_pinmux(0xD,  6,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);  /* PD_6: D20 (function 0) errata */
    scu_pinmux(0xD,  7,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);  /* PD_7: D21 (function 0) errata */
    scu_pinmux(0xD,  8,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);  /* PD_8: D22 (function 0) errata */
    scu_pinmux(0xD,  9,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);  /* PD_9: D23 (function 0) errata */
    scu_pinmux(0xE,  5,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* PE_5: D24 (function 0) errata */
    scu_pinmux(0xE,  6,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* PE_6: D25 (function 0) errata */
    scu_pinmux(0xE,  7,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* PE_7: D26 (function 0) errata */
    scu_pinmux(0xE,  8,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* PE_8: D27 (function 0) errata */
    scu_pinmux(0xE,  9,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* PE_9: D28 (function 0) errata */
    scu_pinmux(0xE, 10,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* PE_10: D29 (function 0) errata */
    scu_pinmux(0xE, 11,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* PE_11: D30 (function 0) errata */
    scu_pinmux(0xE, 12,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* PE_12: D31 (function 0) errata */
#endif
  
  /* ADDRESS LINES A0..A11 > A0..A11 */
	scu_pinmux(0x2,  9,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);	/* P2_9 - EXTBUS_A0 — External memory address line 0 */
	scu_pinmux(0x2, 10,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);	/* P2_10 - EXTBUS_A1 — External memory address line 1 */	
	scu_pinmux(0x2, 11,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);	/* P2_11 - EXTBUS_A2 — External memory address line 2 */	
	scu_pinmux(0x2, 12,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);	/* P2_12 - EXTBUS_A3 — External memory address line 3 */
	scu_pinmux(0x2, 13,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);	/* P2_13 - EXTBUS_A4 — External memory address line 4 */	
	scu_pinmux(0x1,  0,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);	/* P1_0 - EXTBUS_A5 — External memory address line 5 */
	scu_pinmux(0x1,  1,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);	/* P1_1 - EXTBUS_A6 — External memory address line 6 */	
	scu_pinmux(0x1,  2,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);	/* P1_2 - EXTBUS_A7 — External memory address line 7 */	
	scu_pinmux(0x2,  8,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);	/* P2_8 - EXTBUS_A8 — External memory address line 8 */
	scu_pinmux(0x2,  7,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);	/* P2_7 - EXTBUS_A9 — External memory address line 9 */	
	scu_pinmux(0x2,  6,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);	/* P2_6 - EXTBUS_A10 — External memory address line 10 */
	scu_pinmux(0x2,  2,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);	/* P2_2 - EXTBUS_A11 — External memory address line 11 */
	scu_pinmux(0x2,  1,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);	/* P2_1 - EXTBUS_A12 — External memory address line 12 */
	scu_pinmux(0x2,  0,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);	/* P2_0 - EXTBUS_A13 — External memory address line 13 */	
	scu_pinmux(0x6,  8,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC1);	/* P6_8 - EXTBUS_A14 — External memory address line 14 */
	scu_pinmux(0x6,  7,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC1);	/* P6_7 - EXTBUS_A15 — External memory address line 15 */	
	scu_pinmux(0xD, 16,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);	/* PD_16 - EXTBUS_A16 — External memory address line 16 */
	scu_pinmux(0xD, 15,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);	/* PD_15 - EXTBUS_A17 — External memory address line 17 */	
	scu_pinmux(0xE,  0,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);	/* PE_0 - EXTBUS_A18 — External memory address line 18 */
	scu_pinmux(0xE,  1,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);	/* PE_1 - EXTBUS_A19 — External memory address line 19 */
	scu_pinmux(0xE,  2,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);	/* PE_2 - EXTBUS_A20 — External memory address line 20 */
	scu_pinmux(0xE,  3,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);	/* PE_3 - EXTBUS_A21 — External memory address line 21 */
	scu_pinmux(0xE,  4,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);	/* PE_4 - EXTBUS_A22 — External memory address line 22 */	
	scu_pinmux(0xA,  4,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);	/* PA_4 - EXTBUS_A23 — External memory address line 23 */

  /* BYTE ENABLES */
	scu_pinmux(0x1,  4,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);	/* P1_4 - EXTBUS_BLS0 — LOW active Byte Lane select signal 0 */
	scu_pinmux(0x6,  6,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC1);	/* P6_6 - EXTBUS_BLS1 — LOW active Byte Lane select signal 1 */	
	scu_pinmux(0xD, 13,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);	/* PD_13 - EXTBUS_BLS2 — LOW active Byte Lane select signal 2 */
	scu_pinmux(0xD, 10,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);	/* PD_10 - EXTBUS_BLS3 — LOW active Byte Lane select signal 3 */		
    
    scu_pinmux(0x6,  9,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* P6_9: EXTBUS_DYCS0  (function 0) > CS# errata */
    scu_pinmux(0x1,  6,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* P1_6: WE (function 0) errata */
    scu_pinmux(0x6,  4,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* P6_4: CAS  (function 0) > CAS# errata */
    scu_pinmux(0x6,  5,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* P6_5: RAS  (function 0) > RAS# errata */

	LPC_SCU_CLK(0) = 0 + (MD_PLN | MD_EZI | MD_ZI | MD_EHS); /* SFSCLK0: EXTBUS_CLK0  (function 0, from datasheet) > CLK ds */
    LPC_SCU_CLK(1) = 0 + (MD_PLN | MD_EZI | MD_ZI | MD_EHS); /* SFSCLK1: EXTBUS_CLK1  (function 2, from datasheet) */
    LPC_SCU_CLK(2) = 0 + (MD_PLN | MD_EZI | MD_ZI | MD_EHS); /* SFSCLK2: EXTBUS_CLK2  (function 2, from datasheet) */
    LPC_SCU_CLK(3) = 0 + (MD_PLN | MD_EZI | MD_ZI | MD_EHS); /* SFSCLK3: EXTBUS_CLK3  (function 2, from datasheet) */

    scu_pinmux(0x6, 11,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* P6_11: CKEOUT0  (function 0) > CKE errata */
    scu_pinmux(0x6, 12,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* P6_12: DQMOUT0  (function 0) > DQM0 errata */
    scu_pinmux(0x6, 10,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* P6_10: DQMOUT1  (function 0) > DQM1 errata */
    scu_pinmux(0xD,  0,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC2);  /* PD_0: DQMOUT2  (function 2, from datasheet) > DQM2 errata */
    scu_pinmux(0xE, 13,  (MD_PLN | MD_EZI | MD_ZI | MD_EHS), FUNC3);  /* PE_13: DQMOUT3  (function 3, from datasheet) > DQM3 errata */

	scu_pinmux(	1	,	3	,	MD_PLN_FAST	,	3	);	//OE
	scu_pinmux(	1	,	4	,	MD_PLN_FAST	,	3	);	//BLS0
	scu_pinmux(	1	,	5	,	MD_PLN_FAST	,	3	);	//CS0
	scu_pinmux(	1	,	6	,	MD_PLN_FAST	,	3	);	//WE

#endif
}

void EMCFlashInit(void)
{
	// Hitex board SST39VF3201B Flash
	// Read Cycle Time 70 nS minimum
	// Chip Enable Access Time 70 ns maximum
	// Address Access Time 70 ns max
	// Toe 35 ns max
	// CE/OE high to inactive output 16 ns

	/* Set up EMC Controller */
	LPC_EMC->STATICWAITRD0 = DELAYCYCLES(70)+1;

	LPC_EMC->STATICWAITPAG0 = DELAYCYCLES(70)+1;


	LPC_EMC->CONTROL = 0x01;
	LPC_EMC->STATICCONFIG0 = (1UL<<7) | (1UL);
	LPC_EMC->STATICWAITOEN0 = DELAYCYCLES(35)+1;

    /*Enable Buffer for External Flash*/
    LPC_EMC->STATICCONFIG0 |= 1<<19;
}

/* SDRAM refresh time to 16 clock num */
#define EMC_SDRAM_REFRESH(freq,time)  \
  (((uint64_t)((uint64_t)time * freq)/16000000000ull)+1)

void vEMC_InitSRDRAM(uint32_t u32BaseAddr, uint32_t u32Width, uint32_t u32Size, uint32_t u32DataBus, uint32_t u32ColAddrBits)
{
   // adjust the CCU delaye for EMI (default to zero)
    //LPC_SCU->EMCCLKDELAY = (CLK0_DELAY | (CLKE0_DELAY << 16));
	// Move all clock delays together
	LPC_SCU->EMCDELAYCLK = ((CLK0_DELAY) 
						 |  (CLK0_DELAY << 4)
						 |  (CLK0_DELAY << 8)
						 |  (CLK0_DELAY << 12));

   /* Initialize EMC to interface with SDRAM */
	LPC_EMC->CONTROL 			= 0x00000001;   /* Enable the external memory controller */	
	LPC_EMC->CONFIG 			= 0;

	LPC_EMC->DYNAMICCONFIG0 	= ((u32Width << 7) | (u32Size << 9) | (1UL << 12) | (u32DataBus << 14));
	LPC_EMC->DYNAMICCONFIG2 	= ((u32Width << 7) | (u32Size << 9) | (1UL << 12) | (u32DataBus << 14));

    LPC_EMC->DYNAMICRASCAS0 	= (3 << 0) | (3 << 8);      // aem
    LPC_EMC->DYNAMICRASCAS2 	= (3 << 0) | (3 << 8);  // aem
	
	LPC_EMC->DYNAMICREADCONFIG	= EMC_COMMAND_DELAYED_STRATEGY;
	
	LPC_EMC->DYNAMICRP 			= 1;    // calculated from xls sheet
	LPC_EMC->DYNAMICRAS 		= 3;
	LPC_EMC->DYNAMICSREX 		= 5;   
	LPC_EMC->DYNAMICAPR 		= 0;
	LPC_EMC->DYNAMICDAL 		= 4;
	LPC_EMC->DYNAMICWR 			= 1;
	LPC_EMC->DYNAMICRC 			= 5;   
	LPC_EMC->DYNAMICRFC 		= 5;   
	LPC_EMC->DYNAMICXSR 		= 5;   
	LPC_EMC->DYNAMICRRD 		= 1;
	LPC_EMC->DYNAMICMRD 		= 1;
	
	LPC_EMC->DYNAMICCONTROL 	= EMC_CE_ENABLE | EMC_CS_ENABLE | EMC_INIT(EMC_NOP);
	emc_WaitUS(100);
	
	LPC_EMC->DYNAMICCONTROL 	= EMC_CE_ENABLE | EMC_CS_ENABLE | EMC_INIT(EMC_PRECHARGE_ALL);

	LPC_EMC->DYNAMICREFRESH 	= 2;
	emc_WaitUS(100);
	
    LPC_EMC->DYNAMICREFRESH 	= 50;
	
	LPC_EMC->DYNAMICCONTROL 	= EMC_CE_ENABLE | EMC_CS_ENABLE | EMC_INIT(EMC_MODE);

	if(u32DataBus == 0) 
	{
		/* burst size 8 */
        *((volatile uint32_t *)(u32BaseAddr | ((3 | (3 << 4)) << (u32ColAddrBits + 1))));
	}
	else 
	{
		/* burst size 4 */
		*((volatile uint32_t *)(u32BaseAddr | ((2UL | (2UL << 4)) << (u32ColAddrBits + 2))));
	}

	LPC_EMC->DYNAMICCONTROL 	= 0; // EMC_CE_ENABLE | EMC_CS_ENABLE;
	LPC_EMC->DYNAMICCONFIG0 	= ((u32Width << 7) | (u32Size << 9) | (1UL << 12) | (u32DataBus << 14)) | EMC_B_ENABLE;
	LPC_EMC->DYNAMICCONFIG1 	= ((u32Width << 7) | (u32Size << 9) | (1UL << 12) | (u32DataBus << 14)) | EMC_B_ENABLE;
	LPC_EMC->DYNAMICCONFIG2 	= ((u32Width << 7) | (u32Size << 9) | (1UL << 12) | (u32DataBus << 14)) | EMC_B_ENABLE;
	LPC_EMC->DYNAMICCONFIG3 	= ((u32Width << 7) | (u32Size << 9) | (1UL << 12) | (u32DataBus << 14)) | EMC_B_ENABLE;
}

