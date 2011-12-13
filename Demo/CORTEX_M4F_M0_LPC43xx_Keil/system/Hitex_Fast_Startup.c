/**********************************************************************
* $Id: Hitex_Fast_Startup.c 8763 2011-12-08 00:45:50Z nxp21346 $		lpc43xx_emc.c		2011-12-07
*//**
* @file		lpc43xx_emc.c
* @brief	Contains all functions support for Clock Generation and Control
* 			firmware library on lpc43xx
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

#include "LPC43xx.h"
#include "lpc43xx_cgu.h"
#include "lpc43xx_emc.h"
#include "spifi_rom_api.h"

void WaitMinUS( volatile uint32_t us, uint32_t SystemClock )
{
	us *= (SystemClock / 1000000UL) / 3;
	while(us--);
}

void WaitMinMS( uint32_t ms, uint32_t SystemClock )
{
	WaitMinUS( ( ms * 1000 ), SystemClock );
}

/* hardware-control routine used by spifi_rom_api.c */
void pullMISO(int high) {
    /* undocumented bit 7 included as 1, Aug 2 2011 */
	LPC_SCU->SFSP3_6 = high == 0 ? 0xDB	 /* pull down */
					 : high == 1 ? 0xC3  /* pull up */
					             : 0xD3; /* neither */
}

void Hitex_CGU_Init(void)
{

	__disable_irq();
	MemoryPinInit(); // Make sure EMC is in high-speed pin mode

 	/* Set the XTAL oscillator frequency to 12MHz*/
	CGU_SetXTALOSC(__CRYSTAL);
	CGU_EnableEntity(CGU_CLKSRC_XTAL_OSC, ENABLE);
	CGU_EntityConnect(CGU_CLKSRC_XTAL_OSC, CGU_BASE_M3);
	
	/* Set PL160M 12*1 = 12 MHz */
	CGU_EntityConnect(CGU_CLKSRC_XTAL_OSC, CGU_CLKSRC_PLL1);
	CGU_SetPLL1(1);
	CGU_EnableEntity(CGU_CLKSRC_PLL1, ENABLE);

	/* Run SPIFI from PL160M, /2 */
	CGU_EntityConnect(CGU_CLKSRC_PLL1, CGU_CLKSRC_IDIVA);
	CGU_EnableEntity(CGU_CLKSRC_IDIVA, ENABLE);
	CGU_SetDIV(CGU_CLKSRC_IDIVA, 2);
	CGU_EntityConnect(CGU_CLKSRC_IDIVA, CGU_BASE_SPIFI);
	CGU_UpdateClock();

	LPC_CCU1->CLK_M4_EMCDIV_CFG |=    (1<<0) |  (1<<5);		// Turn on clock / 2
	LPC_CREG->CREG6 |= (1<<16);	// EMC divided by 2
    LPC_CCU1->CLK_M4_EMC_CFG |= (1<<0);		// Turn on clock

	/* Set PL160M @ 12*9=108 MHz */
	CGU_SetPLL1(9);

	/* Run base M3 clock from PL160M, no division */
	CGU_EntityConnect(CGU_CLKSRC_PLL1, CGU_BASE_M3);

	WaitMinMS(10, 108000000UL);

	/* Change the clock to 204 MHz */
	/* Set PL160M @ 12*15=180 MHz */
	CGU_SetPLL1(17);

	WaitMinMS(10, 180000000UL);

	CGU_UpdateClock();

	EMCFlashInit();

	vEMC_InitSRDRAM(SDRAM_BASE_ADDR, SDRAM_WIDTH, SDRAM_SIZE_MBITS, SDRAM_DATA_BUS_BITS, SDRAM_COL_ADDR_BITS);
	LPC_SCU->SFSP3_3 = 0xF3; /* high drive for SCLK */
	/* IO pins */
	LPC_SCU->SFSP3_4=LPC_SCU->SFSP3_5=LPC_SCU->SFSP3_6=LPC_SCU->SFSP3_7 = 0xD3;
	LPC_SCU->SFSP3_8 = 0x13; /* CS doesn't need feedback */

	__enable_irq();
}
