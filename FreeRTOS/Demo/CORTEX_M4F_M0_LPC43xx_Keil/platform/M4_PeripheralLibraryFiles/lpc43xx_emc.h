/**********************************************************************
* $Id: lpc43xx_emc.h 8765 2011-12-08 00:51:21Z nxp21346 $		lpc43xx_emc.h		2011-12-07
*//**
* @file		lpc43xx_emc.h
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

#define __CRYSTAL        (12000000UL)    /* Crystal Oscillator frequency          */
#define __PLLMULT		 (15)
#define __PLLOUTHZ		 (__CRYSTAL * __PLLMULT)
#define __EMCDIV		 (2)
#define __EMCHZ			 (__PLLOUTHZ / __EMCDIV)

void MemoryPinInit(void);
void EMCFlashInit(void);

/* SDRAM Address Base for DYCS0*/
#define SDRAM_BASE_ADDR 0x28000000
#define FLASH_BASE_ADDR 0x1C000000

#define EMC_SDRAM_WIDTH_8_BITS		0
#define EMC_SDRAM_WIDTH_16_BITS		1
#define EMC_SDRAM_WIDTH_32_BITS		2

#define EMC_SDRAM_SIZE_16_MBITS		0
#define EMC_SDRAM_SIZE_64_MBITS		1
#define EMC_SDRAM_SIZE_128_MBITS	2
#define EMC_SDRAM_SIZE_256_MBITS	3
#define EMC_SDRAM_SIZE_512_MBITS	4

#define EMC_SDRAM_DATA_BUS_16_BITS	0
#define EMC_SDRAM_DATA_BUS_32_BITS	1

#define EMC_B_ENABLE 					(1 << 19)
#define EMC_ENABLE 						(1 << 0)
#define EMC_CE_ENABLE 					(1 << 0)
#define EMC_CS_ENABLE 					(1 << 1)
#define EMC_CLOCK_DELAYED_STRATEGY 		(0 << 0)
#define EMC_COMMAND_DELAYED_STRATEGY 	(1 << 0)
#define EMC_COMMAND_DELAYED_STRATEGY2 	(2 << 0)
#define EMC_COMMAND_DELAYED_STRATEGY3 	(3 << 0)
#define EMC_INIT(i) 					((i) << 7)
#define EMC_NORMAL 						(0)
#define EMC_MODE 						(1)
#define EMC_PRECHARGE_ALL 				(2)
#define EMC_NOP 						(3)

/* The Hitex LPC18xx Evaluation board contains a 64Mb SDRAM with a 16-bit data bus */
#define SDRAM_SIZE_BYTES		(1024UL * 1024UL * 8UL)
#define SDRAM_WIDTH				EMC_SDRAM_WIDTH_16_BITS
#define SDRAM_SIZE_MBITS		EMC_SDRAM_SIZE_64_MBITS
#define SDRAM_DATA_BUS_BITS		EMC_SDRAM_DATA_BUS_16_BITS			
#define SDRAM_COL_ADDR_BITS		8		
#define CLK0_DELAY     0

void vEMC_InitSRDRAM(uint32_t u32BaseAddr, uint32_t u32Width, uint32_t u32Size, uint32_t u32DataBus, uint32_t u32ColAddrBits);
void emc_WaitUS(volatile uint32_t us);
void emc_WaitMS(uint32_t ms);


