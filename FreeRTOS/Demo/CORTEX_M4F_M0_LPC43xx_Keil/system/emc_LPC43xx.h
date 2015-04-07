//BF: take over the whole file

/***********************************************************************
 * $Id: emc_LPC43xx.h 8389 2011-10-19 13:53:14Z nxp28536 $   emc_LPC18xx_43xx.h
 *
 * Project: NXP LPC18xx/LPC43xx Common
 *
 * Description:  Header file for emc_LPC18xx_43xx.c
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

#ifndef EMC_LPC43XX_H_
#define EMC_LPC43XX_H_


enum {
	PART_WIDTH_8 = 0,
	PART_WIDTH_16 = 1,
	PART_WIDTH_32 = 2
};

enum {
	PART_SIZE_16 = 0,
	PART_SIZE_64 = 1,
	PART_SIZE_128 = 2,
	PART_SIZE_256 = 3,
	PART_SIZE_512 = 4
};

enum {
	EXT_WIDTH_16 = 0,
	EXT_WIDTH_32 = 1
};


#if (PLATFORM == HITEX_A2_BOARD) //defined USE_HITEX_A2

	#define SDRAM_SIZE               0x00800000 	// 8 MByte SDRAM IS42S16400D-7TL
	#define SDRAM_BASE               0x28000000		// base address for DYCS0

	// We have 16 data lines connected to the SDRAM
	#define PART_WIDTH (PART_WIDTH_16)		// part width (possibly smaller than EXT_WIDTH, e.g. two 8-bit chips cascaded as 16-bit memory.
	#define PART_SIZE (PART_SIZE_64)
	#define EXT_WIDTH (EXT_WIDTH_16) 		// external memory bus width
	#define COL_ADDR_BITS (8) 				// for calculating how to write mode bits

#endif

#if (PLATFORM == NXP_VALIDATION_BOARD)

	#define SDRAM_SIZE               0x01000000 	// 16 MByte SDRAM MT48LC4M32
	#define SDRAM_BASE               0x28000000		// base address for DYCS0

	// We have 32 data lines connected to the SDRAM
	#define PART_WIDTH (PART_WIDTH_32)		// part width (possibly smaller than EXT_WIDTH, e.g. two 8-bit chips cascaded as 16-bit memory.
	#define PART_SIZE (PART_SIZE_128)
	#define EXT_WIDTH (EXT_WIDTH_32) 		// external memory bus width
	#define COL_ADDR_BITS (8) 				// for calculating how to write mode bits

#endif



// Function prototypes
void EMC_Init( void );
void EMC_Config_Pinmux( void );
void EMC_Config_Static( void );
void initEmiDelays( void );
void EMC_Init_SRDRAM( uint32_t u32BaseAddr, uint32_t u32Width, uint32_t u32Size, uint32_t u32DataBus, uint32_t u32ColAddrBits );


#endif	 /* EMC_LPC43XX_H_ */



