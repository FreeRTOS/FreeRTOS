/***********************************************************************
 * $Id: system_LPC43xx.h 8242 2011-10-11 15:15:25Z nxp28536 $
 *
 * Project: LPC43xx Common
 *
 * Description:
 *     CMSIS Cortex-M4 Device Peripheral Access Layer Header File
 *     for the NXP LPC43xx Device Series
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


#ifndef __SYSTEM_LPC18xx_H
#define __SYSTEM_LPC18xx_H

#include <stdint.h>
#include "scu.h"

#ifdef __cplusplus
 extern "C" {
#endif 

#define BUTTON0	!((LPC_GPIO3->PIN>>6)&1)	// P6.10
#define BUTTON1	!((LPC_GPIO2->PIN>>0)&1)	// P4.0

/*----------------------------------------------------------------------------
  Clock Variable definitions
  DO NOT SET MANUALLY, SET WITH SetClock AND SetPL160M
 *----------------------------------------------------------------------------*/
extern uint32_t XtalFrequency; 				
extern uint32_t PL160M_0Frequency; 
extern uint32_t PL160M_1Frequency; 
extern uint32_t PL160M_2Frequency; 
extern uint32_t PL550Frequency; 
extern uint32_t PL550FracFrequency;  //New in Falcon
extern uint32_t IDIVAFrequency;
extern uint32_t IDIVBFrequency;
extern uint32_t IDIVCFrequency;
extern uint32_t IDIVDFrequency;
extern uint32_t IDIVEFrequency;
extern uint32_t M0Frequency;
extern uint32_t USB1Frequency;
extern uint32_t M4Frequency;
extern uint32_t SPIFIFrequency;
extern uint32_t SPIFrequency;
extern uint32_t EnetRxFrequency;
extern uint32_t EnetTxFrequency;
extern uint32_t EXTFrequency;
extern uint32_t VPB1Frequency;
extern uint32_t VPB3Frequency;
extern uint32_t LCDFrequency;
extern uint32_t SCIFrequency;
extern uint32_t SDIOFrequency;
extern uint32_t SSP0Frequency;
extern uint32_t SSP1Frequency;
extern uint32_t UART0Frequency;
extern uint32_t UART1Frequency;
extern uint32_t UART2Frequency;
extern uint32_t UART3Frequency;
extern uint32_t OUTFrequency;
extern uint32_t AOTESTFrequency;
extern uint32_t ISOFrequency;
extern uint32_t BSRFrequency;
extern uint32_t CLK_TESTFrequency;
extern uint32_t APLLFrequency;
extern uint32_t SPARE0Frequency;
extern uint32_t SPARE1Frequency;


typedef enum CLKDIV
{
	DIV1	= 1,
	DIV2	= 2,
	DIV4	= 4,
	DIV8 	= 8,
	DIV16	= 16,
	DIV256	= 256,
} CLKDIV_Type;

typedef enum CLKSRC
{
	SRC_OSC32K    	= 0,
	SRC_IRC        	= 1,
	SRC_ENET_RX_CLK	= 2,
	SRC_ENET_TX_CLK = 3,
	SRC_EXT_TCK 	= 4,
	RESERVED    	= 5,  // Do NOT use
	SRC_XTAL       	= 6,
	SRC_PL550M_0   	= 7,
	SRC_PL550M_FRAC	= 8, //New in Falcon
	SRC_PL160M_0   	= 9,
	SRC_PL160M_1   	= 10,
	SRC_PL160M_2   	= 11,
	SRC_IDIV_0     	= 12,
	SRC_IDIV_1     	= 13,
	SRC_IDIV_2     	= 14,
	SRC_IDIV_3     	= 15,
	SRC_IDIV_4     	= 16,
	NOT_DEFINED		= 0xFFFFFFF,	// Force a signed int enum, so every possible frequency can be entered
} CLKSRC_Type;

typedef enum CLKBASE
{
	PL550M 			= 0, //PL550Frac is new, should be added???
	PL160M 			= 1,
	IDIVA_4 		= 2,
	IDIVB_16 		= 3,
	IDIVC_16 		= 4,
	IDIVD_16 		= 5,
	IDIVE_256 		= 6,
	BASE_SAFE_CLK 	= 7,
	BASE_USB0_CLK 	= 8,
	BASE_M0_CLK 	= 9,
	BASE_USB1_CLK 	= 10,
	BASE_M4_CLK 	= 11,
	BASE_SPIFI_CLK 	= 12,
	BASE_SPI_CLK 	= 13,
	BASE_PHY_RX_CLK = 14,
	BASE_PHY_TX_CLK = 15,
	BASE_VPB1_CLK 	= 16,
	BASE_VPB3_CLK 	= 17,
	BASE_LCD_CLK 	= 18,
	BASE_VADC_CLK 	= 19,	//New
	BASE_SDIO_CLK 	= 20,
	BASE_SSP0_CLK 	= 21,
	BASE_SSP1_CLK 	= 22,
	BASE_UART0_CLK 	= 23,
	BASE_UART1_CLK 	= 24,
	BASE_UART2_CLK 	= 25,
	BASE_UART3_CLK 	= 26,
	BASE_OUT_CLK 	= 27,
	BASE_AOTEST_CLK = 28,
	BASE_ISO_TCK 	= 29,
	BASE_BSR_TCK 	= 30,
	BASE_CLK_TEST	= 31,
	BASE_APLL_CLK 	= 32, //New in Falcon
	BASE_SPARE0_CLK	= 33, //New in Falcon
	BASE_SPARE1_CLK	= 34, //New in Falcon
	XTAL			= 253,
	ENET_RX			= 254,
	ENET_TX			= 255,
}CLKBASE_Type;	

// PL550M
#define	MODE1A		(0x3<<2)	// Normal operating mode without post-divider and without pre-divider	
#define	MODE1B	   	(0x2<<2)	// Normal operating mode with post-divider and without pre-divider
#define	MODE1C	   	(0x1<<2)	// Normal operating mode without post-divider and with pre-divider
#define	MODE1D	   	(0x0<<2)	// Normal operating mode with post-divider and with pre-divider.
#define BYPASSOFF 	(0<<1)
#define CLKEN		(1<<4)

// PL160M
#define FBSEL 			(1<<6)
#define MSEL_FBDIV(n)	(n<<16)	// MSEL = feedback-divider value	2*M (1 to 2^15)
#define NSEL_PREDIV(n)	(n<<12)	// NSEL = pre-divider value			N	(1 to 2^8)		  	
#define PSEL_POSTDIV(n)	(n<<8)	// PSEL = post-divider value		P*2	(1 to 2^5)

// Generic clock properties
#define AUTO_BLOCK	(1<<11)
#define PD_ENABLE	(1<<0)

extern void SystemInit(void);
extern void SetClock(CLKBASE_Type target_clk, CLKSRC_Type src_clk, CLKDIV_Type div);
extern void SetPL160M(CLKSRC_Type src_clk, uint32_t mult);
extern void SetPLLUSB(CLKSRC_Type src_clk, uint8_t enable);
extern void EnableSourceClk(CLKSRC_Type src_clk);
extern void DisableSourceClk(CLKSRC_Type src_clk);
extern void IOInit(void);
extern uint32_t GetClockFrequency(CLKSRC_Type src_clk);

#ifdef __cplusplus
}
#endif

#endif /* __SYSTEM_LPC43xx_H */
