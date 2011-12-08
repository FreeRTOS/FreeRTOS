/***********************************************************************
 * $Id: system_LPC43xx.c 8389 2011-10-19 13:53:14Z nxp28536 $
 *
 * Project: LPC43xx Common
 *
 * Description:
 *     CMSIS Cortex-M4 Device Peripheral Access Layer Source File
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

#include <stdint.h>
#if defined CORE_M4
#include "LPC43xx.h"                    /* LPC18xx definitions                */
#endif

#ifdef CORE_M0
#include "LPC43xx_M0.h"                /* LPC18xx definitions                */
#endif

#include "scu.h"
#include "type.h"
#include "config.h"


/*--------------------- Clock Configuration ----------------------------------*/
//#define OTP
#define FLASH_SETUP         0
#define FLASHCFG_Val        0x0000303A

/*----------------------------------------------------------------------------
  Check the register settings
 *----------------------------------------------------------------------------*/
#define CHECK_RANGE(val, min, max)                ((val < min) || (val > max))
#define CHECK_RSVD(val, mask)                     (val & mask)

/* Clock Configuration -------------------------------------------------------*/
#if (CHECK_RSVD((SCS_Val),       ~0x00000030))
   #error "SCS: Invalid values of reserved bits!"
#endif

#if (CHECK_RANGE((CLKSRCSEL_Val), 0, 2))
   #error "CLKSRCSEL: Value out of range!"
#endif

#if (CHECK_RSVD((PLL0CFG_Val),   ~0x00FF7FFF))
   #error "PLL0CFG: Invalid values of reserved bits!"
#endif

#if (CHECK_RSVD((PLL1CFG_Val),   ~0x0000007F))
   #error "PLL1CFG: Invalid values of reserved bits!"
#endif

#if ((CCLKCFG_Val != 0) && (((CCLKCFG_Val - 1) % 2)))
   #error "CCLKCFG: CCLKSEL field does not contain only odd values or 0!"
#endif

#if (CHECK_RSVD((USBCLKCFG_Val), ~0x0000000F))
   #error "USBCLKCFG: Invalid values of reserved bits!"
#endif

#if (CHECK_RSVD((PCLKSEL0_Val),   0x000C0C00))
   #error "PCLKSEL0: Invalid values of reserved bits!"
#endif

#if (CHECK_RSVD((PCLKSEL1_Val),   0x03000300))
   #error "PCLKSEL1: Invalid values of reserved bits!"
#endif

#if (CHECK_RSVD((PCONP_Val),      0x10100821))
   #error "PCONP: Invalid values of reserved bits!"
#endif

#if (CHECK_RSVD((CLKOUTCFG_Val), ~0x000001FF))
   #error "CLKOUTCFG: Invalid values of reserved bits!"
#endif

/* Flash Accelerator Configuration -------------------------------------------*/
#if (CHECK_RSVD((FLASHCFG_Val), ~0x0000F07F))
   #error "FLASHCFG: Invalid values of reserved bits!"
#endif


/*----------------------------------------------------------------------------
  DEFINES
 *----------------------------------------------------------------------------*/
uint32_t XtalFrequency = 0; 				
uint32_t PL160M_0Frequency = 0; 
uint32_t PL160M_1Frequency = 0; 
uint32_t PL160M_2Frequency = 0; 
uint32_t PL550Frequency = 0; 
uint32_t PL550FracFrequency = 0; //New in Falcon
uint32_t IDIVAFrequency = 0;
uint32_t IDIVBFrequency = 0;
uint32_t IDIVCFrequency = 0;
uint32_t IDIVDFrequency = 0;
uint32_t IDIVEFrequency = 0;
uint32_t USB1Frequency = 0;
uint32_t M4Frequency = 0;
uint32_t SPIFIFrequency = 0;
uint32_t SPIFrequency = 0;
uint32_t EnetRxFrequency = 0;
uint32_t EnetTxFrequency = 0;
uint32_t EXTFrequency = 0;
uint32_t VPB1Frequency = 0;
uint32_t VPB3Frequency = 0;
uint32_t LCDFrequency = 0;
uint32_t SCIFrequency = 0;
uint32_t VADCFrequency = 0;	
uint32_t SDIOFrequency = 0;
uint32_t SSP0Frequency = 0;
uint32_t SSP1Frequency = 0;
uint32_t UART0Frequency = 0;
uint32_t UART1Frequency = 0;
uint32_t UART2Frequency = 0;
uint32_t UART3Frequency = 0;
uint32_t OUTFrequency = 0;
uint32_t AOTESTFrequency = 0;
uint32_t ISOFrequency = 0;
uint32_t BSRFrequency = 0;
uint32_t CLK_TESTFrequency = 0;
uint32_t APLLFrequency = 0;   
uint32_t SPARE0Frequency = 0; 
uint32_t SPARE1Frequency = 0; 

/**
 * Initialize the system
 *
 * @param  none
 * @return none
 *
 * @brief  Setup the microcontroller system.
 *         
 */
void SystemInit(void)
{
#ifdef OTP   	
	// Set IRC trim if OTP is not programmed.
	if( *(uint32_t *)LPC_OTP_CTRL_BASE == 0x00FF || 
		*(uint32_t *)(LPC_OTP_CTRL_BASE+4) == 0x0000)
	{
		LPC_CREG->IRCTRM = IRC_TRIM_VAL;
	}
#else
	LPC_CREG->IRCTRM = IRC_TRIM_VAL;
#endif

	// Set all GPIO as input.
	LPC_GPIO0->DIR = 0x0000;
	LPC_GPIO1->DIR = 0x0000;
	LPC_GPIO2->DIR = 0x0000;
	LPC_GPIO3->DIR = 0x0000;
	LPC_GPIO4->DIR = 0x0000;
	LPC_GPIO5->DIR = 0x0000;
	LPC_GPIO6->DIR = 0x0000;
	LPC_GPIO7->DIR = 0x0000;

	// M4 runs on IRC by default
	M4Frequency = IRC_OSC; 
	XtalFrequency = XTAL_FREQ;
	EXTFrequency = EXT_FREQ;
}

/**
 * Set Clock
 *
 * @param  target PLL, source clock, division
 * @return none
 *
 * @brief  Setup a clock 
 */
void SetClock(CLKBASE_Type target_clk, CLKSRC_Type src_clk, CLKDIV_Type div)
{
	volatile uint32_t target_clk_adr;
	volatile uint8_t auto_block=TRUE;
	uint32_t src_freq;

	EnableSourceClk(src_clk);

	switch(div)
	{
		case(DIV1):						// Divide by 1 == no division
			break;
		case(DIV2):	
			LPC_CGU->IDIVA_CTRL = (src_clk<<24) | (1<<2) | AUTO_BLOCK;	
			IDIVAFrequency = GetClockFrequency(src_clk)/2;
			src_clk = SRC_IDIV_0; 		// Set new src_clk for target_clk
			break;
		case(DIV4):	
			LPC_CGU->IDIVB_CTRL = (src_clk<<24) | (3<<2) |AUTO_BLOCK;		
			IDIVBFrequency = GetClockFrequency(src_clk)/4;
			src_clk = SRC_IDIV_1; 		// Set new src_clk for target_clk
			break;
		case(DIV8):	
			LPC_CGU->IDIVC_CTRL = (src_clk<<24) | (7<<2) |AUTO_BLOCK;		
			IDIVCFrequency = GetClockFrequency(src_clk)/8;
			src_clk = SRC_IDIV_2; 		// Set new src_clk for target_clk
			break;
		case(DIV16):	
			LPC_CGU->IDIVD_CTRL = (src_clk<<24) | (15<<2) |AUTO_BLOCK;		
			IDIVDFrequency = GetClockFrequency(src_clk)/16;
			src_clk = SRC_IDIV_3; 		// Set new src_clk for target_clk
			break;
		case(DIV256):
			LPC_CGU->IDIVE_CTRL = (src_clk<<24) | (255<<2) |AUTO_BLOCK;	// MAX 128? IDIV bit 2:9 = 7 bits = 127 max
			IDIVEFrequency = GetClockFrequency(src_clk)/256;
			src_clk = SRC_IDIV_4; 		// Set new src_clk for target_clk
			break;
		default:
			break;
	}

	src_freq = GetClockFrequency(src_clk);

	switch(target_clk)
	{
		case(BASE_OUT_CLK):
		{
			LPC_SCU->SFSCLK_0 = 1; 					// function 1; CGU clk out, diable pull down, disable pull-up
			auto_block = FALSE;
			break;
		}
		case(XTAL):
		{
			XtalFrequency = (uint32_t) src_clk;	  	// convert target clock directly to frequency
			break;
		}
		case(ENET_RX):
		{
			EnetRxFrequency = (uint32_t) src_clk;	// convert target clock directly to frequency
			break;
		}
		case(ENET_TX):
		{
			EnetTxFrequency = (uint32_t) src_clk;	// convert target clock directly to frequency
			break;
		}
		case(BASE_USB1_CLK):
		{
			USB1Frequency = src_freq;
			break;
		}
		case(BASE_M4_CLK):
		{
			M4Frequency = src_freq;
			break;
		}
		case(BASE_SPIFI_CLK):
		{
			SPIFIFrequency = src_freq;
			break;
		}
		case(BASE_SPI_CLK):
		{
			SPIFrequency = src_freq;
			break;
		}
		case(BASE_PHY_RX_CLK):
		{
			EnetRxFrequency = src_freq;
			break;
		}
		case(BASE_PHY_TX_CLK):
		{
			EnetTxFrequency = src_freq;
			break;
		}
		case(BASE_VPB1_CLK):
		{
			VPB1Frequency = src_freq;
			break;
		}
		case(BASE_VPB3_CLK):
		{
			VPB3Frequency = src_freq;
			break;
		}
		case(BASE_LCD_CLK):
		{
			LCDFrequency = src_freq;
			break;
		}
		case (BASE_VADC_CLK) :
		{
			VADCFrequency = src_freq;
			break;
		}
		case(BASE_SDIO_CLK):
		{
			SDIOFrequency = src_freq;
			break;
		}
		case(BASE_SSP0_CLK):
		{
			SSP0Frequency = src_freq;
			break;
		}
		case(BASE_SSP1_CLK):
		{
			SSP1Frequency = src_freq;
			break;
		}
		case(BASE_UART0_CLK):
		{
			UART0Frequency = src_freq;
			break;
		}
		case(BASE_UART1_CLK):
		{
			UART1Frequency = src_freq;
			break;
		}
		case(BASE_UART2_CLK):
		{
			UART2Frequency = src_freq;
			break;
		}
		case(BASE_UART3_CLK):
		{
			UART3Frequency = src_freq;
			break;
		}
		case(BASE_AOTEST_CLK):
		{
			AOTESTFrequency = src_freq;
			break;
		}
		case(BASE_ISO_TCK):
		{
			ISOFrequency = src_freq;
			break;
		}
		case(BASE_BSR_TCK):
		{
			BSRFrequency = src_freq;
			break;
		}
		case(BASE_CLK_TEST):
		{
			CLK_TESTFrequency = src_freq;
			break;
		}
		case(BASE_APLL_CLK): //New in Falcon
		{
			APLLFrequency = src_freq;
			break;
		}
		case(BASE_SPARE0_CLK): //New in Falcon
		{
			SPARE0Frequency = src_freq;
			break;
		}
		case(BASE_SPARE1_CLK): //New in Falcon
		{
			SPARE1Frequency = src_freq;
			break;
		}
		default:
			break;
	}

	if(target_clk<200)
	{
		target_clk_adr = (uint32_t) &LPC_CGU->IDIVA_CTRL + (target_clk-2)*4;	
		*(uint32_t *)target_clk_adr = (src_clk<<24) | (auto_block<<11);	
	}
}

/**
 * Get Clock Frequency
 *
 * @param  source clock
 * @return frequency
 *
 * @brief  returns the current frequency of a base clock
 */
uint32_t GetClockFrequency(CLKSRC_Type src_clk)
{
   	switch(src_clk)
	{
		case(SRC_OSC32K):
			return RTC_CLK;
		case(SRC_IRC):
			return IRC_OSC;
		case(SRC_ENET_RX_CLK):
			return EnetRxFrequency;
		case(SRC_ENET_TX_CLK):
			return EnetTxFrequency;
		case(SRC_EXT_TCK):
			return EXTFrequency;
		case(SRC_XTAL):
			return XtalFrequency;
		case(SRC_PL550M_0):
			return PL550Frequency;
		case(SRC_PL550M_FRAC): //New in Falcon
			return PL550FracFrequency;
		case(SRC_PL160M_0):
			return PL160M_0Frequency;
		case(SRC_PL160M_1):
			return PL160M_1Frequency;
		case(SRC_PL160M_2):
			return PL160M_2Frequency;
		case(SRC_IDIV_0):
			return IDIVAFrequency;
		case(SRC_IDIV_1):
			return IDIVBFrequency;
		case(SRC_IDIV_2):
			return IDIVCFrequency;
		case(SRC_IDIV_3):
			return IDIVDFrequency;
		case(SRC_IDIV_4):
			return IDIVEFrequency;
		default:
		return 0;
	}
}

/**
 * Set PL160M
 *
 * @param  source clock, desired frequency 
 * @return none
 *
 * @brief  	Setup the PL160M PLL 
 *		   	If frequency equals 0 then disable PLL
 *			Integer mode only (fbsel=1, direct=0)				
 *			Fclkout = M * Fclkin/N 
 *			Fcc0 = 2 * P * Fclkout = 2 * P * M * Fclkin/N 
 *			msel+1 = feedback-divider value M 	(1 to 2^15)	
 *			nsel+1 = pre-divider value N		(1 to 2^8)	
 *			psel+1 = post-divider value P(x2)	(1 to 2^5)	
 */
void SetPL160M(CLKSRC_Type src_clk, uint32_t mult) 
{
	uint32_t msel=0, nsel=0, psel=0, pval=1;	

//	EnableSourceClk(src_clk);

	if(mult==0)
	{
		LPC_CGU->PLL1_CTRL |= PD_ENABLE; 	// Power down PLL
		DisableSourceClk(src_clk);
	}
	else
	{
		EnableSourceClk(src_clk);
			 
		switch(src_clk)
		{
			case(SRC_OSC32K):
				PL160M_0Frequency = mult * RTC_CLK;
				break;
			case(SRC_IRC):
				PL160M_0Frequency = mult * IRC_OSC;
				break;
			case(SRC_ENET_RX_CLK):
				PL160M_0Frequency = mult * EnetRxFrequency;
				break;
			case(SRC_ENET_TX_CLK):
				PL160M_0Frequency = mult * EnetTxFrequency;
				break;
			case(SRC_EXT_TCK):
				PL160M_0Frequency = mult * EXTFrequency;
				break;
			case(SRC_XTAL):
				PL160M_0Frequency = mult * XtalFrequency;
				break;
			default:
				PL160M_0Frequency = mult * IRC_OSC;
				break;
		}
	
		// CCO must be in range of 156 - 320 MHz
		// Increase P if FCCO is too low. 
		msel = mult-1;
		//psel is encoded such that 0=1, 1=2, 2=4, 3=8
		while(2*(pval)*PL160M_0Frequency < 156000000) {
			psel++;	
			pval*=2;
		}
//		if(2*(pval)*PL160M_0Frequency > 320000000) {
//			THIS IS OUT OF RANGE!!!
//			HOW DO WE ASSERT IN SAMPLE CODE?
//			__breakpoint(0);
//		}
		LPC_CGU->PLL1_CTRL = (src_clk<<24) | (msel<<16) | (nsel<<12) | (psel<<8) | FBSEL;
		while((LPC_CGU->PLL1_STAT&1) == 0x0); 		// Wait for PLL lock
	}
}

/**
 * Set PLL USB (PL550M)
 *
 * @param  enable
 * @return none
 *
 * @brief  	Setup the USB PLL to 480 MHz 
 *		   	If enable equals 0 then disable PLL
 *		   	Only clock sources IRC and XTAL are valid
 *			Mode1a only: Normal operating mode without post- and pre-divider				
 *			Fclkout = 2 * M * Fclkin
 *			msel+1 = feedback-divider value M 	(1 to 2^15)	
 */
void SetPLLUSB(CLKSRC_Type src_clk, uint8_t enable)
{
	if(!enable)
	{
		LPC_CGU->PLL0USB_CTRL |= PD_ENABLE; 	// Power down PLL
	}
	else
	{
		// Setup PLL550 to generate 480MHz from 12 MHz crystal
		LPC_CGU->PLL0USB_CTRL |= PD_ENABLE; 	// Power down PLL
							//	P			N
		LPC_CGU->PLL0USB_NP_DIV = (98<<0) | (514<<12);
							//	SELP	SELI	SELR	MDEC	 
		LPC_CGU->PLL0USB_MDIV = (0xB<<17)|(0x10<<22)|(0<<28)|(0x7FFA<<0); 					
		LPC_CGU->PLL0USB_CTRL =(SRC_XTAL<<24) | (0x3<<2) | CLKEN;  
		
		// Set the USB0 clock source to PLL550 (480MHz)
		LPC_CGU->BASE_USB0_CLK = (0<<0) | (1<<11) | (SRC_PL550M_0<<24);	
			
		while((LPC_CGU->PLL0USB_STAT&1) == 0x0);	// Wait for PLL lock 
	}

	PL550Frequency = 480000000UL;
}

/**
 * Enable source clock pheripheral
 *
 * @param  clock source
 * @return none
 *
 * @brief  	Enable clock specific peripherals
 */
void EnableSourceClk(CLKSRC_Type src_clk)
{
	uint32_t i=0;

	if(src_clk == SRC_OSC32K)
	{
		LPC_CREG->CREG0 &= ~((1<<3)|(1<<2));		// Active mode of 32 KHz osc and release reset
		LPC_CREG->CREG0 |= (1<<1)|(1<<0);			// Enable 32 kHz & 1 kHz on osc32k
	}
	if(src_clk == SRC_ENET_RX_CLK)scu_pinmux(0xC ,0 , PLAIN_ENABLE, FUNC3); 	// enet_rx_clk on PC_0 func 3
	if(src_clk == SRC_ENET_TX_CLK)scu_pinmux(0x1 ,19, PLAIN_ENABLE, FUNC0); 	// enet_tx_clk on P1_19 func 0
	if(src_clk == SRC_XTAL && (LPC_CGU->XTAL_OSC_CTRL&0x1))
	{
		LPC_CGU->XTAL_OSC_CTRL &= ~(1<<0);								// Enable Xo50M
		for(i=0;i<0xFFFF;i++);
	}
}

/**
 * Disable source clock pheripheral
 *
 * @param  clock source
 * @return none
 *
 * @brief  	Disable clock specific peripherals
 */
void DisableSourceClk(CLKSRC_Type src_clk)
{
	uint32_t i=0;

	if(src_clk == SRC_OSC32K)
	{
		LPC_CREG->CREG0 &= ~((1<<1)|(1<<0));	// Disable 32 kHz & 1 kHz on osc32k
		LPC_CREG->CREG0 |= ((1<<3)|(1<<2));		// osc32k in power down and in reset mode
	}
	if(src_clk == SRC_ENET_RX_CLK)scu_pinmux(0xC ,0 , PLAIN_ENABLE, FUNC0); 	// nc on PC_0 func 0
	if(src_clk == SRC_ENET_TX_CLK)scu_pinmux(0x1 ,19, PLAIN_ENABLE, FUNC2); 	// nc on P1_19 func 2
	if(src_clk == SRC_XTAL)
	{
		LPC_CGU->XTAL_OSC_CTRL = (1<<0);		// Disable Xo50M
		for(i=0;i<0xFFFF;i++);
	}
}
