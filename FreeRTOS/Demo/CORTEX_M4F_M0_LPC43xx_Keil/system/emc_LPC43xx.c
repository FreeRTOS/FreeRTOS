/***********************************************************************
 * $Id: emc_LPC43xx.c 8389 2011-10-19 13:53:14Z nxp28536 $   emc_LPC43xx.c
 *
 * Project: NXP LPC43xx Common
 *
 * Description:  Initialisation of the external memory interface and
 *               configuration for the specific memories connected to
 *               the LPC43xx
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
#include "system_LPC43xx.h"
#include "scu.h"
#include "config.h"
#include "platform_config.h"

#include "emc_LPC43xx.h"


/**********************************************************************
 ** Function prototypes
**********************************************************************/
#define DELAY_1usFreq  (1000000)        // 1MHz equivalent to 1usec
static uint32_t delayBase1us;           // calculated depending on M4/EMI frequency
static void vDelay(uint32_t u32Delay);  // delay function



/****************************************************************************************
* Call the required memory setup functions from here
*
*
****************************************************************************************/
void EMC_Init( void )
{
	// The address/data pins for the memory interface are required for the static and for
  	// dynamic memories
  	EMC_Config_Pinmux();

	// Initialise the control signals for static memories
#if (USE_EXT_STATIC_MEM == YES)

    // Initialise the control signals for static memories
    EMC_Config_Static();

//    #if (USE_EXT_DYNAMIC_MEM == NO)
//      LPC_EMC->CONTROL = 0x00000001;   // Enable the external memory controller	
//	  LPC_EMC->CONFIG = 0;	
//	  // Buffers for the static memories are enabled as well. If there is SDRAM as well,
//	  // then this is done after the initialisation for the dynamic memory interface.
//      LPC_EMC->STATICCONFIG0 = 0x00080081; 	
//    #endif

#endif

#if (USE_EXT_DYNAMIC_MEM == YES)

  	// The setup for dynamic memories (SDRAM)
    EMC_Init_SRDRAM(SDRAM_BASE, PART_WIDTH, PART_SIZE, EXT_WIDTH, COL_ADDR_BITS);

#elif (USE_EXT_DYNAMIC_MEM == NO)

    LPC_EMC->CONTROL = 0x00000001;   // Enable the external memory controller	
	LPC_EMC->CONFIG = 0;	

#endif
	  
	// Buffers for the static memories can now be enabled as well. In a system with static and dynamic memory
	// this should only been done after the SDRAM initialisation --> here
	LPC_EMC->STATICCONFIG0 = 0x00080081;

}


/****************************************************************************************
* Set up the address/data pins for external memory interface in LP43xx
*
* Modify this function in case not all of the address/data pins are needed.
****************************************************************************************/
void EMC_Config_Pinmux(void)
{
	
  // Disable the external memory controller before changing pin control configuration
  LPC_EMC->CONTROL = 0x00000000;

// EMC_OUT	   (PUP_CLEAR | SLEWRATE_FAST | FILTER_DISABLE) 
// EMC_IO	   (PUP_CLEAR | SLEWRATE_FAST | INBUF_ENABLE | FILTER_DISABLE)

  // Data line configuration
  scu_pinmux(0x1,  7, EMC_IO, FUNC3);  // P1_7:   D0
  scu_pinmux(0x1,  8, EMC_IO, FUNC3);  // P1_8:   D1
  scu_pinmux(0x1,  9, EMC_IO, FUNC3);  // P1_9:   D2
  scu_pinmux(0x1, 10, EMC_IO, FUNC3);  // P1_10:  D3
  scu_pinmux(0x1, 11, EMC_IO, FUNC3);  // P1_11:  D4
  scu_pinmux(0x1, 12, EMC_IO, FUNC3);  // P1_12:  D5
  scu_pinmux(0x1, 13, EMC_IO, FUNC3);  // P1_13:  D6
  scu_pinmux(0x1, 14, EMC_IO, FUNC3);  // P1_14:  D7
  scu_pinmux(0x5,  4, EMC_IO, FUNC2);  // P5_4:   D8
  scu_pinmux(0x5,  5, EMC_IO, FUNC2);  // P5_5:   D9
  scu_pinmux(0x5,  6, EMC_IO, FUNC2);  // P5_6:   D10
  scu_pinmux(0x5,  7, EMC_IO, FUNC2);  // P5_7:  D11
  scu_pinmux(0x5,  0, EMC_IO, FUNC2);  // P5_0:  D12
  scu_pinmux(0x5,  1, EMC_IO, FUNC2);  // P5_1:  D13
  scu_pinmux(0x5,  2, EMC_IO, FUNC2);  // P5_2:  D14
  scu_pinmux(0x5,  3, EMC_IO, FUNC2);  // P5_3:  D15
  scu_pinmux(0xD,  2, EMC_IO, FUNC2);  // PD_2:  D16
  scu_pinmux(0xD,  3, EMC_IO, FUNC2);  // PD_3:  D17
  scu_pinmux(0xD,  4, EMC_IO, FUNC2);  // PD_4:  D18
  scu_pinmux(0xD,  5, EMC_IO, FUNC2);  // PD_5:  D19
  scu_pinmux(0xD,  6, EMC_IO, FUNC2);  // PD_6:  D20
  scu_pinmux(0xD,  7, EMC_IO, FUNC2);  // PD_7:  D21
  scu_pinmux(0xD,  8, EMC_IO, FUNC2);  // PD_8:  D22
  scu_pinmux(0xD,  9, EMC_IO, FUNC2);  // PD_9:  D23
  scu_pinmux(0xE,  5, EMC_IO, FUNC3);  // PE_5:  D24
  scu_pinmux(0xE,  6, EMC_IO, FUNC3);  // PE_6:  D25
  scu_pinmux(0xE,  7, EMC_IO, FUNC3);  // PE_7:  D26
  scu_pinmux(0xE,  8, EMC_IO, FUNC3);  // PE_8:  D27
  scu_pinmux(0xE,  9, EMC_IO, FUNC3);  // PE_9:  D28
  scu_pinmux(0xE, 10, EMC_IO, FUNC3);  // PE_10: D29
  scu_pinmux(0xE, 11, EMC_IO, FUNC3);  // PE_11: D30
  scu_pinmux(0xE, 12, EMC_IO, FUNC3);  // PE_12: D31

  // Address line configuration
  scu_pinmux(0x2,  9, EMC_IO, FUNC3);  // P2_9: A0
  scu_pinmux(0x2, 10, EMC_IO, FUNC3);  // P2_10: A1
  scu_pinmux(0x2, 11, EMC_IO, FUNC3);  // P2_11: A2
  scu_pinmux(0x2, 12, EMC_IO, FUNC3);  // P2_12: A3
  scu_pinmux(0x2, 13, EMC_IO, FUNC3);  // P2_13: A4
  scu_pinmux(0x1,  0, EMC_IO, FUNC2);  // P1_0: A5
  scu_pinmux(0x1,  1, EMC_IO, FUNC2);  // P1_1: A6
  scu_pinmux(0x1,  2, EMC_IO, FUNC2);  // P1_2: A7
  scu_pinmux(0x2,  8, EMC_IO, FUNC3);  // P2_8: A8
  scu_pinmux(0x2,  7, EMC_IO, FUNC3);  // P2_7: A9
  scu_pinmux(0x2,  6, EMC_IO, FUNC2);  // P2_6: A10
  scu_pinmux(0x2,  2, EMC_IO, FUNC2);  // P2_2: A11
  scu_pinmux(0x2,  1, EMC_IO, FUNC2);  // P2_0: A12
  scu_pinmux(0x2,  0, EMC_IO, FUNC2);  // P2_0: A13
  scu_pinmux(0x6,  8, EMC_IO, FUNC1);  // P6_8: A14
  scu_pinmux(0x6,  7, EMC_IO, FUNC1);  // P6_7: A15
  scu_pinmux(0xD, 16, EMC_IO, FUNC2);  // PD_16: A16
  scu_pinmux(0xD, 15, EMC_IO, FUNC2);  // PD_15: A17
  scu_pinmux(0xE,  0, EMC_IO, FUNC3);  // PE_0: A18
  scu_pinmux(0xE,  1, EMC_IO, FUNC3);  // PE_1: A19
  scu_pinmux(0xE,  2, EMC_IO, FUNC3);  // PE_2: A20
  scu_pinmux(0xE,  3, EMC_IO, FUNC3);  // PE_3: A21
  scu_pinmux(0xE,  4, EMC_IO, FUNC3);  // PE_4: A22

  // Control signals for static memory
  scu_pinmux(0x1,  6, EMC_IO, FUNC3);  // P1_6: WE
  scu_pinmux(0x1,  5, EMC_IO, FUNC3);  // P1_5: CS0
  scu_pinmux(0x1,  3, EMC_IO, FUNC3);  // P1_6: OE
  scu_pinmux(0x1,  4, EMC_IO, FUNC3);  // P1_5: BLS0
  scu_pinmux(0x6,  6, EMC_IO, FUNC1);  // P1_6: BLS1
  scu_pinmux(0xD, 12, EMC_IO, FUNC2);  // PD_12: CS2

  #if (USE_EXT_DYNAMIC_MEM == YES)
    // Control signals for dynamic memory
    scu_pinmux(0x6,  9, EMC_IO, FUNC3);  // P6_9: DYCS0
    scu_pinmux(0x6,  4, EMC_IO, FUNC3);  // P6_4: CAS
    scu_pinmux(0x6,  5, EMC_IO, FUNC3);  // P6_5: RAS
    scu_pinmux(0x6, 11, EMC_IO, FUNC3);  // P6_11: CKEOUT0
    scu_pinmux(0x6, 12, EMC_IO, FUNC3);  // P6_12: DQMOUT0
    scu_pinmux(0x6, 10, EMC_IO, FUNC3);  // P6_10: DQMOUT1

    LPC_SCU_CLK(0) = 0 + EMC_IO;   // EMC_CLK0 signal on pin CLK0 (needed for SDRAM)
    LPC_SCU_CLK(1) = 0 + EMC_IO;
    LPC_SCU_CLK(2) = 0 + EMC_IO;
    LPC_SCU_CLK(3) = 0 + EMC_IO;
  #endif

}


/****************************************************************************************
* Configure CS0 for 70ns 16-bit flash memory on the Hitex board
* Configure CS2 for 55ns 16-bit SRAM on the Hitex board
*
****************************************************************************************/
void EMC_Config_Static(void)
{

  // Configure CS0 for flash memory
  // @120MHz there should be 8 or 9 waitstates for the 70ns flash, apparently it works with 7
  LPC_EMC->STATICCONFIG0 = 0x00000081;      // CS0: 16 bit = WE
  LPC_EMC->STATICWAITOEN0 = 0;              // CS0: WAITOEN = 0

  #if (PLATFORM == HITEX_A2_BOARD)

    LPC_EMC->STATICWAITRD0 = 7;             // CS0: WAITRD = 7 

    // The Hitex board has external SRAM on CS2
    // @120MHz there should be 7 waitstates for the 55ns SRAM, it should work with 6
    LPC_EMC->STATICCONFIG0 = 0x00000081;     // CS2: 16 bit = WE
    LPC_EMC->STATICWAITOEN2 = 0;             // CS2: WAITOEN = 0
    LPC_EMC->STATICWAITRD2 = 7;              // CS2: WAITRD = 6

  #elif	(PLATFORM == NXP_VALIDATION_BOARD)

  	LPC_EMC->STATICWAITRD0 = check 9;             // CS0: WAITRD = 8 
	// to be added

    LPC_EMC->STATICCONFIG0 = check 0x00000081;     // CS2: 16 bit = WE
    LPC_EMC->STATICWAITOEN2 = check 0;             // CS2: WAITOEN = 0
    LPC_EMC->STATICWAITRD2 = check 7;              // CS2: WAITRD = 6

  #endif
	
}


// Defines for EMC signal delay settings
#define EMC_B_ENABLE                    (1 << 19)
#define EMC_ENABLE                      (1 << 0)
#define EMC_CE_ENABLE                   (1 << 0)
#define EMC_CS_ENABLE                   (1 << 1)
#define EMC_CLOCK_DELAYED_STRATEGY      (0 << 0)
#define EMC_COMMAND_DELAYED_STRATEGY 	(1 << 0)
#define EMC_COMMAND_DELAYED_STRATEGY2 	(2 << 0)
#define EMC_COMMAND_DELAYED_STRATEGY3 	(3 << 0)
#define EMC_INIT(i)                     ((i) << 7)
#define EMC_NORMAL                      (0)
#define EMC_MODE                        (1)
#define EMC_PRECHARGE_ALL               (2)
#define EMC_NOP                         (3)

/****************************************************************************************
* Configure the delays for the SDRAM
*
* - on the Hitex board (IS42S16400D-7TL)
* - on the NXP evaluation board (MT48LC4M32B2)
* - on the NXP validation board (MT48LC4M32B2)
*
****************************************************************************************/
#if (PLATFORM == HITEX_A2_BOARD) || (PLATFORM == NXP_VALIDATION_BOARD)

// Defines for SDRAM devices
#define DOUT_DELAY      0
#define CLK0_DELAY      5
#define CLKE0_DELAY     5
#define RAS_DELAY       0
#define CAS_DELAY       0
#define WE_DELAY        0
#define DYCS0_DELAY     0
#define DQM0_DELAY      0
#define FBCLK0_DELAY    0
#define CCLK_DELAY      0
#define ADDR_DELAY      0
#define DIN_DELAY       0
#define DEN_DELAY       0

#endif

void initEmiDelays(void)
{
    // eventually configure delays, defaults are zero

    // CLK & CLKE0 delay
    *(uint32_t*)(LPC_SCU_BASE + 0xD00) = ((CLK0_DELAY << 16) | (CLKE0_DELAY << 0) );

    // EMCCTRLDELAY, address 0x4008 6D04
    *(uint32_t*)(LPC_SCU_BASE + 0xD04) = ((WE_DELAY << 12)| (CAS_DELAY << 4) | (RAS_DELAY << 0) );

    // DYCS0_DELAY, address 0x4008 6D08
    *(uint32_t*)(LPC_SCU_BASE + 0xD08) = ((DYCS0_DELAY << 0));

    // data out delay for D0 to D31   EMCDOUTDELAY
    *(uint32_t*)(LPC_SCU_BASE + 0xD0C) = ((DOUT_DELAY << 28) | (DOUT_DELAY << 24) | (DOUT_DELAY << 20) | (DOUT_DELAY << 16)|(DQM0_DELAY << 12) | (DQM0_DELAY << 8) | (DQM0_DELAY << 4) | (DQM0_DELAY << 0)) ;

    // EMCFBCLKDELAY, address 0x4008 6D10
    *(uint32_t*)(LPC_SCU_BASE + 0xD10) = ((CCLK_DELAY << 16)|(FBCLK0_DELAY << 12) | (FBCLK0_DELAY << 8) | (FBCLK0_DELAY << 4) | (FBCLK0_DELAY << 0)) ;

    // EMCADDRDELAY, address 0x4008 6D14, 0x4008 6D18, 0x4008 6D1C)
    *(uint32_t*)(LPC_SCU_BASE + 0xD14) = ((ADDR_DELAY << 28)|(ADDR_DELAY << 24)|(ADDR_DELAY << 20)|(ADDR_DELAY << 16)|(ADDR_DELAY << 12) | (ADDR_DELAY << 8) | (ADDR_DELAY << 4) | (ADDR_DELAY << 0)) ;
    *(uint32_t*)(LPC_SCU_BASE + 0xD18) = ((ADDR_DELAY << 28)|(ADDR_DELAY << 24)|(ADDR_DELAY << 20)|(ADDR_DELAY << 16)|(ADDR_DELAY << 12) | (ADDR_DELAY << 8) | (ADDR_DELAY << 4) | (ADDR_DELAY << 0)) ;
    *(uint32_t*)(LPC_SCU_BASE + 0xD1C) = ((ADDR_DELAY << 28)|(ADDR_DELAY << 24)|(ADDR_DELAY << 20)|(ADDR_DELAY << 16)|(ADDR_DELAY << 12) | (ADDR_DELAY << 8) | (ADDR_DELAY << 4) | (ADDR_DELAY << 0)) ;

    // data in delay for D0 to D31   EMCDINDELAY
    *(uint32_t*)(LPC_SCU_BASE + 0xD24) = ((DEN_DELAY << 28)|(DEN_DELAY << 24)|(DEN_DELAY << 20)|(DEN_DELAY << 16)|(DIN_DELAY << 12)|(DIN_DELAY << 8)|(DIN_DELAY << 4)|(DIN_DELAY << 0));
}




/****************************************************************************************
* Configure the EMI for the SDRAM
*
* - on the Hitex board (IS42S16400D-7TL)
* - on the NXP validation board (MT48LC4M32B2)
*
****************************************************************************************/
void EMC_Init_SRDRAM(uint32_t u32BaseAddr, uint32_t u32Width, uint32_t u32Size, uint32_t u32DataBus, uint32_t u32ColAddrBits)
{

	// calculate a 1 usec delay base 	
	delayBase1us = M4Frequency / DELAY_1usFreq;

	// eventually adjust the CCU delays for EMI (default to zero)
	initEmiDelays();

	// Initialize EMC to interface with SDRAM. The EMC needs to run for this.
	LPC_EMC->CONTROL                = 0x00000001;   // (Re-)enable the external memory controller	
	LPC_EMC->CONFIG                 = 0;

#if (PLATFORM == HITEX_A2_BOARD)

	LPC_EMC->DYNAMICCONFIG0 	= ((u32Width << 7) | (u32Size << 9) | (u32DataBus << 14)); // Selects the configuration information for dynamic memory chip select 0.
	LPC_EMC->DYNAMICRASCAS0 	= (2UL << 0) | (2UL << 8); // Selects the RAS and CAS latencies for dynamic memory chip select 0.	
	LPC_EMC->DYNAMICREADCONFIG	= EMC_COMMAND_DELAYED_STRATEGY;	 // Configures the dynamic memory read strategy.
	LPC_EMC->DYNAMICRP 		= 1; // Selects the precharge command period
	LPC_EMC->DYNAMICRAS 		= 3; // Selects the active to precharge command period
	LPC_EMC->DYNAMICSREX 		= 5; // Selects the self-refresh exit time
	LPC_EMC->DYNAMICAPR 		= 0; // Selects the last-data-out to active command time
	LPC_EMC->DYNAMICDAL 		= 4; // Selects the data-in to active command time.
	LPC_EMC->DYNAMICWR 		= 1; // Selects the write recovery time
	LPC_EMC->DYNAMICRC 		= 5; // Selects the active to active command period
	LPC_EMC->DYNAMICRFC 		= 5; // Selects the auto-refresh period
	LPC_EMC->DYNAMICXSR 		= 5; // Selects the exit self-refresh to active command time
	LPC_EMC->DYNAMICRRD 		= 0; // Selects the active bank A to active bank B latency
	LPC_EMC->DYNAMICMRD 		= 0; // Selects the load mode register to active command time
	
	LPC_EMC->DYNAMICCONTROL 	= EMC_CE_ENABLE | EMC_CS_ENABLE | EMC_INIT(EMC_NOP);
	vDelay(100);
	
	LPC_EMC->DYNAMICCONTROL 	= EMC_CE_ENABLE | EMC_CS_ENABLE | EMC_INIT(EMC_PRECHARGE_ALL);

	LPC_EMC->DYNAMICREFRESH 	= 2; // Configures dynamic memory refresh operation
	vDelay(100);
	
	LPC_EMC->DYNAMICREFRESH 	= 83; // Configures dynamic memory refresh operation
	
	LPC_EMC->DYNAMICCONTROL 	= EMC_CE_ENABLE | EMC_CS_ENABLE | EMC_INIT(EMC_MODE);
	
	// Write configuration data to SDRAM device
	if(u32DataBus == 0)   // 16-bit data bus, the EMC enforces a burst size 8
	{
		*((volatile uint32_t *)(u32BaseAddr | ((3UL | (2UL << 4)) << (u32ColAddrBits + 2 + 1))));
	}
	else   // burst size 4 (which is not an option for 16-bit data bus anyway)
	{
		*((volatile uint32_t *)(u32BaseAddr | ((2UL | (2UL << 4)) << (u32ColAddrBits + 2 + 2))));
	}
#endif   // HITEX_BOARD


#if (PLATFORM == NXP_VALIDATION_BOARD)	

	LPC_EMC->DYNAMICCONFIG0 	= ((u32Width << 7) | (u32Size << 9) | (u32DataBus << 14));
	LPC_EMC->DYNAMICRASCAS0 	= (2UL << 0) | (2UL << 8);	
	LPC_EMC->DYNAMICREADCONFIG	= EMC_COMMAND_DELAYED_STRATEGY;	
	LPC_EMC->DYNAMICRP 		= 1;    // calculated from xls sheet
	LPC_EMC->DYNAMICRAS 		= 2;
	LPC_EMC->DYNAMICSREX 		= 5;
	LPC_EMC->DYNAMICAPR 		= 0;
	LPC_EMC->DYNAMICDAL 		= 4;
	LPC_EMC->DYNAMICWR 		= 1;
	LPC_EMC->DYNAMICRC 		= 5;
	LPC_EMC->DYNAMICRFC 		= 5;
	LPC_EMC->DYNAMICXSR 		= 5;
	LPC_EMC->DYNAMICRRD 		= 0;
	LPC_EMC->DYNAMICMRD 		= 0;
	
	LPC_EMC->DYNAMICCONTROL 	= EMC_CE_ENABLE | EMC_CS_ENABLE | EMC_INIT(EMC_NOP);
	vDelay(100);
	
	LPC_EMC->DYNAMICCONTROL 	= EMC_CE_ENABLE | EMC_CS_ENABLE | EMC_INIT(EMC_PRECHARGE_ALL);

	LPC_EMC->DYNAMICREFRESH 	= 2;
	vDelay(100);
	
	LPC_EMC->DYNAMICREFRESH 	= 83;
	
	LPC_EMC->DYNAMICCONTROL 	= EMC_CE_ENABLE | EMC_CS_ENABLE | EMC_INIT(EMC_MODE);
	
	// Write configuration data to SDRAM device
	if(u32DataBus == 0)   // burst size 8
	{
		*((volatile uint32_t *)(u32BaseAddr | ((3UL | (2UL << 4)) << (u32ColAddrBits + 2 + 1))));
	}
	else   // burst size 4
	{
		*((volatile uint32_t *)(u32BaseAddr | ((2UL | (2UL << 4)) << (u32ColAddrBits + 2 + 2))));
	}
#endif   // Validation board

	LPC_EMC->DYNAMICCONTROL   = 0;
	LPC_EMC->DYNAMICCONFIG0 |= EMC_B_ENABLE;   	// Enable the buffers

}


/**********************************************************************
 ** Function name:
 **
 ** Description:
 **
 ** Parameters:
 **
 ** Returned value:
 **********************************************************************/
static void vDelay(uint32_t u32Delay)
{
	volatile uint32_t i;
	
	for(i = 0; i < (u32Delay * delayBase1us); i++);
}

