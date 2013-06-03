/*
 * Copyright(C) NXP Semiconductors, 2012
 * All rights reserved.
 *
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licensor disclaim any and
 * all warranties, express or implied, including all implied warranties of
 * merchantability, fitness for a particular purpose and non-infringement of
 * intellectual property rights.  NXP Semiconductors assumes no responsibility
 * or liability for the use of the software, conveys no license or rights under any
 * patent, copyright, mask work right, or any other intellectual property rights in
 * or to any products. NXP Semiconductors reserves the right to make changes
 * in the software without notification. NXP Semiconductors also makes no
 * representation or warranty that such application will be suitable for the
 * specified use without further testing or modification.
 *
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
 */

#include "board.h"

/** @defgroup BOARD_NGX_XPLORER_18304330_SYSINIT LPC1830 and LPC4330 NGX Xplorer board System Init code
 * @ingroup BOARD_NGX_XPLORER_18304330
 * The System initialization code is called prior to the application and
 * initializes the board for run-time operation. Board initialization
 * for the NGX Xplorer boards includes clock setup and default pin muxing
 * configuration.
 *
 * With the exception of stack space, no RW memory is used for this call.
 *
 * LPC1830 and LPC4330 NGX Xplorer setup<BR>
 *  Clocking:<BR>
 *   All base clocks enabled by default (Save power by disabling un-needed clocks)<BR>
 *   CPU PLL set to maximum clock frequency (as defined by MAX_CLOCK_FREQ value)<BR>
 *   SPIFI FLASH clock setup for fastest speed<BR>
 *   CGU Dividers A, C, D and E are used for the LCD, USB, and SPIFI.
 *  Pin muxing:<BR>
 *   Sets up various pin mux functions for the board (Ethernet, LEDs, etc.)<BR>
 *  Memory:<BR>
 *   There is no memory setup for this board.
 * @{
 */

#ifndef CORE_M0
/* SCR pin definitions for pin muxing */
typedef struct {
	uint8_t pingrp;		/* Pin group */
	uint8_t pinnum;		/* Pin number */
	uint16_t modefunc;	/* Pin mode and function for SCU */
} PINMUX_GRP_T;

/* Structure for initial base clock states */
struct CLK_BASE_STATES {
	CHIP_CGU_BASE_CLK_T clk;	/* Base clock */
	CHIP_CGU_CLKIN_T clkin;	/* Base clock source, see UM for allowable souorces per base clock */
	bool autoblock_enab;/* Set to true to enable autoblocking on frequency change */
	bool powerdn;		/* Set to true if the base clock is initially powered down */
};

/* Initial base clock states are mostly on */
STATIC const struct CLK_BASE_STATES InitClkStates[] = {
	{CLK_BASE_SAFE, CLKIN_IRC, true, false},
	{CLK_BASE_APB1, CLKIN_MAINPLL, true, false},
	{CLK_BASE_APB3, CLKIN_MAINPLL, true, false},
	{CLK_BASE_USB0, CLKIN_USBPLL, true, true},
#if defined(CHIP_LPC43XX)
	{CLK_BASE_PERIPH, CLKIN_MAINPLL, true, false},
	{CLK_BASE_SPI, CLKIN_MAINPLL, true, false},
	{CLK_BASE_VADC, CLKIN_MAINPLL, true, true},
#endif
	{CLK_BASE_PHY_TX, CLKIN_ENET_TX, true, false},
#if defined(USE_RMII)
	{CLK_BASE_PHY_RX, CLKIN_ENET_TX, true, false},
#else
	{CLK_BASE_PHY_RX, CLKIN_ENET_RX, true, false},
#endif
	{CLK_BASE_SDIO, CLKIN_MAINPLL, true, false},
	{CLK_BASE_SSP0, CLKIN_MAINPLL, true, false},
	{CLK_BASE_SSP1, CLKIN_MAINPLL, true, false},
	{CLK_BASE_UART0, CLKIN_MAINPLL, true, false},
	{CLK_BASE_UART1, CLKIN_MAINPLL, true, false},
	{CLK_BASE_UART2, CLKIN_MAINPLL, true, false},
	{CLK_BASE_UART3, CLKIN_MAINPLL, true, false},
	{CLK_BASE_OUT, CLKINPUT_PD, true, false},
	{CLK_BASE_APLL, CLKINPUT_PD, true, false},
	{CLK_BASE_CGU_OUT0, CLKINPUT_PD, true, false},
	{CLK_BASE_CGU_OUT1, CLKINPUT_PD, true, false},

	/* Clocks derived from dividers */
	{CLK_BASE_LCD, CLKIN_IDIVC, true, false},
	{CLK_BASE_USB1, CLKIN_IDIVD, true, true}
};

/* SPIFI high speed pin mode setup */
STATIC const PINMUX_GRP_T spifipinmuxing[] = {
	{0x3, 3,  (SCU_PINIO_FAST | SCU_MODE_FUNC3)},	/* SPIFI CLK */
	{0x3, 4,  (SCU_PINIO_FAST | SCU_MODE_FUNC3)},	/* SPIFI D3 */
	{0x3, 5,  (SCU_PINIO_FAST | SCU_MODE_FUNC3)},	/* SPIFI D2 */
	{0x3, 6,  (SCU_PINIO_FAST | SCU_MODE_FUNC3)},	/* SPIFI D1 */
	{0x3, 7,  (SCU_PINIO_FAST | SCU_MODE_FUNC3)},	/* SPIFI D0 */
	{0x3, 8,  (SCU_PINIO_FAST | SCU_MODE_FUNC3)}	/* SPIFI CS/SSEL */
};

/* USB PLL pre-initialized setup values for 480MHz output rate */
static const CGU_USBAUDIO_PLL_SETUP_T usbPLLSetup = {
	0x0000601D,	/* Default control with main osc input, PLL disabled */
	0x06167FFA,	/* M-divider value for 480MHz output from 12MHz input */
	0x00000000,	/* N-divider value */
	0x00000000	/* Not applicable for USB PLL */
};

/* Audio PLL pre-initialized setup values for FIXME output rate */
// static const CGU_USBAUDIO_PLL_SETUP_T audioPLLSetup = {
//	0x0000601D, /* Default control with main osc input, PLL disabled */
//	0x06167FFA, /* M-divider value for FIXME output from 12MHz input */
//	0x00000000, /* N-divider value */
//	0x00000000  /* FIXME */
// };

/* Setup system clocking */
STATIC void SystemSetupClocking(void)
{
	int i;

	/* Switch main system clocking to crystal */
	Chip_Clock_EnableCrystal();
	Chip_Clock_SetBaseClock(CLK_BASE_MX, CLKIN_CRYSTAL, true, false);

	/* Setup PLL for 100MHz and switch main system clocking */
	Chip_Clock_SetupMainPLLHz(CLKIN_CRYSTAL, CRYSTAL_MAIN_FREQ_IN, 100 * 1000000, 100 * 1000000);
	Chip_Clock_SetBaseClock(CLK_BASE_MX, CLKIN_MAINPLL, true, false);

	/* Setup PLL for maximum clock */
	Chip_Clock_SetupMainPLLHz(CLKIN_CRYSTAL, CRYSTAL_MAIN_FREQ_IN, MAX_CLOCK_FREQ, MAX_CLOCK_FREQ);

	/* Setup system base clocks and initial states. This won't enable and
	   disable individual clocks, but sets up the base clock sources for
	   each individual peripheral clock. */
	for (i = 0; i < (sizeof(InitClkStates) / sizeof(InitClkStates[0])); i++) {
		Chip_Clock_SetBaseClock(InitClkStates[i].clk, InitClkStates[i].clkin,
								InitClkStates[i].autoblock_enab, InitClkStates[i].powerdn);
	}

	/* Reset and enable 32Khz oscillator */
	LPC_CREG->CREG0 &= ~((1 << 3) | (1 << 2));
	LPC_CREG->CREG0 |= (1 << 1) | (1 << 0);

	/* SPIFI pin setup is done prior to setting up system clocking */
	for (i = 0; i < (sizeof(spifipinmuxing) / sizeof(spifipinmuxing[0])); i++) {
		Chip_SCU_PinMuxSet(spifipinmuxing[i].pingrp, spifipinmuxing[i].pinnum,
						   spifipinmuxing[i].modefunc);
	}

	/* Setup a divider E for main PLL clock switch SPIFI clock to that divider.
	   Divide rate is based on CPU speed and speed of SPI FLASH part. */
#if (MAX_CLOCK_FREQ > 180000000)
	Chip_Clock_SetDivider(CLK_IDIV_E, CLKIN_MAINPLL, 5);
#else
	Chip_Clock_SetDivider(CLK_IDIV_E, CLKIN_MAINPLL, 4);
#endif
	Chip_Clock_SetBaseClock(CLK_BASE_SPIFI, CLKIN_IDIVE, true, false);

	/* Attach main PLL clock to divider C with a divider of 2 */
	Chip_Clock_SetDivider(CLK_IDIV_C, CLKIN_MAINPLL, 2);

	/* Setup default USB PLL state for a 480MHz output and attach */
	Chip_Clock_SetupPLL(CLKIN_CRYSTAL, CGU_USB_PLL, &usbPLLSetup);

	/* USB1 needs a 60MHz clock. To get it, a divider of 4 and then 2 are
	   chained to make a divide by 8 function. Connect the output of
	   divider D to the USB1 base clock. */
	Chip_Clock_SetDivider(CLK_IDIV_A, CLKIN_USBPLL, 4);
	Chip_Clock_SetDivider(CLK_IDIV_D, CLKIN_IDIVA, 2);
	Chip_Clock_SetBaseClock(CLK_BASE_USB1, CLKIN_IDIVD, true, true);

	/* Setup default audio PLL state for a FIXME output */
	//	Chip_Clock_SetupPLL(CGU_AUDIO_PLL, &audioPLLSetup); // FIXME
}

STATIC const PINMUX_GRP_T pinmuxing[] = {
	/* RMII pin group */
	{0x1, 15,
	 (SCU_MODE_HIGHSPEEDSLEW_EN | SCU_MODE_MODE_PULLUP | SCU_MODE_INBUFF_EN | SCU_MODE_ZIF_DIS | SCU_MODE_FUNC3)},
	{0x0, 0,
	 (SCU_MODE_HIGHSPEEDSLEW_EN | SCU_MODE_MODE_PULLUP | SCU_MODE_INBUFF_EN | SCU_MODE_ZIF_DIS | SCU_MODE_FUNC2)},
	{0x1, 16,
	 (SCU_MODE_HIGHSPEEDSLEW_EN | SCU_MODE_MODE_PULLUP | SCU_MODE_INBUFF_EN | SCU_MODE_ZIF_DIS | SCU_MODE_FUNC7)},
	{0x0, 1,  (SCU_MODE_HIGHSPEEDSLEW_EN | SCU_MODE_MODE_PULLUP | SCU_MODE_ZIF_DIS | SCU_MODE_FUNC6)},
	{0x1, 19,
	 (SCU_MODE_HIGHSPEEDSLEW_EN | SCU_MODE_MODE_PULLUP | SCU_MODE_INBUFF_EN | SCU_MODE_ZIF_DIS | SCU_MODE_FUNC0)},
	{0x1, 18, (SCU_MODE_HIGHSPEEDSLEW_EN | SCU_MODE_MODE_PULLUP | SCU_MODE_ZIF_DIS | SCU_MODE_FUNC3)},
	{0x1, 20, (SCU_MODE_HIGHSPEEDSLEW_EN | SCU_MODE_MODE_PULLUP | SCU_MODE_ZIF_DIS | SCU_MODE_FUNC3)},
	{0x1, 17,
	 (SCU_MODE_HIGHSPEEDSLEW_EN | SCU_MODE_MODE_PULLUP | SCU_MODE_INBUFF_EN | SCU_MODE_ZIF_DIS | SCU_MODE_FUNC3)},
	{0x2, 0,  (SCU_MODE_HIGHSPEEDSLEW_EN | SCU_MODE_MODE_PULLUP | SCU_MODE_ZIF_DIS | SCU_MODE_FUNC7)},
	/* Board LEDs */
	{0x2, 11, (SCU_MODE_MODE_REPEATER | SCU_MODE_FUNC0)},
	{0x2, 12, (SCU_MODE_MODE_REPEATER | SCU_MODE_FUNC0)},
	/*  I2S  */
	{0x3, 0,  (SCU_PINIO_FAST | SCU_MODE_FUNC2)},
	{0x6, 0,  (SCU_PINIO_FAST | SCU_MODE_FUNC4)},
	{0x7, 2,  (SCU_PINIO_FAST | SCU_MODE_FUNC2)},
	{0x6, 2,  (SCU_PINIO_FAST | SCU_MODE_FUNC3)},
	{0x7, 1,  (SCU_PINIO_FAST | SCU_MODE_FUNC2)},
	{0x6, 1,  (SCU_PINIO_FAST | SCU_MODE_FUNC3)},
};

/* Sets up system pin muxing */
STATIC void SystemSetupMuxing(void)
{
	int i;

	/* Setup system level pin muxing */
	for (i = 0; i < (sizeof(pinmuxing) / sizeof(pinmuxing[0])); i++) {
		Chip_SCU_PinMuxSet(pinmuxing[i].pingrp, pinmuxing[i].pinnum,
						   pinmuxing[i].modefunc);
	}
}

/* Nothing to do for the Xplorer board */
STATIC void SystemSetupMemory(void)
{}

#endif

/**
 * @brief	Setup the system
 * @return	none
 * SystemInit() is called prior to the application and sets up system
 * clocking, memory, and any resources needed prior to the application
 * starting.
 */
void SystemInit(void)
{
#if defined(CORE_M3) || defined(CORE_M4)
	unsigned int *pSCB_VTOR = (unsigned int *) 0xE000ED08;

#if defined(__IAR_SYSTEMS_ICC__)
	extern void *__vector_table;

	*pSCB_VTOR = (unsigned int) &__vector_table;
#elif defined(__CODE_RED)
	extern void *g_pfnVectors;

	*pSCB_VTOR = (unsigned int) &g_pfnVectors;
#elif defined(__ARMCC_VERSION)
	extern void *__Vectors;

	*pSCB_VTOR = (unsigned int) &__Vectors;
#endif

#if defined(__FPU_PRESENT) && __FPU_PRESENT == 1
	fpuInit();
#endif

	/* Setup system clocking and memory. This is done early to allow the
	   application and tools to clear memory and use scatter loading to
	   external memory. */
	SystemSetupClocking();
	SystemSetupMuxing();
	SystemSetupMemory();
#endif
}

/**
 * @}
 */
