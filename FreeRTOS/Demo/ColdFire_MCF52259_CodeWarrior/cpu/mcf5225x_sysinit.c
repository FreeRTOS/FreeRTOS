/*
 * File:		sysinit.c
 * Purpose:		Reset configuration of the M52259EVB
 * 
 * License:     All software covered by license agreement in -
 *              docs/Freescale_Software_License.pdf
 */

#include "common.h"

/********************************************************************/

void mcf5225x_init(void);
void mcf5225x_wtm_init(void);
void mcf5225x_pll_init(void);
void mcf5225x_uart_init(void);
void mcf5225x_scm_init(void);
void mcf5225x_gpio_init(void);

/********************************************************************/
void
mcf5225x_init(void)
{
	register uint32 n;
	register uint8 *dp, *sp;


    /* 
     * Allow interrupts from ABORT, SW1, SW2 (IRQ[1,5,7]) 
     * and USB (IRQ[2,6])
     */
     
  	
    /* Enable IRQ signals on the port */
    MCF_GPIO_PNQPAR = 0
        | MCF_GPIO_PNQPAR_IRQ1_IRQ1   
        | MCF_GPIO_PNQPAR_IRQ5_IRQ5
        | MCF_GPIO_PNQPAR_IRQ7_IRQ7;
    
    /* Set EPORT to look for falling edges */
    MCF_EPORT_EPPAR = 0
        | MCF_EPORT_EPPAR_EPPA1_FALLING  
        | MCF_EPORT_EPPAR_EPPA2_FALLING  
        | MCF_EPORT_EPPAR_EPPA5_FALLING
        | MCF_EPORT_EPPAR_EPPA6_FALLING  
        | MCF_EPORT_EPPAR_EPPA7_FALLING;
        
    /* Clear any currently triggered events on the EPORT  */
    MCF_EPORT_EPIER = 0
        | MCF_EPORT_EPIER_EPIE1
        | MCF_EPORT_EPIER_EPIE2 
        | MCF_EPORT_EPIER_EPIE5
        | MCF_EPORT_EPIER_EPIE6 
        | MCF_EPORT_EPIER_EPIE7;
       
    /* Enable interrupts in the interrupt controller */
    MCF_INTC0_IMRL &= ~(0
        | MCF_INTC_IMRL_INT_MASK1 
        | MCF_INTC_IMRL_INT_MASK2 
        | MCF_INTC_IMRL_INT_MASK5 
        | MCF_INTC_IMRL_INT_MASK6 
        | MCF_INTC_IMRL_INT_MASK7 
        | MCF_INTC_IMRL_MASKALL);

  
	/* Enable debug */
	MCF_GPIO_PDDPAR = 0x0F;
	
	/* Set real time clock freq */

	MCF_CLOCK_RTCCR = 48000000;

	/* Copy the vector table to RAM */
	if (__VECTOR_RAM != VECTOR_TABLE)
	{
		for (n = 0; n < 256; n++)
			__VECTOR_RAM[n] = VECTOR_TABLE[n];
			
		mcf5xxx_wr_vbr((uint32)__VECTOR_RAM);
	}

	/*
	 * Move initialized data from ROM to RAM.
	 */
	if (__DATA_ROM != __DATA_RAM)
	{
		dp = (uint8 *)__DATA_RAM;
		sp = (uint8 *)__DATA_ROM;
		n = (uint32)(__DATA_END - __DATA_RAM);
		while (n--)
			*dp++ = *sp++;
	}

	/*
	 * Zero uninitialized data
	 */
	if (__BSS_START != __BSS_END)
	{
		sp = (uint8 *)__BSS_START;
		n = (uint32)(__BSS_END - __BSS_START);
		while (n--)
			*sp++ = 0;
	}
	mcf5225x_wtm_init();

	mcf5225x_pll_init();
	mcf5225x_scm_init();
	mcf5225x_uart_init();
}
/********************************************************************/
void
mcf5225x_wtm_init(void)
{
	/*
	 * Disable Software Watchdog Timer
	 */
	MCF_SCM_CWCR = 0;
}
/********************************************************************/
void
mcf5225x_pll_init(void)
{
	/*Required if booting with internal relaxation oscillator & pll off, clkmod[1:0]=00 & xtal=1 */
#ifndef OMIT_OCLR_CONFIGURATION
	MCF_CLOCK_OCLR = 0xC0;   //turn on crystal
	MCF_CLOCK_CCLR = 0x00;    //switch to crystal 
    MCF_CLOCK_OCHR = 0x00; //turn off relaxation osc
#endif

	/* The PLL pre divider - 48MHz / 6 = 8MHz */
	MCF_CLOCK_CCHR =0x05;
	 
	 
	/* The PLL pre-divider affects this!!! 
	 * Multiply 48Mhz reference crystal /CCHR by 10 to acheive system clock of 80Mhz
	 */

	MCF_CLOCK_SYNCR &= ~(MCF_CLOCK_SYNCR_PLLEN);

    MCF_CLOCK_SYNCR |= MCF_CLOCK_SYNCR_CLKSRC | MCF_CLOCK_SYNCR_PLLMODE;
	
	//80
	MCF_CLOCK_SYNCR |= MCF_CLOCK_SYNCR_MFD(3) | MCF_CLOCK_SYNCR_RFD(0);
	//64
	//MCF_CLOCK_SYNCR = MCF_CLOCK_SYNCR_MFD(2) | MCF_CLOCK_SYNCR_RFD(0);
	//16
	//MCF_CLOCK_SYNCR = MCF_CLOCK_SYNCR_MFD(2) | MCF_CLOCK_SYNCR_RFD(2);
	//8
	//MCF_CLOCK_SYNCR = MCF_CLOCK_SYNCR_MFD(2) | MCF_CLOCK_SYNCR_RFD(3);
	//1
	//MCF_CLOCK_SYNCR = MCF_CLOCK_SYNCR_MFD(2) | MCF_CLOCK_SYNCR_RFD(6);
	
	MCF_CLOCK_SYNCR |= MCF_CLOCK_SYNCR_PLLEN;

	
	while (!(MCF_CLOCK_SYNSR & MCF_CLOCK_SYNSR_LOCK))
	{
	}
}
/********************************************************************/
void
mcf5225x_scm_init(void)
{
	/*
	 * Enable on-chip modules to access internal SRAM
	 */
	MCF_SCM_RAMBAR = (0
		| MCF_SCM_RAMBAR_BA(SRAM_ADDRESS)
		| MCF_SCM_RAMBAR_BDE);
}
/********************************************************************/
void
mcf5225x_gpio_init(void)
{
	/*
	 * Initialize Port TA to enable Axcel control
	 */
	MCF_GPIO_PTAPAR = 0x00; 
	MCF_GPIO_DDRTA  = 0x0F;
	MCF_GPIO_PORTTA = 0x04;
	
}
/********************************************************************/
void
mcf5225x_uart_init(void)
{
	/*
	 * Initialize all three UARTs for serial communications
	 */

	register uint16 ubgs;

	/*
	 * Set Port UA to initialize URXD0/UTXD0
	 */
    MCF_GPIO_PUAPAR = 0
        | MCF_GPIO_PUAPAR_URXD0_URXD0
        | MCF_GPIO_PUAPAR_UTXD0_UTXD0;

    MCF_GPIO_PUBPAR = 0
        | MCF_GPIO_PUBPAR_URXD1_URXD1
        | MCF_GPIO_PUBPAR_UTXD1_UTXD1;

    MCF_GPIO_PUCPAR = 0
        | MCF_GPIO_PUCPAR_URXD2_URXD2
        | MCF_GPIO_PUCPAR_UTXD2_UTXD2;

	/*
	 * Reset Transmitter
	 */
	MCF_UART0_UCR = MCF_UART_UCR_RESET_TX;
	MCF_UART1_UCR = MCF_UART_UCR_RESET_TX;
	MCF_UART2_UCR = MCF_UART_UCR_RESET_TX;

	/*
	 * Reset Receiver
	 */
	MCF_UART0_UCR = MCF_UART_UCR_RESET_RX;
	MCF_UART1_UCR = MCF_UART_UCR_RESET_RX;
	MCF_UART2_UCR = MCF_UART_UCR_RESET_RX;

	/*
	 * Reset Mode Register
	 */
	MCF_UART0_UCR = MCF_UART_UCR_RESET_MR;
	MCF_UART1_UCR = MCF_UART_UCR_RESET_MR;
	MCF_UART2_UCR = MCF_UART_UCR_RESET_MR;

	/*
	 * No parity, 8-bits per character
	 */
	MCF_UART0_UMR1 = (0
		| MCF_UART_UMR_PM_NONE
		| MCF_UART_UMR_BC_8 );
	MCF_UART1_UMR1 = (0
		| MCF_UART_UMR_PM_NONE
		| MCF_UART_UMR_BC_8 );
	MCF_UART2_UMR1 = (0
		| MCF_UART_UMR_PM_NONE
		| MCF_UART_UMR_BC_8 );

	/*
	 * No echo or loopback, 1 stop bit
	 */
	MCF_UART0_UMR2 = (0
		| MCF_UART_UMR_CM_NORMAL
		| MCF_UART_UMR_SB_STOP_BITS_1);
	MCF_UART1_UMR2 = (0
		| MCF_UART_UMR_CM_NORMAL
		| MCF_UART_UMR_SB_STOP_BITS_1);
	MCF_UART2_UMR2 = (0
		| MCF_UART_UMR_CM_NORMAL
		| MCF_UART_UMR_SB_STOP_BITS_1);

	/*
	 * Set Rx and Tx baud by SYSTEM CLOCK
	 */
	MCF_UART0_UCSR = (0
		| MCF_UART_UCSR_RCS_SYS_CLK
		| MCF_UART_UCSR_TCS_SYS_CLK);
	MCF_UART1_UCSR = (0
		| MCF_UART_UCSR_RCS_SYS_CLK
		| MCF_UART_UCSR_TCS_SYS_CLK);
	MCF_UART2_UCSR = (0
		| MCF_UART_UCSR_RCS_SYS_CLK
		| MCF_UART_UCSR_TCS_SYS_CLK);

	/*
	 * Mask all UART interrupts
	 */
	MCF_UART0_UIMR = 0;
	MCF_UART1_UIMR = 0;
	MCF_UART2_UIMR = 0;

	/*
	 * Calculate baud settings
	 */
	ubgs = (uint16)((SYSTEM_CLOCK*1000000)/(UART_BAUD * 32));

	MCF_UART0_UBG1 = (uint8)((ubgs & 0xFF00) >> 8);
	MCF_UART0_UBG2 = (uint8)(ubgs & 0x00FF);
	MCF_UART1_UBG1 = (uint8)((ubgs & 0xFF00) >> 8);
	MCF_UART1_UBG2 = (uint8)(ubgs & 0x00FF);
	MCF_UART2_UBG1 = (uint8)((ubgs & 0xFF00) >> 8);
	MCF_UART2_UBG2 = (uint8)(ubgs & 0x00FF);

	/*
	 * Enable receiver and transmitter
	 */
	MCF_UART0_UCR = (0
		| MCF_UART_UCR_TX_ENABLED
		| MCF_UART_UCR_RX_ENABLED);
	MCF_UART1_UCR = (0
		| MCF_UART_UCR_TX_ENABLED
		| MCF_UART_UCR_RX_ENABLED);
	MCF_UART2_UCR = (0
		| MCF_UART_UCR_TX_ENABLED
		| MCF_UART_UCR_RX_ENABLED);

}
/********************************************************************/
