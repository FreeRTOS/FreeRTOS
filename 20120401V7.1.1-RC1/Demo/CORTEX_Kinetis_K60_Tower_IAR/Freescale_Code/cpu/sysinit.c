/*
 * File:        sysinit.c
 * Purpose:     Kinetis Configuration
 *              Initializes processor to a default state
 *
 * Notes:
 *
 */

#include "common.h"
#include "sysinit.h"
#include "uart.h"

/********************************************************************/

/* Actual system clock frequency */
int core_clk_khz;
int core_clk_mhz;
int periph_clk_khz;

/********************************************************************/
void sysinit (void)
{
        /*
         * Enable all of the port clocks. These have to be enabled to configure
         * pin muxing options, so most code will need all of these on anyway.
         */
        SIM_SCGC5 |= (SIM_SCGC5_PORTA_MASK
                      | SIM_SCGC5_PORTB_MASK
                      | SIM_SCGC5_PORTC_MASK
                      | SIM_SCGC5_PORTD_MASK
                      | SIM_SCGC5_PORTE_MASK );

 	/* Ramp up the system clock */
	core_clk_mhz = pll_init(CORE_CLK_MHZ, REF_CLK);

	/*
         * Use the value obtained from the pll_init function to define variables
	 * for the core clock in kHz and also the peripheral clock. These
	 * variables can be used by other functions that need awareness of the
	 * system frequency.
	 */
	core_clk_khz = core_clk_mhz * 1000;
  	periph_clk_khz = core_clk_khz / (((SIM_CLKDIV1 & SIM_CLKDIV1_OUTDIV2_MASK) >> 24)+ 1);

  	/* For debugging purposes, enable the trace clock and/or FB_CLK so that
  	 * we'll be able to monitor clocks and know the PLL is at the frequency
  	 * that we expect.
  	 */
	trace_clk_init();
  	fb_clk_init();

  	/* Enable the pins for the selected UART */
         if (TERM_PORT == UART0_BASE_PTR)
         {
            /* Enable the UART0_TXD function on PTD6 */
            PORTD_PCR6 = PORT_PCR_MUX(0x3); // UART is alt3 function for this pin

            /* Enable the UART0_RXD function on PTD7 */
            PORTD_PCR7 = PORT_PCR_MUX(0x3); // UART is alt3 function for this pin
         }

         if (TERM_PORT == UART1_BASE_PTR)
  	 {
                 /* Enable the UART1_TXD function on PTC4 */
  		PORTC_PCR4 = PORT_PCR_MUX(0x3); // UART is alt3 function for this pin

  		/* Enable the UART1_RXD function on PTC3 */
  		PORTC_PCR3 = PORT_PCR_MUX(0x3); // UART is alt3 function for this pin
  	}

  	if (TERM_PORT == UART2_BASE_PTR)
  	{
                 /* Enable the UART2_TXD function on PTD3 */
  		PORTD_PCR3 = PORT_PCR_MUX(0x3); // UART is alt3 function for this pin

  		/* Enable the UART2_RXD function on PTD2 */
  		PORTD_PCR2 = PORT_PCR_MUX(0x3); // UART is alt3 function for this pin
  	}

  	if (TERM_PORT == UART3_BASE_PTR)
  	{
                 /* Enable the UART3_TXD function on PTC17 */
  		PORTC_PCR17 = PORT_PCR_MUX(0x3); // UART is alt3 function for this pin

  		/* Enable the UART3_RXD function on PTC16 */
  		PORTC_PCR16 = PORT_PCR_MUX(0x3); // UART is alt3 function for this pin
  	}
  	if (TERM_PORT == UART4_BASE_PTR)
  	{
                 /* Enable the UART3_TXD function on PTC17 */
  		PORTE_PCR24 = PORT_PCR_MUX(0x3); // UART is alt3 function for this pin

  		/* Enable the UART3_RXD function on PTC16 */
  		PORTE_PCR25 = PORT_PCR_MUX(0x3); // UART is alt3 function for this pin
  	}
  	if (TERM_PORT == UART5_BASE_PTR)
  	{
                 /* Enable the UART3_TXD function on PTC17 */
  		PORTE_PCR8 = PORT_PCR_MUX(0x3); // UART is alt3 function for this pin

  		/* Enable the UART3_RXD function on PTC16 */
  		PORTE_PCR9 = PORT_PCR_MUX(0x3); // UART is alt3 function for this pin
  	}
  	/* UART0 and UART1 are clocked from the core clock, but all other UARTs are
         * clocked from the peripheral clock. So we have to determine which clock
         * to send to the uart_init function.
         */
        if ((TERM_PORT == UART0_BASE_PTR) | (TERM_PORT == UART1_BASE_PTR))
            uart_init (TERM_PORT, core_clk_khz, TERMINAL_BAUD);
        else
  	    uart_init (TERM_PORT, periph_clk_khz, TERMINAL_BAUD);
}
/********************************************************************/
void trace_clk_init(void)
{
	/* Set the trace clock to the core clock frequency */
	SIM_SOPT2 |= SIM_SOPT2_TRACECLKSEL_MASK;

	/* Enable the TRACE_CLKOUT pin function on PTA6 (alt7 function) */
	PORTA_PCR6 = ( PORT_PCR_MUX(0x7));
}
/********************************************************************/
void fb_clk_init(void)
{
	/* Enable the clock to the FlexBus module */
        SIM_SCGC7 |= SIM_SCGC7_FLEXBUS_MASK;

 	/* Enable the FB_CLKOUT function on PTC3 (alt5 function) */
	PORTC_PCR3 = ( PORT_PCR_MUX(0x5));
}
/********************************************************************/
