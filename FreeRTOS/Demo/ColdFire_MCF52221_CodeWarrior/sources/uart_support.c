/*
 * File:        uart_support.c
 * Purpose:     Implements UART basic support, Derivative Specific Interrupt handler and need function needed 
 *              for MSL Support (printf\cout to terminal), defined in <UART.h>
 *
 * Notes:       
 *              
 */
#include "support_common.h"
#include "uart_support.h"

#if ENABLE_UART_SUPPORT==1


#if UART_SUPPORT_TYPE==UART_PSC
/* 5475 & 5485 boards have different names for uart access registers */
void uart_init(int channel, unsigned long systemClockKHz, unsigned long baudRate)
{
	register uint16 ubgs;

	/* 
	 * On Verdi, only PSC 0 & 1 are brought out to RS232 transceivers
	 */

	/* Put PSC in UART mode */
	MCF_PSC_PSCSICR(channel) = MCF_PSC_PSCSICR_SIM_UART;

	/* Rx and Tx baud rate from timers */
	MCF_PSC_PSCCSR(channel) = (0
		| MCF_PSC_PSCCSR_RCSEL_SYS_CLK 
		| MCF_PSC_PSCCSR_TCSEL_SYS_CLK);

	/*
	 * Calculate baud settings
	 */
	ubgs = (uint16)((systemClockKHz * 1000)/(baudRate * 32));

	MCF_PSC_PSCCTUR(channel) =  (uint8) ((ubgs >> 8) & 0xFF);
	MCF_PSC_PSCCTLR(channel) =  (uint8) (ubgs & 0xFF);

	/* Reset transmitter, receiver, mode register, and error conditions */
	MCF_PSC_PSCCR(channel) = MCF_PSC_PSCCR_RESET_RX;
	MCF_PSC_PSCCR(channel) = MCF_PSC_PSCCR_RESET_TX;
	MCF_PSC_PSCCR(channel) = MCF_PSC_PSCCR_RESET_ERROR;
	MCF_PSC_PSCCR(channel) = MCF_PSC_PSCCR_RESET_BKCHGINT;
	MCF_PSC_PSCCR(channel) = MCF_PSC_PSCCR_RESET_MR;

	/* 8-bit data, no parity */
	MCF_PSC_PSCMR(channel) = (0
#ifdef UART_HARDWARE_FLOW_CONTROL
		| MCF_PSC_PSCMR_RXRTS
#endif
		| MCF_PSC_PSCMR_PM_NONE
		| MCF_PSC_PSCMR_BC_8);

	/* No echo or loopback, 1 stop bit */
	MCF_PSC_PSCMR(channel) = (0
#ifdef UART_HARDWARE_FLOW_CONTROL
		| MCF_PSC_PSCMR_TXCTS
#endif 
		| MCF_PSC_PSCMR_CM_NORMAL
		| MCF_PSC_PSCMR_SB_STOP_BITS_1);

	/* Mask all UART interrupts */
	MCF_PSC_PSCIMR(channel) = 0x0000;

	/* Enable RTS to send */
	MCF_PSC_PSCOPSET(channel) = MCF_PSC_PSCOPSET_RTS;

	/* Setup FIFO Alarms */
	MCF_PSC_PSCRFAR(channel) = MCF_PSC_PSCRFAR_ALARM(248);
	MCF_PSC_PSCTFAR(channel) = MCF_PSC_PSCTFAR_ALARM(248);

	/* Enable receiver and transmitter */
	MCF_PSC_PSCCR(channel) =(0
		| MCF_PSC_PSCCR_RX_ENABLED
		| MCF_PSC_PSCCR_TX_ENABLED);
}

/********************************************************************/
/*
 * Wait for a character to be received on the specified UART
 *
 * Return Values:
 *  the received character
 */
char uart_getchar (int channel)
{
	/* Wait until character has been received */
	while (!(MCF_PSC_PSCSR(channel) & MCF_PSC_PSCSR_RXRDY))
	{
	
	}
	return (char)(*((uint8 *) &MCF_PSC_PSCRB_8BIT(channel)));
}

/********************************************************************/
/*
 * Wait for space in the UART Tx FIFO and then send a character
 */ 
void uart_putchar (int channel, char ch)
{
	/* Wait until space is available in the FIFO */
	while (!(MCF_PSC_PSCSR(channel) & MCF_PSC_PSCSR_TXRDY))
		;
	*((uint8 *) &MCF_PSC_PSCTB_8BIT(channel)) = (uint8)ch;
}


#else /* UART_SUPPORT_TYPE==UART_PSC */

#if UART_SUPPORT_TYPE == UART_5407
/********************************************************************/
/* 
 * 5407 derivative doesn't have macros to access URB/UTB by channel number 
 * because they have different sizes for UART0 & UART1
 * But in UART mode only 8 bits of UART1 URB/UTB is used, so define these macros here
 *  if they doesn't defined before
 */
#ifndef MCF_UART_URB
#define MCF_UART_URB(x)                      (*(vuint8 *)(&__MBAR[0x1CC + ((x)*0x40)]))
#endif /* MCF_UART_URB */

#ifndef MCF_UART_UTB
#define MCF_UART_UTB(x)                      (*(vuint8 *)(&__MBAR[0x1CC + ((x)*0x40)]))
#endif /* MCF_UART_UTB */

#endif /* UART_SUPPORT_TYPE == UART_5407 */

void uart_init(int channel, unsigned long systemClockKHz, unsigned long baudRate)
{
	/*
	 * Initialize UART for serial communications
	 */

	register uint16 ubgs;

#if UART_SUPPORT_TYPE==UART_54451
	uint32 vco;
	uint32 divider;
	uint32 bus_clk;

	divider = ((MCF_CLOCK_PCR & 0x000000F0) >> 4) + 1;
	vco = ((MCF_CLOCK_PCR >> 24) * systemClockKHz * 1000);
	bus_clk = (vco / divider);
#endif
	/*
	 * Reset Transmitter
	 */
	MCF_UART_UCR(channel) = MCF_UART_UCR_RESET_TX;

	/*
	 * Reset Receiver
	 */
	MCF_UART_UCR(channel) = MCF_UART_UCR_RESET_RX;

	/*
	 * Reset Mode Register
	 */
	MCF_UART_UCR(channel) = MCF_UART_UCR_RESET_MR;

	/*
	 * No parity, 8-bits per character
	 */
	MCF_UART_UMR(channel) = (0
		| MCF_UART_UMR_PM_NONE
		| MCF_UART_UMR_BC_8 );

	/*
	 * No echo or loopback, 1 stop bit
	 */
	MCF_UART_UMR(channel) = (0
		| MCF_UART_UMR_CM_NORMAL
		| MCF_UART_UMR_SB_STOP_BITS_1);

	/*
	 * Set Rx and Tx baud by SYSTEM CLOCK
	 */
	MCF_UART_UCSR(channel) = (0
		| MCF_UART_UCSR_RCS_SYS_CLK
		| MCF_UART_UCSR_TCS_SYS_CLK);

	/*
	 * Mask all UART interrupts
	 */
	MCF_UART_UIMR(channel) = 0;

	/*
	 * Calculate baud settings
	 */
#if UART_SUPPORT_TYPE==UART_54451
	ubgs = (uint16)(((bus_clk >> 5) + (baudRate >> 1)) / baudRate);
#else
	ubgs = (uint16)((systemClockKHz * 1000)/(baudRate * 32));
#endif

#if UART_SUPPORT_TYPE==UART_DIVIDER || UART_SUPPORT_TYPE == UART_5407
	MCF_UART_UDU(channel) = (uint8)((ubgs & 0xFF00) >> 8);
	MCF_UART_UDL(channel) = (uint8)(ubgs & 0x00FF);
#else /* UART_SUPPORT_TYPE!=UART_DIVIDER */
	MCF_UART_UBG1(channel) = (uint8)((ubgs & 0xFF00) >> 8);
	MCF_UART_UBG2(channel) = (uint8)(ubgs & 0x00FF);
#endif /* UART_SUPPORT_TYPE==UART_DIVIDER */

	/*
	 * Enable receiver and transmitter
	 */
	MCF_UART_UCR(channel) = (0
		| MCF_UART_UCR_TX_ENABLED
		| MCF_UART_UCR_RX_ENABLED);
}

/********************************************************************/
/*
 * Wait for a character to be received on the specified UART
 *
 * Return Values:
 *  the received character
 */
char uart_getchar (int channel)
{
    /* Wait until character has been received */
    while (!(MCF_UART_USR(channel) & MCF_UART_USR_RXRDY)) 
    {
    	
    };

    return (char)MCF_UART_URB(channel);
}

/********************************************************************/
/*
 * Wait for space in the UART Tx FIFO and then send a character
 */ 
void uart_putchar (int channel, char ch)
{
    /* Wait until space is available in the FIFO */
    while (!(MCF_UART_USR(channel) & MCF_UART_USR_TXRDY)) 
    {
    	
    };

    /* Send the character */
    MCF_UART_UTB(channel) = (uint8)ch;
}

#endif /* UART_SUPPORT_TYPE==UART_PSC */
/********************************************************************/

/********************************************************************/
/** <UART.h> Neeeded functions                                     **/
/********************************************************************/

/****************************************************************************/
/*
 * Implementation for CodeWarror MSL interface to serial device (UART.h). 
 * Needed for printf, etc...
 * Only InitializeUART, ReadUARTN, and WriteUARTN are implemented.
 *
 */
UARTError InitializeUART(UARTBaudRate baudRate)
{
#if UART_SUPPORT_TYPE==UART_54451
	baudRate = kBaud115200;
#endif
	uart_init(TERMINAL_PORT, SYSTEM_CLOCK_KHZ, baudRate);
	return kUARTNoError;
}

/****************************************************************************/
/*
	ReadUARTN
	
	Read N bytes from the UART.
	
	bytes			pointer to result buffer
	limit			size of buffer and # of bytes to read
*/
/****************************************************************************/
UARTError ReadUARTN(void* bytes, unsigned long limit)
{
	int count;
	for (count = 0; count < limit; count++) {
    	*( (char *)bytes + count ) = uart_getchar(TERMINAL_PORT);
  	}
	return kUARTNoError;
}

/****************************************************************************/
UARTError WriteUARTN(const void* bytes, unsigned long length)
{
	int count;
	for (count = 0; count < length; count++) {
		uart_putchar(TERMINAL_PORT, *( ((char *)bytes) + count));
	}
	return kUARTNoError;
}
#endif /* ENABLE_UART_SUPPORT */
