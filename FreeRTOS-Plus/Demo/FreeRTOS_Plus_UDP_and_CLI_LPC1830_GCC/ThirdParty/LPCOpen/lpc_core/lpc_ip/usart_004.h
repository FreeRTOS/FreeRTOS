/*
 * @brief	UART/USART Registers and control functions
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * All rights reserved.
 *
 * @par
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
 * @par
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
 */

#ifndef __USART_004_H_
#define __USART_004_H_

#include "sys_config.h"
#include "cmsis.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup IP_USART_004 IP: USART register block and driver (004)
 * @ingroup IP_Drivers
 * @{
 */

/**
 * @brief USART register block structure
 */
typedef struct {							/*!< USARTn Structure       */

	union {
		__IO uint32_t  DLL;					/*!< Divisor Latch LSB. Least significant byte of the baud rate divisor value. The full divisor is used to generate a baud rate from the fractional rate divider (DLAB = 1). */
		__O  uint32_t  THR;					/*!< Transmit Holding Register. The next character to be transmitted is written here (DLAB = 0). */
		__I  uint32_t  RBR;					/*!< Receiver Buffer Register. Contains the next received character to be read (DLAB = 0). */
	};

	union {
		__IO uint32_t IER;					/*!< Interrupt Enable Register. Contains individual interrupt enable bits for the 7 potential UART interrupts (DLAB = 0). */
		__IO uint32_t DLM;					/*!< Divisor Latch MSB. Most significant byte of the baud rate divisor value. The full divisor is used to generate a baud rate from the fractional rate divider (DLAB = 1). */
	};

	union {
		__O  uint32_t FCR;					/*!< FIFO Control Register. Controls UART FIFO usage and modes. */
		__I  uint32_t IIR;					/*!< Interrupt ID Register. Identifies which interrupt(s) are pending. */
	};

	__IO uint32_t LCR;						/*!< Line Control Register. Contains controls for frame formatting and break generation. */
	__IO uint32_t MCR;						/*!< Modem Control Register. Only present on USART ports with full modem support. */
	__I  uint32_t LSR;						/*!< Line Status Register. Contains flags for transmit and receive status, including line errors. */
	__I  uint32_t MSR;						/*!< Modem Status Register. Only present on USART ports with full modem support. */
	__IO uint32_t SCR;						/*!< Scratch Pad Register. Eight-bit temporary storage for software. */
	__IO uint32_t ACR;						/*!< Auto-baud Control Register. Contains controls for the auto-baud feature. */
	__IO uint32_t ICR;						/*!< IrDA control register (not all UARTS) */
	__IO uint32_t FDR;						/*!< Fractional Divider Register. Generates a clock input for the baud rate divider. */

	__IO uint32_t OSR;						/*!< Oversampling Register. Controls the degree of oversampling during each bit time. Only on some UARTS. */
	__IO uint32_t TER1;						/*!< Transmit Enable Register. Turns off USART transmitter for use with software flow control. */
	uint32_t  RESERVED0[3];
	__IO uint32_t HDEN;						/*!< Half-duplex enable Register- only on some UARTs */
	__I  uint32_t RESERVED1[1];
	__IO uint32_t SCICTRL;					/*!< Smart card interface control register- only on some UARTs */

	__IO uint32_t RS485CTRL;				/*!< RS-485/EIA-485 Control. Contains controls to configure various aspects of RS-485/EIA-485 modes. */
	__IO uint32_t RS485ADRMATCH;			/*!< RS-485/EIA-485 address match. Contains the address match value for RS-485/EIA-485 mode. */
	__IO uint32_t RS485DLY;					/*!< RS-485/EIA-485 direction control delay. */

	union {
		__IO uint32_t SYNCCTRL;				/*!< Synchronous mode control register. Only on USARTs. */
		__I  uint32_t FIFOLVL;				/*!< FIFO Level register. Provides the current fill levels of the transmit and receive FIFOs. */
	};

	__IO uint32_t TER2;						/*!< Transmit Enable Register. Only on LPC177X_8X UART4 and LPC18XX/43XX USART0/2/3. */
} IP_USART_001_T;

#define UART_RBR_MASKBIT    (0xFF)		/*!< UART Received Buffer mask bit (8 bits) */

/**
 * @brief	Basic UART initialization
 * @param	pUART	: Pointer to selected UART peripheral
 * @return	Nothing
 * @note	This function performs very basic UART initialization
 */
void IP_UART_Init(IP_USART_001_T *pUART);

/**
 * @brief	UART de-initialization
 * @param	pUART	: Pointer to selected UART peripheral
 * @return	Nothing
 */
STATIC INLINE void IP_UART_DeInit(IP_USART_001_T *pUART) {}

/**
 * @brief	Transmit a single byte through the UART peripheral
 * @param	pUART	: Pointer to selected UART peripheral
 * @param	data	: Byte to transmit
 * @return	Nothing
 * @note	This function attempts to place a byte into the UART transmit
 *			FIFO or transmit hold register regard regardless of UART state.
 */
STATIC INLINE void IP_UART_SendByte(IP_USART_001_T *pUART, const uint8_t data)
{
	pUART->THR = (uint32_t) data;
}

/**
 * @brief	Get a single data from UART peripheral
 * @param	pUART	: Pointer to selected UART peripheral
 * @return	A single byte of data read
 * @note	This function reads a byte from the UART receive FIFO or
 *			receive hold register regard regardless of UART state.
 */
STATIC INLINE uint8_t IP_UART_ReadByte(IP_USART_001_T *pUART)
{
	return (uint8_t) (pUART->RBR & UART_RBR_MASKBIT);
}

/**
 * @brief Macro defines for UART interrupt enable register
 */
#define UART_IER_RBRINT      (1 << 0)	/*!< RBR Interrupt enable*/
#define UART_IER_THREINT     (1 << 1)	/*!< THR Interrupt enable*/
#define UART_IER_RLSINT      (1 << 2)	/*!< RX line status interrupt enable*/
#define UART_IER_MSINT       (1 << 3)	/*!< Modem status interrupt enable */
#define UART_IER_CTSINT      (1 << 7)	/*!< CTS1 signal transition interrupt enable */
#define UART_IER_ABEOINT     (1 << 8)	/*!< Enables the end of auto-baud interrupt */
#define UART_IER_ABTOINT     (1 << 9)	/*!< Enables the auto-baud time-out interrupt */
#define UART_IER_BITMASK     (0x307)		/*!< UART interrupt enable register bit mask */
#define UART1_IER_BITMASK    (0x38F)		/*!< UART1 interrupt enable register bit mask */

/**
 * @brief	Enable UART interrupts
 * @param	pUART	: Pointer to selected UART peripheral
 * @param	intMask	: Or'ed Interrupts to enable in the Interrupt Enable Register (IER)
 * @return	Nothing
 * @note	Use an Or'ed value of UART_IER_* definitions with this call
 *			to enable specific UART interrupts. The Divisor Latch Access Bit
 *			(DLAB) in LCR must be cleared in order to access the IER register.
 *			This function doesn't alter the DLAB state.
 */
STATIC INLINE void IP_UART_IntEnable(IP_USART_001_T *pUART, uint32_t intMask)
{
	pUART->IER |= intMask;
}

/**
 * @brief	Disable UART interrupts
 * @param	pUART	: Pointer to selected UART peripheral
 * @param	intMask	: Or'ed Interrupts to disable in the Interrupt Enable Register (IER)
 * @return	Nothing
 * @note	Use an Or'ed value of UART_IER_* definitions with this call
 *			to disable specific UART interrupts. The Divisor Latch Access Bit
 *			(DLAB) in LCR must be cleared in order to access the IER register.
 *			This function doesn't alter the DLAB state.
 */
STATIC INLINE void IP_UART_IntDisable(IP_USART_001_T *pUART, uint32_t intMask)
{
	pUART->IER &= ~intMask;
}

/**
 * @brief Macro defines for UART interrupt identification register
 */
#define UART_IIR_INTSTAT_PEND   (1 << 0)	/*!<Interrupt Status - Active low */
#define UART_IIR_INTID_RLS      (3 << 1)	/*!<Interrupt identification: Receive line status*/
#define UART_IIR_INTID_RDA      (2 << 1)	/*!<Interrupt identification: Receive data available*/
#define UART_IIR_INTID_CTI      (6 << 1)	/*!<Interrupt identification: Character time-out indicator*/
#define UART_IIR_INTID_THRE     (1 << 1)	/*!<Interrupt identification: THRE interrupt*/
#define UART_IIR_INTID_MODEM    (0 << 1)	/*!<Interrupt identification: Modem interrupt*/
#define UART_IIR_INTID_MASK     (7 << 1)	/*!<Interrupt identification: Interrupt ID mask */
#define UART_IIR_FIFO_EN        (3 << 6)	/*!<These bits are equivalent to UnFCR[0] */
#define UART_IIR_ABEO_INT       (1 << 8)	/*!< End of auto-baud interrupt */
#define UART_IIR_ABTO_INT       (1 << 9)	/*!< Auto-baud time-out interrupt */
#define UART_IIR_BITMASK        (0x3CF)		/*!< UART interrupt identification register bit mask */

/**
 * @brief	Read the Interrupt Identification Register (IIR)
 * @param	pUART	: Pointer to selected UART peripheral
 * @return	Current pending interrupt status per the IIR register
 */
STATIC INLINE uint32_t IP_UART_ReadIntIDReg(IP_USART_001_T *pUART)
{
	return pUART->IIR;
}

/**
 * @brief Macro defines for UART FIFO control register
 */
#define UART_FCR_FIFO_EN        (1 << 0)	/*!< UART FIFO enable */
#define UART_FCR_RX_RS          (1 << 1)	/*!< UART FIFO RX reset */
#define UART_FCR_TX_RS          (1 << 2)	/*!< UART FIFO TX reset */
#define UART_FCR_DMAMODE_SEL    (1 << 3)	/*!< UART DMA mode selection */
#define UART_FCR_TRG_LEV0       (0)			/*!< UART FIFO trigger level 0: 1 character */
#define UART_FCR_TRG_LEV1       (1 << 6)	/*!< UART FIFO trigger level 1: 4 character */
#define UART_FCR_TRG_LEV2       (2 << 6)	/*!< UART FIFO trigger level 2: 8 character */
#define UART_FCR_TRG_LEV3       (3 << 6)	/*!< UART FIFO trigger level 3: 14 character */
#define UART_FCR_BITMASK        (0xCF)		/*!< UART FIFO control bit mask */
#define UART_TX_FIFO_SIZE       (16)

/**
 * @brief	Setup the UART FIFOs
 * @param	pUART	: Pointer to selected UART peripheral
 * @param	fcr		: FIFO control register setup OR'ed flags
 * @return	Nothing
 * @note	Use an Or'ed value of UART_FCR_* definitions with this call
 *			to select specific options.
 */
STATIC INLINE void IP_UART_SetupFIFOS(IP_USART_001_T *pUART, uint32_t fcr)
{
	pUART->FCR = fcr;
}

/**
 * @brief Macro defines for UART line control register
 */
#define UART_LCR_WLEN5          (0)				/*!< UART 5 bit data mode */
#define UART_LCR_WLEN6          (1 << 0)		/*!< UART 6 bit data mode */
#define UART_LCR_WLEN7          (2 << 0)		/*!< UART 7 bit data mode */
#define UART_LCR_WLEN8          (3 << 0)		/*!< UART 8 bit data mode */
#define UART_LCR_SBS_1BIT       (0 << 2)		/*!< UART One Stop Bit Select */
#define UART_LCR_SBS_2BIT       (1 << 2)		/*!< UART Two Stop Bits Select */
#define UART_LCR_PARITY_EN      (1 << 3)		/*!< UART Parity Enable */
#define UART_LCR_PARITY_DIS     (0 << 3)		/*!< UART Parity Disable */
#define UART_LCR_PARITY_ODD     (0)				/*!< UART Odd Parity Select */
#define UART_LCR_PARITY_EVEN    (1 << 4)		/*!< UART Even Parity Select */
#define UART_LCR_PARITY_F_1     (2 << 4)		/*!< UART force 1 stick parity */
#define UART_LCR_PARITY_F_0     (3 << 4)		/*!< UART force 0 stick parity */
#define UART_LCR_BREAK_EN       (1 << 6)		/*!< UART Transmission Break enable */
#define UART_LCR_DLAB_EN        (1 << 7)		/*!< UART Divisor Latches Access bit enable */
#define UART_LCR_BITMASK        (0xFF)			/*!< UART line control bit mask */

/**
 * @brief	Setup the UART operation mode in the Line Control Register (LCR)
 * @param	pUART	: Pointer to selected UART peripheral
 * @param	lcr		: OR'ed flags
 * @return	Nothing
 * @note	Sets up the UART transmit mode (data bits, stop bits, parity,
 *			and break). Use an Or'ed value of UART_LCR_* definitions with this
 *			call to select specific options. Unless the UART_LCR_DLAB_EN
 *			option is passed in lcd, DLAB will be cleared and divisor access
 *			will be disabled.
 */
STATIC INLINE void IP_UART_SetMode(IP_USART_001_T *pUART, uint32_t lcr)
{
	pUART->LCR = lcr;
}

/**
 * @brief	Enable access to Divisor Latches
 * @param	pUART	: Pointer to selected UART peripheral
 * @return	Nothing
 */
STATIC INLINE void IP_UART_EnableDivisorAccess(IP_USART_001_T *pUART)
{
	pUART->LCR |= UART_LCR_DLAB_EN;
}

/**
 * @brief	Disable access to Divisor Latches
 * @param	pUART	: Pointer to selected UART peripheral
 * @return	Nothing
 */
STATIC INLINE void IP_UART_DisableDivisorAccess(IP_USART_001_T *pUART)
{
	pUART->LCR &= ~UART_LCR_DLAB_EN;
}

#define UART_DLL_MASKBIT    (0xFF)		/*!< Divisor latch LSB (DLL) bit mask */
#define UART_DLM_MASKBIT    (0xFF)		/*!< Divisor latch MSB (DLM) bit mask */

/**
 * @brief	Set LSB and MSB divisor latch registers
 * @param	pUART	: Pointer to selected UART peripheral
 * @param	dll		: Divisor Latch LSB value
 * @param	dlm		: Divisor Latch MSB value
 * @return	Nothing
 * @note	The Divisor Latch Access Bit (DLAB) in LCR must be set in
 *			order to access the USART Divisor Latches. This function
 *			doesn't alter the DLAB state.
 */
STATIC INLINE void IP_UART_SetDivisorLatches(IP_USART_001_T *pUART, uint8_t dll, uint8_t dlm)
{
	pUART->DLL = (uint32_t) dll;
	pUART->DLM = (uint32_t) dlm;
}

/**
 * @brief Macro defines for UART Modem control register
 */
#define UART_MCR_DTR_CTRL       (1 << 0)		/*!< Source for modem output pin DTR */
#define UART_MCR_RTS_CTRL       (1 << 1)		/*!< Source for modem output pin RTS */
#define UART_MCR_LOOPB_EN       (1 << 4)		/*!< Loop back mode select */
#define UART_MCR_AUTO_RTS_EN    (1 << 6)		/*!< Enable Auto RTS flow-control */
#define UART_MCR_AUTO_CTS_EN    (1 << 7)		/*!< Enable Auto CTS flow-control */
#define UART_MCR_BITMASK        (0x0F3)			/*!< UART1 bit mask value */

/**
 * @brief	Return modem control register/status
 * @param	pUART	: Pointer to selected UART peripheral
 * @return	Modem control register (status)
 * @note	Mask bits of the returned status value with UART_MCR_*
 *			definitions for specific statuses.
 */
STATIC INLINE uint32_t IP_UART_ReadModemControl(IP_USART_001_T *pUART)
{
	return pUART->MCR;
}

/**
 * @brief	Set modem control register/status
 * @param	pUART	: Pointer to selected UART peripheral
 * @param	mcr		: Modem control register flags to set
 * @return	Nothing
 * @note	Use an Or'ed value of UART_MCR_* definitions with this
 *			call to set specific options.
 */
STATIC INLINE void IP_UART_SetModemControl(IP_USART_001_T *pUART, uint32_t mcr)
{
	pUART->MCR |= mcr;
}

/**
 * @brief	Clear modem control register/status
 * @param	pUART	: Pointer to selected UART peripheral
 * @param	mcr		: Modem control register flags to clear
 * @return	Nothing
 * @note	Use an Or'ed value of UART_MCR_* definitions with this
 *			call to clear specific options.
 */
STATIC INLINE void IP_UART_ClearModemControl(IP_USART_001_T *pUART, uint32_t mcr)
{
	pUART->MCR &= ~mcr;
}

/**
 * @brief Macro defines for UART line status register
 */
#define UART_LSR_RDR        (1 << 0)	/*!< Line status register: Receive data ready */
#define UART_LSR_OE         (1 << 1)	/*!< Line status register: Overrun error */
#define UART_LSR_PE         (1 << 2)	/*!< Line status register: Parity error */
#define UART_LSR_FE         (1 << 3)	/*!< Line status register: Framing error */
#define UART_LSR_BI         (1 << 4)	/*!< Line status register: Break interrupt */
#define UART_LSR_THRE       (1 << 5)	/*!< Line status register: Transmit holding register empty */
#define UART_LSR_TEMT       (1 << 6)	/*!< Line status register: Transmitter empty */
#define UART_LSR_RXFE       (1 << 7)	/*!< Error in RX FIFO */
#define UART_LSR_BITMASK    (0xFF)		/*!< UART Line status bit mask */

/**
 * @brief	Return Line Status register/status (LSR)
 * @param	pUART	: Pointer to selected UART peripheral
 * @return	Line Status register (status)
 * @note	Mask bits of the returned status value with UART_LSR_*
 *			definitions for specific statuses.
 */
STATIC INLINE uint32_t IP_UART_ReadLineStatus(IP_USART_001_T *pUART)
{
	return pUART->LSR;
}

/**
 * @brief Macro defines for UART Modem status register
 */
#define UART_MSR_DELTA_CTS      (1 << 0)	/*!< Set upon state change of input CTS */
#define UART_MSR_DELTA_DSR      (1 << 1)	/*!< Set upon state change of input DSR */
#define UART_MSR_LO2HI_RI       (1 << 2)	/*!< Set upon low to high transition of input RI */
#define UART_MSR_DELTA_DCD      (1 << 3)	/*!< Set upon state change of input DCD */
#define UART_MSR_CTS            (1 << 4)	/*!< Clear To Send State */
#define UART_MSR_DSR            (1 << 5)	/*!< Data Set Ready State */
#define UART_MSR_RI             (1 << 6)	/*!< Ring Indicator State */
#define UART_MSR_DCD            (1 << 7)	/*!< Data Carrier Detect State */
#define UART_MSR_BITMASK        (0xFF)		/*!< MSR register bit-mask value */

/**
 * @brief	Return Modem Status register/status (MSR)
 * @param	pUART	: Pointer to selected UART peripheral
 * @return	Modem Status register (status)
 * @note	Mask bits of the returned status value with UART_MSR_*
 *			definitions for specific statuses.
 */
STATIC INLINE uint32_t IP_UART_ReadModemStatus(IP_USART_001_T *pUART)
{
	return pUART->MSR;
}

/**
 * @brief	Write a byte to the scratchpad register
 * @param	pUART	: Pointer to selected UART peripheral
 * @param	data	: Byte value to write
 * @return	Nothing
 */
STATIC INLINE void IP_UART_SetScratch(IP_USART_001_T *pUART, uint8_t data)
{
	pUART->SCR = (uint32_t) data;
}

/**
 * @brief	Returns current byte value in the scratchpad register
 * @param	pUART	: Pointer to selected UART peripheral
 * @return	Byte value read from scratchpad register
 */
STATIC INLINE uint8_t IP_UART_ReadScratch(IP_USART_001_T *pUART)
{
	return (uint8_t) (pUART->SCR & 0xFF);
}

/**
 * @brief Macro defines for UART Auto baudrate control register
 */
#define UART_ACR_START              (1 << 0)	/*!< UART Auto-baud start */
#define UART_ACR_MODE               (1 << 1)	/*!< UART Auto baudrate Mode 1 */
#define UART_ACR_AUTO_RESTART       (1 << 2)	/*!< UART Auto baudrate restart */
#define UART_ACR_ABEOINT_CLR        (1 << 8)	/*!< UART End of auto-baud interrupt clear */
#define UART_ACR_ABTOINT_CLR        (1 << 9)	/*!< UART Auto-baud time-out interrupt clear */
#define UART_ACR_BITMASK            (0x307)		/*!< UART Auto Baudrate register bit mask */

/**
 * @brief	Set autobaud register options
 * @param	pUART	: Pointer to selected UART peripheral
 * @param	acr		: Or'ed values to set for ACR register
 * @return	Nothing
 * @note	Use an Or'ed value of UART_ACR_* definitions with this
 *			call to set specific options.
 */
STATIC INLINE void IP_UART_SetAutoBaudReg(IP_USART_001_T *pUART, uint32_t acr)
{
	pUART->ACR |= acr;
}

/**
 * @brief	Clear autobaud register options
 * @param	pUART	: Pointer to selected UART peripheral
 * @param	acr		: Or'ed values to clear for ACR register
 * @return	Nothing
 * @note	Use an Or'ed value of UART_ACR_* definitions with this
 *			call to clear specific options.
 */
STATIC INLINE void IP_UART_ClearAutoBaudReg(IP_USART_001_T *pUART, uint32_t acr)
{
	pUART->ACR &= ~acr;
}

/**
 * @brief	Enable transmission on UART TxD pin
 * @param	pUART	: Pointer to selected UART peripheral
 * @return Nothing
 */
STATIC INLINE void IP_UART_TXEnable(IP_USART_001_T *pUART)
{
	pUART->TER1 = (1 << 7);
}

/**
 * @brief	Disable transmission on UART TxD pin
 * @param	pUART	: Pointer to selected UART peripheral
 * @return Nothing
 */
STATIC INLINE void IP_UART_TXDisable(IP_USART_001_T *pUART)
{
	pUART->TER1 = 0;
}

/**
 * @brief Macro defines for UART1 RS485 Control register
 */
#define UART_RS485CTRL_NMM_EN       (1 << 0)	/*!< RS-485/EIA-485 Normal Multi-drop Mode (NMM) is disabled */
#define UART_RS485CTRL_RX_DIS       (1 << 1)	/*!< The receiver is disabled */
#define UART_RS485CTRL_AADEN        (1 << 2)	/*!< Auto Address Detect (AAD) is enabled */
#define UART_RS485CTRL_SEL_DTR      (1 << 3)	/*!< If direction control is enabled (bit DCTRL = 1), pin DTR is
												        used for direction control */
#define UART_RS485CTRL_DCTRL_EN     (1 << 4)	/*!< Enable Auto Direction Control */
#define UART_RS485CTRL_OINV_1       (1 << 5)	/*!< This bit reverses the polarity of the direction
												       control signal on the RTS (or DTR) pin. The direction control pin
												       will be driven to logic "1" when the transmitter has data to be sent */
#define UART_RS485CTRL_BITMASK      (0x3F)		/*!< RS485 control bit-mask value */

/**
 * @brief	Set RS485 control register options
 * @param	pUART	: Pointer to selected UART peripheral
 * @param	ctrl	: Or'ed values to set for RS485 control register
 * @return	Nothing
 * @note	Use an Or'ed value of UART_RS485CTRL_* definitions with this
 *			call to set specific options.
 */
STATIC INLINE void IP_UART_SetRS485Flags(IP_USART_001_T *pUART, uint32_t ctrl)
{
	pUART->RS485CTRL |= ctrl;
}

/**
 * @brief	Clear RS485 control register options
 * @param	pUART	: Pointer to selected UART peripheral
 * @param	ctrl	: Or'ed values to clear for RS485 control register
 * @return	Nothing
 * @note	Use an Or'ed value of UART_RS485CTRL_* definitions with this
 *			call to clear specific options.
 */
STATIC INLINE void IP_UART_ClearRS485Flags(IP_USART_001_T *pUART, uint32_t ctrl)
{
	pUART->RS485CTRL &= ~ctrl;
}

/**
 * @brief	Set RS485 address match value
 * @param	pUART	: Pointer to selected UART peripheral
 * @param	addr	: Address match value for RS-485/EIA-485 mode
 * @return	Nothing
 */
STATIC INLINE void IP_UART_SetRS485Addr(IP_USART_001_T *pUART, uint8_t addr)
{
	pUART->RS485ADRMATCH = (uint32_t) addr;
}

/**
 * @brief	Read RS485 address match value
 * @param	pUART	: Pointer to selected UART peripheral
 * @return	Address match value for RS-485/EIA-485 mode
 */
STATIC INLINE uint8_t IP_UART_GetRS485Addr(IP_USART_001_T *pUART)
{
	return (uint8_t) (pUART->RS485ADRMATCH & 0xFF);
}

/**
 * @brief	Set RS485 direction control (RTS or DTR) delay value
 * @param	pUART	: Pointer to selected UART peripheral
 * @param	dly		: direction control (RTS or DTR) delay value
 * @return	Nothing
 * @note	This delay time is in periods of the baud clock. Any delay
 *			time from 0 to 255 bit times may be programmed.
 */
STATIC INLINE void IP_UART_SetRS485Delay(IP_USART_001_T *pUART, uint8_t dly)
{
	pUART->RS485DLY = (uint32_t) dly;
}

/**
 * @brief	Read RS485 direction control (RTS or DTR) delay value
 * @param	pUART	: Pointer to selected UART peripheral
 * @return	direction control (RTS or DTR) delay value
 * @note	This delay time is in periods of the baud clock. Any delay
 *			time from 0 to 255 bit times may be programmed.
 */
STATIC INLINE uint8_t IP_UART_GetRS485Delay(IP_USART_001_T *pUART)
{
	return (uint8_t) (pUART->RS485DLY & 0xFF);
}

/**
 * @brief	Determines and sets best dividers to get a target bit rate
 * @param	pUART		: Pointer to selected UART peripheral
 * @param	baudrate	: Target baud rate (baud rate = bit rate)
 * @param	uClk		: Clock rate into UART peripheral
 * @return	The actual baud rate, or 0 if no rate can be found
 * @note	Once you've computed your baud rate, you can remove this function
 *			to make your image smaller.
 */
uint32_t IP_UART_SetBaud(IP_USART_001_T *pUART, uint32_t baudrate, uint32_t uClk);

#if 0	// FIXME
// FIXME
// FDR handled at chip layer
// OSR not ready
// TER1 not ready
// HDEN handled at chip layer
// SCICTRL handled at chip layer
// TER2 handled at chip layer

/**
 * @brief Macro defines for UART IrDA control register
 */
#define UART_ICR_IRDAEN         ((uint32_t) (1 << 0))			/*!< IrDA mode enable */
#define UART_ICR_IRDAINV        ((uint32_t) (1 << 1))			/*!< IrDA serial input inverted */
#define UART_ICR_FIXPULSE_EN    ((uint32_t) (1 << 2))			/*!< IrDA fixed pulse width mode */
#define UART_ICR_PULSEDIV(n)    ((uint32_t) ((n & 0x07) << 3))	/*!< PulseDiv - Configures the pulse when FixPulseEn = 1 */
#define UART_ICR_BITMASK        ((uint32_t) (0x3F))				/*!< UART IRDA bit mask */

/**
 * @brief Macro defines for UART half duplex register
 */
#define UART_HDEN_HDEN          ((uint32_t) (1 << 0))			/*!< enable half-duplex mode*/

/**
 * @brief Macro defines for UART smart card interface control register
 */
#define UART_SCICTRL_SCIEN      ((uint32_t) (1 << 0))				/*!< enable asynchronous half-duplex smart card interface*/
#define UART_SCICTRL_NACKDIS    ((uint32_t) (1 << 1))				/*!< NACK response is inhibited*/
#define UART_SCICTRL_PROTSEL_T1 ((uint32_t) (1 << 2))				/*!< ISO7816-3 protocol T1 is selected*/
#define UART_SCICTRL_TXRETRY(n) ((uint32_t) ((n & 0x07) << 5))		/*!< number of retransmission*/
#define UART_SCICTRL_GUARDTIME(n)   ((uint32_t) ((n & 0xFF) << 8))	/*!< Extra guard time*/

/**
 * @brief Macro defines for UART Fractional divider register
 */
#define UART_FDR_DIVADDVAL(n)   ((uint32_t) (n & 0x0F))			/*!< Baud-rate generation pre-scaler divisor */
#define UART_FDR_MULVAL(n)      ((uint32_t) ((n << 4) & 0xF0))	/*!< Baud-rate pre-scaler multiplier value */
#define UART_FDR_BITMASK        ((uint32_t) (0xFF))				/*!< UART Fractional Divider register bit mask */

/**
 * @brief Macro defines for UART Tx Enable register
 */
#define UART_TER1_TXEN          ((uint8_t) (1 << 7))		/*!< Transmit enable bit */
#define UART_TER1_BITMASK       ((uint8_t) (0x80))			/*!< UART Transmit Enable Register bit mask */
#define UART_TER2_TXEN      ((uint8_t) (1 << 0))			/*!< Transmit enable bit */
#define UART_TER2_BITMASK   ((uint8_t) (0x01))				/*!< UART Transmit Enable Register bit mask */

/**
 * @brief Macro defines for UART synchronous control register
 */
#define UART_SYNCCTRL_SYNC      ((uint32_t) (1 << 0))			/*!< enable synchronous mode*/
#define UART_SYNCCTRL_CSRC_MASTER   ((uint32_t) (1 << 1))		/*!< synchronous master mode*/
#define UART_SYNCCTRL_FES       ((uint32_t) (1 << 2))			/*!< sample on falling edge*/
#define UART_SYNCCTRL_TSBYPASS  ((uint32_t) (1 << 3))			/*!< to be defined*/
#define UART_SYNCCTRL_CSCEN     ((uint32_t) (1 << 4))			/*!< continuous running clock enable (master mode only)*/
#define UART_SYNCCTRL_STARTSTOPDISABLE  ((uint32_t) (1 << 5))	/*!< do not send start/stop bit*/
#define UART_SYNCCTRL_CCCLR     ((uint32_t) (1 << 6))			/*!< stop continuous clock*/

#endif

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __USART_004_H_ */
