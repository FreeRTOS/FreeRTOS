/******************************************************************************
*
* (c) Copyright 2010-13 Xilinx, Inc. All rights reserved.
*
* This file contains confidential and proprietary information of Xilinx, Inc.
* and is protected under U.S. and international copyright and other
* intellectual property laws.
*
* DISCLAIMER
* This disclaimer is not a license and does not grant any rights to the
* materials distributed herewith. Except as otherwise provided in a valid
* license issued to you by Xilinx, and to the maximum extent permitted by
* applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
* FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS,
* IMPLIED, OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF
* MERCHANTABILITY, NON-INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE;
* and (2) Xilinx shall not be liable (whether in contract or tort, including
* negligence, or under any other theory of liability) for any loss or damage
* of any kind or nature related to, arising under or in connection with these
* materials, including for any direct, or any indirect, special, incidental,
* or consequential loss or damage (including loss of data, profits, goodwill,
* or any type of loss or damage suffered as a result of any action brought by
* a third party) even if such damage or loss was reasonably foreseeable or
* Xilinx had been advised of the possibility of the same.
*
* CRITICAL APPLICATIONS
* Xilinx products are not designed or intended to be fail-safe, or for use in
* any application requiring fail-safe performance, such as life-support or
* safety devices or systems, Class III medical devices, nuclear facilities,
* applications related to the deployment of airbags, or any other applications
* that could lead to death, personal injury, or severe property or
* environmental damage (individually and collectively, "Critical
* Applications"). Customer assumes the sole risk and liability of any use of
* Xilinx products in Critical Applications, subject only to applicable laws
* and regulations governing limitations on product liability.
*
* THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE
* AT ALL TIMES.
*
******************************************************************************/
/*****************************************************************************/
/**
*
* @file xuartps_hw.h
*
* This header file contains the hardware interface of an XUartPs device.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- ------ -------- ----------------------------------------------
* 1.00	drg/jz 01/12/10 First Release
* 1.03a sg     09/04/12 Added defines for XUARTPS_IXR_TOVR,  XUARTPS_IXR_TNFUL
*			and XUARTPS_IXR_TTRIG.
*			Modified the names of these defines
*			XUARTPS_MEDEMSR_DCDX to XUARTPS_MODEMSR_DDCD
*			XUARTPS_MEDEMSR_RIX to XUARTPS_MODEMSR_TERI
*			XUARTPS_MEDEMSR_DSRX to XUARTPS_MODEMSR_DDSR
*			XUARTPS_MEDEMSR_CTSX to XUARTPS_MODEMSR_DCTS
* 1.05a hk     08/22/13 Added prototype for uart reset and related
*			constant definitions.
*
* </pre>
*
******************************************************************************/
#ifndef XUARTPS_HW_H		/* prevent circular inclusions */
#define XUARTPS_HW_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"

/************************** Constant Definitions *****************************/

/** @name Register Map
 *
 * Register offsets for the UART.
 * @{
 */
#define XUARTPS_CR_OFFSET	0x00  /**< Control Register [8:0] */
#define XUARTPS_MR_OFFSET	0x04  /**< Mode Register [9:0] */
#define XUARTPS_IER_OFFSET	0x08  /**< Interrupt Enable [12:0] */
#define XUARTPS_IDR_OFFSET	0x0C  /**< Interrupt Disable [12:0] */
#define XUARTPS_IMR_OFFSET	0x10  /**< Interrupt Mask [12:0] */
#define XUARTPS_ISR_OFFSET	0x14  /**< Interrupt Status [12:0]*/
#define XUARTPS_BAUDGEN_OFFSET	0x18  /**< Baud Rate Generator [15:0] */
#define XUARTPS_RXTOUT_OFFSET	0x1C  /**< RX Timeout [7:0] */
#define XUARTPS_RXWM_OFFSET	0x20  /**< RX FIFO Trigger Level [5:0] */
#define XUARTPS_MODEMCR_OFFSET	0x24  /**< Modem Control [5:0] */
#define XUARTPS_MODEMSR_OFFSET	0x28  /**< Modem Status [8:0] */
#define XUARTPS_SR_OFFSET	0x2C  /**< Channel Status [14:0] */
#define XUARTPS_FIFO_OFFSET	0x30  /**< FIFO [7:0] */
#define XUARTPS_BAUDDIV_OFFSET	0x34  /**< Baud Rate Divider [7:0] */
#define XUARTPS_FLOWDEL_OFFSET	0x38  /**< Flow Delay [5:0] */
#define XUARTPS_TXWM_OFFSET	0x44  /**< TX FIFO Trigger Level [5:0] */
/* @} */

/** @name Control Register
 *
 * The Control register (CR) controls the major functions of the device.
 *
 * Control Register Bit Definition
 */

#define XUARTPS_CR_STOPBRK	0x00000100  /**< Stop transmission of break */
#define XUARTPS_CR_STARTBRK	0x00000080  /**< Set break */
#define XUARTPS_CR_TORST	0x00000040  /**< RX timeout counter restart */
#define XUARTPS_CR_TX_DIS	0x00000020  /**< TX disabled. */
#define XUARTPS_CR_TX_EN	0x00000010  /**< TX enabled */
#define XUARTPS_CR_RX_DIS	0x00000008  /**< RX disabled. */
#define XUARTPS_CR_RX_EN	0x00000004  /**< RX enabled */
#define XUARTPS_CR_EN_DIS_MASK	0x0000003C  /**< Enable/disable Mask */
#define XUARTPS_CR_TXRST	0x00000002  /**< TX logic reset */
#define XUARTPS_CR_RXRST	0x00000001  /**< RX logic reset */
/* @}*/


/** @name Mode Register
 *
 * The mode register (MR) defines the mode of transfer as well as the data
 * format. If this register is modified during transmission or reception,
 * data validity cannot be guaranteed.
 *
 * Mode Register Bit Definition
 * @{
 */
#define XUARTPS_MR_CCLK			0x00000400 /**< Input clock selection */
#define XUARTPS_MR_CHMODE_R_LOOP	0x00000300 /**< Remote loopback mode */
#define XUARTPS_MR_CHMODE_L_LOOP	0x00000200 /**< Local loopback mode */
#define XUARTPS_MR_CHMODE_ECHO		0x00000100 /**< Auto echo mode */
#define XUARTPS_MR_CHMODE_NORM		0x00000000 /**< Normal mode */
#define XUARTPS_MR_CHMODE_SHIFT			8  /**< Mode shift */
#define XUARTPS_MR_CHMODE_MASK		0x00000300 /**< Mode mask */
#define XUARTPS_MR_STOPMODE_2_BIT	0x00000080 /**< 2 stop bits */
#define XUARTPS_MR_STOPMODE_1_5_BIT	0x00000040 /**< 1.5 stop bits */
#define XUARTPS_MR_STOPMODE_1_BIT	0x00000000 /**< 1 stop bit */
#define XUARTPS_MR_STOPMODE_SHIFT		6  /**< Stop bits shift */
#define XUARTPS_MR_STOPMODE_MASK	0x000000A0 /**< Stop bits mask */
#define XUARTPS_MR_PARITY_NONE		0x00000020 /**< No parity mode */
#define XUARTPS_MR_PARITY_MARK		0x00000018 /**< Mark parity mode */
#define XUARTPS_MR_PARITY_SPACE		0x00000010 /**< Space parity mode */
#define XUARTPS_MR_PARITY_ODD		0x00000008 /**< Odd parity mode */
#define XUARTPS_MR_PARITY_EVEN		0x00000000 /**< Even parity mode */
#define XUARTPS_MR_PARITY_SHIFT			3  /**< Parity setting shift */
#define XUARTPS_MR_PARITY_MASK		0x00000038 /**< Parity mask */
#define XUARTPS_MR_CHARLEN_6_BIT	0x00000006 /**< 6 bits data */
#define XUARTPS_MR_CHARLEN_7_BIT	0x00000004 /**< 7 bits data */
#define XUARTPS_MR_CHARLEN_8_BIT	0x00000000 /**< 8 bits data */
#define XUARTPS_MR_CHARLEN_SHIFT		1  /**< Data Length shift */
#define XUARTPS_MR_CHARLEN_MASK		0x00000006 /**< Data length mask */
#define XUARTPS_MR_CLKSEL		0x00000001 /**< Input clock selection */
/* @} */


/** @name Interrupt Registers
 *
 * Interrupt control logic uses the interrupt enable register (IER) and the
 * interrupt disable register (IDR) to set the value of the bits in the
 * interrupt mask register (IMR). The IMR determines whether to pass an
 * interrupt to the interrupt status register (ISR).
 * Writing a 1 to IER Enbables an interrupt, writing a 1 to IDR disables an
 * interrupt. IMR and ISR are read only, and IER and IDR are write only.
 * Reading either IER or IDR returns 0x00.
 *
 * All four registers have the same bit definitions.
 *
 * @{
 */
#define XUARTPS_IXR_TOVR	0x00001000 /**< Tx FIFO Overflow interrupt */
#define XUARTPS_IXR_TNFUL	0x00000800 /**< Tx FIFO Nearly Full interrupt */
#define XUARTPS_IXR_TTRIG	0x00000400 /**< Tx Trig interrupt */
#define XUARTPS_IXR_DMS		0x00000200 /**< Modem status change interrupt */
#define XUARTPS_IXR_TOUT	0x00000100 /**< Timeout error interrupt */
#define XUARTPS_IXR_PARITY 	0x00000080 /**< Parity error interrupt */
#define XUARTPS_IXR_FRAMING	0x00000040 /**< Framing error interrupt */
#define XUARTPS_IXR_OVER	0x00000020 /**< Overrun error interrupt */
#define XUARTPS_IXR_TXFULL 	0x00000010 /**< TX FIFO full interrupt. */
#define XUARTPS_IXR_TXEMPTY	0x00000008 /**< TX FIFO empty interrupt. */
#define XUARTPS_IXR_RXFULL 	0x00000004 /**< RX FIFO full interrupt. */
#define XUARTPS_IXR_RXEMPTY	0x00000002 /**< RX FIFO empty interrupt. */
#define XUARTPS_IXR_RXOVR  	0x00000001 /**< RX FIFO trigger interrupt. */
#define XUARTPS_IXR_MASK	0x00001FFF /**< Valid bit mask */
/* @} */


/** @name Baud Rate Generator Register
 *
 * The baud rate generator control register (BRGR) is a 16 bit register that
 * controls the receiver bit sample clock and baud rate.
 * Valid values are 1 - 65535.
 *
 * Bit Sample Rate = CCLK / BRGR, where the CCLK is selected by the MR_CCLK bit
 * in the MR register.
 * @{
 */
#define XUARTPS_BAUDGEN_DISABLE		0x00000000 /**< Disable clock */
#define XUARTPS_BAUDGEN_MASK		0x0000FFFF /**< Valid bits mask */
#define XUARTPS_BAUDGEN_RESET_VAL	0x0000028B /**< Reset value */

/** @name Baud Divisor Rate register
 *
 * The baud rate divider register (BDIV) controls how much the bit sample
 * rate is divided by. It sets the baud rate.
 * Valid values are 0x04 to 0xFF. Writing a value less than 4 will be ignored.
 *
 * Baud rate = CCLK / ((BAUDDIV + 1) x BRGR), where the CCLK is selected by
 * the MR_CCLK bit in the MR register.
 * @{
 */
#define XUARTPS_BAUDDIV_MASK        0x000000FF	/**< 8 bit baud divider mask */
#define XUARTPS_BAUDDIV_RESET_VAL   0x0000000F	/**< Reset value */
/* @} */


/** @name Receiver Timeout Register
 *
 * Use the receiver timeout register (RTR) to detect an idle condition on
 * the receiver data line.
 *
 * @{
 */
#define XUARTPS_RXTOUT_DISABLE		0x00000000  /**< Disable time out */
#define XUARTPS_RXTOUT_MASK		0x000000FF  /**< Valid bits mask */

/** @name Receiver FIFO Trigger Level Register
 *
 * Use the Receiver FIFO Trigger Level Register (RTRIG) to set the value at
 * which the RX FIFO triggers an interrupt event.
 * @{
 */

#define XUARTPS_RXWM_DISABLE	0x00000000  /**< Disable RX trigger interrupt */
#define XUARTPS_RXWM_MASK	0x0000003F  /**< Valid bits mask */
#define XUARTPS_RXWM_RESET_VAL	0x00000020  /**< Reset value */
/* @} */

/** @name Transmit FIFO Trigger Level Register
 *
 * Use the Transmit FIFO Trigger Level Register (TTRIG) to set the value at
 * which the TX FIFO triggers an interrupt event.
 * @{
 */

#define XUARTPS_TXWM_MASK	0x0000003F  /**< Valid bits mask */
#define XUARTPS_TXWM_RESET_VAL	0x00000020  /**< Reset value */
/* @} */

/** @name Modem Control Register
 *
 * This register (MODEMCR) controls the interface with the modem or data set,
 * or a peripheral device emulating a modem.
 *
 * @{
 */
#define XUARTPS_MODEMCR_FCM	0x00000010  /**< Flow control mode */
#define XUARTPS_MODEMCR_RTS	0x00000002  /**< Request to send */
#define XUARTPS_MODEMCR_DTR	0x00000001  /**< Data terminal ready */
/* @} */

/** @name Modem Status Register
 *
 * This register (MODEMSR) indicates the current state of the control lines
 * from a modem, or another peripheral device, to the CPU. In addition, four
 * bits of the modem status register provide change information. These bits
 * are set to a logic 1 whenever a control input from the modem changes state.
 *
 * Note: Whenever the DCTS, DDSR, TERI, or DDCD bit is set to logic 1, a modem
 * status interrupt is generated and this is reflected in the modem status
 * register.
 *
 * @{
 */
#define XUARTPS_MODEMSR_FCMS	0x00000100  /**< Flow control mode (FCMS) */
#define XUARTPS_MODEMSR_DCD	0x00000080  /**< Complement of DCD input */
#define XUARTPS_MODEMSR_RI	0x00000040  /**< Complement of RI input */
#define XUARTPS_MODEMSR_DSR	0x00000020  /**< Complement of DSR input */
#define XUARTPS_MODEMSR_CTS	0x00000010  /**< Complement of CTS input */
#define XUARTPS_MODEMSR_DDCD	0x00000008  /**< Delta DCD indicator */
#define XUARTPS_MODEMSR_TERI	0x00000004  /**< Trailing Edge Ring Indicator */
#define XUARTPS_MODEMSR_DDSR	0x00000002  /**< Change of DSR */
#define XUARTPS_MODEMSR_DCTS	0x00000001  /**< Change of CTS */
/* @} */

/** @name Channel Status Register
 *
 * The channel status register (CSR) is provided to enable the control logic
 * to monitor the status of bits in the channel interrupt status register,
 * even if these are masked out by the interrupt mask register.
 *
 * @{
 */
#define XUARTPS_SR_TNFUL	0x00004000 /**< TX FIFO Nearly Full Status */
#define XUARTPS_SR_TTRIG	0x00002000 /**< TX FIFO Trigger Status */
#define XUARTPS_SR_FLOWDEL	0x00001000 /**< RX FIFO fill over flow delay */
#define XUARTPS_SR_TACTIVE	0x00000800 /**< TX active */
#define XUARTPS_SR_RACTIVE	0x00000400 /**< RX active */
#define XUARTPS_SR_DMS		0x00000200 /**< Delta modem status change */
#define XUARTPS_SR_TOUT		0x00000100 /**< RX timeout */
#define XUARTPS_SR_PARITY	0x00000080 /**< RX parity error */
#define XUARTPS_SR_FRAME	0x00000040 /**< RX frame error */
#define XUARTPS_SR_OVER		0x00000020 /**< RX overflow error */
#define XUARTPS_SR_TXFULL	0x00000010 /**< TX FIFO full */
#define XUARTPS_SR_TXEMPTY	0x00000008 /**< TX FIFO empty */
#define XUARTPS_SR_RXFULL	0x00000004 /**< RX FIFO full */
#define XUARTPS_SR_RXEMPTY	0x00000002 /**< RX FIFO empty */
#define XUARTPS_SR_RXOVR	0x00000001 /**< RX FIFO fill over trigger */
/* @} */

/** @name Flow Delay Register
 *
 * Operation of the flow delay register (FLOWDEL) is very similar to the
 * receive FIFO trigger register. An internal trigger signal activates when the
 * FIFO is filled to the level set by this register. This trigger will not
 * cause an interrupt, although it can be read through the channel status
 * register. In hardware flow control mode, RTS is deactivated when the trigger
 * becomes active. RTS only resets when the FIFO level is four less than the
 * level of the flow delay trigger and the flow delay trigger is not activated.
 * A value less than 4 disables the flow delay.
 * @{
 */
#define XUARTPS_FLOWDEL_MASK	XUARTPS_RXWM_MASK	/**< Valid bit mask */
/* @} */



/*
 * Defines for backwards compatabilty, will be removed
 * in the next version of the driver
 */
#define XUARTPS_MEDEMSR_DCDX  XUARTPS_MODEMSR_DDCD
#define XUARTPS_MEDEMSR_RIX   XUARTPS_MODEMSR_TERI
#define XUARTPS_MEDEMSR_DSRX  XUARTPS_MODEMSR_DDSR
#define	XUARTPS_MEDEMSR_CTSX  XUARTPS_MODEMSR_DCTS



/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/**
* Read a UART register.
*
* @param	BaseAddress contains the base address of the device.
* @param	RegOffset contains the offset from the base address of the
*		device.
*
* @return	The value read from the register.
*
* @note		C-Style signature:
*		u32 XUartPs_ReadReg(u32 BaseAddress, int RegOffset)
*
******************************************************************************/
#define XUartPs_ReadReg(BaseAddress, RegOffset) \
	Xil_In32((BaseAddress) + (RegOffset))

/***************************************************************************/
/**
* Write a UART register.
*
* @param	BaseAddress contains the base address of the device.
* @param	RegOffset contains the offset from the base address of the
*		device.
* @param	RegisterValue is the value to be written to the register.
*
* @return	None.
*
* @note		C-Style signature:
*		void XUartPs_WriteReg(u32 BaseAddress, int RegOffset,
*						   u16 RegisterValue)
*
******************************************************************************/
#define XUartPs_WriteReg(BaseAddress, RegOffset, RegisterValue) \
	Xil_Out32((BaseAddress) + (RegOffset), (RegisterValue))

/****************************************************************************/
/**
* Determine if there is receive data in the receiver and/or FIFO.
*
* @param	BaseAddress contains the base address of the device.
*
* @return	TRUE if there is receive data, FALSE otherwise.
*
* @note		C-Style signature:
*		u32 XUartPs_IsReceiveData(u32 BaseAddress)
*
******************************************************************************/
#define XUartPs_IsReceiveData(BaseAddress)			 \
	!((Xil_In32((BaseAddress) + XUARTPS_SR_OFFSET) & 	\
	XUARTPS_SR_RXEMPTY) == XUARTPS_SR_RXEMPTY)

/****************************************************************************/
/**
* Determine if a byte of data can be sent with the transmitter.
*
* @param	BaseAddress contains the base address of the device.
*
* @return	TRUE if the TX FIFO is full, FALSE if a byte can be put in the
*		FIFO.
*
* @note		C-Style signature:
*		u32 XUartPs_IsTransmitFull(u32 BaseAddress)
*
******************************************************************************/
#define XUartPs_IsTransmitFull(BaseAddress)			 \
	((Xil_In32((BaseAddress) + XUARTPS_SR_OFFSET) & 	\
	 XUARTPS_SR_TXFULL) == XUARTPS_SR_TXFULL)

/************************** Function Prototypes ******************************/

void XUartPs_SendByte(u32 BaseAddress, u8 Data);

u8 XUartPs_RecvByte(u32 BaseAddress);

void XUartPs_ResetHw(u32 BaseAddress);

/************************** Variable Definitions *****************************/

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
