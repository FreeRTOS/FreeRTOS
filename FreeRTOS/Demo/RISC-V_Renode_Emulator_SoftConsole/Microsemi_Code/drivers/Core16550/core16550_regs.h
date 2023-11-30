/*******************************************************************************
 * (c) Copyright 2007-2015 Microsemi SoC Products Group. All rights reserved.
 *
 * IP core registers definitions. This file contains the definitions required
 * for accessing the IP core through the hardware abstraction layer (HAL).
 * This file was automatically generated, using "get_header.exe" version 0.4.0,
 * from the IP-XACT description for:
 *
 *             Core16550    version: 2.0.0
 *
 * SVN $Revision: 7963 $
 * SVN $Date: 2015-10-09 17:58:21 +0530 (Fri, 09 Oct 2015) $
 *
 *******************************************************************************/
#ifndef CORE_16550_REGISTERS_H_
#define CORE_16550_REGISTERS_H_ 1

#ifdef __cplusplus
extern "C" {
#endif

/*******************************************************************************
 * RBR register:
 *------------------------------------------------------------------------------
 * Receive Buffer Register
 */
#define RBR_REG_OFFSET	0x00U

/*******************************************************************************
 * THR register:
 *------------------------------------------------------------------------------
 * Transmit Holding Register
 */
#define THR_REG_OFFSET	0x00U

/*******************************************************************************
 * DLR register:
 *------------------------------------------------------------------------------
 * Divisor Latch(LSB) Register
 */
#define DLR_REG_OFFSET	0x00U

/*******************************************************************************
 * DMR register:
 *------------------------------------------------------------------------------
 * Divisor Latch(MSB) Register
 */
#define DMR_REG_OFFSET	0x04U

/*******************************************************************************
 * IER register:
 *------------------------------------------------------------------------------
 * Interrupt Enable Register
 */
#define IER_REG_OFFSET	0x04U

/*------------------------------------------------------------------------------
 * IER_ERBFI:
 *   ERBFI field of register IER.
 *------------------------------------------------------------------------------
 * Enables Received Data Available Interrupt. 0 - Disabled; 1 - Enabled
 */
#define IER_ERBFI_OFFSET   0x04U
#define IER_ERBFI_MASK     0x01U
#define IER_ERBFI_SHIFT    0U

/*------------------------------------------------------------------------------
 * IER_ETBEI:
 *   ETBEI field of register IER.
 *------------------------------------------------------------------------------
 * Enables the Transmitter Holding Register Empty Interrupt. 0 - Disabled; 1 - 
 * Enabled
 */
#define IER_ETBEI_OFFSET   0x04U
#define IER_ETBEI_MASK     0x02U
#define IER_ETBEI_SHIFT    1U

/*------------------------------------------------------------------------------
 * IER_ELSI:
 *   ELSI field of register IER.
 *------------------------------------------------------------------------------
 * Enables the Receiver Line Status Interrupt. 0 - Disabled; 1 - Enabled
 */
#define IER_ELSI_OFFSET   0x04U
#define IER_ELSI_MASK     0x04U
#define IER_ELSI_SHIFT    2U

/*------------------------------------------------------------------------------
 * IER_EDSSI:
 *   EDSSI field of register IER.
 *------------------------------------------------------------------------------
 *  Enables the Modem Status Interrupt 0 - Disabled; 1 - Enabled
 */
#define IER_EDSSI_OFFSET   0x04U
#define IER_EDSSI_MASK     0x08U
#define IER_EDSSI_SHIFT    3U

/*******************************************************************************
 * IIR register:
 *------------------------------------------------------------------------------
 * Interrupt Identification
 */
#define IIR_REG_OFFSET	0x08U

/*------------------------------------------------------------------------------
 * IIR_IIR:
 *   IIR field of register IIR.
 *------------------------------------------------------------------------------
 * Interrupt Identification bits.
 */
#define IIR_IIR_OFFSET   0x08U
#define IIR_IIR_MASK     0x0FU
#define IIR_IIR_SHIFT    0U

/*------------------------------------------------------------------------------
 * IIR_IIR:
 *   IIR field of register IIR.
 *------------------------------------------------------------------------------
 * Interrupt Identification bits.
 */

/*------------------------------------------------------------------------------
 * IIR_Mode:
 *   Mode field of register IIR.
 *------------------------------------------------------------------------------
 * 11 - FIFO mode
 */
#define IIR_MODE_OFFSET   0x08U
#define IIR_MODE_MASK     0xC0U
#define IIR_MODE_SHIFT    6U

/*******************************************************************************
 * FCR register:
 *------------------------------------------------------------------------------
 * FIFO Control Register
 */
#define FCR_REG_OFFSET	0x08

/*------------------------------------------------------------------------------
 * FCR_Bit0:
 *   Bit0 field of register FCR.
 *------------------------------------------------------------------------------
 * This bit enables both the TX and RX FIFOs.
 */
#define FCR_BIT0_OFFSET   0x08U
#define FCR_BIT0_MASK     0x01U
#define FCR_BIT0_SHIFT    0U

#define FCR_ENABLE_OFFSET   0x08U
#define FCR_ENABLE_MASK     0x01U
#define FCR_ENABLE_SHIFT    0U

/*------------------------------------------------------------------------------
 * FCR_Bit1:
 *   Bit1 field of register FCR.
 *------------------------------------------------------------------------------
 * Clears all bytes in the RX FIFO and resets its counter logic. The shift 
 * register is not cleared.  0 - Disabled; 1 - Enabled
 */
#define FCR_BIT1_OFFSET   0x08U
#define FCR_BIT1_MASK     0x02U
#define FCR_BIT1_SHIFT    1U

#define FCR_CLEAR_RX_OFFSET   0x08U
#define FCR_CLEAR_RX_MASK     0x02U
#define FCR_CLEAR_RX_SHIFT    1U

/*------------------------------------------------------------------------------
 * FCR_Bit2:
 *   Bit2 field of register FCR.
 *------------------------------------------------------------------------------
 * Clears all bytes in the TX FIFO and resets its counter logic. The shift 
 * register is not cleared.  0 - Disabled; 1 - Enabled
 */
#define FCR_BIT2_OFFSET   0x08U
#define FCR_BIT2_MASK     0x04U
#define FCR_BIT2_SHIFT    2U

#define FCR_CLEAR_TX_OFFSET   0x08U
#define FCR_CLEAR_TX_MASK     0x04U
#define FCR_CLEAR_TX_SHIFT    2U

/*------------------------------------------------------------------------------
 * FCR_Bit3:
 *   Bit3 field of register FCR.
 *------------------------------------------------------------------------------
 * Enables RXRDYN and TXRDYN pins when set to 1. Otherwise, they are disabled.
 */
#define FCR_BIT3_OFFSET   0x08U
#define FCR_BIT3_MASK     0x08U
#define FCR_BIT3_SHIFT    3U

#define FCR_RDYN_EN_OFFSET   0x08U
#define FCR_RDYN_EN_MASK     0x08U
#define FCR_RDYN_EN_SHIFT    3U

/*------------------------------------------------------------------------------
 * FCR_Bit6:
 *   Bit6 field of register FCR.
 *------------------------------------------------------------------------------
 * These bits are used to set the trigger level for the RX FIFO interrupt. RX 
 * FIFO Trigger Level: 0 - 1; 1 - 4; 2 - 8; 3 - 14
 */
#define FCR_BIT6_OFFSET   0x08U
#define FCR_BIT6_MASK     0xC0U
#define FCR_BIT6_SHIFT    6U

#define FCR_TRIG_LEVEL_OFFSET   0x08U
#define FCR_TRIG_LEVEL_MASK     0xC0U
#define FCR_TRIG_LEVEL_SHIFT    6U

/*******************************************************************************
 * LCR register:
 *------------------------------------------------------------------------------
 * Line Control Register
 */
#define LCR_REG_OFFSET	0x0CU

/*------------------------------------------------------------------------------
 * LCR_WLS:
 *   WLS field of register LCR.
 *------------------------------------------------------------------------------
 * Word Length Select: 00 - 5 bits; 01 - 6 bits; 10 - 7 bits; 11 - 8 bits
 */
#define LCR_WLS_OFFSET   0x0CU
#define LCR_WLS_MASK     0x03U
#define LCR_WLS_SHIFT    0U

/*------------------------------------------------------------------------------
 * LCR_STB:
 *   STB field of register LCR.
 *------------------------------------------------------------------------------
 * Number of Stop Bits: 0 - 1 stop bit; 1 - 1½ stop bits when WLS = 00, 2 stop 
 * bits in other cases
 */
#define LCR_STB_OFFSET   0x0CU
#define LCR_STB_MASK     0x04U
#define LCR_STB_SHIFT    2U

/*------------------------------------------------------------------------------
 * LCR_PEN:
 *   PEN field of register LCR.
 *------------------------------------------------------------------------------
 * Parity Enable 0 - Disabled; 1 - Enabled. Parity is added in transmission and 
 * checked in receiving.
 */
#define LCR_PEN_OFFSET   0x0CU
#define LCR_PEN_MASK     0x08U
#define LCR_PEN_SHIFT    3U

/*------------------------------------------------------------------------------
 * LCR_EPS:
 *   EPS field of register LCR.
 *------------------------------------------------------------------------------
 * Even Parity Select 0 - Odd parity; 1 - Even parity
 */
#define LCR_EPS_OFFSET   0x0CU
#define LCR_EPS_MASK     0x10U
#define LCR_EPS_SHIFT    4U

/*------------------------------------------------------------------------------
 * LCR_SP:
 *   SP field of register LCR.
 *------------------------------------------------------------------------------
 * Stick Parity 0 - Disabled; 1 - Enabled When stick parity is enabled, it 
 * works as follows: Bits 4..3, 11 - 0 will be sent as a parity bit, and 
 * checked in receiving.  01 - 1 will be sent as a parity bit, and checked in 
 * receiving.
 */
#define LCR_SP_OFFSET   0x0CU
#define LCR_SP_MASK     0x20U
#define LCR_SP_SHIFT    5U

/*------------------------------------------------------------------------------
 * LCR_SB:
 *   SB field of register LCR.
 *------------------------------------------------------------------------------
 * Set Break 0 - Disabled 1 - Set break. SOUT is forced to 0. This does not 
 * have any effect on transmitter logic. The break is disabled by setting the 
 * bit to 0.
 */
#define LCR_SB_OFFSET   0x0CU
#define LCR_SB_MASK     0x40U
#define LCR_SB_SHIFT    6U

/*------------------------------------------------------------------------------
 * LCR_DLAB:
 *   DLAB field of register LCR.
 *------------------------------------------------------------------------------
 * Divisor Latch Access Bit 0 - Disabled. Normal addressing mode in use 1 - 
 * Enabled. Enables access to the Divisor Latch registers during read or write 
 * operation to addresses 0 and 1.
 */
#define LCR_DLAB_OFFSET   0x0CU
#define LCR_DLAB_MASK     0x80U
#define LCR_DLAB_SHIFT    7U

/*******************************************************************************
 * MCR register:
 *------------------------------------------------------------------------------
 * Modem Control Register
 */
#define MCR_REG_OFFSET	0x10U

/*------------------------------------------------------------------------------
 * MCR_DTR:
 *   DTR field of register MCR.
 *------------------------------------------------------------------------------
 * Controls the Data Terminal Ready (DTRn) output.  0 - DTRn <= 1; 1 - DTRn <= 0
 */
#define MCR_DTR_OFFSET   0x10U
#define MCR_DTR_MASK     0x01U
#define MCR_DTR_SHIFT    0U

/*------------------------------------------------------------------------------
 * MCR_RTS:
 *   RTS field of register MCR.
 *------------------------------------------------------------------------------
 * Controls the Request to Send (RTSn) output.  0 - RTSn <= 1; 1 - RTSn <= 0
 */
#define MCR_RTS_OFFSET   0x10U
#define MCR_RTS_MASK     0x02U
#define MCR_RTS_SHIFT    1U

/*------------------------------------------------------------------------------
 * MCR_Out1:
 *   Out1 field of register MCR.
 *------------------------------------------------------------------------------
 * Controls the Output1 (OUT1n) signal.  0 - OUT1n <= 1; 1 - OUT1n <= 0
 */
#define MCR_OUT1_OFFSET   0x10U
#define MCR_OUT1_MASK     0x04U
#define MCR_OUT1_SHIFT    2U

/*------------------------------------------------------------------------------
 * MCR_Out2:
 *   Out2 field of register MCR.
 *------------------------------------------------------------------------------
 * Controls the Output2 (OUT2n) signal.  0 - OUT2n <=1; 1 - OUT2n <=0
 */
#define MCR_OUT2_OFFSET   0x10U
#define MCR_OUT2_MASK     0x08U
#define MCR_OUT2_SHIFT    3U

/*------------------------------------------------------------------------------
 * MCR_Loop:
 *   Loop field of register MCR.
 *------------------------------------------------------------------------------
 * Loop enable bit 0 - Disabled; 1 - Enabled. The following happens in loop 
 * mode: SOUT is set to 1. The SIN, DSRn, CTSn, RIn, and DCDn inputs are 
 * disconnected.  The output of the Transmitter Shift Register is looped back 
 * into the Receiver Shift Register. The modem control outputs (DTRn, RTSn, 
 * OUT1n, and OUT2n) are connected internally to the modem control inputs, and 
 * the modem control output pins are set at 1. In loopback mode, the 
 * transmitted data is immediately received, allowing the CPU to check the 
 * operation of the UART. The interrupts are operating in loop mode.
 */
#define MCR_LOOP_OFFSET   0x10U
#define MCR_LOOP_MASK     0x10U
#define MCR_LOOP_SHIFT    4U

/*******************************************************************************
 * LSR register:
 *------------------------------------------------------------------------------
 * Line Status Register
 */
#define LSR_REG_OFFSET	0x14U

/*------------------------------------------------------------------------------
 * LSR_DR:
 *   DR field of register LSR.
 *------------------------------------------------------------------------------
 * Data Ready indicator 1 when a data byte has been received and stored in the 
 * FIFO. DR is cleared to 0 when the CPU reads the data from the FIFO.
 */
#define LSR_DR_OFFSET   0x14U
#define LSR_DR_MASK     0x01U
#define LSR_DR_SHIFT    0U

/*------------------------------------------------------------------------------
 * LSR_OE:
 *   OE field of register LSR.
 *------------------------------------------------------------------------------
 * Overrun Error indicator Indicates that the new byte was received before the 
 * CPU read the byte from the receive buffer, and that the earlier data byte 
 * was destroyed. OE is cleared when the CPU reads the Line Status Register. If 
 * the data continues to fill the FIFO beyond the trigger level, an overrun 
 * error will occur once the FIFO is full and the next character has been 
 * completely received in the shift register. The character in the shift 
 * register is overwritten, but it is not transferred to the FIFO.
 */
#define LSR_OE_OFFSET   0x14U
#define LSR_OE_MASK     0x02U
#define LSR_OE_SHIFT    1U

/*------------------------------------------------------------------------------
 * LSR_PE:
 *   PE field of register LSR.
 *------------------------------------------------------------------------------
 * Parity Error indicator Indicates that the received byte had a parity error. 
 * PE is cleared when the CPU reads the Line Status Register. This error is 
 * revealed to the CPU when its associated character is at the top of the FIFO.
 */
#define LSR_PE_OFFSET   0x14U
#define LSR_PE_MASK     0x04U
#define LSR_PE_SHIFT    2U

/*------------------------------------------------------------------------------
 * LSR_FE:
 *   FE field of register LSR.
 *------------------------------------------------------------------------------
 *  Framing Error indicator Indicates that the received byte did not have a 
 * valid Stop bit. FE is cleared when the CPU reads the Line Status Register. 
 * The UART will try to re-synchronize after a framing error. To do this, it
 * assumes that the framing error was due to the next start bit, so it samples 
 * this start bit twice, and then starts receiving the data.  This error is 
 * revealed to the CPU when its associated character is at the top of the FIFO.
 */
#define LSR_FE_OFFSET   0x14U
#define LSR_FE_MASK     0x08U
#define LSR_FE_SHIFT    3U

/*------------------------------------------------------------------------------
 * LSR_BI:
 *   BI field of register LSR.
 *------------------------------------------------------------------------------
 * Break Interrupt indicator Indicates that the received data is at 0 longer 
 * than a full word transmission time (start bit + data bits + parity + stop 
 * bits). BI is cleared when the CPU reads the Line Status Register. This error 
 * is revealed to the CPU when its associated character is at the top of the 
 * FIFO. When break occurs, only one zero character is loaded into the FIFO.
 */
#define LSR_BI_OFFSET   0x14U
#define LSR_BI_MASK     0x10U
#define LSR_BI_SHIFT    4U

/*------------------------------------------------------------------------------
 * LSR_THRE:
 *   THRE field of register LSR.
 *------------------------------------------------------------------------------
 *  Transmitter Holding Register Empty indicator Indicates that the UART is 
 * ready to transmit a new data byte. THRE causes an interrupt to the CPU when 
 * bit 1 (ETBEI) in the Interrupt Enable Register is 1.  This bit is set when 
 * the TX FIFO is empty. It is cleared when at least one byte is written to the 
 * TX FIFO.
 */
#define LSR_THRE_OFFSET   0x14U
#define LSR_THRE_MASK     0x20U
#define LSR_THRE_SHIFT    5U

/*------------------------------------------------------------------------------
 * LSR_TEMT:
 *   TEMT field of register LSR.
 *------------------------------------------------------------------------------
 *  Transmitter Empty indicator This bit is set to 1 when both the transmitter 
 * FIFO and shift registers are empty.
 */
#define LSR_TEMT_OFFSET   0x14U
#define LSR_TEMT_MASK     0x40U
#define LSR_TEMT_SHIFT    6U

/*------------------------------------------------------------------------------
 * LSR_FIER:
 *   FIER field of register LSR.
 *------------------------------------------------------------------------------
 *  This bit is set when there is at least one parity error, framing error, or 
 * break indication in the FIFO. FIER is cleared when the CPU reads the LSR if 
 * there are no subsequent errors in the FIFO.
 */
#define LSR_FIER_OFFSET   0x14U
#define LSR_FIER_MASK     0x80U
#define LSR_FIER_SHIFT    7U

/*******************************************************************************
 * MSR register:
 *------------------------------------------------------------------------------
 * Modem Status Register
 */
#define MSR_REG_OFFSET	0x18U

/*------------------------------------------------------------------------------
 * MSR_DCTS:
 *   DCTS field of register MSR.
 *------------------------------------------------------------------------------
 * Delta Clear to Send indicator.  Indicates that the CTSn input has changed 
 * state since the last time it was read by the CPU.
 */
#define MSR_DCTS_OFFSET   0x18U
#define MSR_DCTS_MASK     0x01U
#define MSR_DCTS_SHIFT    0U

/*------------------------------------------------------------------------------
 * MSR_DDSR:
 *   DDSR field of register MSR.
 *------------------------------------------------------------------------------
 * Delta Data Set Ready indicator Indicates that the DSRn input has changed 
 * state since the last time it was read by the CPU.
 */
#define MSR_DDSR_OFFSET   0x18U
#define MSR_DDSR_MASK     0x02U
#define MSR_DDSR_SHIFT    1U

/*------------------------------------------------------------------------------
 * MSR_TERI:
 *   TERI field of register MSR.
 *------------------------------------------------------------------------------
 * Trailing Edge of Ring Indicator detector. Indicates that RI input has 
 * changed from 0 to 1.
 */
#define MSR_TERI_OFFSET   0x18U
#define MSR_TERI_MASK     0x04U
#define MSR_TERI_SHIFT    2U

/*------------------------------------------------------------------------------
 * MSR_DDCD:
 *   DDCD field of register MSR.
 *------------------------------------------------------------------------------
 * Delta Data Carrier Detect indicator Indicates that DCD input has changed 
 * state.  NOTE: Whenever bit 0, 1, 2, or 3 is set to 1, a Modem Status 
 * Interrupt is generated.
 */
#define MSR_DDCD_OFFSET   0x18U
#define MSR_DDCD_MASK     0x08U
#define MSR_DDCD_SHIFT    3U

/*------------------------------------------------------------------------------
 * MSR_CTS:
 *   CTS field of register MSR.
 *------------------------------------------------------------------------------
 * Clear to Send The complement of the CTSn input. When bit 4 of the Modem 
 * Control Register (MCR) is set to 1 (loop), this bit is equivalent to DTR in 
 * the MCR.
 */
#define MSR_CTS_OFFSET   0x18U
#define MSR_CTS_MASK     0x10U
#define MSR_CTS_SHIFT    4U

/*------------------------------------------------------------------------------
 * MSR_DSR:
 *   DSR field of register MSR.
 *------------------------------------------------------------------------------
 * Data Set Ready The complement of the DSR input. When bit 4 of the MCR is set 
 * to 1 (loop), this bit is equivalent to RTSn in the MCR.
 */
#define MSR_DSR_OFFSET   0x18U
#define MSR_DSR_MASK     0x20U
#define MSR_DSR_SHIFT    5U

/*------------------------------------------------------------------------------
 * MSR_RI:
 *   RI field of register MSR.
 *------------------------------------------------------------------------------
 * Ring Indicator The complement of the RIn input. When bit 4 of the MCR is set 
 * to 1 (loop), this bit is equivalent to OUT1 in the MCR.
 */
#define MSR_RI_OFFSET   0x18U
#define MSR_RI_MASK     0x40U
#define MSR_RI_SHIFT    6U

/*------------------------------------------------------------------------------
 * MSR_DCD:
 *   DCD field of register MSR.
 *------------------------------------------------------------------------------
 * Data Carrier Detect The complement of DCDn input. When bit 4 of the MCR is 
 * set to 1 (loop), this bit is equivalent to OUT2 in the MCR.
 */
#define MSR_DCD_OFFSET   0x18U
#define MSR_DCD_MASK     0x80U
#define MSR_DCD_SHIFT    7U

/*******************************************************************************
 * SR register:
 *------------------------------------------------------------------------------
 * Scratch Register
 */
#define SR_REG_OFFSET	0x1CU

#ifdef __cplusplus
}
#endif

#endif /* CORE_16550_REGISTERS_H_*/
