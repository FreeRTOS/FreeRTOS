/*******************************************************************************
*                                                                              *
* Copyright 2013 Altera Corporation. All Rights Reserved.                      *
*                                                                              *
* Redistribution and use in source and binary forms, with or without           *
* modification, are permitted provided that the following conditions are met:  *
*                                                                              *
* 1. Redistributions of source code must retain the above copyright notice,    *
*    this list of conditions and the following disclaimer.                     *
*                                                                              *
* 2. Redistributions in binary form must reproduce the above copyright notice, *
*    this list of conditions and the following disclaimer in the documentation *
*    and/or other materials provided with the distribution.                    *
*                                                                              *
* 3. The name of the author may not be used to endorse or promote products     *
*    derived from this software without specific prior written permission.     *
*                                                                              *
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR *
* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF *
* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO  *
* EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,       *
* SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, *
* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;  *
* OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,     *
* WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR      *
* OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF       *
* ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                                   *
*                                                                              *
*******************************************************************************/

/* Altera - ALT_UART */

#ifndef __ALTERA_ALT_UART_H__
#define __ALTERA_ALT_UART_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : UART Module - ALT_UART
 * UART Module
 * 
 * Registers in the UART module
 * 
 */
/*
 * Register : Rx Buffer, Tx Holding, and Divisor Latch Low - rbr_thr_dll
 * 
 * This is a multi-function register. This register holds receives and transmit
 * data and controls the least-signficant 8 bits of the baud rate divisor.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [7:0]  | RW     | 0x0   | Value      
 *  [31:8] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Value - value
 * 
 * Receive Buffer Register:
 * 
 * This register contains the data byte received on the serial input port
 * (uart_rxd). The data in this register is valid only if the Data Ready ( bit [0]
 * in the Line Status Register(LSR)) is set to 1. If FIFOs are disabled(bit[0] of
 * Register FCR is set to 0) the data in the RBR must be read before the next data
 * arrives, otherwise it will be overwritten, resulting in an overrun error. If
 * FIFOs are enabled(bit [0] of Register FCR is set to 1) this register accesses
 * the head of the receive FIFO. If the receive FIFO is full, and this register is
 * not read before the next data character arrives, then the data already in the
 * FIFO will be preserved but any incoming data will be lost. An overrun error will
 * also occur.
 * 
 * Transmit Holding Register:
 * 
 * This register contains data to be transmitted on the serial output port. Data
 * should only be written to the THR when the THR Empty bit [5] of the LSR Register
 * is set to 1. If FIFOs are disabled (bit [0] of Register FCR) is set to 0 and
 * THRE is set to 1, writing a single character to the THR clears the THRE. Any
 * additional writes to the THR before the THRE is set again causes the THR data to
 * be overwritten. If FIFO's are enabled bit [0] of Register FCR is set to 1 and
 * THRE is set up to 128 characters of data may be written to the THR before the
 * FIFO is full. Any attempt to write data when the FIFO is full results in the
 * write data being lost.
 * 
 * Divisor Latch Low:
 * 
 * This register makes up the lower 8-bits of a 16-bit, Read/write, Divisor Latch
 * register that contains the baud rate divisor for the UART. This register may
 * only be accessed when the DLAB bit [7] of the LCR Register is set to 1. The
 * output baud rate is equal to the serial clock l4_sp_clk frequency divided by
 * sixteen times the value of the baud rate divisor, as follows:
 * 
 * baud rate = (serial clock freq) / (16 * divisor)
 * 
 * Note that with the Divisor Latch Registers (DLL and DLH) set to zero, the baud
 * clock is disabled and no serial communications will occur. Also, once the DLL is
 * set, at least 8 l4_sp_clk clock cycles should be allowed to pass before
 * transmitting or receiving data.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_RBR_THR_DLL_VALUE register field. */
#define ALT_UART_RBR_THR_DLL_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_RBR_THR_DLL_VALUE register field. */
#define ALT_UART_RBR_THR_DLL_VALUE_MSB        7
/* The width in bits of the ALT_UART_RBR_THR_DLL_VALUE register field. */
#define ALT_UART_RBR_THR_DLL_VALUE_WIDTH      8
/* The mask used to set the ALT_UART_RBR_THR_DLL_VALUE register field value. */
#define ALT_UART_RBR_THR_DLL_VALUE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_UART_RBR_THR_DLL_VALUE register field value. */
#define ALT_UART_RBR_THR_DLL_VALUE_CLR_MSK    0xffffff00
/* The reset value of the ALT_UART_RBR_THR_DLL_VALUE register field. */
#define ALT_UART_RBR_THR_DLL_VALUE_RESET      0x0
/* Extracts the ALT_UART_RBR_THR_DLL_VALUE field value from a register. */
#define ALT_UART_RBR_THR_DLL_VALUE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_UART_RBR_THR_DLL_VALUE register field value suitable for setting the register. */
#define ALT_UART_RBR_THR_DLL_VALUE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_RBR_THR_DLL.
 */
struct ALT_UART_RBR_THR_DLL_s
{
    uint32_t  value :  8;  /* Value */
    uint32_t        : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_RBR_THR_DLL. */
typedef volatile struct ALT_UART_RBR_THR_DLL_s  ALT_UART_RBR_THR_DLL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_RBR_THR_DLL register from the beginning of the component. */
#define ALT_UART_RBR_THR_DLL_OFST        0x0
/* The address of the ALT_UART_RBR_THR_DLL register. */
#define ALT_UART_RBR_THR_DLL_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_RBR_THR_DLL_OFST))

/*
 * Register : Interrupt Enable and Divisor Latch High - ier_dlh
 * 
 * This is a multi-function register. This register enables/disables receive and
 * transmit interrupts and also controls the most-significant 8-bits of the baud
 * rate divisor.
 * 
 * Divisor Latch High Register:
 * 
 * This register is accessed when the DLAB bit [7] of the LCR Register is set to
 * 1.Bits[7:0] contain the high order 8-bits of the baud rate divisor.The output
 * baud rate is equal to the serial clock l4_sp_clk frequency divided by sixteen
 * times the value of the baud rate divisor, as follows:
 * 
 * baud rate = (serial clock freq) / (16 * divisor):
 * 
 * Note that with the Divisor Latch Registers (DLLand DLH) set to zero, the baud
 * clock is disabled and no serial communications will occur. Also, once the DLL is
 * set, at least 8 l4_sp_clk clock cycles should be allowed to pass before
 * transmitting or receiving data.
 * 
 * Interrupt Enable Register:
 * 
 * This register may only be accessed when the DLAB bit [7] of the LCR Register is
 * set to 0.Allows control of the Interrupt Enables for transmit and receive
 * functions.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                                
 * :-------|:-------|:------|:--------------------------------------------
 *  [0]    | RW     | 0x0   | DLH[0] and Receive Data Interrupt Enable   
 *  [1]    | RW     | 0x0   | DLH[1] and Transmit Data Interrupt Control 
 *  [2]    | RW     | 0x0   | DLH[2] and Enable Receiver Line Status     
 *  [3]    | RW     | 0x0   | DLH[3] and Enable Modem Status Interrupt   
 *  [4]    | RW     | 0x0   | DLH[4]                                     
 *  [5]    | RW     | 0x0   | DLH[5]                                     
 *  [6]    | RW     | 0x0   | DLH[6]                                     
 *  [7]    | RW     | 0x0   | DLH[7] and PTIME THRE Interrupt Mode Enable
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                                
 * 
 */
/*
 * Field : DLH[0] and Receive Data Interrupt Enable - erbfi_dlh0
 * 
 * Divisor Latch High Register:
 * 
 * Bit 0 of DLH value.
 * 
 * Interrupt Enable Register:
 * 
 * Used to enable/disable the generation of the Receive Data Available Interrupt
 * and the Character Timeout Interrupt(if FIFO's enabled). These are the second
 * highest priority interrupts.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description      
 * :-----------------------------------|:------|:------------------
 *  ALT_UART_IER_DLH_ERBFI_DLH0_E_DISD | 0x0   | Interrupt Disable
 *  ALT_UART_IER_DLH_ERBFI_DLH0_E_END  | 0x1   | Interrupt Enable 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_IER_DLH_ERBFI_DLH0
 * 
 * Interrupt Disable
 */
#define ALT_UART_IER_DLH_ERBFI_DLH0_E_DISD  0x0
/*
 * Enumerated value for register field ALT_UART_IER_DLH_ERBFI_DLH0
 * 
 * Interrupt Enable
 */
#define ALT_UART_IER_DLH_ERBFI_DLH0_E_END   0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_IER_DLH_ERBFI_DLH0 register field. */
#define ALT_UART_IER_DLH_ERBFI_DLH0_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_IER_DLH_ERBFI_DLH0 register field. */
#define ALT_UART_IER_DLH_ERBFI_DLH0_MSB        0
/* The width in bits of the ALT_UART_IER_DLH_ERBFI_DLH0 register field. */
#define ALT_UART_IER_DLH_ERBFI_DLH0_WIDTH      1
/* The mask used to set the ALT_UART_IER_DLH_ERBFI_DLH0 register field value. */
#define ALT_UART_IER_DLH_ERBFI_DLH0_SET_MSK    0x00000001
/* The mask used to clear the ALT_UART_IER_DLH_ERBFI_DLH0 register field value. */
#define ALT_UART_IER_DLH_ERBFI_DLH0_CLR_MSK    0xfffffffe
/* The reset value of the ALT_UART_IER_DLH_ERBFI_DLH0 register field. */
#define ALT_UART_IER_DLH_ERBFI_DLH0_RESET      0x0
/* Extracts the ALT_UART_IER_DLH_ERBFI_DLH0 field value from a register. */
#define ALT_UART_IER_DLH_ERBFI_DLH0_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_UART_IER_DLH_ERBFI_DLH0 register field value suitable for setting the register. */
#define ALT_UART_IER_DLH_ERBFI_DLH0_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : DLH[1] and Transmit Data Interrupt Control - etbei_dlhl
 * 
 * Divisor Latch High Register:
 * 
 * Bit 1 of DLH value.
 * 
 * Interrupt Enable Register:
 * 
 * Enable Transmit Holding Register Empty Interrupt. This is used to enable/disable
 * the generation of Transmitter Holding Register Empty Interrupt. This is the
 * third highest priority interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description
 * :-----------------------------------|:------|:------------
 *  ALT_UART_IER_DLH_ETBEI_DLHL_E_DISD | 0x0   | Tx disable 
 *  ALT_UART_IER_DLH_ETBEI_DLHL_E_END  | 0x1   | Tx enable  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_IER_DLH_ETBEI_DLHL
 * 
 * Tx disable
 */
#define ALT_UART_IER_DLH_ETBEI_DLHL_E_DISD  0x0
/*
 * Enumerated value for register field ALT_UART_IER_DLH_ETBEI_DLHL
 * 
 * Tx enable
 */
#define ALT_UART_IER_DLH_ETBEI_DLHL_E_END   0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_IER_DLH_ETBEI_DLHL register field. */
#define ALT_UART_IER_DLH_ETBEI_DLHL_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_UART_IER_DLH_ETBEI_DLHL register field. */
#define ALT_UART_IER_DLH_ETBEI_DLHL_MSB        1
/* The width in bits of the ALT_UART_IER_DLH_ETBEI_DLHL register field. */
#define ALT_UART_IER_DLH_ETBEI_DLHL_WIDTH      1
/* The mask used to set the ALT_UART_IER_DLH_ETBEI_DLHL register field value. */
#define ALT_UART_IER_DLH_ETBEI_DLHL_SET_MSK    0x00000002
/* The mask used to clear the ALT_UART_IER_DLH_ETBEI_DLHL register field value. */
#define ALT_UART_IER_DLH_ETBEI_DLHL_CLR_MSK    0xfffffffd
/* The reset value of the ALT_UART_IER_DLH_ETBEI_DLHL register field. */
#define ALT_UART_IER_DLH_ETBEI_DLHL_RESET      0x0
/* Extracts the ALT_UART_IER_DLH_ETBEI_DLHL field value from a register. */
#define ALT_UART_IER_DLH_ETBEI_DLHL_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_UART_IER_DLH_ETBEI_DLHL register field value suitable for setting the register. */
#define ALT_UART_IER_DLH_ETBEI_DLHL_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : DLH[2] and Enable Receiver Line Status - elsi_dhl2
 * 
 * Divisor Latch High Register:
 * 
 * Bit 2 of DLH value.
 * 
 * Interrupt Enable Register:
 * 
 * This is used to enable/disable the generation of Receiver Line Status Interrupt.
 * This is the highest priority interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                
 * :----------------------------------|:------|:----------------------------
 *  ALT_UART_IER_DLH_ELSI_DHL2_E_DISD | 0x0   | Disable interrupt line stat
 *  ALT_UART_IER_DLH_ELSI_DHL2_E_END  | 0x1   | Enable interrupt line stat 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_IER_DLH_ELSI_DHL2
 * 
 * Disable interrupt line stat
 */
#define ALT_UART_IER_DLH_ELSI_DHL2_E_DISD   0x0
/*
 * Enumerated value for register field ALT_UART_IER_DLH_ELSI_DHL2
 * 
 * Enable interrupt line stat
 */
#define ALT_UART_IER_DLH_ELSI_DHL2_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_IER_DLH_ELSI_DHL2 register field. */
#define ALT_UART_IER_DLH_ELSI_DHL2_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_UART_IER_DLH_ELSI_DHL2 register field. */
#define ALT_UART_IER_DLH_ELSI_DHL2_MSB        2
/* The width in bits of the ALT_UART_IER_DLH_ELSI_DHL2 register field. */
#define ALT_UART_IER_DLH_ELSI_DHL2_WIDTH      1
/* The mask used to set the ALT_UART_IER_DLH_ELSI_DHL2 register field value. */
#define ALT_UART_IER_DLH_ELSI_DHL2_SET_MSK    0x00000004
/* The mask used to clear the ALT_UART_IER_DLH_ELSI_DHL2 register field value. */
#define ALT_UART_IER_DLH_ELSI_DHL2_CLR_MSK    0xfffffffb
/* The reset value of the ALT_UART_IER_DLH_ELSI_DHL2 register field. */
#define ALT_UART_IER_DLH_ELSI_DHL2_RESET      0x0
/* Extracts the ALT_UART_IER_DLH_ELSI_DHL2 field value from a register. */
#define ALT_UART_IER_DLH_ELSI_DHL2_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_UART_IER_DLH_ELSI_DHL2 register field value suitable for setting the register. */
#define ALT_UART_IER_DLH_ELSI_DHL2_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : DLH[3] and Enable Modem Status Interrupt - edssi_dhl3
 * 
 * Divisor Latch High Register:
 * 
 * Bit 3 of DLH value.
 * 
 * Interrupt Enable Register:
 * 
 * This is used to enable/disable the generation of Modem Status Interrupts. This
 * is the fourth highest priority interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                   
 * :-----------------------------------|:------|:-------------------------------
 *  ALT_UART_IER_DLH_EDSSI_DHL3_E_DISD | 0x0   | disable modem status interrupt
 *  ALT_UART_IER_DLH_EDSSI_DHL3_E_END  | 0x1   | enable modem status interrupt 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_IER_DLH_EDSSI_DHL3
 * 
 * disable modem status interrupt
 */
#define ALT_UART_IER_DLH_EDSSI_DHL3_E_DISD  0x0
/*
 * Enumerated value for register field ALT_UART_IER_DLH_EDSSI_DHL3
 * 
 * enable modem status interrupt
 */
#define ALT_UART_IER_DLH_EDSSI_DHL3_E_END   0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_IER_DLH_EDSSI_DHL3 register field. */
#define ALT_UART_IER_DLH_EDSSI_DHL3_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_UART_IER_DLH_EDSSI_DHL3 register field. */
#define ALT_UART_IER_DLH_EDSSI_DHL3_MSB        3
/* The width in bits of the ALT_UART_IER_DLH_EDSSI_DHL3 register field. */
#define ALT_UART_IER_DLH_EDSSI_DHL3_WIDTH      1
/* The mask used to set the ALT_UART_IER_DLH_EDSSI_DHL3 register field value. */
#define ALT_UART_IER_DLH_EDSSI_DHL3_SET_MSK    0x00000008
/* The mask used to clear the ALT_UART_IER_DLH_EDSSI_DHL3 register field value. */
#define ALT_UART_IER_DLH_EDSSI_DHL3_CLR_MSK    0xfffffff7
/* The reset value of the ALT_UART_IER_DLH_EDSSI_DHL3 register field. */
#define ALT_UART_IER_DLH_EDSSI_DHL3_RESET      0x0
/* Extracts the ALT_UART_IER_DLH_EDSSI_DHL3 field value from a register. */
#define ALT_UART_IER_DLH_EDSSI_DHL3_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_UART_IER_DLH_EDSSI_DHL3 register field value suitable for setting the register. */
#define ALT_UART_IER_DLH_EDSSI_DHL3_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : DLH[4] - dlh4
 * 
 * Bit 4 of DLH value.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_IER_DLH_DLH4 register field. */
#define ALT_UART_IER_DLH_DLH4_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_UART_IER_DLH_DLH4 register field. */
#define ALT_UART_IER_DLH_DLH4_MSB        4
/* The width in bits of the ALT_UART_IER_DLH_DLH4 register field. */
#define ALT_UART_IER_DLH_DLH4_WIDTH      1
/* The mask used to set the ALT_UART_IER_DLH_DLH4 register field value. */
#define ALT_UART_IER_DLH_DLH4_SET_MSK    0x00000010
/* The mask used to clear the ALT_UART_IER_DLH_DLH4 register field value. */
#define ALT_UART_IER_DLH_DLH4_CLR_MSK    0xffffffef
/* The reset value of the ALT_UART_IER_DLH_DLH4 register field. */
#define ALT_UART_IER_DLH_DLH4_RESET      0x0
/* Extracts the ALT_UART_IER_DLH_DLH4 field value from a register. */
#define ALT_UART_IER_DLH_DLH4_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_UART_IER_DLH_DLH4 register field value suitable for setting the register. */
#define ALT_UART_IER_DLH_DLH4_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : DLH[5] - dlh5
 * 
 * Bit 5 of DLH value.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_IER_DLH_DLH5 register field. */
#define ALT_UART_IER_DLH_DLH5_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_UART_IER_DLH_DLH5 register field. */
#define ALT_UART_IER_DLH_DLH5_MSB        5
/* The width in bits of the ALT_UART_IER_DLH_DLH5 register field. */
#define ALT_UART_IER_DLH_DLH5_WIDTH      1
/* The mask used to set the ALT_UART_IER_DLH_DLH5 register field value. */
#define ALT_UART_IER_DLH_DLH5_SET_MSK    0x00000020
/* The mask used to clear the ALT_UART_IER_DLH_DLH5 register field value. */
#define ALT_UART_IER_DLH_DLH5_CLR_MSK    0xffffffdf
/* The reset value of the ALT_UART_IER_DLH_DLH5 register field. */
#define ALT_UART_IER_DLH_DLH5_RESET      0x0
/* Extracts the ALT_UART_IER_DLH_DLH5 field value from a register. */
#define ALT_UART_IER_DLH_DLH5_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_UART_IER_DLH_DLH5 register field value suitable for setting the register. */
#define ALT_UART_IER_DLH_DLH5_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : DLH[6] - dlh6
 * 
 * Bit 6 of DLH value.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_IER_DLH_DLH6 register field. */
#define ALT_UART_IER_DLH_DLH6_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_UART_IER_DLH_DLH6 register field. */
#define ALT_UART_IER_DLH_DLH6_MSB        6
/* The width in bits of the ALT_UART_IER_DLH_DLH6 register field. */
#define ALT_UART_IER_DLH_DLH6_WIDTH      1
/* The mask used to set the ALT_UART_IER_DLH_DLH6 register field value. */
#define ALT_UART_IER_DLH_DLH6_SET_MSK    0x00000040
/* The mask used to clear the ALT_UART_IER_DLH_DLH6 register field value. */
#define ALT_UART_IER_DLH_DLH6_CLR_MSK    0xffffffbf
/* The reset value of the ALT_UART_IER_DLH_DLH6 register field. */
#define ALT_UART_IER_DLH_DLH6_RESET      0x0
/* Extracts the ALT_UART_IER_DLH_DLH6 field value from a register. */
#define ALT_UART_IER_DLH_DLH6_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_UART_IER_DLH_DLH6 register field value suitable for setting the register. */
#define ALT_UART_IER_DLH_DLH6_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : DLH[7] and PTIME THRE Interrupt Mode Enable - ptime_dlh7
 * 
 * Divisor Latch High Register:
 * 
 * Bit 7 of DLH value.
 * 
 * Interrupt Enable Register:
 * 
 * This is used to enable/disable the generation of THRE Interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                        
 * :-----------------------------------|:------|:------------------------------------
 *  ALT_UART_IER_DLH_PTIME_DLH7_E_DISD | 0x0   | disable tx-hold-reg-empty interrupt
 *  ALT_UART_IER_DLH_PTIME_DLH7_E_END  | 0x1   | enable tx-hold-reg-empty interrupt 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_IER_DLH_PTIME_DLH7
 * 
 * disable tx-hold-reg-empty interrupt
 */
#define ALT_UART_IER_DLH_PTIME_DLH7_E_DISD  0x0
/*
 * Enumerated value for register field ALT_UART_IER_DLH_PTIME_DLH7
 * 
 * enable tx-hold-reg-empty interrupt
 */
#define ALT_UART_IER_DLH_PTIME_DLH7_E_END   0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_IER_DLH_PTIME_DLH7 register field. */
#define ALT_UART_IER_DLH_PTIME_DLH7_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_UART_IER_DLH_PTIME_DLH7 register field. */
#define ALT_UART_IER_DLH_PTIME_DLH7_MSB        7
/* The width in bits of the ALT_UART_IER_DLH_PTIME_DLH7 register field. */
#define ALT_UART_IER_DLH_PTIME_DLH7_WIDTH      1
/* The mask used to set the ALT_UART_IER_DLH_PTIME_DLH7 register field value. */
#define ALT_UART_IER_DLH_PTIME_DLH7_SET_MSK    0x00000080
/* The mask used to clear the ALT_UART_IER_DLH_PTIME_DLH7 register field value. */
#define ALT_UART_IER_DLH_PTIME_DLH7_CLR_MSK    0xffffff7f
/* The reset value of the ALT_UART_IER_DLH_PTIME_DLH7 register field. */
#define ALT_UART_IER_DLH_PTIME_DLH7_RESET      0x0
/* Extracts the ALT_UART_IER_DLH_PTIME_DLH7 field value from a register. */
#define ALT_UART_IER_DLH_PTIME_DLH7_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_UART_IER_DLH_PTIME_DLH7 register field value suitable for setting the register. */
#define ALT_UART_IER_DLH_PTIME_DLH7_SET(value) (((value) << 7) & 0x00000080)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_IER_DLH.
 */
struct ALT_UART_IER_DLH_s
{
    uint32_t  erbfi_dlh0 :  1;  /* DLH[0] and Receive Data Interrupt Enable */
    uint32_t  etbei_dlhl :  1;  /* DLH[1] and Transmit Data Interrupt Control */
    uint32_t  elsi_dhl2  :  1;  /* DLH[2] and Enable Receiver Line Status */
    uint32_t  edssi_dhl3 :  1;  /* DLH[3] and Enable Modem Status Interrupt */
    uint32_t  dlh4       :  1;  /* DLH[4] */
    uint32_t  dlh5       :  1;  /* DLH[5] */
    uint32_t  dlh6       :  1;  /* DLH[6] */
    uint32_t  ptime_dlh7 :  1;  /* DLH[7] and PTIME THRE Interrupt Mode Enable */
    uint32_t             : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_IER_DLH. */
typedef volatile struct ALT_UART_IER_DLH_s  ALT_UART_IER_DLH_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_IER_DLH register from the beginning of the component. */
#define ALT_UART_IER_DLH_OFST        0x4
/* The address of the ALT_UART_IER_DLH register. */
#define ALT_UART_IER_DLH_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_IER_DLH_OFST))

/*
 * Register : Interrupt Identity Register (when read) - iir
 * 
 * Returns interrupt identification and FIFO enable/disable when read.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description 
 * :-------|:-------|:------|:-------------
 *  [3:0]  | R      | 0x1   | Interrupt ID
 *  [5:4]  | ???    | 0x0   | *UNDEFINED* 
 *  [7:6]  | R      | 0x0   | FIFO Enabled
 *  [31:8] | ???    | 0x0   | *UNDEFINED* 
 * 
 */
/*
 * Field : Interrupt ID - id
 * 
 * This indicates the highest priority pending interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description           
 * :---------------------------------|:------|:-----------------------
 *  ALT_UART_IIR_ID_E_MODMSTAT       | 0x0   | Modem status          
 *  ALT_UART_IIR_ID_E_NOINTRPENDING  | 0x1   | No Interrupt pending  
 *  ALT_UART_IIR_ID_E_THREMPTY       | 0x2   | THR empty             
 *  ALT_UART_IIR_ID_E_RXDATAVAILABLE | 0x4   | Receive data available
 *  ALT_UART_IIR_ID_E_RXLINESTAT     | 0x6   | Receive line status   
 *  ALT_UART_IIR_ID_E_CHARTMO        | 0xc   | Character timeout     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_IIR_ID
 * 
 * Modem status
 */
#define ALT_UART_IIR_ID_E_MODMSTAT          0x0
/*
 * Enumerated value for register field ALT_UART_IIR_ID
 * 
 * No Interrupt pending
 */
#define ALT_UART_IIR_ID_E_NOINTRPENDING     0x1
/*
 * Enumerated value for register field ALT_UART_IIR_ID
 * 
 * THR empty
 */
#define ALT_UART_IIR_ID_E_THREMPTY          0x2
/*
 * Enumerated value for register field ALT_UART_IIR_ID
 * 
 * Receive data available
 */
#define ALT_UART_IIR_ID_E_RXDATAVAILABLE    0x4
/*
 * Enumerated value for register field ALT_UART_IIR_ID
 * 
 * Receive line status
 */
#define ALT_UART_IIR_ID_E_RXLINESTAT        0x6
/*
 * Enumerated value for register field ALT_UART_IIR_ID
 * 
 * Character timeout
 */
#define ALT_UART_IIR_ID_E_CHARTMO           0xc

/* The Least Significant Bit (LSB) position of the ALT_UART_IIR_ID register field. */
#define ALT_UART_IIR_ID_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_IIR_ID register field. */
#define ALT_UART_IIR_ID_MSB        3
/* The width in bits of the ALT_UART_IIR_ID register field. */
#define ALT_UART_IIR_ID_WIDTH      4
/* The mask used to set the ALT_UART_IIR_ID register field value. */
#define ALT_UART_IIR_ID_SET_MSK    0x0000000f
/* The mask used to clear the ALT_UART_IIR_ID register field value. */
#define ALT_UART_IIR_ID_CLR_MSK    0xfffffff0
/* The reset value of the ALT_UART_IIR_ID register field. */
#define ALT_UART_IIR_ID_RESET      0x1
/* Extracts the ALT_UART_IIR_ID field value from a register. */
#define ALT_UART_IIR_ID_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_UART_IIR_ID register field value suitable for setting the register. */
#define ALT_UART_IIR_ID_SET(value) (((value) << 0) & 0x0000000f)

/*
 * Field : FIFO Enabled - fifoen
 * 
 * This is used to indicate whether the FIFO's are enabled or disabled.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description  
 * :---------------------------|:------|:--------------
 *  ALT_UART_IIR_FIFOEN_E_DISD | 0x0   | FIFO disabled
 *  ALT_UART_IIR_FIFOEN_E_END  | 0x3   | FIFO enabled 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_IIR_FIFOEN
 * 
 * FIFO disabled
 */
#define ALT_UART_IIR_FIFOEN_E_DISD  0x0
/*
 * Enumerated value for register field ALT_UART_IIR_FIFOEN
 * 
 * FIFO enabled
 */
#define ALT_UART_IIR_FIFOEN_E_END   0x3

/* The Least Significant Bit (LSB) position of the ALT_UART_IIR_FIFOEN register field. */
#define ALT_UART_IIR_FIFOEN_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_UART_IIR_FIFOEN register field. */
#define ALT_UART_IIR_FIFOEN_MSB        7
/* The width in bits of the ALT_UART_IIR_FIFOEN register field. */
#define ALT_UART_IIR_FIFOEN_WIDTH      2
/* The mask used to set the ALT_UART_IIR_FIFOEN register field value. */
#define ALT_UART_IIR_FIFOEN_SET_MSK    0x000000c0
/* The mask used to clear the ALT_UART_IIR_FIFOEN register field value. */
#define ALT_UART_IIR_FIFOEN_CLR_MSK    0xffffff3f
/* The reset value of the ALT_UART_IIR_FIFOEN register field. */
#define ALT_UART_IIR_FIFOEN_RESET      0x0
/* Extracts the ALT_UART_IIR_FIFOEN field value from a register. */
#define ALT_UART_IIR_FIFOEN_GET(value) (((value) & 0x000000c0) >> 6)
/* Produces a ALT_UART_IIR_FIFOEN register field value suitable for setting the register. */
#define ALT_UART_IIR_FIFOEN_SET(value) (((value) << 6) & 0x000000c0)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_IIR.
 */
struct ALT_UART_IIR_s
{
    const uint32_t  id     :  4;  /* Interrupt ID */
    uint32_t               :  2;  /* *UNDEFINED* */
    const uint32_t  fifoen :  2;  /* FIFO Enabled */
    uint32_t               : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_IIR. */
typedef volatile struct ALT_UART_IIR_s  ALT_UART_IIR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_IIR register from the beginning of the component. */
#define ALT_UART_IIR_OFST        0x8
/* The address of the ALT_UART_IIR register. */
#define ALT_UART_IIR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_IIR_OFST))

/*
 * Register : FIFO Control (when written) - fcr
 * 
 * Controls FIFO Operations when written.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description           
 * :-------|:-------|:--------|:-----------------------
 *  [0]    | W      | Unknown | FIFO Enable           
 *  [1]    | W      | Unknown | Rx FIFO Reset         
 *  [2]    | W      | Unknown | Tx FIFO Reset         
 *  [3]    | W      | Unknown | DMA Mode              
 *  [5:4]  | W      | Unknown | Tx Empty Trigger Level
 *  [7:6]  | W      | Unknown | Rx Trigger Level      
 *  [31:8] | ???    | 0x0     | *UNDEFINED*           
 * 
 */
/*
 * Field : FIFO Enable - fifoe
 * 
 * Enables/disables the transmit (Tx) and receive (Rx ) FIFO's. Whenever the value
 * of this bit is changed both the Tx and Rx  controller portion of FIFO's will be
 * reset.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description   
 * :--------------------------|:------|:---------------
 *  ALT_UART_FCR_FIFOE_E_DISD | 0x0   | FIFOs disabled
 *  ALT_UART_FCR_FIFOE_E_END  | 0x1   | FIFOs enabled 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_FCR_FIFOE
 * 
 * FIFOs disabled
 */
#define ALT_UART_FCR_FIFOE_E_DISD   0x0
/*
 * Enumerated value for register field ALT_UART_FCR_FIFOE
 * 
 * FIFOs enabled
 */
#define ALT_UART_FCR_FIFOE_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_FCR_FIFOE register field. */
#define ALT_UART_FCR_FIFOE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_FCR_FIFOE register field. */
#define ALT_UART_FCR_FIFOE_MSB        0
/* The width in bits of the ALT_UART_FCR_FIFOE register field. */
#define ALT_UART_FCR_FIFOE_WIDTH      1
/* The mask used to set the ALT_UART_FCR_FIFOE register field value. */
#define ALT_UART_FCR_FIFOE_SET_MSK    0x00000001
/* The mask used to clear the ALT_UART_FCR_FIFOE register field value. */
#define ALT_UART_FCR_FIFOE_CLR_MSK    0xfffffffe
/* The reset value of the ALT_UART_FCR_FIFOE register field is UNKNOWN. */
#define ALT_UART_FCR_FIFOE_RESET      0x0
/* Extracts the ALT_UART_FCR_FIFOE field value from a register. */
#define ALT_UART_FCR_FIFOE_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_UART_FCR_FIFOE register field value suitable for setting the register. */
#define ALT_UART_FCR_FIFOE_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Rx FIFO Reset - rfifor
 * 
 * Resets the control portion of the receive FIFO and treats the FIFO as empty.
 * This will also de-assert the DMA Rxrequest and single signals. Note that this
 * bit is self-clearing' and it is not necessary to clear this bit.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                
 * :----------------------------|:------|:----------------------------
 *  ALT_UART_FCR_RFIFOR_E_NORST | 0x0   | No Reset of Rx FIFO Control
 *  ALT_UART_FCR_RFIFOR_E_RST   | 0x1   | Resets of Rx FIFO Control  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_FCR_RFIFOR
 * 
 * No Reset of Rx FIFO Control
 */
#define ALT_UART_FCR_RFIFOR_E_NORST 0x0
/*
 * Enumerated value for register field ALT_UART_FCR_RFIFOR
 * 
 * Resets of Rx FIFO Control
 */
#define ALT_UART_FCR_RFIFOR_E_RST   0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_FCR_RFIFOR register field. */
#define ALT_UART_FCR_RFIFOR_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_UART_FCR_RFIFOR register field. */
#define ALT_UART_FCR_RFIFOR_MSB        1
/* The width in bits of the ALT_UART_FCR_RFIFOR register field. */
#define ALT_UART_FCR_RFIFOR_WIDTH      1
/* The mask used to set the ALT_UART_FCR_RFIFOR register field value. */
#define ALT_UART_FCR_RFIFOR_SET_MSK    0x00000002
/* The mask used to clear the ALT_UART_FCR_RFIFOR register field value. */
#define ALT_UART_FCR_RFIFOR_CLR_MSK    0xfffffffd
/* The reset value of the ALT_UART_FCR_RFIFOR register field is UNKNOWN. */
#define ALT_UART_FCR_RFIFOR_RESET      0x0
/* Extracts the ALT_UART_FCR_RFIFOR field value from a register. */
#define ALT_UART_FCR_RFIFOR_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_UART_FCR_RFIFOR register field value suitable for setting the register. */
#define ALT_UART_FCR_RFIFOR_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Tx FIFO Reset - xfifor
 * 
 * Resets the control portion of the transmit FIFO and treats the FIFO as empty.
 * This will also de-assert the DMA Tx request and single signals when additional
 * DMA handshaking is used.
 * 
 * Note that this bit is 'self-clearing' and it is not necessary to clear this bit.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                
 * :----------------------------|:------|:----------------------------
 *  ALT_UART_FCR_XFIFOR_E_NORST | 0x0   | No Reset of Tx FIFO Control
 *  ALT_UART_FCR_XFIFOR_E_RST   | 0x1   | Resets Tx FIFO Control     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_FCR_XFIFOR
 * 
 * No Reset of Tx FIFO Control
 */
#define ALT_UART_FCR_XFIFOR_E_NORST 0x0
/*
 * Enumerated value for register field ALT_UART_FCR_XFIFOR
 * 
 * Resets Tx FIFO Control
 */
#define ALT_UART_FCR_XFIFOR_E_RST   0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_FCR_XFIFOR register field. */
#define ALT_UART_FCR_XFIFOR_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_UART_FCR_XFIFOR register field. */
#define ALT_UART_FCR_XFIFOR_MSB        2
/* The width in bits of the ALT_UART_FCR_XFIFOR register field. */
#define ALT_UART_FCR_XFIFOR_WIDTH      1
/* The mask used to set the ALT_UART_FCR_XFIFOR register field value. */
#define ALT_UART_FCR_XFIFOR_SET_MSK    0x00000004
/* The mask used to clear the ALT_UART_FCR_XFIFOR register field value. */
#define ALT_UART_FCR_XFIFOR_CLR_MSK    0xfffffffb
/* The reset value of the ALT_UART_FCR_XFIFOR register field is UNKNOWN. */
#define ALT_UART_FCR_XFIFOR_RESET      0x0
/* Extracts the ALT_UART_FCR_XFIFOR field value from a register. */
#define ALT_UART_FCR_XFIFOR_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_UART_FCR_XFIFOR register field value suitable for setting the register. */
#define ALT_UART_FCR_XFIFOR_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : DMA Mode - dmam
 * 
 * This determines the DMA signalling mode used for the uart_dma_tx_req_n and
 * uart_dma_rx_req_n output signals when additional DMA handshaking signals are not
 * selected. DMA mode 0 supports single DMA data transfers at a time. In mode 0,
 * the uart_dma_tx_req_n signal goes active low under the following conditions:
 * 
 * * When the Transmitter Holding Register is empty in non-FIFO mode.
 * 
 * * When the transmitter FIFO is empty in FIFO mode with Programmable  THRE
 *   interrupt mode disabled.
 * 
 * * When the transmitter FIFO is at or below the programmed threshold  with
 *   Programmable THRE interrupt mode enabled.
 * 
 * It goes inactive under the following conditions
 * 
 * * When a single character has been written into the Transmitter  Holding
 *   Register or transmitter FIFO with Programmable THRE interrupt mode disabled.
 * 
 * * When the transmitter FIFO is above the threshold with Programmable THRE
 *   interrupt mode enabled.
 * 
 * DMA mode 1 supports multi-DMA data transfers, where multiple transfers are made
 * continuously until the receiver FIFO has been emptied or the transmit FIFO has
 * been filled. In mode 1 the uart_dma_tx_req_n signal is asserted under the
 * following conditions:
 * 
 * * When the transmitter FIFO is empty with Programmable THRE  interrupt mode
 *   disabled.
 * 
 * * When the transmitter FIFO is at or below the programmed  threshold with
 *   Programmable THRE interrupt mode enabled.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description               
 * :---------------------------|:------|:---------------------------
 *  ALT_UART_FCR_DMAM_E_SINGLE | 0x0   | Single DMA Transfer Mode  
 *  ALT_UART_FCR_DMAM_E_MULT   | 0x1   | Multiple DMA Transfer Mode
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_FCR_DMAM
 * 
 * Single DMA Transfer Mode
 */
#define ALT_UART_FCR_DMAM_E_SINGLE  0x0
/*
 * Enumerated value for register field ALT_UART_FCR_DMAM
 * 
 * Multiple DMA Transfer Mode
 */
#define ALT_UART_FCR_DMAM_E_MULT    0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_FCR_DMAM register field. */
#define ALT_UART_FCR_DMAM_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_UART_FCR_DMAM register field. */
#define ALT_UART_FCR_DMAM_MSB        3
/* The width in bits of the ALT_UART_FCR_DMAM register field. */
#define ALT_UART_FCR_DMAM_WIDTH      1
/* The mask used to set the ALT_UART_FCR_DMAM register field value. */
#define ALT_UART_FCR_DMAM_SET_MSK    0x00000008
/* The mask used to clear the ALT_UART_FCR_DMAM register field value. */
#define ALT_UART_FCR_DMAM_CLR_MSK    0xfffffff7
/* The reset value of the ALT_UART_FCR_DMAM register field is UNKNOWN. */
#define ALT_UART_FCR_DMAM_RESET      0x0
/* Extracts the ALT_UART_FCR_DMAM field value from a register. */
#define ALT_UART_FCR_DMAM_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_UART_FCR_DMAM register field value suitable for setting the register. */
#define ALT_UART_FCR_DMAM_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Tx Empty Trigger Level - tet
 * 
 * This is used to select the empty threshold level at which the THRE Interrupts
 * will be generated when the mode is active. It also determines when the uart DMA
 * transmit request signal uart_dma_tx_req_n will be asserted when in certain modes
 * of operation.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description           
 * :-------------------------------|:------|:-----------------------
 *  ALT_UART_FCR_TET_E_FIFOEMPTY   | 0x0   | FIFO empty            
 *  ALT_UART_FCR_TET_E_TWOCHARS    | 0x1   | Two characters in FIFO
 *  ALT_UART_FCR_TET_E_QUARTERFULL | 0x2   | FIFO 1/4 full         
 *  ALT_UART_FCR_TET_E_HALFFULL    | 0x3   | FIFO 1/2 full         
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_FCR_TET
 * 
 * FIFO empty
 */
#define ALT_UART_FCR_TET_E_FIFOEMPTY    0x0
/*
 * Enumerated value for register field ALT_UART_FCR_TET
 * 
 * Two characters in FIFO
 */
#define ALT_UART_FCR_TET_E_TWOCHARS     0x1
/*
 * Enumerated value for register field ALT_UART_FCR_TET
 * 
 * FIFO 1/4 full
 */
#define ALT_UART_FCR_TET_E_QUARTERFULL  0x2
/*
 * Enumerated value for register field ALT_UART_FCR_TET
 * 
 * FIFO 1/2 full
 */
#define ALT_UART_FCR_TET_E_HALFFULL     0x3

/* The Least Significant Bit (LSB) position of the ALT_UART_FCR_TET register field. */
#define ALT_UART_FCR_TET_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_UART_FCR_TET register field. */
#define ALT_UART_FCR_TET_MSB        5
/* The width in bits of the ALT_UART_FCR_TET register field. */
#define ALT_UART_FCR_TET_WIDTH      2
/* The mask used to set the ALT_UART_FCR_TET register field value. */
#define ALT_UART_FCR_TET_SET_MSK    0x00000030
/* The mask used to clear the ALT_UART_FCR_TET register field value. */
#define ALT_UART_FCR_TET_CLR_MSK    0xffffffcf
/* The reset value of the ALT_UART_FCR_TET register field is UNKNOWN. */
#define ALT_UART_FCR_TET_RESET      0x0
/* Extracts the ALT_UART_FCR_TET field value from a register. */
#define ALT_UART_FCR_TET_GET(value) (((value) & 0x00000030) >> 4)
/* Produces a ALT_UART_FCR_TET register field value suitable for setting the register. */
#define ALT_UART_FCR_TET_SET(value) (((value) << 4) & 0x00000030)

/*
 * Field : Rx Trigger Level - rt
 * 
 * This register is configured to implement FIFOs. Bits[7:6], Rx Trigger (or RT):
 * This is used to select the trigger level in the receiver FIFO at which the
 * Received Data Available Interrupt will be generated. In auto flow control mode
 * it is used to determine when the uart_rts_n signal will be de-asserted. It also
 * determines when the uart_dma_rx_req_n signal will be asserted when in certain
 * modes of operation.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description          
 * :------------------------------|:------|:----------------------
 *  ALT_UART_FCR_RT_E_ONECHAR     | 0x0   | one character in fifo
 *  ALT_UART_FCR_RT_E_QUARTERFULL | 0x1   | FIFO 1/4 full        
 *  ALT_UART_FCR_RT_E_HALFFULL    | 0x2   | FIFO 1/2 full        
 *  ALT_UART_FCR_RT_E_FULLLESS2   | 0x3   | FIFO 2 less than full
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_FCR_RT
 * 
 * one character in fifo
 */
#define ALT_UART_FCR_RT_E_ONECHAR       0x0
/*
 * Enumerated value for register field ALT_UART_FCR_RT
 * 
 * FIFO 1/4 full
 */
#define ALT_UART_FCR_RT_E_QUARTERFULL   0x1
/*
 * Enumerated value for register field ALT_UART_FCR_RT
 * 
 * FIFO 1/2 full
 */
#define ALT_UART_FCR_RT_E_HALFFULL      0x2
/*
 * Enumerated value for register field ALT_UART_FCR_RT
 * 
 * FIFO 2 less than full
 */
#define ALT_UART_FCR_RT_E_FULLLESS2     0x3

/* The Least Significant Bit (LSB) position of the ALT_UART_FCR_RT register field. */
#define ALT_UART_FCR_RT_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_UART_FCR_RT register field. */
#define ALT_UART_FCR_RT_MSB        7
/* The width in bits of the ALT_UART_FCR_RT register field. */
#define ALT_UART_FCR_RT_WIDTH      2
/* The mask used to set the ALT_UART_FCR_RT register field value. */
#define ALT_UART_FCR_RT_SET_MSK    0x000000c0
/* The mask used to clear the ALT_UART_FCR_RT register field value. */
#define ALT_UART_FCR_RT_CLR_MSK    0xffffff3f
/* The reset value of the ALT_UART_FCR_RT register field is UNKNOWN. */
#define ALT_UART_FCR_RT_RESET      0x0
/* Extracts the ALT_UART_FCR_RT field value from a register. */
#define ALT_UART_FCR_RT_GET(value) (((value) & 0x000000c0) >> 6)
/* Produces a ALT_UART_FCR_RT register field value suitable for setting the register. */
#define ALT_UART_FCR_RT_SET(value) (((value) << 6) & 0x000000c0)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_FCR.
 */
struct ALT_UART_FCR_s
{
    uint32_t  fifoe  :  1;  /* FIFO Enable */
    uint32_t  rfifor :  1;  /* Rx FIFO Reset */
    uint32_t  xfifor :  1;  /* Tx FIFO Reset */
    uint32_t  dmam   :  1;  /* DMA Mode */
    uint32_t  tet    :  2;  /* Tx Empty Trigger Level */
    uint32_t  rt     :  2;  /* Rx Trigger Level */
    uint32_t         : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_FCR. */
typedef volatile struct ALT_UART_FCR_s  ALT_UART_FCR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_FCR register from the beginning of the component. */
#define ALT_UART_FCR_OFST        0x8
/* The address of the ALT_UART_FCR register. */
#define ALT_UART_FCR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_FCR_OFST))

/*
 * Register : Line Control Register (When Written) - lcr
 * 
 * Formats serial data.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description             
 * :-------|:-------|:------|:-------------------------
 *  [1:0]  | RW     | 0x0   | Data Length Select      
 *  [2]    | RW     | 0x0   | Stop Bits               
 *  [3]    | RW     | 0x0   | Parity Enable           
 *  [4]    | RW     | 0x0   | Even Parity Select      
 *  [5]    | ???    | 0x0   | *UNDEFINED*             
 *  [6]    | RW     | 0x0   | Break Control Bit       
 *  [7]    | RW     | 0x0   | Divisor Latch Access Bit
 *  [31:8] | ???    | 0x0   | *UNDEFINED*             
 * 
 */
/*
 * Field : Data Length Select - dls
 * 
 * Data Length Select.Selects the number of data bits per character that the
 * peripheral will transmit and receive.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                    | Value | Description
 * :------------------------|:------|:------------
 *  ALT_UART_LCR_DLS_E_LEN5 | 0x0   | 5 bits     
 *  ALT_UART_LCR_DLS_E_LEN6 | 0x1   | 6 bits     
 *  ALT_UART_LCR_DLS_E_LEN7 | 0x2   | 7 bits     
 *  ALT_UART_LCR_DLS_E_LEN8 | 0x3   | 8 bits     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_LCR_DLS
 * 
 * 5 bits
 */
#define ALT_UART_LCR_DLS_E_LEN5 0x0
/*
 * Enumerated value for register field ALT_UART_LCR_DLS
 * 
 * 6 bits
 */
#define ALT_UART_LCR_DLS_E_LEN6 0x1
/*
 * Enumerated value for register field ALT_UART_LCR_DLS
 * 
 * 7 bits
 */
#define ALT_UART_LCR_DLS_E_LEN7 0x2
/*
 * Enumerated value for register field ALT_UART_LCR_DLS
 * 
 * 8 bits
 */
#define ALT_UART_LCR_DLS_E_LEN8 0x3

/* The Least Significant Bit (LSB) position of the ALT_UART_LCR_DLS register field. */
#define ALT_UART_LCR_DLS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_LCR_DLS register field. */
#define ALT_UART_LCR_DLS_MSB        1
/* The width in bits of the ALT_UART_LCR_DLS register field. */
#define ALT_UART_LCR_DLS_WIDTH      2
/* The mask used to set the ALT_UART_LCR_DLS register field value. */
#define ALT_UART_LCR_DLS_SET_MSK    0x00000003
/* The mask used to clear the ALT_UART_LCR_DLS register field value. */
#define ALT_UART_LCR_DLS_CLR_MSK    0xfffffffc
/* The reset value of the ALT_UART_LCR_DLS register field. */
#define ALT_UART_LCR_DLS_RESET      0x0
/* Extracts the ALT_UART_LCR_DLS field value from a register. */
#define ALT_UART_LCR_DLS_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_UART_LCR_DLS register field value suitable for setting the register. */
#define ALT_UART_LCR_DLS_SET(value) (((value) << 0) & 0x00000003)

/*
 * Field : Stop Bits - stop
 * 
 * Number of stop bits. Used to select the number of stop bits per character that
 * the peripheral will transmit and receive.Note that regardless of the number of
 * stop bits selected the receiver will only check the first stop bit.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                              
 * :----------------------------------|:------|:------------------------------------------
 *  ALT_UART_LCR_STOP_E_ONESTOP       | 0x0   | one stop bit                             
 *  ALT_UART_LCR_STOP_E_ONEPOINT5STOP | 0x1   | 1.5 stop bits when DLS (LCR[1:0]) is zero
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_LCR_STOP
 * 
 * one stop bit
 */
#define ALT_UART_LCR_STOP_E_ONESTOP         0x0
/*
 * Enumerated value for register field ALT_UART_LCR_STOP
 * 
 * 1.5 stop bits when DLS (LCR[1:0]) is zero
 */
#define ALT_UART_LCR_STOP_E_ONEPOINT5STOP   0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_LCR_STOP register field. */
#define ALT_UART_LCR_STOP_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_UART_LCR_STOP register field. */
#define ALT_UART_LCR_STOP_MSB        2
/* The width in bits of the ALT_UART_LCR_STOP register field. */
#define ALT_UART_LCR_STOP_WIDTH      1
/* The mask used to set the ALT_UART_LCR_STOP register field value. */
#define ALT_UART_LCR_STOP_SET_MSK    0x00000004
/* The mask used to clear the ALT_UART_LCR_STOP register field value. */
#define ALT_UART_LCR_STOP_CLR_MSK    0xfffffffb
/* The reset value of the ALT_UART_LCR_STOP register field. */
#define ALT_UART_LCR_STOP_RESET      0x0
/* Extracts the ALT_UART_LCR_STOP field value from a register. */
#define ALT_UART_LCR_STOP_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_UART_LCR_STOP register field value suitable for setting the register. */
#define ALT_UART_LCR_STOP_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Parity Enable - pen
 * 
 * This bit is used to enable and disable parity generation and detection in a
 * transmitted and received data character.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                    | Value | Description    
 * :------------------------|:------|:----------------
 *  ALT_UART_LCR_PEN_E_DISD | 0x0   | parity disabled
 *  ALT_UART_LCR_PEN_E_END  | 0x1   | parity enabled 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_LCR_PEN
 * 
 * parity disabled
 */
#define ALT_UART_LCR_PEN_E_DISD 0x0
/*
 * Enumerated value for register field ALT_UART_LCR_PEN
 * 
 * parity enabled
 */
#define ALT_UART_LCR_PEN_E_END  0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_LCR_PEN register field. */
#define ALT_UART_LCR_PEN_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_UART_LCR_PEN register field. */
#define ALT_UART_LCR_PEN_MSB        3
/* The width in bits of the ALT_UART_LCR_PEN register field. */
#define ALT_UART_LCR_PEN_WIDTH      1
/* The mask used to set the ALT_UART_LCR_PEN register field value. */
#define ALT_UART_LCR_PEN_SET_MSK    0x00000008
/* The mask used to clear the ALT_UART_LCR_PEN register field value. */
#define ALT_UART_LCR_PEN_CLR_MSK    0xfffffff7
/* The reset value of the ALT_UART_LCR_PEN register field. */
#define ALT_UART_LCR_PEN_RESET      0x0
/* Extracts the ALT_UART_LCR_PEN field value from a register. */
#define ALT_UART_LCR_PEN_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_UART_LCR_PEN register field value suitable for setting the register. */
#define ALT_UART_LCR_PEN_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Even Parity Select - eps
 * 
 * This is used to select between even and odd parity, when parity is enabled (PEN
 * set to one). If set to one, an even number of logic '1's is transmitted or
 * checked. If set to zero, an odd number of logic '1's is transmitted or checked.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description
 * :---------------------------|:------|:------------
 *  ALT_UART_LCR_EPS_E_ODDPAR  | 0x0   | odd parity 
 *  ALT_UART_LCR_EPS_E_EVENPAR | 0x1   | even parity
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_LCR_EPS
 * 
 * odd parity
 */
#define ALT_UART_LCR_EPS_E_ODDPAR   0x0
/*
 * Enumerated value for register field ALT_UART_LCR_EPS
 * 
 * even parity
 */
#define ALT_UART_LCR_EPS_E_EVENPAR  0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_LCR_EPS register field. */
#define ALT_UART_LCR_EPS_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_UART_LCR_EPS register field. */
#define ALT_UART_LCR_EPS_MSB        4
/* The width in bits of the ALT_UART_LCR_EPS register field. */
#define ALT_UART_LCR_EPS_WIDTH      1
/* The mask used to set the ALT_UART_LCR_EPS register field value. */
#define ALT_UART_LCR_EPS_SET_MSK    0x00000010
/* The mask used to clear the ALT_UART_LCR_EPS register field value. */
#define ALT_UART_LCR_EPS_CLR_MSK    0xffffffef
/* The reset value of the ALT_UART_LCR_EPS register field. */
#define ALT_UART_LCR_EPS_RESET      0x0
/* Extracts the ALT_UART_LCR_EPS field value from a register. */
#define ALT_UART_LCR_EPS_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_UART_LCR_EPS register field value suitable for setting the register. */
#define ALT_UART_LCR_EPS_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Break Control Bit - break
 * 
 * This is used to cause a break condition to be transmitted to the receiving
 * device. If set to one the serial output is forced to the spacing (logic 0)
 * state. When not in Loopback Mode, as determined by MCR[4], the sout line is
 * forced low until the Break bit is cleared. When in Loopback Mode, the break
 * condition is internally looped back to the receiver and the sir_out_n line is
 * forced low.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_LCR_BREAK register field. */
#define ALT_UART_LCR_BREAK_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_UART_LCR_BREAK register field. */
#define ALT_UART_LCR_BREAK_MSB        6
/* The width in bits of the ALT_UART_LCR_BREAK register field. */
#define ALT_UART_LCR_BREAK_WIDTH      1
/* The mask used to set the ALT_UART_LCR_BREAK register field value. */
#define ALT_UART_LCR_BREAK_SET_MSK    0x00000040
/* The mask used to clear the ALT_UART_LCR_BREAK register field value. */
#define ALT_UART_LCR_BREAK_CLR_MSK    0xffffffbf
/* The reset value of the ALT_UART_LCR_BREAK register field. */
#define ALT_UART_LCR_BREAK_RESET      0x0
/* Extracts the ALT_UART_LCR_BREAK field value from a register. */
#define ALT_UART_LCR_BREAK_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_UART_LCR_BREAK register field value suitable for setting the register. */
#define ALT_UART_LCR_BREAK_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Divisor Latch Access Bit - dlab
 * 
 * Used to enable reading and writing of the Divisor Latch  register (DLL and DLH)
 * to set the baud rate of the  UART. This bit must be cleared after initial baud
 * rate setup in order to access other registers.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_LCR_DLAB register field. */
#define ALT_UART_LCR_DLAB_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_UART_LCR_DLAB register field. */
#define ALT_UART_LCR_DLAB_MSB        7
/* The width in bits of the ALT_UART_LCR_DLAB register field. */
#define ALT_UART_LCR_DLAB_WIDTH      1
/* The mask used to set the ALT_UART_LCR_DLAB register field value. */
#define ALT_UART_LCR_DLAB_SET_MSK    0x00000080
/* The mask used to clear the ALT_UART_LCR_DLAB register field value. */
#define ALT_UART_LCR_DLAB_CLR_MSK    0xffffff7f
/* The reset value of the ALT_UART_LCR_DLAB register field. */
#define ALT_UART_LCR_DLAB_RESET      0x0
/* Extracts the ALT_UART_LCR_DLAB field value from a register. */
#define ALT_UART_LCR_DLAB_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_UART_LCR_DLAB register field value suitable for setting the register. */
#define ALT_UART_LCR_DLAB_SET(value) (((value) << 7) & 0x00000080)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_LCR.
 */
struct ALT_UART_LCR_s
{
    uint32_t  dls    :  2;  /* Data Length Select */
    uint32_t  stop   :  1;  /* Stop Bits */
    uint32_t  pen    :  1;  /* Parity Enable */
    uint32_t  eps    :  1;  /* Even Parity Select */
    uint32_t         :  1;  /* *UNDEFINED* */
    uint32_t  break_ :  1;  /* Break Control Bit */
    uint32_t  dlab   :  1;  /* Divisor Latch Access Bit */
    uint32_t         : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_LCR. */
typedef volatile struct ALT_UART_LCR_s  ALT_UART_LCR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_LCR register from the beginning of the component. */
#define ALT_UART_LCR_OFST        0xc
/* The address of the ALT_UART_LCR register. */
#define ALT_UART_LCR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_LCR_OFST))

/*
 * Register : Modem Control Register - mcr
 * 
 * Reports various operations of the modem signals
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description             
 * :-------|:-------|:------|:-------------------------
 *  [0]    | RW     | 0x0   | Data Terminal Ready     
 *  [1]    | RW     | 0x0   | Request to Send         
 *  [2]    | RW     | 0x0   | Out1                    
 *  [3]    | RW     | 0x0   | out2                    
 *  [4]    | RW     | 0x0   | LoopBack Bit            
 *  [5]    | RW     | 0x0   | Auto Flow Control Enable
 *  [31:6] | ???    | 0x0   | *UNDEFINED*             
 * 
 */
/*
 * Field : Data Terminal Ready - dtr
 * 
 * This is used to directly control the Data Terminal Ready output. The value
 * written to this location is inverted and driven out on uart_dtr_n, that is: The
 * Data Terminal Ready output is used to inform the modem or data set that the UART
 * is ready to establish communications.
 * 
 * Note that Loopback mode bit [4] of MCR is set to one, the uart_dtr_n output is
 * held inactive high while the value of this location is internally looped  back
 * to an input.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description                     
 * :--------------------------|:------|:---------------------------------
 *  ALT_UART_MCR_DTR_E_LOGIC1 | 0x0   | uart_dtr_n de-asserted (logic 1)
 *  ALT_UART_MCR_DTR_E_LOGIC0 | 0x1   | uart_dtr_n asserted (logic 0)   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_MCR_DTR
 * 
 * uart_dtr_n de-asserted (logic 1)
 */
#define ALT_UART_MCR_DTR_E_LOGIC1   0x0
/*
 * Enumerated value for register field ALT_UART_MCR_DTR
 * 
 * uart_dtr_n asserted (logic 0)
 */
#define ALT_UART_MCR_DTR_E_LOGIC0   0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_MCR_DTR register field. */
#define ALT_UART_MCR_DTR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_MCR_DTR register field. */
#define ALT_UART_MCR_DTR_MSB        0
/* The width in bits of the ALT_UART_MCR_DTR register field. */
#define ALT_UART_MCR_DTR_WIDTH      1
/* The mask used to set the ALT_UART_MCR_DTR register field value. */
#define ALT_UART_MCR_DTR_SET_MSK    0x00000001
/* The mask used to clear the ALT_UART_MCR_DTR register field value. */
#define ALT_UART_MCR_DTR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_UART_MCR_DTR register field. */
#define ALT_UART_MCR_DTR_RESET      0x0
/* Extracts the ALT_UART_MCR_DTR field value from a register. */
#define ALT_UART_MCR_DTR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_UART_MCR_DTR register field value suitable for setting the register. */
#define ALT_UART_MCR_DTR_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Request to Send - rts
 * 
 * This is used to directly control the Request to Send (uart_rts_n) output. The
 * Request to Send (uart_rts_n) output is used to inform the modem or data set that
 * the UART is ready to exchange data. When Auto RTS Flow Control is not enabled
 * (MCR[5] set to zero), the uart_rts_n signal is set low by programming MCR[1]
 * (RTS) to a high. If Auto Flow Control is active (MCR[5] set to one) and FIFO's
 * enable (FCR[0] set to one), the uart_rts_n output is controlled in the same way,
 * but is also gated with the receiver FIFO threshold trigger (uart_rts_n is
 * inactive high when above the threshold). The uart_rts_n signal will be de-
 * asserted when MCR[1] is set low.
 * 
 * Note that in Loopback mode (MCR[4] set to one), the uart_rts_n output is held
 * inactive high while the value of this location is internally looped back to an
 * input.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description                     
 * :--------------------------|:------|:---------------------------------
 *  ALT_UART_MCR_RTS_E_LOGIC1 | 0x0   | uart_rts_n de-asserted (logic 1)
 *  ALT_UART_MCR_RTS_E_LOGIC0 | 0x1   | uart_rts_n asserted (logic 0)   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_MCR_RTS
 * 
 * uart_rts_n de-asserted (logic 1)
 */
#define ALT_UART_MCR_RTS_E_LOGIC1   0x0
/*
 * Enumerated value for register field ALT_UART_MCR_RTS
 * 
 * uart_rts_n asserted (logic 0)
 */
#define ALT_UART_MCR_RTS_E_LOGIC0   0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_MCR_RTS register field. */
#define ALT_UART_MCR_RTS_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_UART_MCR_RTS register field. */
#define ALT_UART_MCR_RTS_MSB        1
/* The width in bits of the ALT_UART_MCR_RTS register field. */
#define ALT_UART_MCR_RTS_WIDTH      1
/* The mask used to set the ALT_UART_MCR_RTS register field value. */
#define ALT_UART_MCR_RTS_SET_MSK    0x00000002
/* The mask used to clear the ALT_UART_MCR_RTS register field value. */
#define ALT_UART_MCR_RTS_CLR_MSK    0xfffffffd
/* The reset value of the ALT_UART_MCR_RTS register field. */
#define ALT_UART_MCR_RTS_RESET      0x0
/* Extracts the ALT_UART_MCR_RTS field value from a register. */
#define ALT_UART_MCR_RTS_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_UART_MCR_RTS register field value suitable for setting the register. */
#define ALT_UART_MCR_RTS_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Out1 - out1
 * 
 * The value written to this location is inverted and driven out on uart_out1_n
 * pin.
 * 
 * Note that in Loopback mode (MCR[4] set to one), the uart_out1_n output is held
 * inactive high while the value of this location is internally looped back to an
 * input.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                      
 * :---------------------------|:------|:----------------------------------
 *  ALT_UART_MCR_OUT1_E_LOGIC1 | 0x0   | uart_out1_n de-asserted (logic 1)
 *  ALT_UART_MCR_OUT1_E_LOGIC0 | 0x1   | uart_out1_n asserted (logic 0)   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_MCR_OUT1
 * 
 * uart_out1_n de-asserted (logic 1)
 */
#define ALT_UART_MCR_OUT1_E_LOGIC1  0x0
/*
 * Enumerated value for register field ALT_UART_MCR_OUT1
 * 
 * uart_out1_n asserted (logic 0)
 */
#define ALT_UART_MCR_OUT1_E_LOGIC0  0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_MCR_OUT1 register field. */
#define ALT_UART_MCR_OUT1_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_UART_MCR_OUT1 register field. */
#define ALT_UART_MCR_OUT1_MSB        2
/* The width in bits of the ALT_UART_MCR_OUT1 register field. */
#define ALT_UART_MCR_OUT1_WIDTH      1
/* The mask used to set the ALT_UART_MCR_OUT1 register field value. */
#define ALT_UART_MCR_OUT1_SET_MSK    0x00000004
/* The mask used to clear the ALT_UART_MCR_OUT1 register field value. */
#define ALT_UART_MCR_OUT1_CLR_MSK    0xfffffffb
/* The reset value of the ALT_UART_MCR_OUT1 register field. */
#define ALT_UART_MCR_OUT1_RESET      0x0
/* Extracts the ALT_UART_MCR_OUT1 field value from a register. */
#define ALT_UART_MCR_OUT1_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_UART_MCR_OUT1 register field value suitable for setting the register. */
#define ALT_UART_MCR_OUT1_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : out2 - out2
 * 
 * This is used to directly control the user-designated uart_out2_n output. The
 * value written to this location is inverted and driven out on uart_out2_n
 * 
 * Note: In Loopback mode bit 4 of the modem control register (MCR) is set to one,
 * the uart_out2_n output is held inactive high while the value of this location is
 * internally looped back to an input.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                      
 * :---------------------------|:------|:----------------------------------
 *  ALT_UART_MCR_OUT2_E_LOGIC1 | 0x0   | uart_out2_n de-asserted (logic 1)
 *  ALT_UART_MCR_OUT2_E_LOGIC0 | 0x1   | uart_out2_n asserted (logic 0)   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_MCR_OUT2
 * 
 * uart_out2_n de-asserted (logic 1)
 */
#define ALT_UART_MCR_OUT2_E_LOGIC1  0x0
/*
 * Enumerated value for register field ALT_UART_MCR_OUT2
 * 
 * uart_out2_n asserted (logic 0)
 */
#define ALT_UART_MCR_OUT2_E_LOGIC0  0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_MCR_OUT2 register field. */
#define ALT_UART_MCR_OUT2_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_UART_MCR_OUT2 register field. */
#define ALT_UART_MCR_OUT2_MSB        3
/* The width in bits of the ALT_UART_MCR_OUT2 register field. */
#define ALT_UART_MCR_OUT2_WIDTH      1
/* The mask used to set the ALT_UART_MCR_OUT2 register field value. */
#define ALT_UART_MCR_OUT2_SET_MSK    0x00000008
/* The mask used to clear the ALT_UART_MCR_OUT2 register field value. */
#define ALT_UART_MCR_OUT2_CLR_MSK    0xfffffff7
/* The reset value of the ALT_UART_MCR_OUT2 register field. */
#define ALT_UART_MCR_OUT2_RESET      0x0
/* Extracts the ALT_UART_MCR_OUT2 field value from a register. */
#define ALT_UART_MCR_OUT2_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_UART_MCR_OUT2 register field value suitable for setting the register. */
#define ALT_UART_MCR_OUT2_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : LoopBack Bit - loopback
 * 
 * This is used to put the UART into a diagnostic mode for test purposes. If UART
 * mode is NOT active, bit [6] of the modem control register MCR is set to zero,
 * data on the sout line is held high, while serial data output is looped back to
 * the sin line, internally. In this mode all the interrupts are fully functional.
 * Also, in loopback mode, the modem control inputs (uart_dsr_n, uart_cts_n,
 * uart_ri_n, uart_dcd_n) are disconnected and the modem control outputs
 * (uart_dtr_n, uart_rts_n, uart_out1_n, uart_out2_n) are loopedback to the inputs,
 * internally.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_MCR_LOOPBACK register field. */
#define ALT_UART_MCR_LOOPBACK_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_UART_MCR_LOOPBACK register field. */
#define ALT_UART_MCR_LOOPBACK_MSB        4
/* The width in bits of the ALT_UART_MCR_LOOPBACK register field. */
#define ALT_UART_MCR_LOOPBACK_WIDTH      1
/* The mask used to set the ALT_UART_MCR_LOOPBACK register field value. */
#define ALT_UART_MCR_LOOPBACK_SET_MSK    0x00000010
/* The mask used to clear the ALT_UART_MCR_LOOPBACK register field value. */
#define ALT_UART_MCR_LOOPBACK_CLR_MSK    0xffffffef
/* The reset value of the ALT_UART_MCR_LOOPBACK register field. */
#define ALT_UART_MCR_LOOPBACK_RESET      0x0
/* Extracts the ALT_UART_MCR_LOOPBACK field value from a register. */
#define ALT_UART_MCR_LOOPBACK_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_UART_MCR_LOOPBACK register field value suitable for setting the register. */
#define ALT_UART_MCR_LOOPBACK_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Auto Flow Control Enable - afce
 * 
 * When FIFOs are enabled, the Auto Flow Control enable bits are active.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                     | Value | Description                    
 * :-------------------------|:------|:--------------------------------
 *  ALT_UART_MCR_AFCE_E_DISD | 0x0   | Auto Flow Control Mode disabled
 *  ALT_UART_MCR_AFCE_E_END  | 0x1   | Auto Flow Control Mode enabled 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_MCR_AFCE
 * 
 * Auto Flow Control Mode disabled
 */
#define ALT_UART_MCR_AFCE_E_DISD    0x0
/*
 * Enumerated value for register field ALT_UART_MCR_AFCE
 * 
 * Auto Flow Control Mode enabled
 */
#define ALT_UART_MCR_AFCE_E_END     0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_MCR_AFCE register field. */
#define ALT_UART_MCR_AFCE_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_UART_MCR_AFCE register field. */
#define ALT_UART_MCR_AFCE_MSB        5
/* The width in bits of the ALT_UART_MCR_AFCE register field. */
#define ALT_UART_MCR_AFCE_WIDTH      1
/* The mask used to set the ALT_UART_MCR_AFCE register field value. */
#define ALT_UART_MCR_AFCE_SET_MSK    0x00000020
/* The mask used to clear the ALT_UART_MCR_AFCE register field value. */
#define ALT_UART_MCR_AFCE_CLR_MSK    0xffffffdf
/* The reset value of the ALT_UART_MCR_AFCE register field. */
#define ALT_UART_MCR_AFCE_RESET      0x0
/* Extracts the ALT_UART_MCR_AFCE field value from a register. */
#define ALT_UART_MCR_AFCE_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_UART_MCR_AFCE register field value suitable for setting the register. */
#define ALT_UART_MCR_AFCE_SET(value) (((value) << 5) & 0x00000020)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_MCR.
 */
struct ALT_UART_MCR_s
{
    uint32_t  dtr      :  1;  /* Data Terminal Ready */
    uint32_t  rts      :  1;  /* Request to Send */
    uint32_t  out1     :  1;  /* Out1 */
    uint32_t  out2     :  1;  /* out2 */
    uint32_t  loopback :  1;  /* LoopBack Bit */
    uint32_t  afce     :  1;  /* Auto Flow Control Enable */
    uint32_t           : 26;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_MCR. */
typedef volatile struct ALT_UART_MCR_s  ALT_UART_MCR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_MCR register from the beginning of the component. */
#define ALT_UART_MCR_OFST        0x10
/* The address of the ALT_UART_MCR register. */
#define ALT_UART_MCR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_MCR_OFST))

/*
 * Register : Line Status Register - lsr
 * 
 * Reports status of transmit and receive.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                        
 * :-------|:-------|:------|:------------------------------------
 *  [0]    | R      | 0x0   | Data Ready bit                     
 *  [1]    | R      | 0x0   | Overrun error                      
 *  [2]    | R      | 0x0   | Parity Error                       
 *  [3]    | R      | 0x0   | Framing Error                      
 *  [4]    | R      | 0x0   | Break Interrupt                    
 *  [5]    | R      | 0x1   | Transmit Holding Register Empty bit
 *  [6]    | R      | 0x1   | Transmitter Empty bit              
 *  [7]    | R      | 0x0   | Receiver FIFO Error bit            
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                        
 * 
 */
/*
 * Field : Data Ready bit - dr
 * 
 * This is used to indicate that the receiver contains at least one character in
 * the RBR or the receiver FIFO. This bit is cleared when the RBR is read in the
 * non-FIFO mode, or when the receiver FIFO is empty, in the FIFO mode.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description  
 * :----------------------------|:------|:--------------
 *  ALT_UART_LSR_DR_E_NODATARDY | 0x0   | no data ready
 *  ALT_UART_LSR_DR_E_DATARDY   | 0x1   | data ready   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_LSR_DR
 * 
 * no data ready
 */
#define ALT_UART_LSR_DR_E_NODATARDY 0x0
/*
 * Enumerated value for register field ALT_UART_LSR_DR
 * 
 * data ready
 */
#define ALT_UART_LSR_DR_E_DATARDY   0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_LSR_DR register field. */
#define ALT_UART_LSR_DR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_LSR_DR register field. */
#define ALT_UART_LSR_DR_MSB        0
/* The width in bits of the ALT_UART_LSR_DR register field. */
#define ALT_UART_LSR_DR_WIDTH      1
/* The mask used to set the ALT_UART_LSR_DR register field value. */
#define ALT_UART_LSR_DR_SET_MSK    0x00000001
/* The mask used to clear the ALT_UART_LSR_DR register field value. */
#define ALT_UART_LSR_DR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_UART_LSR_DR register field. */
#define ALT_UART_LSR_DR_RESET      0x0
/* Extracts the ALT_UART_LSR_DR field value from a register. */
#define ALT_UART_LSR_DR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_UART_LSR_DR register field value suitable for setting the register. */
#define ALT_UART_LSR_DR_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Overrun error - oe
 * 
 * This is used to indicate the occurrence of an overrun error. This occurs if a
 * new data character was received before the previous data was read. In the non-
 * FIFO mode, the OE bit is set when a new character arrives in the receiver before
 * the previous character was read from the RBR. When this happens, the data in the
 * RBR is overwritten. In the FIFO mode, an overrun error occurs when the FIFO is
 * full and new character arrives at the receiver. The data in the FIFO is retained
 * and the data in the receive shift register is lost.Reading the LSR clears the OE
 * bit.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description     
 * :----------------------------|:------|:-----------------
 *  ALT_UART_LSR_OE_E_NOOVERRUN | 0x0   | no overrun error
 *  ALT_UART_LSR_OE_E_OVERRUN   | 0x1   | overrun error   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_LSR_OE
 * 
 * no overrun error
 */
#define ALT_UART_LSR_OE_E_NOOVERRUN 0x0
/*
 * Enumerated value for register field ALT_UART_LSR_OE
 * 
 * overrun error
 */
#define ALT_UART_LSR_OE_E_OVERRUN   0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_LSR_OE register field. */
#define ALT_UART_LSR_OE_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_UART_LSR_OE register field. */
#define ALT_UART_LSR_OE_MSB        1
/* The width in bits of the ALT_UART_LSR_OE register field. */
#define ALT_UART_LSR_OE_WIDTH      1
/* The mask used to set the ALT_UART_LSR_OE register field value. */
#define ALT_UART_LSR_OE_SET_MSK    0x00000002
/* The mask used to clear the ALT_UART_LSR_OE register field value. */
#define ALT_UART_LSR_OE_CLR_MSK    0xfffffffd
/* The reset value of the ALT_UART_LSR_OE register field. */
#define ALT_UART_LSR_OE_RESET      0x0
/* Extracts the ALT_UART_LSR_OE field value from a register. */
#define ALT_UART_LSR_OE_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_UART_LSR_OE register field value suitable for setting the register. */
#define ALT_UART_LSR_OE_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Parity Error - pe
 * 
 * This is used to indicate the occurrence of a parity error in the receiver if the
 * Parity Enable (PEN) bit (LCR[3]) is set. Since the parity error is associated
 * with a character received, it is revealed when the character with the parity
 * error arrives at the top of the FIFO. It should be noted that the Parity Error
 * (PE) bit (LSR[2]) will be set if a break interrupt has occurred, as indicated by
 * Break Interrupt (BI) bit (LSR[4]). Reading the LSR clears the PE bit.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description    
 * :------------------------------|:------|:----------------
 *  ALT_UART_LSR_PE_E_NOPARITYERR | 0x0   | no parity error
 *  ALT_UART_LSR_PE_E_PARITYERR   | 0x1   | no parity error
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_LSR_PE
 * 
 * no parity error
 */
#define ALT_UART_LSR_PE_E_NOPARITYERR   0x0
/*
 * Enumerated value for register field ALT_UART_LSR_PE
 * 
 * no parity error
 */
#define ALT_UART_LSR_PE_E_PARITYERR     0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_LSR_PE register field. */
#define ALT_UART_LSR_PE_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_UART_LSR_PE register field. */
#define ALT_UART_LSR_PE_MSB        2
/* The width in bits of the ALT_UART_LSR_PE register field. */
#define ALT_UART_LSR_PE_WIDTH      1
/* The mask used to set the ALT_UART_LSR_PE register field value. */
#define ALT_UART_LSR_PE_SET_MSK    0x00000004
/* The mask used to clear the ALT_UART_LSR_PE register field value. */
#define ALT_UART_LSR_PE_CLR_MSK    0xfffffffb
/* The reset value of the ALT_UART_LSR_PE register field. */
#define ALT_UART_LSR_PE_RESET      0x0
/* Extracts the ALT_UART_LSR_PE field value from a register. */
#define ALT_UART_LSR_PE_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_UART_LSR_PE register field value suitable for setting the register. */
#define ALT_UART_LSR_PE_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Framing Error - fe
 * 
 * This is used to indicate the occurrence of a framing error in the receiver. A
 * framing error occurs when the receiver does not detect a valid STOP bit in the
 * received data. In the FIFO mode, since the framing error is associated with a
 * character received, it is revealed when the character with the framing error is
 * at the top of the FIFO. When a framing error occurs the UART will try to
 * resynchronize. It does this by assuming that the error was due to the start bit
 * of the next character and then continues receiving the other bit i.e. data,
 * and/or parity and stop. It should be noted that the Framing Error (FE)
 * bit(LSR[3]) will be set if a break interrupt has occurred, as indicated by a
 * Break Interrupt BIT bit (LSR[4]). Reading the LSR clears the FE bit.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description     
 * :---------------------------|:------|:-----------------
 *  ALT_UART_LSR_FE_E_NOFRMERR | 0x0   | no framing error
 *  ALT_UART_LSR_FE_E_FRMERR   | 0x1   | framing error   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_LSR_FE
 * 
 * no framing error
 */
#define ALT_UART_LSR_FE_E_NOFRMERR  0x0
/*
 * Enumerated value for register field ALT_UART_LSR_FE
 * 
 * framing error
 */
#define ALT_UART_LSR_FE_E_FRMERR    0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_LSR_FE register field. */
#define ALT_UART_LSR_FE_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_UART_LSR_FE register field. */
#define ALT_UART_LSR_FE_MSB        3
/* The width in bits of the ALT_UART_LSR_FE register field. */
#define ALT_UART_LSR_FE_WIDTH      1
/* The mask used to set the ALT_UART_LSR_FE register field value. */
#define ALT_UART_LSR_FE_SET_MSK    0x00000008
/* The mask used to clear the ALT_UART_LSR_FE register field value. */
#define ALT_UART_LSR_FE_CLR_MSK    0xfffffff7
/* The reset value of the ALT_UART_LSR_FE register field. */
#define ALT_UART_LSR_FE_RESET      0x0
/* Extracts the ALT_UART_LSR_FE field value from a register. */
#define ALT_UART_LSR_FE_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_UART_LSR_FE register field value suitable for setting the register. */
#define ALT_UART_LSR_FE_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Break Interrupt - bi
 * 
 * This is used to indicate the detection of a break sequence on the serial input
 * data.  Set whenever the serial input, sin, is held in a logic 0 state for longer
 * than the sum of start time + data bits + parity + stop bits. A break condition
 * on serial input causes one and only one character, consisting of all zeros, to
 * be received by the UART. The character associated with the break condition is
 * carried through the FIFO and is revealed when the character is at the top of the
 * FIFO. Reading the LSR clears the BI bit.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_LSR_BI register field. */
#define ALT_UART_LSR_BI_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_UART_LSR_BI register field. */
#define ALT_UART_LSR_BI_MSB        4
/* The width in bits of the ALT_UART_LSR_BI register field. */
#define ALT_UART_LSR_BI_WIDTH      1
/* The mask used to set the ALT_UART_LSR_BI register field value. */
#define ALT_UART_LSR_BI_SET_MSK    0x00000010
/* The mask used to clear the ALT_UART_LSR_BI register field value. */
#define ALT_UART_LSR_BI_CLR_MSK    0xffffffef
/* The reset value of the ALT_UART_LSR_BI register field. */
#define ALT_UART_LSR_BI_RESET      0x0
/* Extracts the ALT_UART_LSR_BI field value from a register. */
#define ALT_UART_LSR_BI_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_UART_LSR_BI register field value suitable for setting the register. */
#define ALT_UART_LSR_BI_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Transmit Holding Register Empty bit - thre
 * 
 * If THRE mode is disabled (IER[7] set to zero) this bit indicates that the THR or
 * Tx FIFO is empty. This bit is set whenever data is transferred from the THR or
 * Tx FIFO to the transmitter shift register and no new data has been written to
 * the THR or Tx FIFO. This also causes a THRE Interrupt to occur, if the THRE
 * Interrupt is enabled. If both THRE and FIFOs are enabled, both (IER[7] set to
 * one and FCR[0] set to one respectively), the functionality will indicate the
 * transmitter FIFO is full, and no longer controls THRE interrupts, which are then
 * controlled by the FCR[5:4] thresholdsetting.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_LSR_THRE register field. */
#define ALT_UART_LSR_THRE_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_UART_LSR_THRE register field. */
#define ALT_UART_LSR_THRE_MSB        5
/* The width in bits of the ALT_UART_LSR_THRE register field. */
#define ALT_UART_LSR_THRE_WIDTH      1
/* The mask used to set the ALT_UART_LSR_THRE register field value. */
#define ALT_UART_LSR_THRE_SET_MSK    0x00000020
/* The mask used to clear the ALT_UART_LSR_THRE register field value. */
#define ALT_UART_LSR_THRE_CLR_MSK    0xffffffdf
/* The reset value of the ALT_UART_LSR_THRE register field. */
#define ALT_UART_LSR_THRE_RESET      0x1
/* Extracts the ALT_UART_LSR_THRE field value from a register. */
#define ALT_UART_LSR_THRE_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_UART_LSR_THRE register field value suitable for setting the register. */
#define ALT_UART_LSR_THRE_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Transmitter Empty bit - temt
 * 
 * If in FIFO mode and FIFO's enabled (FCR[0] set to one), this bit is set whenever
 * the Transmitter Shift Register and the FIFO are both empty. If FIFO's are
 * disabled, this bit is set whenever the Transmitter Holding Register and the
 * Transmitter Shift Register are both empty.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description           
 * :-----------------------------|:------|:-----------------------
 *  ALT_UART_LSR_TEMT_E_NOTEMPTY | 0x0   | Transmit Empty not set
 *  ALT_UART_LSR_TEMT_E_EMPTY    | 0x1   | Transmit Empty set    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_LSR_TEMT
 * 
 * Transmit Empty not set
 */
#define ALT_UART_LSR_TEMT_E_NOTEMPTY    0x0
/*
 * Enumerated value for register field ALT_UART_LSR_TEMT
 * 
 * Transmit Empty set
 */
#define ALT_UART_LSR_TEMT_E_EMPTY       0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_LSR_TEMT register field. */
#define ALT_UART_LSR_TEMT_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_UART_LSR_TEMT register field. */
#define ALT_UART_LSR_TEMT_MSB        6
/* The width in bits of the ALT_UART_LSR_TEMT register field. */
#define ALT_UART_LSR_TEMT_WIDTH      1
/* The mask used to set the ALT_UART_LSR_TEMT register field value. */
#define ALT_UART_LSR_TEMT_SET_MSK    0x00000040
/* The mask used to clear the ALT_UART_LSR_TEMT register field value. */
#define ALT_UART_LSR_TEMT_CLR_MSK    0xffffffbf
/* The reset value of the ALT_UART_LSR_TEMT register field. */
#define ALT_UART_LSR_TEMT_RESET      0x1
/* Extracts the ALT_UART_LSR_TEMT field value from a register. */
#define ALT_UART_LSR_TEMT_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_UART_LSR_TEMT register field value suitable for setting the register. */
#define ALT_UART_LSR_TEMT_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Receiver FIFO Error bit - rfe
 * 
 * This bit is only relevant when FIFO's are enabled (FCR[0] set to one). This is
 * used to indicate if there is at least one parity error, framing error, or break
 * indication in the FIFO. This bit is cleared when the LSR is read and the
 * character with the error is at the top of the receiver FIFO and there are no
 * subsequent errors in the FIFO.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                     | Value | Description        
 * :-------------------------|:------|:--------------------
 *  ALT_UART_LSR_RFE_E_NOERR | 0x0   | no error in Rx FIFO
 *  ALT_UART_LSR_RFE_E_ERR   | 0x1   | error in Rx FIFO   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_LSR_RFE
 * 
 * no error in Rx FIFO
 */
#define ALT_UART_LSR_RFE_E_NOERR    0x0
/*
 * Enumerated value for register field ALT_UART_LSR_RFE
 * 
 * error in Rx FIFO
 */
#define ALT_UART_LSR_RFE_E_ERR      0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_LSR_RFE register field. */
#define ALT_UART_LSR_RFE_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_UART_LSR_RFE register field. */
#define ALT_UART_LSR_RFE_MSB        7
/* The width in bits of the ALT_UART_LSR_RFE register field. */
#define ALT_UART_LSR_RFE_WIDTH      1
/* The mask used to set the ALT_UART_LSR_RFE register field value. */
#define ALT_UART_LSR_RFE_SET_MSK    0x00000080
/* The mask used to clear the ALT_UART_LSR_RFE register field value. */
#define ALT_UART_LSR_RFE_CLR_MSK    0xffffff7f
/* The reset value of the ALT_UART_LSR_RFE register field. */
#define ALT_UART_LSR_RFE_RESET      0x0
/* Extracts the ALT_UART_LSR_RFE field value from a register. */
#define ALT_UART_LSR_RFE_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_UART_LSR_RFE register field value suitable for setting the register. */
#define ALT_UART_LSR_RFE_SET(value) (((value) << 7) & 0x00000080)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_LSR.
 */
struct ALT_UART_LSR_s
{
    const uint32_t  dr   :  1;  /* Data Ready bit */
    const uint32_t  oe   :  1;  /* Overrun error */
    const uint32_t  pe   :  1;  /* Parity Error */
    const uint32_t  fe   :  1;  /* Framing Error */
    const uint32_t  bi   :  1;  /* Break Interrupt */
    const uint32_t  thre :  1;  /* Transmit Holding Register Empty bit */
    const uint32_t  temt :  1;  /* Transmitter Empty bit */
    const uint32_t  rfe  :  1;  /* Receiver FIFO Error bit */
    uint32_t             : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_LSR. */
typedef volatile struct ALT_UART_LSR_s  ALT_UART_LSR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_LSR register from the beginning of the component. */
#define ALT_UART_LSR_OFST        0x14
/* The address of the ALT_UART_LSR register. */
#define ALT_UART_LSR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_LSR_OFST))

/*
 * Register : Modem Status Register - msr
 * 
 * It should be noted that whenever bits 0, 1, 2 or 3 are set to logic one, to
 * indicate a change on the modem control inputs, a modem status interrupt will be
 * generated if enabled via the IER regardless of when the change occurred. Since
 * the delta bits (bits 0, 1, 3) can get set after a reset if their respective
 * modem signals are active (see individual bits for details), a read of the MSR
 * after reset can be performed to prevent unwanted interrupts.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                    
 * :-------|:-------|:------|:--------------------------------
 *  [0]    | R      | 0x0   | Delta Clear to Send            
 *  [1]    | R      | 0x0   | Delta Data Set Ready           
 *  [2]    | R      | 0x0   | Trailing Edge of Ring Indicator
 *  [3]    | R      | 0x0   | Delta Data Carrier Detect      
 *  [4]    | R      | 0x0   | Clear to Send                  
 *  [5]    | R      | 0x0   | Data Set Ready                 
 *  [6]    | R      | 0x0   | Ring Indicator                 
 *  [7]    | R      | 0x0   | Data Carrier Detect            
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                    
 * 
 */
/*
 * Field : Delta Clear to Send - dcts
 * 
 * This is used to indicate that the modem control line uart_cts_n has changed
 * since the last time the MSR was read. That is: Reading the MSR clears the DCTS
 * bit. In Loopback Mode bit [4] of MCR set to one, DCTS reflects changes on bit
 * [1] RTS of register MCR.
 * 
 * Note: If the DCTS bit is not set and the uart_cts_n signal is asserted (low) and
 * a reset occurs (software or otherwise), then the DCTS bit will get set when the
 * reset is removed if the uart_cts_n signal remains asserted.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description                                   
 * :--------------------------|:------|:-----------------------------------------------
 *  ALT_UART_MSR_DCTS_E_NOCHG | 0x0   | no change on uart_cts_n since last read of MSR
 *  ALT_UART_MSR_DCTS_E_CHG   | 0x1   | change on uart_cts_n since last read of MSR   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_MSR_DCTS
 * 
 * no change on uart_cts_n since last read of MSR
 */
#define ALT_UART_MSR_DCTS_E_NOCHG   0x0
/*
 * Enumerated value for register field ALT_UART_MSR_DCTS
 * 
 * change on uart_cts_n since last read of MSR
 */
#define ALT_UART_MSR_DCTS_E_CHG     0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_MSR_DCTS register field. */
#define ALT_UART_MSR_DCTS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_MSR_DCTS register field. */
#define ALT_UART_MSR_DCTS_MSB        0
/* The width in bits of the ALT_UART_MSR_DCTS register field. */
#define ALT_UART_MSR_DCTS_WIDTH      1
/* The mask used to set the ALT_UART_MSR_DCTS register field value. */
#define ALT_UART_MSR_DCTS_SET_MSK    0x00000001
/* The mask used to clear the ALT_UART_MSR_DCTS register field value. */
#define ALT_UART_MSR_DCTS_CLR_MSK    0xfffffffe
/* The reset value of the ALT_UART_MSR_DCTS register field. */
#define ALT_UART_MSR_DCTS_RESET      0x0
/* Extracts the ALT_UART_MSR_DCTS field value from a register. */
#define ALT_UART_MSR_DCTS_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_UART_MSR_DCTS register field value suitable for setting the register. */
#define ALT_UART_MSR_DCTS_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Delta Data Set Ready - ddsr
 * 
 * This is used to indicate that the modem control line uart_dsr_n has changed
 * since the last time the MSR was read. Reading the MSR clears the DDSR bit.In
 * Loopback Mode (MCR[4] set to one), DDSR reflects changes on bit [0] DTR of
 * register MCR .
 * 
 * Note, if the DDSR bit is not set and the uart_dsr_n signal is asserted (low) and
 * a reset occurs (software or otherwise), then the DDSR bit will get set when the
 * reset is removed if the uart_dsr_n signal remains asserted.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description                                   
 * :--------------------------|:------|:-----------------------------------------------
 *  ALT_UART_MSR_DDSR_E_NOCHG | 0x0   | no change on uart_dsr_n since last read of MSR
 *  ALT_UART_MSR_DDSR_E_CHG   | 0x1   | change on uart_dsr_n since last read of MSR   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_MSR_DDSR
 * 
 * no change on uart_dsr_n since last read of MSR
 */
#define ALT_UART_MSR_DDSR_E_NOCHG   0x0
/*
 * Enumerated value for register field ALT_UART_MSR_DDSR
 * 
 * change on uart_dsr_n since last read of MSR
 */
#define ALT_UART_MSR_DDSR_E_CHG     0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_MSR_DDSR register field. */
#define ALT_UART_MSR_DDSR_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_UART_MSR_DDSR register field. */
#define ALT_UART_MSR_DDSR_MSB        1
/* The width in bits of the ALT_UART_MSR_DDSR register field. */
#define ALT_UART_MSR_DDSR_WIDTH      1
/* The mask used to set the ALT_UART_MSR_DDSR register field value. */
#define ALT_UART_MSR_DDSR_SET_MSK    0x00000002
/* The mask used to clear the ALT_UART_MSR_DDSR register field value. */
#define ALT_UART_MSR_DDSR_CLR_MSK    0xfffffffd
/* The reset value of the ALT_UART_MSR_DDSR register field. */
#define ALT_UART_MSR_DDSR_RESET      0x0
/* Extracts the ALT_UART_MSR_DDSR field value from a register. */
#define ALT_UART_MSR_DDSR_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_UART_MSR_DDSR register field value suitable for setting the register. */
#define ALT_UART_MSR_DDSR_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Trailing Edge of Ring Indicator - teri
 * 
 * This is used to indicate that a change on the input uart_ri_n (from an active
 * low, to an inactive high state) has occurred since the last time the MSR was
 * read. Reading the MSR clears the TERI bit. In Loopback Mode bit [4] of register
 * MCR is set to one, TERI reflects when bit [2] of register MCR has changed state
 * from a high to a low.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description                                  
 * :--------------------------|:------|:----------------------------------------------
 *  ALT_UART_MSR_TERI_E_NOCHG | 0x0   | no change on uart_ri_n since last read of MSR
 *  ALT_UART_MSR_TERI_E_CHG   | 0x1   | change on uart_ri_n since last read of MSR   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_MSR_TERI
 * 
 * no change on uart_ri_n since last read of MSR
 */
#define ALT_UART_MSR_TERI_E_NOCHG   0x0
/*
 * Enumerated value for register field ALT_UART_MSR_TERI
 * 
 * change on uart_ri_n since last read of MSR
 */
#define ALT_UART_MSR_TERI_E_CHG     0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_MSR_TERI register field. */
#define ALT_UART_MSR_TERI_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_UART_MSR_TERI register field. */
#define ALT_UART_MSR_TERI_MSB        2
/* The width in bits of the ALT_UART_MSR_TERI register field. */
#define ALT_UART_MSR_TERI_WIDTH      1
/* The mask used to set the ALT_UART_MSR_TERI register field value. */
#define ALT_UART_MSR_TERI_SET_MSK    0x00000004
/* The mask used to clear the ALT_UART_MSR_TERI register field value. */
#define ALT_UART_MSR_TERI_CLR_MSK    0xfffffffb
/* The reset value of the ALT_UART_MSR_TERI register field. */
#define ALT_UART_MSR_TERI_RESET      0x0
/* Extracts the ALT_UART_MSR_TERI field value from a register. */
#define ALT_UART_MSR_TERI_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_UART_MSR_TERI register field value suitable for setting the register. */
#define ALT_UART_MSR_TERI_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Delta Data Carrier Detect - ddcd
 * 
 * This is used to indicate that the modem control line dcd_n has changed since the
 * last time the MSR was read. Reading the MSR clears the DDCD bit. In Loopback
 * Mode bit [4] of register MCR is set to one, DDCD reflects changes bit [3]
 * uart_out2 of register MCR.
 * 
 * Note: If the DDCD bit is not set and the uart_dcd_n signal is asserted (low) and
 * a reset occurs (software or otherwise), then the DDCD bit will get set when the
 * reset is removed if the uart_dcd_n signal remains asserted.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description                                   
 * :--------------------------|:------|:-----------------------------------------------
 *  ALT_UART_MSR_DDCD_E_NOCHG | 0x0   | no change on uart_dcd_n since last read of MSR
 *  ALT_UART_MSR_DDCD_E_CHG   | 0x1   | change on uart_dcd_n since last read of MSR   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_MSR_DDCD
 * 
 * no change on uart_dcd_n since last read of MSR
 */
#define ALT_UART_MSR_DDCD_E_NOCHG   0x0
/*
 * Enumerated value for register field ALT_UART_MSR_DDCD
 * 
 * change on uart_dcd_n since last read of MSR
 */
#define ALT_UART_MSR_DDCD_E_CHG     0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_MSR_DDCD register field. */
#define ALT_UART_MSR_DDCD_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_UART_MSR_DDCD register field. */
#define ALT_UART_MSR_DDCD_MSB        3
/* The width in bits of the ALT_UART_MSR_DDCD register field. */
#define ALT_UART_MSR_DDCD_WIDTH      1
/* The mask used to set the ALT_UART_MSR_DDCD register field value. */
#define ALT_UART_MSR_DDCD_SET_MSK    0x00000008
/* The mask used to clear the ALT_UART_MSR_DDCD register field value. */
#define ALT_UART_MSR_DDCD_CLR_MSK    0xfffffff7
/* The reset value of the ALT_UART_MSR_DDCD register field. */
#define ALT_UART_MSR_DDCD_RESET      0x0
/* Extracts the ALT_UART_MSR_DDCD field value from a register. */
#define ALT_UART_MSR_DDCD_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_UART_MSR_DDCD register field value suitable for setting the register. */
#define ALT_UART_MSR_DDCD_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Clear to Send - cts
 * 
 * This is used to indicate the current state of the modem control line uart_cts_n.
 * That is, this bit is the complement uart_cts_n. When the Clear to Send input
 * (uart_cts_n) is asserted it is an indication that the modem or data set is ready
 * to exchange data with the uart. In Loopback Mode bit [4] of register MCR is set
 * to one, CTS is the same as bit [1] RTS of register MCR.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description                              
 * :--------------------------|:------|:------------------------------------------
 *  ALT_UART_MSR_CTS_E_LOGIC1 | 0x0   | uart_cts_n input is de-asserted (logic 1)
 *  ALT_UART_MSR_CTS_E_LOGIC0 | 0x1   | uart_cts_n input is asserted (logic 0)   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_MSR_CTS
 * 
 * uart_cts_n input is de-asserted (logic 1)
 */
#define ALT_UART_MSR_CTS_E_LOGIC1   0x0
/*
 * Enumerated value for register field ALT_UART_MSR_CTS
 * 
 * uart_cts_n input is asserted (logic 0)
 */
#define ALT_UART_MSR_CTS_E_LOGIC0   0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_MSR_CTS register field. */
#define ALT_UART_MSR_CTS_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_UART_MSR_CTS register field. */
#define ALT_UART_MSR_CTS_MSB        4
/* The width in bits of the ALT_UART_MSR_CTS register field. */
#define ALT_UART_MSR_CTS_WIDTH      1
/* The mask used to set the ALT_UART_MSR_CTS register field value. */
#define ALT_UART_MSR_CTS_SET_MSK    0x00000010
/* The mask used to clear the ALT_UART_MSR_CTS register field value. */
#define ALT_UART_MSR_CTS_CLR_MSK    0xffffffef
/* The reset value of the ALT_UART_MSR_CTS register field. */
#define ALT_UART_MSR_CTS_RESET      0x0
/* Extracts the ALT_UART_MSR_CTS field value from a register. */
#define ALT_UART_MSR_CTS_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_UART_MSR_CTS register field value suitable for setting the register. */
#define ALT_UART_MSR_CTS_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Data Set Ready - dsr
 * 
 * This is used to indicate the current state of the modem control line uart_dsr_n.
 * That is this bit is the complement f uart_dsr_n. When the Data Set Ready input
 * (uart_dsr_n) is asserted it is an indication that the modem or data set is ready
 * to establish communications with the uart. In Loopback Mode bit [4] of register
 * MCR is set to one, DSR is the same as bit [0] (DTR) of register MCR.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description                              
 * :--------------------------|:------|:------------------------------------------
 *  ALT_UART_MSR_DSR_E_LOGIC1 | 0x0   | uart_dsr_n input is de-asserted (logic 1)
 *  ALT_UART_MSR_DSR_E_LOGIC0 | 0x1   | uart_dsr_n input is asserted (logic 0)   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_MSR_DSR
 * 
 * uart_dsr_n input is de-asserted (logic 1)
 */
#define ALT_UART_MSR_DSR_E_LOGIC1   0x0
/*
 * Enumerated value for register field ALT_UART_MSR_DSR
 * 
 * uart_dsr_n input is asserted (logic 0)
 */
#define ALT_UART_MSR_DSR_E_LOGIC0   0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_MSR_DSR register field. */
#define ALT_UART_MSR_DSR_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_UART_MSR_DSR register field. */
#define ALT_UART_MSR_DSR_MSB        5
/* The width in bits of the ALT_UART_MSR_DSR register field. */
#define ALT_UART_MSR_DSR_WIDTH      1
/* The mask used to set the ALT_UART_MSR_DSR register field value. */
#define ALT_UART_MSR_DSR_SET_MSK    0x00000020
/* The mask used to clear the ALT_UART_MSR_DSR register field value. */
#define ALT_UART_MSR_DSR_CLR_MSK    0xffffffdf
/* The reset value of the ALT_UART_MSR_DSR register field. */
#define ALT_UART_MSR_DSR_RESET      0x0
/* Extracts the ALT_UART_MSR_DSR field value from a register. */
#define ALT_UART_MSR_DSR_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_UART_MSR_DSR register field value suitable for setting the register. */
#define ALT_UART_MSR_DSR_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Ring Indicator - ri
 * 
 * This bit is used to indicate the current state of the modem control line
 * uart_ri_n. That is this bit is the complement uart_ri_n. When the Ring Indicator
 * input (uart_ri_n) is asserted it is an indication that a telephone ringing
 * signal has been received by the modem or data set. In Loopback Mode bit [4] of
 * register MCR set to one, RI is the same as bit [2] uart_out1_n of register MCR.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                     | Value | Description                             
 * :-------------------------|:------|:-----------------------------------------
 *  ALT_UART_MSR_RI_E_LOGIC1 | 0x0   | uart_ri_n input is de-asserted (logic 1)
 *  ALT_UART_MSR_RI_E_LOGIC0 | 0x1   | uart_ri_n input is asserted (logic 0)   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_MSR_RI
 * 
 * uart_ri_n input is de-asserted (logic 1)
 */
#define ALT_UART_MSR_RI_E_LOGIC1    0x0
/*
 * Enumerated value for register field ALT_UART_MSR_RI
 * 
 * uart_ri_n input is asserted (logic 0)
 */
#define ALT_UART_MSR_RI_E_LOGIC0    0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_MSR_RI register field. */
#define ALT_UART_MSR_RI_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_UART_MSR_RI register field. */
#define ALT_UART_MSR_RI_MSB        6
/* The width in bits of the ALT_UART_MSR_RI register field. */
#define ALT_UART_MSR_RI_WIDTH      1
/* The mask used to set the ALT_UART_MSR_RI register field value. */
#define ALT_UART_MSR_RI_SET_MSK    0x00000040
/* The mask used to clear the ALT_UART_MSR_RI register field value. */
#define ALT_UART_MSR_RI_CLR_MSK    0xffffffbf
/* The reset value of the ALT_UART_MSR_RI register field. */
#define ALT_UART_MSR_RI_RESET      0x0
/* Extracts the ALT_UART_MSR_RI field value from a register. */
#define ALT_UART_MSR_RI_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_UART_MSR_RI register field value suitable for setting the register. */
#define ALT_UART_MSR_RI_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Data Carrier Detect - dcd
 * 
 * This is used to indicate the current state of the modem control line uart_dcd_n.
 * That is this bit is the complement uart_dcd_n. When the Data Carrier Detect
 * input (uart_dcd_n) is asserted it is an indication that the carrier has been
 * detected by the modem or data set. In Loopback Mode (MCR[4] set to one), DCD is
 * the same as MCR[3] (uart_out2).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description                              
 * :--------------------------|:------|:------------------------------------------
 *  ALT_UART_MSR_DCD_E_LOGIC1 | 0x0   | uart_dcd_n input is de-asserted (logic 1)
 *  ALT_UART_MSR_DCD_E_LOGIC0 | 0x1   | uart_dcd_n input is asserted (logic 0)   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_MSR_DCD
 * 
 * uart_dcd_n input is de-asserted (logic 1)
 */
#define ALT_UART_MSR_DCD_E_LOGIC1   0x0
/*
 * Enumerated value for register field ALT_UART_MSR_DCD
 * 
 * uart_dcd_n input is asserted (logic 0)
 */
#define ALT_UART_MSR_DCD_E_LOGIC0   0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_MSR_DCD register field. */
#define ALT_UART_MSR_DCD_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_UART_MSR_DCD register field. */
#define ALT_UART_MSR_DCD_MSB        7
/* The width in bits of the ALT_UART_MSR_DCD register field. */
#define ALT_UART_MSR_DCD_WIDTH      1
/* The mask used to set the ALT_UART_MSR_DCD register field value. */
#define ALT_UART_MSR_DCD_SET_MSK    0x00000080
/* The mask used to clear the ALT_UART_MSR_DCD register field value. */
#define ALT_UART_MSR_DCD_CLR_MSK    0xffffff7f
/* The reset value of the ALT_UART_MSR_DCD register field. */
#define ALT_UART_MSR_DCD_RESET      0x0
/* Extracts the ALT_UART_MSR_DCD field value from a register. */
#define ALT_UART_MSR_DCD_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_UART_MSR_DCD register field value suitable for setting the register. */
#define ALT_UART_MSR_DCD_SET(value) (((value) << 7) & 0x00000080)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_MSR.
 */
struct ALT_UART_MSR_s
{
    const uint32_t  dcts :  1;  /* Delta Clear to Send */
    const uint32_t  ddsr :  1;  /* Delta Data Set Ready */
    const uint32_t  teri :  1;  /* Trailing Edge of Ring Indicator */
    const uint32_t  ddcd :  1;  /* Delta Data Carrier Detect */
    const uint32_t  cts  :  1;  /* Clear to Send */
    const uint32_t  dsr  :  1;  /* Data Set Ready */
    const uint32_t  ri   :  1;  /* Ring Indicator */
    const uint32_t  dcd  :  1;  /* Data Carrier Detect */
    uint32_t             : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_MSR. */
typedef volatile struct ALT_UART_MSR_s  ALT_UART_MSR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_MSR register from the beginning of the component. */
#define ALT_UART_MSR_OFST        0x18
/* The address of the ALT_UART_MSR register. */
#define ALT_UART_MSR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_MSR_OFST))

/*
 * Register : Scratchpad Register - scr
 * 
 * Scratchpad Register
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description        
 * :-------|:-------|:------|:--------------------
 *  [7:0]  | RW     | 0x0   | Scratchpad Register
 *  [31:8] | ???    | 0x0   | *UNDEFINED*        
 * 
 */
/*
 * Field : Scratchpad Register - scr
 * 
 * This register is for programmers to use as a temporary storage space.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_SCR_SCR register field. */
#define ALT_UART_SCR_SCR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_SCR_SCR register field. */
#define ALT_UART_SCR_SCR_MSB        7
/* The width in bits of the ALT_UART_SCR_SCR register field. */
#define ALT_UART_SCR_SCR_WIDTH      8
/* The mask used to set the ALT_UART_SCR_SCR register field value. */
#define ALT_UART_SCR_SCR_SET_MSK    0x000000ff
/* The mask used to clear the ALT_UART_SCR_SCR register field value. */
#define ALT_UART_SCR_SCR_CLR_MSK    0xffffff00
/* The reset value of the ALT_UART_SCR_SCR register field. */
#define ALT_UART_SCR_SCR_RESET      0x0
/* Extracts the ALT_UART_SCR_SCR field value from a register. */
#define ALT_UART_SCR_SCR_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_UART_SCR_SCR register field value suitable for setting the register. */
#define ALT_UART_SCR_SCR_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_SCR.
 */
struct ALT_UART_SCR_s
{
    uint32_t  scr :  8;  /* Scratchpad Register */
    uint32_t      : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_SCR. */
typedef volatile struct ALT_UART_SCR_s  ALT_UART_SCR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_SCR register from the beginning of the component. */
#define ALT_UART_SCR_OFST        0x1c
/* The address of the ALT_UART_SCR register. */
#define ALT_UART_SCR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_SCR_OFST))

/*
 * Register : Shadow Receive Buffer Register - srbr
 * 
 * Used to accomadate burst accesses from the master.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description          
 * :-------|:-------|:------|:----------------------
 *  [7:0]  | RW     | 0x0   | Shadow Receive Buffer
 *  [31:8] | ???    | 0x0   | *UNDEFINED*          
 * 
 */
/*
 * Field : Shadow Receive Buffer - srbr
 * 
 * This is a shadow register for the RBR and has been allocated one 32-bit location
 * so as to accommodate burst accesses from the master.This register contains the
 * data byte received on the serial input port (sin). The data in this register is
 * valid only if the Data Ready (DR) bit in the Line status Register (LSR) is set.
 * If FIFOs are disabled, bit [0] of register FCR set to zero, the data in the RBR
 * must be read before the next data arrives, otherwise it will be overwritten,
 * resulting in an overrun error. If FIFOs are enabled (FCR[0] set to one), this
 * register accesses the head of the receive FIFO. If the receive FIFO is full and
 * this register is not read before the next data character arrives, then the data
 * already in the FIFO will be preserved but any incoming data will be lost. An
 * overrun error will also occur.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_SRBR_SRBR register field. */
#define ALT_UART_SRBR_SRBR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_SRBR_SRBR register field. */
#define ALT_UART_SRBR_SRBR_MSB        7
/* The width in bits of the ALT_UART_SRBR_SRBR register field. */
#define ALT_UART_SRBR_SRBR_WIDTH      8
/* The mask used to set the ALT_UART_SRBR_SRBR register field value. */
#define ALT_UART_SRBR_SRBR_SET_MSK    0x000000ff
/* The mask used to clear the ALT_UART_SRBR_SRBR register field value. */
#define ALT_UART_SRBR_SRBR_CLR_MSK    0xffffff00
/* The reset value of the ALT_UART_SRBR_SRBR register field. */
#define ALT_UART_SRBR_SRBR_RESET      0x0
/* Extracts the ALT_UART_SRBR_SRBR field value from a register. */
#define ALT_UART_SRBR_SRBR_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_UART_SRBR_SRBR register field value suitable for setting the register. */
#define ALT_UART_SRBR_SRBR_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_SRBR.
 */
struct ALT_UART_SRBR_s
{
    uint32_t  srbr :  8;  /* Shadow Receive Buffer */
    uint32_t       : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_SRBR. */
typedef volatile struct ALT_UART_SRBR_s  ALT_UART_SRBR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_SRBR register from the beginning of the component. */
#define ALT_UART_SRBR_OFST        0x30
/* The address of the ALT_UART_SRBR register. */
#define ALT_UART_SRBR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_SRBR_OFST))

/*
 * Register : Shadow Transmit Buffer Register - sthr
 * 
 * Used to accomadate burst accesses from the master.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description           
 * :-------|:-------|:------|:-----------------------
 *  [7:0]  | RW     | 0x0   | Shadow Transmit Buffer
 *  [31:8] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : Shadow Transmit Buffer - sthr
 * 
 * This is a shadow register for the THR and has been allocated sixteen 32-bit
 * locations so as to accommodate burst accesses from the master. This register
 * contains data to be transmitted on the serial output port (sout). Data should
 * only be written to the THR when the THR Empty (THRE) bit (LSR[5]) is set. If
 * FIFO's are disabled bit [0] of register FCR set to zero and THRE is set, writing
 * a single character to the THR clears the THRE. Any additional writes to the THR
 * before the THRE is set again causes the THR data to be overwritten. If FIFO's
 * are enabled bit [0] of register FCR set to one and THRE is set, 128 characters
 * of data may be written to the THR before the FIFO is full. The UART FIFO depth
 * is configured for 128 characters. Any attempt to write data when the FIFO is
 * full results in the write data being lost.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_STHR_STHR register field. */
#define ALT_UART_STHR_STHR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_STHR_STHR register field. */
#define ALT_UART_STHR_STHR_MSB        7
/* The width in bits of the ALT_UART_STHR_STHR register field. */
#define ALT_UART_STHR_STHR_WIDTH      8
/* The mask used to set the ALT_UART_STHR_STHR register field value. */
#define ALT_UART_STHR_STHR_SET_MSK    0x000000ff
/* The mask used to clear the ALT_UART_STHR_STHR register field value. */
#define ALT_UART_STHR_STHR_CLR_MSK    0xffffff00
/* The reset value of the ALT_UART_STHR_STHR register field. */
#define ALT_UART_STHR_STHR_RESET      0x0
/* Extracts the ALT_UART_STHR_STHR field value from a register. */
#define ALT_UART_STHR_STHR_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_UART_STHR_STHR register field value suitable for setting the register. */
#define ALT_UART_STHR_STHR_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_STHR.
 */
struct ALT_UART_STHR_s
{
    uint32_t  sthr :  8;  /* Shadow Transmit Buffer */
    uint32_t       : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_STHR. */
typedef volatile struct ALT_UART_STHR_s  ALT_UART_STHR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_STHR register from the beginning of the component. */
#define ALT_UART_STHR_OFST        0x34
/* The address of the ALT_UART_STHR register. */
#define ALT_UART_STHR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_STHR_OFST))

/*
 * Register : FIFO Access Register - far
 * 
 * This register is used in FIFO access testing.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description    
 * :-------|:-------|:------|:----------------
 *  [0]    | RW     | 0x0   | FIFO ACCESS Bit
 *  [31:1] | ???    | 0x0   | *UNDEFINED*    
 * 
 */
/*
 * Field : FIFO ACCESS Bit - srbr_sthr
 * 
 * This register is used to enable a FIFO access mode for testing, so that the
 * receive FIFO can be written by the master and the transmit FIFO can be read by
 * the master when FIFO's are enabled. When FIFO's are not enabled it allows the
 * RBR to be written by the master and the THR to be read by the master
 * 
 * Note: That when the FIFO access mode is enabled/disabled, the control portion of
 * the receive FIFO and transmit FIFO is reset and the FIFO's are treated as empty.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description              
 * :------------------------------|:------|:--------------------------
 *  ALT_UART_FAR_SRBR_STHR_E_DISD | 0x0   | FIFO access mode disabled
 *  ALT_UART_FAR_SRBR_STHR_E_END  | 0x1   | FIFO access mode enabled 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_FAR_SRBR_STHR
 * 
 * FIFO access mode disabled
 */
#define ALT_UART_FAR_SRBR_STHR_E_DISD   0x0
/*
 * Enumerated value for register field ALT_UART_FAR_SRBR_STHR
 * 
 * FIFO access mode enabled
 */
#define ALT_UART_FAR_SRBR_STHR_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_FAR_SRBR_STHR register field. */
#define ALT_UART_FAR_SRBR_STHR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_FAR_SRBR_STHR register field. */
#define ALT_UART_FAR_SRBR_STHR_MSB        0
/* The width in bits of the ALT_UART_FAR_SRBR_STHR register field. */
#define ALT_UART_FAR_SRBR_STHR_WIDTH      1
/* The mask used to set the ALT_UART_FAR_SRBR_STHR register field value. */
#define ALT_UART_FAR_SRBR_STHR_SET_MSK    0x00000001
/* The mask used to clear the ALT_UART_FAR_SRBR_STHR register field value. */
#define ALT_UART_FAR_SRBR_STHR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_UART_FAR_SRBR_STHR register field. */
#define ALT_UART_FAR_SRBR_STHR_RESET      0x0
/* Extracts the ALT_UART_FAR_SRBR_STHR field value from a register. */
#define ALT_UART_FAR_SRBR_STHR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_UART_FAR_SRBR_STHR register field value suitable for setting the register. */
#define ALT_UART_FAR_SRBR_STHR_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_FAR.
 */
struct ALT_UART_FAR_s
{
    uint32_t  srbr_sthr :  1;  /* FIFO ACCESS Bit */
    uint32_t            : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_FAR. */
typedef volatile struct ALT_UART_FAR_s  ALT_UART_FAR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_FAR register from the beginning of the component. */
#define ALT_UART_FAR_OFST        0x70
/* The address of the ALT_UART_FAR register. */
#define ALT_UART_FAR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_FAR_OFST))

/*
 * Register : Transmit FIFO Read Register - tfr
 * 
 * Used in FIFO Access test mode.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description       
 * :-------|:-------|:------|:-------------------
 *  [7:0]  | R      | 0x0   | Transmit FIFO Read
 *  [31:8] | ???    | 0x0   | *UNDEFINED*       
 * 
 */
/*
 * Field : Transmit FIFO Read - tfr
 * 
 * These bits are only valid when FIFO access mode is enabled (FAR[0] is set to
 * one). When FIFO's are enabled, reading this register gives the data at the top
 * of the transmit FIFO. Each consecutive read pops the transmit FIFO and gives the
 * next data value that is currently at the top of the FIFO. When FIFO's are not
 * enabled, reading this register gives the data in the THR.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_TFR_TFR register field. */
#define ALT_UART_TFR_TFR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_TFR_TFR register field. */
#define ALT_UART_TFR_TFR_MSB        7
/* The width in bits of the ALT_UART_TFR_TFR register field. */
#define ALT_UART_TFR_TFR_WIDTH      8
/* The mask used to set the ALT_UART_TFR_TFR register field value. */
#define ALT_UART_TFR_TFR_SET_MSK    0x000000ff
/* The mask used to clear the ALT_UART_TFR_TFR register field value. */
#define ALT_UART_TFR_TFR_CLR_MSK    0xffffff00
/* The reset value of the ALT_UART_TFR_TFR register field. */
#define ALT_UART_TFR_TFR_RESET      0x0
/* Extracts the ALT_UART_TFR_TFR field value from a register. */
#define ALT_UART_TFR_TFR_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_UART_TFR_TFR register field value suitable for setting the register. */
#define ALT_UART_TFR_TFR_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_TFR.
 */
struct ALT_UART_TFR_s
{
    const uint32_t  tfr :  8;  /* Transmit FIFO Read */
    uint32_t            : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_TFR. */
typedef volatile struct ALT_UART_TFR_s  ALT_UART_TFR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_TFR register from the beginning of the component. */
#define ALT_UART_TFR_OFST        0x74
/* The address of the ALT_UART_TFR register. */
#define ALT_UART_TFR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_TFR_OFST))

/*
 * Register : Receive FIFO Write - RFW
 * 
 * Used only with FIFO access test mode.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description               
 * :--------|:-------|:------|:---------------------------
 *  [7:0]   | W      | 0x0   | Receive FIFO Write Field  
 *  [8]     | W      | 0x0   | Receive FIFO Parity Error 
 *  [9]     | W      | 0x0   | Receive FIFO Framing Error
 *  [31:10] | ???    | 0x0   | *UNDEFINED*               
 * 
 */
/*
 * Field : Receive FIFO Write Field - rfwd
 * 
 * These bits are only valid when FIFO access mode is enabled (FAR[0] is set to
 * one). When FIFO's are enabled, the data that is written to the RFWD is pushed
 * into the receive FIFO. Each consecutive write pushes the new data to the next
 * write location in the receive FIFO. When FIFO's are not enabled, the data that
 * is written to the RFWD is pushed into the RBR.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_RFW_RFWD register field. */
#define ALT_UART_RFW_RFWD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_RFW_RFWD register field. */
#define ALT_UART_RFW_RFWD_MSB        7
/* The width in bits of the ALT_UART_RFW_RFWD register field. */
#define ALT_UART_RFW_RFWD_WIDTH      8
/* The mask used to set the ALT_UART_RFW_RFWD register field value. */
#define ALT_UART_RFW_RFWD_SET_MSK    0x000000ff
/* The mask used to clear the ALT_UART_RFW_RFWD register field value. */
#define ALT_UART_RFW_RFWD_CLR_MSK    0xffffff00
/* The reset value of the ALT_UART_RFW_RFWD register field. */
#define ALT_UART_RFW_RFWD_RESET      0x0
/* Extracts the ALT_UART_RFW_RFWD field value from a register. */
#define ALT_UART_RFW_RFWD_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_UART_RFW_RFWD register field value suitable for setting the register. */
#define ALT_UART_RFW_RFWD_SET(value) (((value) << 0) & 0x000000ff)

/*
 * Field : Receive FIFO Parity Error - rfpe
 * 
 * These bits are only valid when FIFO access mode is enabled (FAR[0] is set to
 * one). When FIFO's are enabled, this bit is used to write parity error detection
 * information to the receive FIFO. When FIFO's are not enabled, this bit is used
 * to write parity error detection information to the RBR.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_RFW_RFPE register field. */
#define ALT_UART_RFW_RFPE_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_UART_RFW_RFPE register field. */
#define ALT_UART_RFW_RFPE_MSB        8
/* The width in bits of the ALT_UART_RFW_RFPE register field. */
#define ALT_UART_RFW_RFPE_WIDTH      1
/* The mask used to set the ALT_UART_RFW_RFPE register field value. */
#define ALT_UART_RFW_RFPE_SET_MSK    0x00000100
/* The mask used to clear the ALT_UART_RFW_RFPE register field value. */
#define ALT_UART_RFW_RFPE_CLR_MSK    0xfffffeff
/* The reset value of the ALT_UART_RFW_RFPE register field. */
#define ALT_UART_RFW_RFPE_RESET      0x0
/* Extracts the ALT_UART_RFW_RFPE field value from a register. */
#define ALT_UART_RFW_RFPE_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_UART_RFW_RFPE register field value suitable for setting the register. */
#define ALT_UART_RFW_RFPE_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Receive FIFO Framing Error - RFFE
 * 
 * These bits are only valid when FIFO access mode is enabled (FAR[0] is set to
 * one). When FIFO's are enabled, this bit is used to write framing error detection
 * information to the receive FIFO. When FIFO's are not enabled, this bit is used
 * to write framing error detection information to the RBR.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_RFW_RFFE register field. */
#define ALT_UART_RFW_RFFE_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_UART_RFW_RFFE register field. */
#define ALT_UART_RFW_RFFE_MSB        9
/* The width in bits of the ALT_UART_RFW_RFFE register field. */
#define ALT_UART_RFW_RFFE_WIDTH      1
/* The mask used to set the ALT_UART_RFW_RFFE register field value. */
#define ALT_UART_RFW_RFFE_SET_MSK    0x00000200
/* The mask used to clear the ALT_UART_RFW_RFFE register field value. */
#define ALT_UART_RFW_RFFE_CLR_MSK    0xfffffdff
/* The reset value of the ALT_UART_RFW_RFFE register field. */
#define ALT_UART_RFW_RFFE_RESET      0x0
/* Extracts the ALT_UART_RFW_RFFE field value from a register. */
#define ALT_UART_RFW_RFFE_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_UART_RFW_RFFE register field value suitable for setting the register. */
#define ALT_UART_RFW_RFFE_SET(value) (((value) << 9) & 0x00000200)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_RFW.
 */
struct ALT_UART_RFW_s
{
    uint32_t  rfwd :  8;  /* Receive FIFO Write Field */
    uint32_t  rfpe :  1;  /* Receive FIFO Parity Error */
    uint32_t  RFFE :  1;  /* Receive FIFO Framing Error */
    uint32_t       : 22;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_RFW. */
typedef volatile struct ALT_UART_RFW_s  ALT_UART_RFW_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_RFW register from the beginning of the component. */
#define ALT_UART_RFW_OFST        0x78
/* The address of the ALT_UART_RFW register. */
#define ALT_UART_RFW_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_RFW_OFST))

/*
 * Register : UART Status Register - usr
 * 
 * Status of FIFO Operations.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description           
 * :-------|:-------|:------|:-----------------------
 *  [0]    | ???    | 0x0   | *UNDEFINED*           
 *  [1]    | R      | 0x1   | Transmit FIFO Not Full
 *  [2]    | R      | 0x1   | Transmit FIFO Empty   
 *  [3]    | R      | 0x0   | Receive FIFO Not Empty
 *  [4]    | R      | 0x0   | Receive FIFO Full     
 *  [31:5] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : Transmit FIFO Not Full - tfnf
 * 
 * This Bit is used to indicate that the transmit FIFO in not full. This bit is
 * cleared when the Tx FIFO is full.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description              
 * :----------------------------|:------|:--------------------------
 *  ALT_UART_USR_TFNF_E_FULL    | 0x0   | Transmit FIFO is full    
 *  ALT_UART_USR_TFNF_E_NOTFULL | 0x1   | Transmit FIFO is not full
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_USR_TFNF
 * 
 * Transmit FIFO is full
 */
#define ALT_UART_USR_TFNF_E_FULL    0x0
/*
 * Enumerated value for register field ALT_UART_USR_TFNF
 * 
 * Transmit FIFO is not full
 */
#define ALT_UART_USR_TFNF_E_NOTFULL 0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_USR_TFNF register field. */
#define ALT_UART_USR_TFNF_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_UART_USR_TFNF register field. */
#define ALT_UART_USR_TFNF_MSB        1
/* The width in bits of the ALT_UART_USR_TFNF register field. */
#define ALT_UART_USR_TFNF_WIDTH      1
/* The mask used to set the ALT_UART_USR_TFNF register field value. */
#define ALT_UART_USR_TFNF_SET_MSK    0x00000002
/* The mask used to clear the ALT_UART_USR_TFNF register field value. */
#define ALT_UART_USR_TFNF_CLR_MSK    0xfffffffd
/* The reset value of the ALT_UART_USR_TFNF register field. */
#define ALT_UART_USR_TFNF_RESET      0x1
/* Extracts the ALT_UART_USR_TFNF field value from a register. */
#define ALT_UART_USR_TFNF_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_UART_USR_TFNF register field value suitable for setting the register. */
#define ALT_UART_USR_TFNF_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Transmit FIFO Empty - tfe
 * 
 * This is used to indicate that the transmit FIFO is completely empty. This bit is
 * cleared when the Tx FIFO is no longer empty.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description               
 * :----------------------------|:------|:---------------------------
 *  ALT_UART_USR_TFE_E_NOTEMPTY | 0x0   | Transmit FIFO is not empty
 *  ALT_UART_USR_TFE_E_EMPTY    | 0x1   | Transmit FIFO is empty    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_USR_TFE
 * 
 * Transmit FIFO is not empty
 */
#define ALT_UART_USR_TFE_E_NOTEMPTY 0x0
/*
 * Enumerated value for register field ALT_UART_USR_TFE
 * 
 * Transmit FIFO is empty
 */
#define ALT_UART_USR_TFE_E_EMPTY    0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_USR_TFE register field. */
#define ALT_UART_USR_TFE_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_UART_USR_TFE register field. */
#define ALT_UART_USR_TFE_MSB        2
/* The width in bits of the ALT_UART_USR_TFE register field. */
#define ALT_UART_USR_TFE_WIDTH      1
/* The mask used to set the ALT_UART_USR_TFE register field value. */
#define ALT_UART_USR_TFE_SET_MSK    0x00000004
/* The mask used to clear the ALT_UART_USR_TFE register field value. */
#define ALT_UART_USR_TFE_CLR_MSK    0xfffffffb
/* The reset value of the ALT_UART_USR_TFE register field. */
#define ALT_UART_USR_TFE_RESET      0x1
/* Extracts the ALT_UART_USR_TFE field value from a register. */
#define ALT_UART_USR_TFE_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_UART_USR_TFE register field value suitable for setting the register. */
#define ALT_UART_USR_TFE_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Receive FIFO Not Empty - rfne
 * 
 * This Bit is used to indicate that the receive FIFO contains one or more entries.
 * This bit is cleared when the Rx FIFO is empty.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description              
 * :-----------------------------|:------|:--------------------------
 *  ALT_UART_USR_RFNE_E_EMPTY    | 0x0   | Receiive FIFO is empty   
 *  ALT_UART_USR_RFNE_E_NOTEMPTY | 0x1   | Receive FIFO is not empty
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_USR_RFNE
 * 
 * Receiive FIFO is empty
 */
#define ALT_UART_USR_RFNE_E_EMPTY       0x0
/*
 * Enumerated value for register field ALT_UART_USR_RFNE
 * 
 * Receive FIFO is not empty
 */
#define ALT_UART_USR_RFNE_E_NOTEMPTY    0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_USR_RFNE register field. */
#define ALT_UART_USR_RFNE_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_UART_USR_RFNE register field. */
#define ALT_UART_USR_RFNE_MSB        3
/* The width in bits of the ALT_UART_USR_RFNE register field. */
#define ALT_UART_USR_RFNE_WIDTH      1
/* The mask used to set the ALT_UART_USR_RFNE register field value. */
#define ALT_UART_USR_RFNE_SET_MSK    0x00000008
/* The mask used to clear the ALT_UART_USR_RFNE register field value. */
#define ALT_UART_USR_RFNE_CLR_MSK    0xfffffff7
/* The reset value of the ALT_UART_USR_RFNE register field. */
#define ALT_UART_USR_RFNE_RESET      0x0
/* Extracts the ALT_UART_USR_RFNE field value from a register. */
#define ALT_UART_USR_RFNE_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_UART_USR_RFNE register field value suitable for setting the register. */
#define ALT_UART_USR_RFNE_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Receive FIFO Full - rff
 * 
 * This Bit is used to indicate that the receive FIFO is completely full. This bit
 * is cleared when the Rx FIFO is no longer full.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description           
 * :---------------------------|:------|:-----------------------
 *  ALT_UART_USR_RFF_E_NOTFULL | 0x0   | Receiive FIFO not full
 *  ALT_UART_USR_RFF_E_FULL    | 0x1   | Transmit FIFO is full 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_USR_RFF
 * 
 * Receiive FIFO not full
 */
#define ALT_UART_USR_RFF_E_NOTFULL  0x0
/*
 * Enumerated value for register field ALT_UART_USR_RFF
 * 
 * Transmit FIFO is full
 */
#define ALT_UART_USR_RFF_E_FULL     0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_USR_RFF register field. */
#define ALT_UART_USR_RFF_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_UART_USR_RFF register field. */
#define ALT_UART_USR_RFF_MSB        4
/* The width in bits of the ALT_UART_USR_RFF register field. */
#define ALT_UART_USR_RFF_WIDTH      1
/* The mask used to set the ALT_UART_USR_RFF register field value. */
#define ALT_UART_USR_RFF_SET_MSK    0x00000010
/* The mask used to clear the ALT_UART_USR_RFF register field value. */
#define ALT_UART_USR_RFF_CLR_MSK    0xffffffef
/* The reset value of the ALT_UART_USR_RFF register field. */
#define ALT_UART_USR_RFF_RESET      0x0
/* Extracts the ALT_UART_USR_RFF field value from a register. */
#define ALT_UART_USR_RFF_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_UART_USR_RFF register field value suitable for setting the register. */
#define ALT_UART_USR_RFF_SET(value) (((value) << 4) & 0x00000010)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_USR.
 */
struct ALT_UART_USR_s
{
    uint32_t             :  1;  /* *UNDEFINED* */
    const uint32_t  tfnf :  1;  /* Transmit FIFO Not Full */
    const uint32_t  tfe  :  1;  /* Transmit FIFO Empty */
    const uint32_t  rfne :  1;  /* Receive FIFO Not Empty */
    const uint32_t  rff  :  1;  /* Receive FIFO Full */
    uint32_t             : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_USR. */
typedef volatile struct ALT_UART_USR_s  ALT_UART_USR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_USR register from the beginning of the component. */
#define ALT_UART_USR_OFST        0x7c
/* The address of the ALT_UART_USR register. */
#define ALT_UART_USR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_USR_OFST))

/*
 * Register : Transmit FIFO Level - tfl
 * 
 * This register is used to specify the number of data entries in the Tx FIFO.
 * Status Bits in USR register monitor the FIFO state.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description        
 * :-------|:-------|:------|:--------------------
 *  [4:0]  | R      | 0x0   | Transmit FIFO Level
 *  [31:5] | ???    | 0x0   | *UNDEFINED*        
 * 
 */
/*
 * Field : Transmit FIFO Level - tfl
 * 
 * This indicates the number of data entries in the transmit FIFO.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_TFL_TFL register field. */
#define ALT_UART_TFL_TFL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_TFL_TFL register field. */
#define ALT_UART_TFL_TFL_MSB        4
/* The width in bits of the ALT_UART_TFL_TFL register field. */
#define ALT_UART_TFL_TFL_WIDTH      5
/* The mask used to set the ALT_UART_TFL_TFL register field value. */
#define ALT_UART_TFL_TFL_SET_MSK    0x0000001f
/* The mask used to clear the ALT_UART_TFL_TFL register field value. */
#define ALT_UART_TFL_TFL_CLR_MSK    0xffffffe0
/* The reset value of the ALT_UART_TFL_TFL register field. */
#define ALT_UART_TFL_TFL_RESET      0x0
/* Extracts the ALT_UART_TFL_TFL field value from a register. */
#define ALT_UART_TFL_TFL_GET(value) (((value) & 0x0000001f) >> 0)
/* Produces a ALT_UART_TFL_TFL register field value suitable for setting the register. */
#define ALT_UART_TFL_TFL_SET(value) (((value) << 0) & 0x0000001f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_TFL.
 */
struct ALT_UART_TFL_s
{
    const uint32_t  tfl :  5;  /* Transmit FIFO Level */
    uint32_t            : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_TFL. */
typedef volatile struct ALT_UART_TFL_s  ALT_UART_TFL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_TFL register from the beginning of the component. */
#define ALT_UART_TFL_OFST        0x80
/* The address of the ALT_UART_TFL register. */
#define ALT_UART_TFL_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_TFL_OFST))

/*
 * Register : Receive FIFO Level Write - rfl
 * 
 * This register is used to specify the number of data entries in the Tx FIFO.
 * Status Bits in USR register monitor the FIFO state.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description              
 * :-------|:-------|:------|:--------------------------
 *  [4:0]  | R      | 0x0   | Receive FIFO Level Status
 *  [31:5] | ???    | 0x0   | *UNDEFINED*              
 * 
 */
/*
 * Field : Receive FIFO Level Status - rfl
 * 
 * This indicates the number of data entries in the receive FIFO.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_RFL_RFL register field. */
#define ALT_UART_RFL_RFL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_RFL_RFL register field. */
#define ALT_UART_RFL_RFL_MSB        4
/* The width in bits of the ALT_UART_RFL_RFL register field. */
#define ALT_UART_RFL_RFL_WIDTH      5
/* The mask used to set the ALT_UART_RFL_RFL register field value. */
#define ALT_UART_RFL_RFL_SET_MSK    0x0000001f
/* The mask used to clear the ALT_UART_RFL_RFL register field value. */
#define ALT_UART_RFL_RFL_CLR_MSK    0xffffffe0
/* The reset value of the ALT_UART_RFL_RFL register field. */
#define ALT_UART_RFL_RFL_RESET      0x0
/* Extracts the ALT_UART_RFL_RFL field value from a register. */
#define ALT_UART_RFL_RFL_GET(value) (((value) & 0x0000001f) >> 0)
/* Produces a ALT_UART_RFL_RFL register field value suitable for setting the register. */
#define ALT_UART_RFL_RFL_SET(value) (((value) << 0) & 0x0000001f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_RFL.
 */
struct ALT_UART_RFL_s
{
    const uint32_t  rfl :  5;  /* Receive FIFO Level Status */
    uint32_t            : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_RFL. */
typedef volatile struct ALT_UART_RFL_s  ALT_UART_RFL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_RFL register from the beginning of the component. */
#define ALT_UART_RFL_OFST        0x84
/* The address of the ALT_UART_RFL register. */
#define ALT_UART_RFL_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_RFL_OFST))

/*
 * Register : Software Reset Register - srr
 * 
 * Provides Software Resets for Tx/Rx FIFO's and the uart.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description  
 * :-------|:-------|:------|:--------------
 *  [0]    | W      | 0x0   | UART Reset   
 *  [1]    | W      | 0x0   | Rx FIFO Reset
 *  [2]    | W      | 0x0   | Tx FIFO Reset
 *  [31:3] | ???    | 0x0   | *UNDEFINED*  
 * 
 */
/*
 * Field : UART Reset - ur
 * 
 * This asynchronously resets the UART and synchronously removes the reset
 * assertion.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                    | Value | Description  
 * :------------------------|:------|:--------------
 *  ALT_UART_SRR_UR_E_NORST | 0x0   | No reset Uart
 *  ALT_UART_SRR_UR_E_RST   | 0x1   | Reset Uart   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_SRR_UR
 * 
 * No reset Uart
 */
#define ALT_UART_SRR_UR_E_NORST 0x0
/*
 * Enumerated value for register field ALT_UART_SRR_UR
 * 
 * Reset Uart
 */
#define ALT_UART_SRR_UR_E_RST   0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_SRR_UR register field. */
#define ALT_UART_SRR_UR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_SRR_UR register field. */
#define ALT_UART_SRR_UR_MSB        0
/* The width in bits of the ALT_UART_SRR_UR register field. */
#define ALT_UART_SRR_UR_WIDTH      1
/* The mask used to set the ALT_UART_SRR_UR register field value. */
#define ALT_UART_SRR_UR_SET_MSK    0x00000001
/* The mask used to clear the ALT_UART_SRR_UR register field value. */
#define ALT_UART_SRR_UR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_UART_SRR_UR register field. */
#define ALT_UART_SRR_UR_RESET      0x0
/* Extracts the ALT_UART_SRR_UR field value from a register. */
#define ALT_UART_SRR_UR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_UART_SRR_UR register field value suitable for setting the register. */
#define ALT_UART_SRR_UR_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Rx FIFO Reset - rfr
 * 
 * This is a shadow register for the Rx  FIFO Reset bit (FCR[1]). This can be used
 * to remove the burden on software having to store previously written FCR values
 * (which are pretty static) just to reset the receive FIFO. This resets the
 * control portion of the receive FIFO and treats the FIFO as empty. This will also
 * de-assert the DMA Rx request and single signals. Note that this bit is 'self-
 * clearing' and it is not necessary to clear this bit.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                     | Value | Description     
 * :-------------------------|:------|:-----------------
 *  ALT_UART_SRR_RFR_E_NORST | 0x0   | No reset Rx FIFO
 *  ALT_UART_SRR_RFR_E_RST   | 0x1   | Reset Rx FIFO   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_SRR_RFR
 * 
 * No reset Rx FIFO
 */
#define ALT_UART_SRR_RFR_E_NORST    0x0
/*
 * Enumerated value for register field ALT_UART_SRR_RFR
 * 
 * Reset Rx FIFO
 */
#define ALT_UART_SRR_RFR_E_RST      0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_SRR_RFR register field. */
#define ALT_UART_SRR_RFR_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_UART_SRR_RFR register field. */
#define ALT_UART_SRR_RFR_MSB        1
/* The width in bits of the ALT_UART_SRR_RFR register field. */
#define ALT_UART_SRR_RFR_WIDTH      1
/* The mask used to set the ALT_UART_SRR_RFR register field value. */
#define ALT_UART_SRR_RFR_SET_MSK    0x00000002
/* The mask used to clear the ALT_UART_SRR_RFR register field value. */
#define ALT_UART_SRR_RFR_CLR_MSK    0xfffffffd
/* The reset value of the ALT_UART_SRR_RFR register field. */
#define ALT_UART_SRR_RFR_RESET      0x0
/* Extracts the ALT_UART_SRR_RFR field value from a register. */
#define ALT_UART_SRR_RFR_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_UART_SRR_RFR register field value suitable for setting the register. */
#define ALT_UART_SRR_RFR_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Tx FIFO Reset - xfr
 * 
 * This is a  shadow register forthe Tx FIFO Reset bit (FCR[2]). This can be used
 * to remove the burden on software having to store previously written FCR values
 * (which are pretty static) just to reset the transmit FIFO.This resets the
 * control portion of the transmit FIFO and treats the FIFO as empty. This will
 * also de-assert the DMA Tx request and single signals.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                     | Value | Description     
 * :-------------------------|:------|:-----------------
 *  ALT_UART_SRR_XFR_E_NORST | 0x0   | No reset Tx FIFO
 *  ALT_UART_SRR_XFR_E_RST   | 0x1   | Reset Tx FIFO   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_SRR_XFR
 * 
 * No reset Tx FIFO
 */
#define ALT_UART_SRR_XFR_E_NORST    0x0
/*
 * Enumerated value for register field ALT_UART_SRR_XFR
 * 
 * Reset Tx FIFO
 */
#define ALT_UART_SRR_XFR_E_RST      0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_SRR_XFR register field. */
#define ALT_UART_SRR_XFR_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_UART_SRR_XFR register field. */
#define ALT_UART_SRR_XFR_MSB        2
/* The width in bits of the ALT_UART_SRR_XFR register field. */
#define ALT_UART_SRR_XFR_WIDTH      1
/* The mask used to set the ALT_UART_SRR_XFR register field value. */
#define ALT_UART_SRR_XFR_SET_MSK    0x00000004
/* The mask used to clear the ALT_UART_SRR_XFR register field value. */
#define ALT_UART_SRR_XFR_CLR_MSK    0xfffffffb
/* The reset value of the ALT_UART_SRR_XFR register field. */
#define ALT_UART_SRR_XFR_RESET      0x0
/* Extracts the ALT_UART_SRR_XFR field value from a register. */
#define ALT_UART_SRR_XFR_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_UART_SRR_XFR register field value suitable for setting the register. */
#define ALT_UART_SRR_XFR_SET(value) (((value) << 2) & 0x00000004)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_SRR.
 */
struct ALT_UART_SRR_s
{
    uint32_t  ur  :  1;  /* UART Reset */
    uint32_t  rfr :  1;  /* Rx FIFO Reset */
    uint32_t  xfr :  1;  /* Tx FIFO Reset */
    uint32_t      : 29;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_SRR. */
typedef volatile struct ALT_UART_SRR_s  ALT_UART_SRR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_SRR register from the beginning of the component. */
#define ALT_UART_SRR_OFST        0x88
/* The address of the ALT_UART_SRR register. */
#define ALT_UART_SRR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_SRR_OFST))

/*
 * Register : Shadow Request to Send - srts
 * 
 * This is a shadow register for the RTS status (MCR[1]), this can be used to
 * remove the burden of having to performing a read modify write on the MCR.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description           
 * :-------|:-------|:------|:-----------------------
 *  [0]    | RW     | 0x0   | Shadow Request to Send
 *  [31:1] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : Shadow Request to Send - srts
 * 
 * This is used to directly control the Request to Send (uart_rts_n) output. The
 * Request to Send (uart_rts_n) output is used to inform the modem or data set that
 * the UART is read to exchange data. The uart_rts_n signal is set low by
 * programming MCR[1] (RTS) to a high. In Auto Flow Control, (MCR[5] set to one)
 * and FIFO's are enabled (FCR[0] set to one), the uart_rts_n output is controlled
 * in the same way, but is also gated with the receiver FIFO threshold trigger
 * (uart_rts_n is inactive high when above the threshold).
 * 
 * Note that in Loopback mode (MCR[4] set to one), the uart_rts_n output is held
 * inactive high while the value of this location is internally looped back to an
 * input.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description      
 * :----------------------------|:------|:------------------
 *  ALT_UART_SRTS_SRTS_E_LOGIC0 | 0x1   | uart_rts_n logic0
 *  ALT_UART_SRTS_SRTS_E_LOGIC1 | 0x0   | uart_rts_n logic1
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_SRTS_SRTS
 * 
 * uart_rts_n logic0
 */
#define ALT_UART_SRTS_SRTS_E_LOGIC0 0x1
/*
 * Enumerated value for register field ALT_UART_SRTS_SRTS
 * 
 * uart_rts_n logic1
 */
#define ALT_UART_SRTS_SRTS_E_LOGIC1 0x0

/* The Least Significant Bit (LSB) position of the ALT_UART_SRTS_SRTS register field. */
#define ALT_UART_SRTS_SRTS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_SRTS_SRTS register field. */
#define ALT_UART_SRTS_SRTS_MSB        0
/* The width in bits of the ALT_UART_SRTS_SRTS register field. */
#define ALT_UART_SRTS_SRTS_WIDTH      1
/* The mask used to set the ALT_UART_SRTS_SRTS register field value. */
#define ALT_UART_SRTS_SRTS_SET_MSK    0x00000001
/* The mask used to clear the ALT_UART_SRTS_SRTS register field value. */
#define ALT_UART_SRTS_SRTS_CLR_MSK    0xfffffffe
/* The reset value of the ALT_UART_SRTS_SRTS register field. */
#define ALT_UART_SRTS_SRTS_RESET      0x0
/* Extracts the ALT_UART_SRTS_SRTS field value from a register. */
#define ALT_UART_SRTS_SRTS_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_UART_SRTS_SRTS register field value suitable for setting the register. */
#define ALT_UART_SRTS_SRTS_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_SRTS.
 */
struct ALT_UART_SRTS_s
{
    uint32_t  srts :  1;  /* Shadow Request to Send */
    uint32_t       : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_SRTS. */
typedef volatile struct ALT_UART_SRTS_s  ALT_UART_SRTS_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_SRTS register from the beginning of the component. */
#define ALT_UART_SRTS_OFST        0x8c
/* The address of the ALT_UART_SRTS register. */
#define ALT_UART_SRTS_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_SRTS_OFST))

/*
 * Register : Shadow Break Control Register - sbcr
 * 
 * This is a shadow register for the Break bit [6] of the register LCR. This can be
 * used to remove the burden of having to performing a read modify write on the
 * LCR.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description         
 * :-------|:-------|:------|:---------------------
 *  [0]    | RW     | 0x0   | Shadow Break Control
 *  [31:1] | ???    | 0x0   | *UNDEFINED*         
 * 
 */
/*
 * Field : Shadow Break Control - sbcr
 * 
 * This is used to cause a break condition to be transmitted to the receiving
 * device. If set to one the serial output is forced to the spacing (logic 0)
 * state. When not in Loopback Mode, as determined by MCR[4], the uart_txd line is
 * forced low until the Break bit is cleared. When in Loopback Mode, the break
 * condition is internally looped back to the receiver.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description                
 * :--------------------------|:------|:----------------------------
 *  ALT_UART_SBCR_SBCR_E_DISD | 0x0   | no break                   
 *  ALT_UART_SBCR_SBCR_E_END  | 0x1   | break serial output spacing
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_SBCR_SBCR
 * 
 * no break
 */
#define ALT_UART_SBCR_SBCR_E_DISD   0x0
/*
 * Enumerated value for register field ALT_UART_SBCR_SBCR
 * 
 * break serial output spacing
 */
#define ALT_UART_SBCR_SBCR_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_SBCR_SBCR register field. */
#define ALT_UART_SBCR_SBCR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_SBCR_SBCR register field. */
#define ALT_UART_SBCR_SBCR_MSB        0
/* The width in bits of the ALT_UART_SBCR_SBCR register field. */
#define ALT_UART_SBCR_SBCR_WIDTH      1
/* The mask used to set the ALT_UART_SBCR_SBCR register field value. */
#define ALT_UART_SBCR_SBCR_SET_MSK    0x00000001
/* The mask used to clear the ALT_UART_SBCR_SBCR register field value. */
#define ALT_UART_SBCR_SBCR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_UART_SBCR_SBCR register field. */
#define ALT_UART_SBCR_SBCR_RESET      0x0
/* Extracts the ALT_UART_SBCR_SBCR field value from a register. */
#define ALT_UART_SBCR_SBCR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_UART_SBCR_SBCR register field value suitable for setting the register. */
#define ALT_UART_SBCR_SBCR_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_SBCR.
 */
struct ALT_UART_SBCR_s
{
    uint32_t  sbcr :  1;  /* Shadow Break Control */
    uint32_t       : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_SBCR. */
typedef volatile struct ALT_UART_SBCR_s  ALT_UART_SBCR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_SBCR register from the beginning of the component. */
#define ALT_UART_SBCR_OFST        0x90
/* The address of the ALT_UART_SBCR register. */
#define ALT_UART_SBCR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_SBCR_OFST))

/*
 * Register : Shadow DMA Mode - sdmam
 * 
 * This is a shadow register for the DMA mode bit (FCR[3]).
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description    
 * :-------|:-------|:------|:----------------
 *  [0]    | RW     | 0x0   | Shadow DMA Mode
 *  [31:1] | ???    | 0x0   | *UNDEFINED*    
 * 
 */
/*
 * Field : Shadow DMA Mode - sdmam
 * 
 * This can be used to remove the burden of having to store the previously written
 * value to the FCR in memory and having to mask this value so that only the DMA
 * Mode bit gets updated.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description               
 * :------------------------------|:------|:---------------------------
 *  ALT_UART_SDMAM_SDMAM_E_SINGLE | 0x0   | Single DMA Transfer Mode  
 *  ALT_UART_SDMAM_SDMAM_E_MULT   | 0x1   | Multiple DMA Transfer Mode
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_SDMAM_SDMAM
 * 
 * Single DMA Transfer Mode
 */
#define ALT_UART_SDMAM_SDMAM_E_SINGLE   0x0
/*
 * Enumerated value for register field ALT_UART_SDMAM_SDMAM
 * 
 * Multiple DMA Transfer Mode
 */
#define ALT_UART_SDMAM_SDMAM_E_MULT     0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_SDMAM_SDMAM register field. */
#define ALT_UART_SDMAM_SDMAM_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_SDMAM_SDMAM register field. */
#define ALT_UART_SDMAM_SDMAM_MSB        0
/* The width in bits of the ALT_UART_SDMAM_SDMAM register field. */
#define ALT_UART_SDMAM_SDMAM_WIDTH      1
/* The mask used to set the ALT_UART_SDMAM_SDMAM register field value. */
#define ALT_UART_SDMAM_SDMAM_SET_MSK    0x00000001
/* The mask used to clear the ALT_UART_SDMAM_SDMAM register field value. */
#define ALT_UART_SDMAM_SDMAM_CLR_MSK    0xfffffffe
/* The reset value of the ALT_UART_SDMAM_SDMAM register field. */
#define ALT_UART_SDMAM_SDMAM_RESET      0x0
/* Extracts the ALT_UART_SDMAM_SDMAM field value from a register. */
#define ALT_UART_SDMAM_SDMAM_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_UART_SDMAM_SDMAM register field value suitable for setting the register. */
#define ALT_UART_SDMAM_SDMAM_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_SDMAM.
 */
struct ALT_UART_SDMAM_s
{
    uint32_t  sdmam :  1;  /* Shadow DMA Mode */
    uint32_t        : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_SDMAM. */
typedef volatile struct ALT_UART_SDMAM_s  ALT_UART_SDMAM_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_SDMAM register from the beginning of the component. */
#define ALT_UART_SDMAM_OFST        0x94
/* The address of the ALT_UART_SDMAM register. */
#define ALT_UART_SDMAM_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_SDMAM_OFST))

/*
 * Register : Shadow FIFO Enable - sfe
 * 
 * This is a shadow register for the FIFO enable bit [0] of register FCR.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description       
 * :-------|:-------|:------|:-------------------
 *  [0]    | RW     | 0x0   | Shadow FIFO Enable
 *  [31:1] | ???    | 0x0   | *UNDEFINED*       
 * 
 */
/*
 * Field : Shadow FIFO Enable - sfe
 * 
 * This can be used to remove the burden of having to store the previously written
 * value to the FCR in memory and having to mask this value so that only the FIFO
 * enable bit gets updated. This enables/disables the transmit (Tx) and receive (Rx
 * ) FIFO's. If this bit is set to zero (disabled) after being enabled then both
 * the Tx and Rx  controller portion of FIFO's will be reset.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                    | Value | Description  
 * :------------------------|:------|:--------------
 *  ALT_UART_SFE_SFE_E_DISD | 0x0   | Disable Rx/Tx
 *  ALT_UART_SFE_SFE_E_END  | 0x1   | Enable Rx/Tx 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_SFE_SFE
 * 
 * Disable Rx/Tx
 */
#define ALT_UART_SFE_SFE_E_DISD 0x0
/*
 * Enumerated value for register field ALT_UART_SFE_SFE
 * 
 * Enable Rx/Tx
 */
#define ALT_UART_SFE_SFE_E_END  0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_SFE_SFE register field. */
#define ALT_UART_SFE_SFE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_SFE_SFE register field. */
#define ALT_UART_SFE_SFE_MSB        0
/* The width in bits of the ALT_UART_SFE_SFE register field. */
#define ALT_UART_SFE_SFE_WIDTH      1
/* The mask used to set the ALT_UART_SFE_SFE register field value. */
#define ALT_UART_SFE_SFE_SET_MSK    0x00000001
/* The mask used to clear the ALT_UART_SFE_SFE register field value. */
#define ALT_UART_SFE_SFE_CLR_MSK    0xfffffffe
/* The reset value of the ALT_UART_SFE_SFE register field. */
#define ALT_UART_SFE_SFE_RESET      0x0
/* Extracts the ALT_UART_SFE_SFE field value from a register. */
#define ALT_UART_SFE_SFE_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_UART_SFE_SFE register field value suitable for setting the register. */
#define ALT_UART_SFE_SFE_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_SFE.
 */
struct ALT_UART_SFE_s
{
    uint32_t  sfe :  1;  /* Shadow FIFO Enable */
    uint32_t      : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_SFE. */
typedef volatile struct ALT_UART_SFE_s  ALT_UART_SFE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_SFE register from the beginning of the component. */
#define ALT_UART_SFE_OFST        0x98
/* The address of the ALT_UART_SFE register. */
#define ALT_UART_SFE_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_SFE_OFST))

/*
 * Register : Shadow Rx Trigger - srt
 * 
 * This is a shadow register for the Rx trigger bits (FCR[7:6]).
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description            
 * :-------|:-------|:------|:------------------------
 *  [1:0]  | RW     | 0x0   | Shadow Rx  Trigger Bits
 *  [31:2] | ???    | 0x0   | *UNDEFINED*            
 * 
 */
/*
 * Field : Shadow Rx  Trigger Bits - srt
 * 
 * This can be used to remove the burden of having to store the previously written
 * value to the FCR in memory and having to mask this value so that only the Rx
 * trigger bit gets updated. This is used to select the trigger level in the
 * receiver FIFO at which the Received Data Available Interrupt will be generated.
 * It also determines when the uart_dma_rx_req_n signal will be asserted when DMA
 * Mode (FCR[3]) is set to one. The enum below shows trigger levels that are
 * supported.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description          
 * :-------------------------------|:------|:----------------------
 *  ALT_UART_SRT_SRT_E_ONECHAR     | 0x0   | one character in fifo
 *  ALT_UART_SRT_SRT_E_QUARTERFULL | 0x1   | FIFO 1/4 full        
 *  ALT_UART_SRT_SRT_E_HALFFULL    | 0x2   | FIFO 1/2 full        
 *  ALT_UART_SRT_SRT_E_FULLLESS2   | 0x3   | FIFO 2 less than full
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_SRT_SRT
 * 
 * one character in fifo
 */
#define ALT_UART_SRT_SRT_E_ONECHAR      0x0
/*
 * Enumerated value for register field ALT_UART_SRT_SRT
 * 
 * FIFO 1/4 full
 */
#define ALT_UART_SRT_SRT_E_QUARTERFULL  0x1
/*
 * Enumerated value for register field ALT_UART_SRT_SRT
 * 
 * FIFO 1/2 full
 */
#define ALT_UART_SRT_SRT_E_HALFFULL     0x2
/*
 * Enumerated value for register field ALT_UART_SRT_SRT
 * 
 * FIFO 2 less than full
 */
#define ALT_UART_SRT_SRT_E_FULLLESS2    0x3

/* The Least Significant Bit (LSB) position of the ALT_UART_SRT_SRT register field. */
#define ALT_UART_SRT_SRT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_SRT_SRT register field. */
#define ALT_UART_SRT_SRT_MSB        1
/* The width in bits of the ALT_UART_SRT_SRT register field. */
#define ALT_UART_SRT_SRT_WIDTH      2
/* The mask used to set the ALT_UART_SRT_SRT register field value. */
#define ALT_UART_SRT_SRT_SET_MSK    0x00000003
/* The mask used to clear the ALT_UART_SRT_SRT register field value. */
#define ALT_UART_SRT_SRT_CLR_MSK    0xfffffffc
/* The reset value of the ALT_UART_SRT_SRT register field. */
#define ALT_UART_SRT_SRT_RESET      0x0
/* Extracts the ALT_UART_SRT_SRT field value from a register. */
#define ALT_UART_SRT_SRT_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_UART_SRT_SRT register field value suitable for setting the register. */
#define ALT_UART_SRT_SRT_SET(value) (((value) << 0) & 0x00000003)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_SRT.
 */
struct ALT_UART_SRT_s
{
    uint32_t  srt :  2;  /* Shadow Rx  Trigger Bits */
    uint32_t      : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_SRT. */
typedef volatile struct ALT_UART_SRT_s  ALT_UART_SRT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_SRT register from the beginning of the component. */
#define ALT_UART_SRT_OFST        0x9c
/* The address of the ALT_UART_SRT register. */
#define ALT_UART_SRT_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_SRT_OFST))

/*
 * Register : Shadow Tx Empty Trigger - stet
 * 
 * This is a shadow register for the Tx empty trigger bits (FCR[5:4]).
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                 
 * :-------|:-------|:------|:-----------------------------
 *  [1:0]  | RW     | 0x0   | Shadow Tx Empty Trigger Bits
 *  [31:2] | ???    | 0x0   | *UNDEFINED*                 
 * 
 */
/*
 * Field : Shadow Tx Empty Trigger Bits - stet
 * 
 * This can be used to remove the burden of having to store the previously written
 * value to the FCR in memory and having to mask this value so that only the Tx
 * empty trigger bit gets updated. This is used to select the empty threshold level
 * at which the THRE Interrupts will be generated when the mode is active. These
 * threshold levels are also described in. The enum trigger levels are supported.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description           
 * :---------------------------------|:------|:-----------------------
 *  ALT_UART_STET_STET_E_FIFOEMPTY   | 0x0   | FIFO empty            
 *  ALT_UART_STET_STET_E_TWOCHARS    | 0x1   | Two characters in FIFO
 *  ALT_UART_STET_STET_E_QUARTERFULL | 0x2   | FIFO quarter full     
 *  ALT_UART_STET_STET_E_HALFFULL    | 0x3   | FIFO half full        
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_STET_STET
 * 
 * FIFO empty
 */
#define ALT_UART_STET_STET_E_FIFOEMPTY      0x0
/*
 * Enumerated value for register field ALT_UART_STET_STET
 * 
 * Two characters in FIFO
 */
#define ALT_UART_STET_STET_E_TWOCHARS       0x1
/*
 * Enumerated value for register field ALT_UART_STET_STET
 * 
 * FIFO quarter full
 */
#define ALT_UART_STET_STET_E_QUARTERFULL    0x2
/*
 * Enumerated value for register field ALT_UART_STET_STET
 * 
 * FIFO half full
 */
#define ALT_UART_STET_STET_E_HALFFULL       0x3

/* The Least Significant Bit (LSB) position of the ALT_UART_STET_STET register field. */
#define ALT_UART_STET_STET_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_STET_STET register field. */
#define ALT_UART_STET_STET_MSB        1
/* The width in bits of the ALT_UART_STET_STET register field. */
#define ALT_UART_STET_STET_WIDTH      2
/* The mask used to set the ALT_UART_STET_STET register field value. */
#define ALT_UART_STET_STET_SET_MSK    0x00000003
/* The mask used to clear the ALT_UART_STET_STET register field value. */
#define ALT_UART_STET_STET_CLR_MSK    0xfffffffc
/* The reset value of the ALT_UART_STET_STET register field. */
#define ALT_UART_STET_STET_RESET      0x0
/* Extracts the ALT_UART_STET_STET field value from a register. */
#define ALT_UART_STET_STET_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_UART_STET_STET register field value suitable for setting the register. */
#define ALT_UART_STET_STET_SET(value) (((value) << 0) & 0x00000003)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_STET.
 */
struct ALT_UART_STET_s
{
    uint32_t  stet :  2;  /* Shadow Tx Empty Trigger Bits */
    uint32_t       : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_STET. */
typedef volatile struct ALT_UART_STET_s  ALT_UART_STET_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_STET register from the beginning of the component. */
#define ALT_UART_STET_OFST        0xa0
/* The address of the ALT_UART_STET register. */
#define ALT_UART_STET_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_STET_OFST))

/*
 * Register : Halt Tx - htx
 * 
 * Used to halt transmission for testing.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description 
 * :-------|:-------|:------|:-------------
 *  [0]    | RW     | 0x0   | Halt Tx Bits
 *  [31:1] | ???    | 0x0   | *UNDEFINED* 
 * 
 */
/*
 * Field : Halt Tx Bits - htx
 * 
 * This register is use to halt transmissions for testing, so that the transmit
 * FIFO can be filled by the master when FIFO's are enabled.
 * 
 * Note, if FIFO's are not enabled, the setting of the halt Tx register will have
 * no effect on operation.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                    | Value | Description     
 * :------------------------|:------|:-----------------
 *  ALT_UART_HTX_HTX_E_DISD | 0x0   | Halt Tx disabled
 *  ALT_UART_HTX_HTX_E_END  | 0x1   | Halt Tx enabled 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_HTX_HTX
 * 
 * Halt Tx disabled
 */
#define ALT_UART_HTX_HTX_E_DISD 0x0
/*
 * Enumerated value for register field ALT_UART_HTX_HTX
 * 
 * Halt Tx enabled
 */
#define ALT_UART_HTX_HTX_E_END  0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_HTX_HTX register field. */
#define ALT_UART_HTX_HTX_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_HTX_HTX register field. */
#define ALT_UART_HTX_HTX_MSB        0
/* The width in bits of the ALT_UART_HTX_HTX register field. */
#define ALT_UART_HTX_HTX_WIDTH      1
/* The mask used to set the ALT_UART_HTX_HTX register field value. */
#define ALT_UART_HTX_HTX_SET_MSK    0x00000001
/* The mask used to clear the ALT_UART_HTX_HTX register field value. */
#define ALT_UART_HTX_HTX_CLR_MSK    0xfffffffe
/* The reset value of the ALT_UART_HTX_HTX register field. */
#define ALT_UART_HTX_HTX_RESET      0x0
/* Extracts the ALT_UART_HTX_HTX field value from a register. */
#define ALT_UART_HTX_HTX_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_UART_HTX_HTX register field value suitable for setting the register. */
#define ALT_UART_HTX_HTX_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_HTX.
 */
struct ALT_UART_HTX_s
{
    uint32_t  htx :  1;  /* Halt Tx Bits */
    uint32_t      : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_HTX. */
typedef volatile struct ALT_UART_HTX_s  ALT_UART_HTX_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_HTX register from the beginning of the component. */
#define ALT_UART_HTX_OFST        0xa4
/* The address of the ALT_UART_HTX register. */
#define ALT_UART_HTX_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_HTX_OFST))

/*
 * Register : DMA Software Acknowledge - dmasa
 * 
 * DMA Operation Control
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                  
 * :-------|:-------|:------|:------------------------------
 *  [0]    | W      | 0x0   | DMA Software Acknowledge Bits
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : DMA Software Acknowledge Bits - dmasa
 * 
 * This register is used to perform DMA software acknowledge if a transfer needs to
 * be terminated due to an error condition. For example, if the DMA disables the
 * channel, then the uart should clear its request. This will cause the Tx request,
 * Tx single, Rx request and Rx single signals to de-assert. Note that this bit is
 * 'self-clearing' and it is not necessary to clear this bit.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_DMASA_DMASA register field. */
#define ALT_UART_DMASA_DMASA_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_DMASA_DMASA register field. */
#define ALT_UART_DMASA_DMASA_MSB        0
/* The width in bits of the ALT_UART_DMASA_DMASA register field. */
#define ALT_UART_DMASA_DMASA_WIDTH      1
/* The mask used to set the ALT_UART_DMASA_DMASA register field value. */
#define ALT_UART_DMASA_DMASA_SET_MSK    0x00000001
/* The mask used to clear the ALT_UART_DMASA_DMASA register field value. */
#define ALT_UART_DMASA_DMASA_CLR_MSK    0xfffffffe
/* The reset value of the ALT_UART_DMASA_DMASA register field. */
#define ALT_UART_DMASA_DMASA_RESET      0x0
/* Extracts the ALT_UART_DMASA_DMASA field value from a register. */
#define ALT_UART_DMASA_DMASA_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_UART_DMASA_DMASA register field value suitable for setting the register. */
#define ALT_UART_DMASA_DMASA_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_DMASA.
 */
struct ALT_UART_DMASA_s
{
    uint32_t  dmasa :  1;  /* DMA Software Acknowledge Bits */
    uint32_t        : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_DMASA. */
typedef volatile struct ALT_UART_DMASA_s  ALT_UART_DMASA_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_DMASA register from the beginning of the component. */
#define ALT_UART_DMASA_OFST        0xa8
/* The address of the ALT_UART_DMASA register. */
#define ALT_UART_DMASA_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_DMASA_OFST))

/*
 * Register : Component Parameter Register - cpr
 * 
 * Describes various fixed hardware setups states.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                      
 * :--------|:-------|:------|:----------------------------------
 *  [1:0]   | R      | 0x2   | APB DATA WIDTH                   
 *  [3:2]   | ???    | 0x0   | *UNDEFINED*                      
 *  [4]     | R      | 0x1   | Auto Flow Control                
 *  [5]     | R      | 0x1   | THRE MODE                        
 *  [6]     | R      | 0x0   | SIR MODE Unsupported             
 *  [7]     | R      | 0x0   | SIR LP MODE Unsupported          
 *  [8]     | R      | 0x1   | ADDITIONAL FEATURES Supported    
 *  [9]     | R      | 0x1   | FIFO ACCESS Supported            
 *  [10]    | R      | 0x1   | FIFO STAT Supported              
 *  [11]    | R      | 0x1   | SHADOW Supported                 
 *  [12]    | R      | 0x1   | Configuartion ID Register Present
 *  [13]    | R      | 0x1   | DMA EXTRA Supported              
 *  [15:14] | ???    | 0x0   | *UNDEFINED*                      
 *  [23:16] | R      | 0x37  | FIFO Depth                       
 *  [31:24] | ???    | 0x0   | *UNDEFINED*                      
 * 
 */
/*
 * Field : APB DATA WIDTH - apbdatawidth
 * 
 * Fixed to support an ABP data bus width of 32-bits.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                    | Value | Description             
 * :----------------------------------------|:------|:-------------------------
 *  ALT_UART_CPR_APBDATAWIDTH_E_WIDTH32BITS | 0x2   | APB Data Width = 32-bits
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_CPR_APBDATAWIDTH
 * 
 * APB Data Width = 32-bits
 */
#define ALT_UART_CPR_APBDATAWIDTH_E_WIDTH32BITS 0x2

/* The Least Significant Bit (LSB) position of the ALT_UART_CPR_APBDATAWIDTH register field. */
#define ALT_UART_CPR_APBDATAWIDTH_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_CPR_APBDATAWIDTH register field. */
#define ALT_UART_CPR_APBDATAWIDTH_MSB        1
/* The width in bits of the ALT_UART_CPR_APBDATAWIDTH register field. */
#define ALT_UART_CPR_APBDATAWIDTH_WIDTH      2
/* The mask used to set the ALT_UART_CPR_APBDATAWIDTH register field value. */
#define ALT_UART_CPR_APBDATAWIDTH_SET_MSK    0x00000003
/* The mask used to clear the ALT_UART_CPR_APBDATAWIDTH register field value. */
#define ALT_UART_CPR_APBDATAWIDTH_CLR_MSK    0xfffffffc
/* The reset value of the ALT_UART_CPR_APBDATAWIDTH register field. */
#define ALT_UART_CPR_APBDATAWIDTH_RESET      0x2
/* Extracts the ALT_UART_CPR_APBDATAWIDTH field value from a register. */
#define ALT_UART_CPR_APBDATAWIDTH_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_UART_CPR_APBDATAWIDTH register field value suitable for setting the register. */
#define ALT_UART_CPR_APBDATAWIDTH_SET(value) (((value) << 0) & 0x00000003)

/*
 * Field : Auto Flow Control - afce_mode
 * 
 * Allows auto flow control.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description
 * :----------------------------|:------|:------------
 *  ALT_UART_CPR_AFCE_MOD_E_END | 0x1   | Auto Flow  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_CPR_AFCE_MOD
 * 
 * Auto Flow
 */
#define ALT_UART_CPR_AFCE_MOD_E_END 0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_CPR_AFCE_MOD register field. */
#define ALT_UART_CPR_AFCE_MOD_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_UART_CPR_AFCE_MOD register field. */
#define ALT_UART_CPR_AFCE_MOD_MSB        4
/* The width in bits of the ALT_UART_CPR_AFCE_MOD register field. */
#define ALT_UART_CPR_AFCE_MOD_WIDTH      1
/* The mask used to set the ALT_UART_CPR_AFCE_MOD register field value. */
#define ALT_UART_CPR_AFCE_MOD_SET_MSK    0x00000010
/* The mask used to clear the ALT_UART_CPR_AFCE_MOD register field value. */
#define ALT_UART_CPR_AFCE_MOD_CLR_MSK    0xffffffef
/* The reset value of the ALT_UART_CPR_AFCE_MOD register field. */
#define ALT_UART_CPR_AFCE_MOD_RESET      0x1
/* Extracts the ALT_UART_CPR_AFCE_MOD field value from a register. */
#define ALT_UART_CPR_AFCE_MOD_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_UART_CPR_AFCE_MOD register field value suitable for setting the register. */
#define ALT_UART_CPR_AFCE_MOD_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : THRE MODE - thre_mode
 * 
 * Programmable Transmitter Hold Register Empty interrupt
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                              
 * :----------------------------|:------|:------------------------------------------
 *  ALT_UART_CPR_THRE_MOD_E_END | 0x1   | Programmable Tx Hold Reg. Empty interrupt
 * :                            |       | present                                  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_CPR_THRE_MOD
 * 
 * Programmable Tx Hold Reg. Empty interrupt present
 */
#define ALT_UART_CPR_THRE_MOD_E_END 0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_CPR_THRE_MOD register field. */
#define ALT_UART_CPR_THRE_MOD_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_UART_CPR_THRE_MOD register field. */
#define ALT_UART_CPR_THRE_MOD_MSB        5
/* The width in bits of the ALT_UART_CPR_THRE_MOD register field. */
#define ALT_UART_CPR_THRE_MOD_WIDTH      1
/* The mask used to set the ALT_UART_CPR_THRE_MOD register field value. */
#define ALT_UART_CPR_THRE_MOD_SET_MSK    0x00000020
/* The mask used to clear the ALT_UART_CPR_THRE_MOD register field value. */
#define ALT_UART_CPR_THRE_MOD_CLR_MSK    0xffffffdf
/* The reset value of the ALT_UART_CPR_THRE_MOD register field. */
#define ALT_UART_CPR_THRE_MOD_RESET      0x1
/* Extracts the ALT_UART_CPR_THRE_MOD field value from a register. */
#define ALT_UART_CPR_THRE_MOD_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_UART_CPR_THRE_MOD register field value suitable for setting the register. */
#define ALT_UART_CPR_THRE_MOD_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : SIR MODE Unsupported - sir_mode
 * 
 * Sir mode not used in this application.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description           
 * :----------------------------|:------|:-----------------------
 *  ALT_UART_CPR_SIR_MOD_E_DISD | 0x0   | Sir Mode Not Supported
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_CPR_SIR_MOD
 * 
 * Sir Mode Not Supported
 */
#define ALT_UART_CPR_SIR_MOD_E_DISD 0x0

/* The Least Significant Bit (LSB) position of the ALT_UART_CPR_SIR_MOD register field. */
#define ALT_UART_CPR_SIR_MOD_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_UART_CPR_SIR_MOD register field. */
#define ALT_UART_CPR_SIR_MOD_MSB        6
/* The width in bits of the ALT_UART_CPR_SIR_MOD register field. */
#define ALT_UART_CPR_SIR_MOD_WIDTH      1
/* The mask used to set the ALT_UART_CPR_SIR_MOD register field value. */
#define ALT_UART_CPR_SIR_MOD_SET_MSK    0x00000040
/* The mask used to clear the ALT_UART_CPR_SIR_MOD register field value. */
#define ALT_UART_CPR_SIR_MOD_CLR_MSK    0xffffffbf
/* The reset value of the ALT_UART_CPR_SIR_MOD register field. */
#define ALT_UART_CPR_SIR_MOD_RESET      0x0
/* Extracts the ALT_UART_CPR_SIR_MOD field value from a register. */
#define ALT_UART_CPR_SIR_MOD_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_UART_CPR_SIR_MOD register field value suitable for setting the register. */
#define ALT_UART_CPR_SIR_MOD_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : SIR LP MODE Unsupported - sir_lp_mode
 * 
 * LP Sir Mode not used in this application.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description              
 * :-------------------------------|:------|:--------------------------
 *  ALT_UART_CPR_SIR_LP_MOD_E_DISD | 0x0   | LP Sir Mode Not Supported
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_CPR_SIR_LP_MOD
 * 
 * LP Sir Mode Not Supported
 */
#define ALT_UART_CPR_SIR_LP_MOD_E_DISD  0x0

/* The Least Significant Bit (LSB) position of the ALT_UART_CPR_SIR_LP_MOD register field. */
#define ALT_UART_CPR_SIR_LP_MOD_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_UART_CPR_SIR_LP_MOD register field. */
#define ALT_UART_CPR_SIR_LP_MOD_MSB        7
/* The width in bits of the ALT_UART_CPR_SIR_LP_MOD register field. */
#define ALT_UART_CPR_SIR_LP_MOD_WIDTH      1
/* The mask used to set the ALT_UART_CPR_SIR_LP_MOD register field value. */
#define ALT_UART_CPR_SIR_LP_MOD_SET_MSK    0x00000080
/* The mask used to clear the ALT_UART_CPR_SIR_LP_MOD register field value. */
#define ALT_UART_CPR_SIR_LP_MOD_CLR_MSK    0xffffff7f
/* The reset value of the ALT_UART_CPR_SIR_LP_MOD register field. */
#define ALT_UART_CPR_SIR_LP_MOD_RESET      0x0
/* Extracts the ALT_UART_CPR_SIR_LP_MOD field value from a register. */
#define ALT_UART_CPR_SIR_LP_MOD_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_UART_CPR_SIR_LP_MOD register field value suitable for setting the register. */
#define ALT_UART_CPR_SIR_LP_MOD_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : ADDITIONAL FEATURES Supported - additional_feat
 * 
 * Configures the uart to include fifo status register, shadow registers and
 * encoded parameter register.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                  
 * :-----------------------------------|:------|:------------------------------
 *  ALT_UART_CPR_ADDITIONAL_FEAT_E_END | 0x1   | Additional Features Supported
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_CPR_ADDITIONAL_FEAT
 * 
 * Additional Features Supported
 */
#define ALT_UART_CPR_ADDITIONAL_FEAT_E_END  0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_CPR_ADDITIONAL_FEAT register field. */
#define ALT_UART_CPR_ADDITIONAL_FEAT_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_UART_CPR_ADDITIONAL_FEAT register field. */
#define ALT_UART_CPR_ADDITIONAL_FEAT_MSB        8
/* The width in bits of the ALT_UART_CPR_ADDITIONAL_FEAT register field. */
#define ALT_UART_CPR_ADDITIONAL_FEAT_WIDTH      1
/* The mask used to set the ALT_UART_CPR_ADDITIONAL_FEAT register field value. */
#define ALT_UART_CPR_ADDITIONAL_FEAT_SET_MSK    0x00000100
/* The mask used to clear the ALT_UART_CPR_ADDITIONAL_FEAT register field value. */
#define ALT_UART_CPR_ADDITIONAL_FEAT_CLR_MSK    0xfffffeff
/* The reset value of the ALT_UART_CPR_ADDITIONAL_FEAT register field. */
#define ALT_UART_CPR_ADDITIONAL_FEAT_RESET      0x1
/* Extracts the ALT_UART_CPR_ADDITIONAL_FEAT field value from a register. */
#define ALT_UART_CPR_ADDITIONAL_FEAT_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_UART_CPR_ADDITIONAL_FEAT register field value suitable for setting the register. */
#define ALT_UART_CPR_ADDITIONAL_FEAT_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : FIFO ACCESS Supported - fifo_access
 * 
 * Configures the peripheral to have a programmable FIFO access mode. This is used
 * for test purposes, to allow the receiver FIFO to be written and the transmit
 * FIFO to be read when FIFOs are implemented and enabled.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description          
 * :-------------------------------|:------|:----------------------
 *  ALT_UART_CPR_FIFO_ACCESS_E_END | 0x1   | FIFO Access Supported
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_CPR_FIFO_ACCESS
 * 
 * FIFO Access Supported
 */
#define ALT_UART_CPR_FIFO_ACCESS_E_END  0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_CPR_FIFO_ACCESS register field. */
#define ALT_UART_CPR_FIFO_ACCESS_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_UART_CPR_FIFO_ACCESS register field. */
#define ALT_UART_CPR_FIFO_ACCESS_MSB        9
/* The width in bits of the ALT_UART_CPR_FIFO_ACCESS register field. */
#define ALT_UART_CPR_FIFO_ACCESS_WIDTH      1
/* The mask used to set the ALT_UART_CPR_FIFO_ACCESS register field value. */
#define ALT_UART_CPR_FIFO_ACCESS_SET_MSK    0x00000200
/* The mask used to clear the ALT_UART_CPR_FIFO_ACCESS register field value. */
#define ALT_UART_CPR_FIFO_ACCESS_CLR_MSK    0xfffffdff
/* The reset value of the ALT_UART_CPR_FIFO_ACCESS register field. */
#define ALT_UART_CPR_FIFO_ACCESS_RESET      0x1
/* Extracts the ALT_UART_CPR_FIFO_ACCESS field value from a register. */
#define ALT_UART_CPR_FIFO_ACCESS_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_UART_CPR_FIFO_ACCESS register field value suitable for setting the register. */
#define ALT_UART_CPR_FIFO_ACCESS_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : FIFO STAT Supported - fifo_stat
 * 
 * Configures the peripheral to have three additional FIFO status registers.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description        
 * :-----------------------------|:------|:--------------------
 *  ALT_UART_CPR_FIFO_STAT_E_END | 0x1   | FIFO Stat Supported
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_CPR_FIFO_STAT
 * 
 * FIFO Stat Supported
 */
#define ALT_UART_CPR_FIFO_STAT_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_CPR_FIFO_STAT register field. */
#define ALT_UART_CPR_FIFO_STAT_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_UART_CPR_FIFO_STAT register field. */
#define ALT_UART_CPR_FIFO_STAT_MSB        10
/* The width in bits of the ALT_UART_CPR_FIFO_STAT register field. */
#define ALT_UART_CPR_FIFO_STAT_WIDTH      1
/* The mask used to set the ALT_UART_CPR_FIFO_STAT register field value. */
#define ALT_UART_CPR_FIFO_STAT_SET_MSK    0x00000400
/* The mask used to clear the ALT_UART_CPR_FIFO_STAT register field value. */
#define ALT_UART_CPR_FIFO_STAT_CLR_MSK    0xfffffbff
/* The reset value of the ALT_UART_CPR_FIFO_STAT register field. */
#define ALT_UART_CPR_FIFO_STAT_RESET      0x1
/* Extracts the ALT_UART_CPR_FIFO_STAT field value from a register. */
#define ALT_UART_CPR_FIFO_STAT_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_UART_CPR_FIFO_STAT register field value suitable for setting the register. */
#define ALT_UART_CPR_FIFO_STAT_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : SHADOW Supported - shadow
 * 
 * Configures the peripheral to have seven additional registers that shadow some of
 * the existing register bits that are regularly modified by software. These can be
 * used to reduce the software overhead that is introduced by having to perform
 * read-modify writes.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description     
 * :--------------------------|:------|:-----------------
 *  ALT_UART_CPR_SHADOW_E_END | 0x1   | Shadow Supported
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_CPR_SHADOW
 * 
 * Shadow Supported
 */
#define ALT_UART_CPR_SHADOW_E_END   0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_CPR_SHADOW register field. */
#define ALT_UART_CPR_SHADOW_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_UART_CPR_SHADOW register field. */
#define ALT_UART_CPR_SHADOW_MSB        11
/* The width in bits of the ALT_UART_CPR_SHADOW register field. */
#define ALT_UART_CPR_SHADOW_WIDTH      1
/* The mask used to set the ALT_UART_CPR_SHADOW register field value. */
#define ALT_UART_CPR_SHADOW_SET_MSK    0x00000800
/* The mask used to clear the ALT_UART_CPR_SHADOW register field value. */
#define ALT_UART_CPR_SHADOW_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_UART_CPR_SHADOW register field. */
#define ALT_UART_CPR_SHADOW_RESET      0x1
/* Extracts the ALT_UART_CPR_SHADOW field value from a register. */
#define ALT_UART_CPR_SHADOW_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_UART_CPR_SHADOW register field value suitable for setting the register. */
#define ALT_UART_CPR_SHADOW_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : Configuartion ID Register Present - uart_add_encoded_param
 * 
 * Configures the peripheral to have a configuration identification register.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                  | Value | Description        
 * :--------------------------------------|:------|:--------------------
 *  ALT_UART_CPR_UART_ADD_ENC_PARAM_E_END | 0x1   | ID register present
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_CPR_UART_ADD_ENC_PARAM
 * 
 * ID register present
 */
#define ALT_UART_CPR_UART_ADD_ENC_PARAM_E_END   0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_CPR_UART_ADD_ENC_PARAM register field. */
#define ALT_UART_CPR_UART_ADD_ENC_PARAM_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_UART_CPR_UART_ADD_ENC_PARAM register field. */
#define ALT_UART_CPR_UART_ADD_ENC_PARAM_MSB        12
/* The width in bits of the ALT_UART_CPR_UART_ADD_ENC_PARAM register field. */
#define ALT_UART_CPR_UART_ADD_ENC_PARAM_WIDTH      1
/* The mask used to set the ALT_UART_CPR_UART_ADD_ENC_PARAM register field value. */
#define ALT_UART_CPR_UART_ADD_ENC_PARAM_SET_MSK    0x00001000
/* The mask used to clear the ALT_UART_CPR_UART_ADD_ENC_PARAM register field value. */
#define ALT_UART_CPR_UART_ADD_ENC_PARAM_CLR_MSK    0xffffefff
/* The reset value of the ALT_UART_CPR_UART_ADD_ENC_PARAM register field. */
#define ALT_UART_CPR_UART_ADD_ENC_PARAM_RESET      0x1
/* Extracts the ALT_UART_CPR_UART_ADD_ENC_PARAM field value from a register. */
#define ALT_UART_CPR_UART_ADD_ENC_PARAM_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_UART_CPR_UART_ADD_ENC_PARAM register field value suitable for setting the register. */
#define ALT_UART_CPR_UART_ADD_ENC_PARAM_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : DMA EXTRA Supported - dma_extra
 * 
 * Configures the peripheral to have four additional DMA signals on the interface.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description        
 * :-----------------------------|:------|:--------------------
 *  ALT_UART_CPR_DMA_EXTRA_E_END | 0x1   | DMA Extra Supported
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_CPR_DMA_EXTRA
 * 
 * DMA Extra Supported
 */
#define ALT_UART_CPR_DMA_EXTRA_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_UART_CPR_DMA_EXTRA register field. */
#define ALT_UART_CPR_DMA_EXTRA_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_UART_CPR_DMA_EXTRA register field. */
#define ALT_UART_CPR_DMA_EXTRA_MSB        13
/* The width in bits of the ALT_UART_CPR_DMA_EXTRA register field. */
#define ALT_UART_CPR_DMA_EXTRA_WIDTH      1
/* The mask used to set the ALT_UART_CPR_DMA_EXTRA register field value. */
#define ALT_UART_CPR_DMA_EXTRA_SET_MSK    0x00002000
/* The mask used to clear the ALT_UART_CPR_DMA_EXTRA register field value. */
#define ALT_UART_CPR_DMA_EXTRA_CLR_MSK    0xffffdfff
/* The reset value of the ALT_UART_CPR_DMA_EXTRA register field. */
#define ALT_UART_CPR_DMA_EXTRA_RESET      0x1
/* Extracts the ALT_UART_CPR_DMA_EXTRA field value from a register. */
#define ALT_UART_CPR_DMA_EXTRA_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_UART_CPR_DMA_EXTRA register field value suitable for setting the register. */
#define ALT_UART_CPR_DMA_EXTRA_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : FIFO Depth - fifo_mode
 * 
 * Receiver and Transmitter FIFO depth in bytes.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description         
 * :-------------------------------------|:------|:---------------------
 *  ALT_UART_CPR_FIFO_MOD_E_FIFO128BYTES | 0x80  | FIFO Depth 128 bytes
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_UART_CPR_FIFO_MOD
 * 
 * FIFO Depth 128 bytes
 */
#define ALT_UART_CPR_FIFO_MOD_E_FIFO128BYTES    0x80

/* The Least Significant Bit (LSB) position of the ALT_UART_CPR_FIFO_MOD register field. */
#define ALT_UART_CPR_FIFO_MOD_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_UART_CPR_FIFO_MOD register field. */
#define ALT_UART_CPR_FIFO_MOD_MSB        23
/* The width in bits of the ALT_UART_CPR_FIFO_MOD register field. */
#define ALT_UART_CPR_FIFO_MOD_WIDTH      8
/* The mask used to set the ALT_UART_CPR_FIFO_MOD register field value. */
#define ALT_UART_CPR_FIFO_MOD_SET_MSK    0x00ff0000
/* The mask used to clear the ALT_UART_CPR_FIFO_MOD register field value. */
#define ALT_UART_CPR_FIFO_MOD_CLR_MSK    0xff00ffff
/* The reset value of the ALT_UART_CPR_FIFO_MOD register field. */
#define ALT_UART_CPR_FIFO_MOD_RESET      0x37
/* Extracts the ALT_UART_CPR_FIFO_MOD field value from a register. */
#define ALT_UART_CPR_FIFO_MOD_GET(value) (((value) & 0x00ff0000) >> 16)
/* Produces a ALT_UART_CPR_FIFO_MOD register field value suitable for setting the register. */
#define ALT_UART_CPR_FIFO_MOD_SET(value) (((value) << 16) & 0x00ff0000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_CPR.
 */
struct ALT_UART_CPR_s
{
    const uint32_t  apbdatawidth           :  2;  /* APB DATA WIDTH */
    uint32_t                               :  2;  /* *UNDEFINED* */
    const uint32_t  afce_mode              :  1;  /* Auto Flow Control */
    const uint32_t  thre_mode              :  1;  /* THRE MODE */
    const uint32_t  sir_mode               :  1;  /* SIR MODE Unsupported */
    const uint32_t  sir_lp_mode            :  1;  /* SIR LP MODE Unsupported */
    const uint32_t  additional_feat        :  1;  /* ADDITIONAL FEATURES Supported */
    const uint32_t  fifo_access            :  1;  /* FIFO ACCESS Supported */
    const uint32_t  fifo_stat              :  1;  /* FIFO STAT Supported */
    const uint32_t  shadow                 :  1;  /* SHADOW Supported */
    const uint32_t  uart_add_encoded_param :  1;  /* Configuartion ID Register Present */
    const uint32_t  dma_extra              :  1;  /* DMA EXTRA Supported */
    uint32_t                               :  2;  /* *UNDEFINED* */
    const uint32_t  fifo_mode              :  8;  /* FIFO Depth */
    uint32_t                               :  8;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_UART_CPR. */
typedef volatile struct ALT_UART_CPR_s  ALT_UART_CPR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_CPR register from the beginning of the component. */
#define ALT_UART_CPR_OFST        0xf4
/* The address of the ALT_UART_CPR register. */
#define ALT_UART_CPR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_CPR_OFST))

/*
 * Register : Component Version - ucv
 * 
 * Used only with Additional Features
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset      | Description  
 * :-------|:-------|:-----------|:--------------
 *  [31:0] | R      | 0x3331312a | ASCII version
 * 
 */
/*
 * Field : ASCII version - uart_component_version
 * 
 * ASCII value for each number in the version, followed by *For example 32_30_31_2A
 * represents the version 2.01a
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_UCV_UART_COMPONENT_VER register field. */
#define ALT_UART_UCV_UART_COMPONENT_VER_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_UCV_UART_COMPONENT_VER register field. */
#define ALT_UART_UCV_UART_COMPONENT_VER_MSB        31
/* The width in bits of the ALT_UART_UCV_UART_COMPONENT_VER register field. */
#define ALT_UART_UCV_UART_COMPONENT_VER_WIDTH      32
/* The mask used to set the ALT_UART_UCV_UART_COMPONENT_VER register field value. */
#define ALT_UART_UCV_UART_COMPONENT_VER_SET_MSK    0xffffffff
/* The mask used to clear the ALT_UART_UCV_UART_COMPONENT_VER register field value. */
#define ALT_UART_UCV_UART_COMPONENT_VER_CLR_MSK    0x00000000
/* The reset value of the ALT_UART_UCV_UART_COMPONENT_VER register field. */
#define ALT_UART_UCV_UART_COMPONENT_VER_RESET      0x3331312a
/* Extracts the ALT_UART_UCV_UART_COMPONENT_VER field value from a register. */
#define ALT_UART_UCV_UART_COMPONENT_VER_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_UART_UCV_UART_COMPONENT_VER register field value suitable for setting the register. */
#define ALT_UART_UCV_UART_COMPONENT_VER_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_UCV.
 */
struct ALT_UART_UCV_s
{
    const uint32_t  uart_component_version : 32;  /* ASCII version */
};

/* The typedef declaration for register ALT_UART_UCV. */
typedef volatile struct ALT_UART_UCV_s  ALT_UART_UCV_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_UCV register from the beginning of the component. */
#define ALT_UART_UCV_OFST        0xf8
/* The address of the ALT_UART_UCV register. */
#define ALT_UART_UCV_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_UCV_OFST))

/*
 * Register : Component Type Register - ctr
 * 
 * Describes a hex value associated with the component.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset      | Description  
 * :-------|:-------|:-----------|:--------------
 *  [31:0] | R      | 0x44570110 | Peripheral ID
 * 
 */
/*
 * Field : Peripheral ID - peripheral_id
 * 
 * This register contains the peripherals identification code.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_UART_CTR_PERIPHERAL_ID register field. */
#define ALT_UART_CTR_PERIPHERAL_ID_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_UART_CTR_PERIPHERAL_ID register field. */
#define ALT_UART_CTR_PERIPHERAL_ID_MSB        31
/* The width in bits of the ALT_UART_CTR_PERIPHERAL_ID register field. */
#define ALT_UART_CTR_PERIPHERAL_ID_WIDTH      32
/* The mask used to set the ALT_UART_CTR_PERIPHERAL_ID register field value. */
#define ALT_UART_CTR_PERIPHERAL_ID_SET_MSK    0xffffffff
/* The mask used to clear the ALT_UART_CTR_PERIPHERAL_ID register field value. */
#define ALT_UART_CTR_PERIPHERAL_ID_CLR_MSK    0x00000000
/* The reset value of the ALT_UART_CTR_PERIPHERAL_ID register field. */
#define ALT_UART_CTR_PERIPHERAL_ID_RESET      0x44570110
/* Extracts the ALT_UART_CTR_PERIPHERAL_ID field value from a register. */
#define ALT_UART_CTR_PERIPHERAL_ID_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_UART_CTR_PERIPHERAL_ID register field value suitable for setting the register. */
#define ALT_UART_CTR_PERIPHERAL_ID_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_UART_CTR.
 */
struct ALT_UART_CTR_s
{
    const uint32_t  peripheral_id : 32;  /* Peripheral ID */
};

/* The typedef declaration for register ALT_UART_CTR. */
typedef volatile struct ALT_UART_CTR_s  ALT_UART_CTR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_UART_CTR register from the beginning of the component. */
#define ALT_UART_CTR_OFST        0xfc
/* The address of the ALT_UART_CTR register. */
#define ALT_UART_CTR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_UART_CTR_OFST))

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_UART.
 */
struct ALT_UART_s
{
    volatile ALT_UART_RBR_THR_DLL_t  rbr_thr_dll;         /* ALT_UART_RBR_THR_DLL */
    volatile ALT_UART_IER_DLH_t      ier_dlh;             /* ALT_UART_IER_DLH */
    /* Union for registers colocated at base address offset #0x. */
    union
    {
        volatile ALT_UART_IIR_t          iir;                 /* ALT_UART_IIR */
        volatile ALT_UART_FCR_t          fcr;                 /* ALT_UART_FCR */
    } _u_0x8;
    volatile ALT_UART_LCR_t          lcr;                 /* ALT_UART_LCR */
    volatile ALT_UART_MCR_t          mcr;                 /* ALT_UART_MCR */
    volatile ALT_UART_LSR_t          lsr;                 /* ALT_UART_LSR */
    volatile ALT_UART_MSR_t          msr;                 /* ALT_UART_MSR */
    volatile ALT_UART_SCR_t          scr;                 /* ALT_UART_SCR */
    volatile uint32_t                _pad_0x20_0x2f[4];   /* *UNDEFINED* */
    volatile ALT_UART_SRBR_t         srbr;                /* ALT_UART_SRBR */
    volatile ALT_UART_STHR_t         sthr;                /* ALT_UART_STHR */
    volatile uint32_t                _pad_0x38_0x6f[14];  /* *UNDEFINED* */
    volatile ALT_UART_FAR_t          far;                 /* ALT_UART_FAR */
    volatile ALT_UART_TFR_t          tfr;                 /* ALT_UART_TFR */
    volatile ALT_UART_RFW_t          RFW;                 /* ALT_UART_RFW */
    volatile ALT_UART_USR_t          usr;                 /* ALT_UART_USR */
    volatile ALT_UART_TFL_t          tfl;                 /* ALT_UART_TFL */
    volatile ALT_UART_RFL_t          rfl;                 /* ALT_UART_RFL */
    volatile ALT_UART_SRR_t          srr;                 /* ALT_UART_SRR */
    volatile ALT_UART_SRTS_t         srts;                /* ALT_UART_SRTS */
    volatile ALT_UART_SBCR_t         sbcr;                /* ALT_UART_SBCR */
    volatile ALT_UART_SDMAM_t        sdmam;               /* ALT_UART_SDMAM */
    volatile ALT_UART_SFE_t          sfe;                 /* ALT_UART_SFE */
    volatile ALT_UART_SRT_t          srt;                 /* ALT_UART_SRT */
    volatile ALT_UART_STET_t         stet;                /* ALT_UART_STET */
    volatile ALT_UART_HTX_t          htx;                 /* ALT_UART_HTX */
    volatile ALT_UART_DMASA_t        dmasa;               /* ALT_UART_DMASA */
    volatile uint32_t                _pad_0xac_0xf3[18];  /* *UNDEFINED* */
    volatile ALT_UART_CPR_t          cpr;                 /* ALT_UART_CPR */
    volatile ALT_UART_UCV_t          ucv;                 /* ALT_UART_UCV */
    volatile ALT_UART_CTR_t          ctr;                 /* ALT_UART_CTR */
};

/* The typedef declaration for register group ALT_UART. */
typedef volatile struct ALT_UART_s  ALT_UART_t;
/* The struct declaration for the raw register contents of register group ALT_UART. */
struct ALT_UART_raw_s
{
    volatile uint32_t  rbr_thr_dll;         /* ALT_UART_RBR_THR_DLL */
    volatile uint32_t  ier_dlh;             /* ALT_UART_IER_DLH */
    /* Union for registers colocated at base address offset #0x. */
    union
    {
    volatile uint32_t  iir;                 /* ALT_UART_IIR */
    volatile uint32_t  fcr;                 /* ALT_UART_FCR */
    } _u_0x8;
    volatile uint32_t  lcr;                 /* ALT_UART_LCR */
    volatile uint32_t  mcr;                 /* ALT_UART_MCR */
    volatile uint32_t  lsr;                 /* ALT_UART_LSR */
    volatile uint32_t  msr;                 /* ALT_UART_MSR */
    volatile uint32_t  scr;                 /* ALT_UART_SCR */
    volatile uint32_t  _pad_0x20_0x2f[4];   /* *UNDEFINED* */
    volatile uint32_t  srbr;                /* ALT_UART_SRBR */
    volatile uint32_t  sthr;                /* ALT_UART_STHR */
    volatile uint32_t  _pad_0x38_0x6f[14];  /* *UNDEFINED* */
    volatile uint32_t  far;                 /* ALT_UART_FAR */
    volatile uint32_t  tfr;                 /* ALT_UART_TFR */
    volatile uint32_t  RFW;                 /* ALT_UART_RFW */
    volatile uint32_t  usr;                 /* ALT_UART_USR */
    volatile uint32_t  tfl;                 /* ALT_UART_TFL */
    volatile uint32_t  rfl;                 /* ALT_UART_RFL */
    volatile uint32_t  srr;                 /* ALT_UART_SRR */
    volatile uint32_t  srts;                /* ALT_UART_SRTS */
    volatile uint32_t  sbcr;                /* ALT_UART_SBCR */
    volatile uint32_t  sdmam;               /* ALT_UART_SDMAM */
    volatile uint32_t  sfe;                 /* ALT_UART_SFE */
    volatile uint32_t  srt;                 /* ALT_UART_SRT */
    volatile uint32_t  stet;                /* ALT_UART_STET */
    volatile uint32_t  htx;                 /* ALT_UART_HTX */
    volatile uint32_t  dmasa;               /* ALT_UART_DMASA */
    volatile uint32_t  _pad_0xac_0xf3[18];  /* *UNDEFINED* */
    volatile uint32_t  cpr;                 /* ALT_UART_CPR */
    volatile uint32_t  ucv;                 /* ALT_UART_UCV */
    volatile uint32_t  ctr;                 /* ALT_UART_CTR */
};

/* The typedef declaration for the raw register contents of register group ALT_UART. */
typedef volatile struct ALT_UART_raw_s  ALT_UART_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_UART_H__ */

