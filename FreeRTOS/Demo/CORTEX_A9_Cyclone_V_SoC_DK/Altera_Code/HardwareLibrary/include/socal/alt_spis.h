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

/* Altera - ALT_SPIS */

#ifndef __ALTERA_ALT_SPIS_H__
#define __ALTERA_ALT_SPIS_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : SPI Slave Module - ALT_SPIS
 * SPI Slave Module
 * 
 * Registers in the SPI Slave module
 * 
 */
/*
 * Register : Control Register 0 - ctrlr0
 * 
 * This register controls the serial data transfer. It is impossible to write to
 * this register when the SPI Slave is enabled. The SPI Slave is enabled and
 * disabled by writing to the SPIENR register.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description          
 * :--------|:-------|:------|:----------------------
 *  [3:0]   | RW     | 0x7   | Data Frame Size      
 *  [5:4]   | RW     | 0x0   | Frame Format         
 *  [6]     | RW     | 0x0   | Serial Clock Phase   
 *  [7]     | RW     | 0x0   | Serial Clock Polarity
 *  [9:8]   | RW     | 0x0   | Transfer Mode        
 *  [10]    | RW     | 0x0   | Slave Output Enable  
 *  [11]    | RW     | 0x0   | Shift Register Loop  
 *  [15:12] | RW     | 0x0   | Control Frame Size   
 *  [31:16] | ???    | 0x0   | *UNDEFINED*          
 * 
 */
/*
 * Field : Data Frame Size - dfs
 * 
 * Selects the data frame length. When the data frame size is programmed to be less
 * than 16 bits, the receive data are automatically right-justified by the receive
 * logic, with the upper bits of the receiver FIFO zero-padded. You must right-
 * justify transmit data before writing into the transmit FIFO. The transmit logic
 * ignores the upper unused bits when transmitting the data.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description                
 * :--------------------------------|:------|:----------------------------
 *  ALT_SPIS_CTLR0_DFS_E_WIDTH4BIT  | 0x3   | 4-bit serial data transfer 
 *  ALT_SPIS_CTLR0_DFS_E_WIDTH5BIT  | 0x4   | 5-bit serial data transfer 
 *  ALT_SPIS_CTLR0_DFS_E_WIDTH6BIT  | 0x5   | 6-bit serial data transfer 
 *  ALT_SPIS_CTLR0_DFS_E_WIDTH7BIT  | 0x6   | 7-bit serial data transfer 
 *  ALT_SPIS_CTLR0_DFS_E_WIDTH8BIT  | 0x7   | 8-bit serial data transfer 
 *  ALT_SPIS_CTLR0_DFS_E_WIDTH9BIT  | 0x8   | 9-bit serial data transfer 
 *  ALT_SPIS_CTLR0_DFS_E_WIDTH10BIT | 0x9   | 10-bit serial data transfer
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_DFS
 * 
 * 4-bit serial data transfer
 */
#define ALT_SPIS_CTLR0_DFS_E_WIDTH4BIT  0x3
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_DFS
 * 
 * 5-bit serial data transfer
 */
#define ALT_SPIS_CTLR0_DFS_E_WIDTH5BIT  0x4
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_DFS
 * 
 * 6-bit serial data transfer
 */
#define ALT_SPIS_CTLR0_DFS_E_WIDTH6BIT  0x5
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_DFS
 * 
 * 7-bit serial data transfer
 */
#define ALT_SPIS_CTLR0_DFS_E_WIDTH7BIT  0x6
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_DFS
 * 
 * 8-bit serial data transfer
 */
#define ALT_SPIS_CTLR0_DFS_E_WIDTH8BIT  0x7
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_DFS
 * 
 * 9-bit serial data transfer
 */
#define ALT_SPIS_CTLR0_DFS_E_WIDTH9BIT  0x8
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_DFS
 * 
 * 10-bit serial data transfer
 */
#define ALT_SPIS_CTLR0_DFS_E_WIDTH10BIT 0x9

/* The Least Significant Bit (LSB) position of the ALT_SPIS_CTLR0_DFS register field. */
#define ALT_SPIS_CTLR0_DFS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_CTLR0_DFS register field. */
#define ALT_SPIS_CTLR0_DFS_MSB        3
/* The width in bits of the ALT_SPIS_CTLR0_DFS register field. */
#define ALT_SPIS_CTLR0_DFS_WIDTH      4
/* The mask used to set the ALT_SPIS_CTLR0_DFS register field value. */
#define ALT_SPIS_CTLR0_DFS_SET_MSK    0x0000000f
/* The mask used to clear the ALT_SPIS_CTLR0_DFS register field value. */
#define ALT_SPIS_CTLR0_DFS_CLR_MSK    0xfffffff0
/* The reset value of the ALT_SPIS_CTLR0_DFS register field. */
#define ALT_SPIS_CTLR0_DFS_RESET      0x7
/* Extracts the ALT_SPIS_CTLR0_DFS field value from a register. */
#define ALT_SPIS_CTLR0_DFS_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_SPIS_CTLR0_DFS register field value suitable for setting the register. */
#define ALT_SPIS_CTLR0_DFS_SET(value) (((value) << 0) & 0x0000000f)

/*
 * Field : Frame Format - frf
 * 
 * Selects which serial protocol transfers the data.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description            
 * :----------------------------|:------|:------------------------
 *  ALT_SPIS_CTLR0_FRF_E_MOTSPI | 0x0   | Motorola SPI           
 *  ALT_SPIS_CTLR0_FRF_E_TISSP  | 0x1   | Texas instruments  SSP 
 *  ALT_SPIS_CTLR0_FRF_E_NATMW  | 0x2   | National Semi Microwire
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_FRF
 * 
 * Motorola SPI
 */
#define ALT_SPIS_CTLR0_FRF_E_MOTSPI 0x0
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_FRF
 * 
 * Texas instruments  SSP
 */
#define ALT_SPIS_CTLR0_FRF_E_TISSP  0x1
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_FRF
 * 
 * National Semi Microwire
 */
#define ALT_SPIS_CTLR0_FRF_E_NATMW  0x2

/* The Least Significant Bit (LSB) position of the ALT_SPIS_CTLR0_FRF register field. */
#define ALT_SPIS_CTLR0_FRF_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SPIS_CTLR0_FRF register field. */
#define ALT_SPIS_CTLR0_FRF_MSB        5
/* The width in bits of the ALT_SPIS_CTLR0_FRF register field. */
#define ALT_SPIS_CTLR0_FRF_WIDTH      2
/* The mask used to set the ALT_SPIS_CTLR0_FRF register field value. */
#define ALT_SPIS_CTLR0_FRF_SET_MSK    0x00000030
/* The mask used to clear the ALT_SPIS_CTLR0_FRF register field value. */
#define ALT_SPIS_CTLR0_FRF_CLR_MSK    0xffffffcf
/* The reset value of the ALT_SPIS_CTLR0_FRF register field. */
#define ALT_SPIS_CTLR0_FRF_RESET      0x0
/* Extracts the ALT_SPIS_CTLR0_FRF field value from a register. */
#define ALT_SPIS_CTLR0_FRF_GET(value) (((value) & 0x00000030) >> 4)
/* Produces a ALT_SPIS_CTLR0_FRF register field value suitable for setting the register. */
#define ALT_SPIS_CTLR0_FRF_SET(value) (((value) << 4) & 0x00000030)

/*
 * Field : Serial Clock Phase - scph
 * 
 * Valid when the frame format (FRF) is set to Motorola SPI. The serial clock phase
 * selects the relationship of the serial clock with the slave select signal. When
 * SCPH = 0, data are captured on the first edge of the serial clock. When SCPH =
 * 1, the serial clock starts toggling one cycle after the slave select line is
 * activated, and data are captured on the second edge of the serial clock.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description                           
 * :--------------------------------|:------|:---------------------------------------
 *  ALT_SPIS_CTLR0_SCPH_E_INACTLOW  | 0x0   | Inactive state of serial clock is low 
 *  ALT_SPIS_CTLR0_SCPH_E_INACTHIGH | 0x1   | Inactive state of serial clock is high
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_SCPH
 * 
 * Inactive state of serial clock is low
 */
#define ALT_SPIS_CTLR0_SCPH_E_INACTLOW  0x0
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_SCPH
 * 
 * Inactive state of serial clock is high
 */
#define ALT_SPIS_CTLR0_SCPH_E_INACTHIGH 0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_CTLR0_SCPH register field. */
#define ALT_SPIS_CTLR0_SCPH_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_SPIS_CTLR0_SCPH register field. */
#define ALT_SPIS_CTLR0_SCPH_MSB        6
/* The width in bits of the ALT_SPIS_CTLR0_SCPH register field. */
#define ALT_SPIS_CTLR0_SCPH_WIDTH      1
/* The mask used to set the ALT_SPIS_CTLR0_SCPH register field value. */
#define ALT_SPIS_CTLR0_SCPH_SET_MSK    0x00000040
/* The mask used to clear the ALT_SPIS_CTLR0_SCPH register field value. */
#define ALT_SPIS_CTLR0_SCPH_CLR_MSK    0xffffffbf
/* The reset value of the ALT_SPIS_CTLR0_SCPH register field. */
#define ALT_SPIS_CTLR0_SCPH_RESET      0x0
/* Extracts the ALT_SPIS_CTLR0_SCPH field value from a register. */
#define ALT_SPIS_CTLR0_SCPH_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_SPIS_CTLR0_SCPH register field value suitable for setting the register. */
#define ALT_SPIS_CTLR0_SCPH_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Serial Clock Polarity - scpol
 * 
 * Valid when the frame format (FRF) is set to Motorola SPI. Used to select the
 * polarity of the inactive serial clock, which is held inactive when the spi
 * master is not actively transferring data on the serial bus.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description                                     
 * :--------------------------------|:------|:-------------------------------------------------
 *  ALT_SPIS_CTLR0_SCPOL_E_MIDBIT   | 0x0   | Serial clock toggles in middle of first data bit
 *  ALT_SPIS_CTLR0_SCPOL_E_STARTBIT | 0x1   | Serial clock toggles at start of first data bit 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_SCPOL
 * 
 * Serial clock toggles in middle of first data bit
 */
#define ALT_SPIS_CTLR0_SCPOL_E_MIDBIT   0x0
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_SCPOL
 * 
 * Serial clock toggles at start of first data bit
 */
#define ALT_SPIS_CTLR0_SCPOL_E_STARTBIT 0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_CTLR0_SCPOL register field. */
#define ALT_SPIS_CTLR0_SCPOL_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_SPIS_CTLR0_SCPOL register field. */
#define ALT_SPIS_CTLR0_SCPOL_MSB        7
/* The width in bits of the ALT_SPIS_CTLR0_SCPOL register field. */
#define ALT_SPIS_CTLR0_SCPOL_WIDTH      1
/* The mask used to set the ALT_SPIS_CTLR0_SCPOL register field value. */
#define ALT_SPIS_CTLR0_SCPOL_SET_MSK    0x00000080
/* The mask used to clear the ALT_SPIS_CTLR0_SCPOL register field value. */
#define ALT_SPIS_CTLR0_SCPOL_CLR_MSK    0xffffff7f
/* The reset value of the ALT_SPIS_CTLR0_SCPOL register field. */
#define ALT_SPIS_CTLR0_SCPOL_RESET      0x0
/* Extracts the ALT_SPIS_CTLR0_SCPOL field value from a register. */
#define ALT_SPIS_CTLR0_SCPOL_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_SPIS_CTLR0_SCPOL register field value suitable for setting the register. */
#define ALT_SPIS_CTLR0_SCPOL_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Transfer Mode - tmod
 * 
 * Selects the mode of transfer for serial communication. This field does not
 * affect the transfer duplicity. Only indicates whether the receive or transmit
 * data are valid. In transmit-only mode, data received from the external device is
 * not valid and is not stored in the receive FIFO memory; it is overwritten on the
 * next transfer. In receive-only mode, transmitted data are not valid. After the
 * first write to the transmit FIFO, the same word is retransmitted for the
 * duration of the transfer. In transmit-and-receive mode, both transmit and
 * receive data are valid. The transfer continues until the transmit FIFO is empty.
 * Data received from the external device are stored into the receive FIFO memory
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description           
 * :-----------------------------|:------|:-----------------------
 *  ALT_SPIS_CTLR0_TMOD_E_TXRX   | 0x0   | Transmit & and Receive
 *  ALT_SPIS_CTLR0_TMOD_E_TXONLY | 0x1   | Transmit Only         
 *  ALT_SPIS_CTLR0_TMOD_E_RXONLY | 0x2   | Receive Only          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_TMOD
 * 
 * Transmit & and Receive
 */
#define ALT_SPIS_CTLR0_TMOD_E_TXRX      0x0
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_TMOD
 * 
 * Transmit Only
 */
#define ALT_SPIS_CTLR0_TMOD_E_TXONLY    0x1
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_TMOD
 * 
 * Receive Only
 */
#define ALT_SPIS_CTLR0_TMOD_E_RXONLY    0x2

/* The Least Significant Bit (LSB) position of the ALT_SPIS_CTLR0_TMOD register field. */
#define ALT_SPIS_CTLR0_TMOD_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_SPIS_CTLR0_TMOD register field. */
#define ALT_SPIS_CTLR0_TMOD_MSB        9
/* The width in bits of the ALT_SPIS_CTLR0_TMOD register field. */
#define ALT_SPIS_CTLR0_TMOD_WIDTH      2
/* The mask used to set the ALT_SPIS_CTLR0_TMOD register field value. */
#define ALT_SPIS_CTLR0_TMOD_SET_MSK    0x00000300
/* The mask used to clear the ALT_SPIS_CTLR0_TMOD register field value. */
#define ALT_SPIS_CTLR0_TMOD_CLR_MSK    0xfffffcff
/* The reset value of the ALT_SPIS_CTLR0_TMOD register field. */
#define ALT_SPIS_CTLR0_TMOD_RESET      0x0
/* Extracts the ALT_SPIS_CTLR0_TMOD field value from a register. */
#define ALT_SPIS_CTLR0_TMOD_GET(value) (((value) & 0x00000300) >> 8)
/* Produces a ALT_SPIS_CTLR0_TMOD register field value suitable for setting the register. */
#define ALT_SPIS_CTLR0_TMOD_SET(value) (((value) << 8) & 0x00000300)

/*
 * Field : Slave Output Enable - slv_oe
 * 
 * This bit enables or disables the setting of the spis0_ssi_oe_n output from the
 * SPI Slave. When SLV_OE = 1, the spis0_ssi_oe_n output can never be active. When
 * the spis0_ssi_oe_n output controls the tri-state buffer on the txd output from
 * the slave, a high impedance state is always present on the slave spis0_txd
 * output when SLV_OE = 1. This is useful when the master transmits in broadcast
 * mode (master transmits data to all slave devices). Only one slave may respond
 * with data on the master spis0_rxd line. This bit is enabled after reset and must
 * be disabled by software (when broadcast mode is used), if you do not want this
 * device to respond with data.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description          
 * :-----------------------------|:------|:----------------------
 *  ALT_SPIS_CTLR0_SLV_OE_E_END  | 0x0   | Slave txd is enabled 
 *  ALT_SPIS_CTLR0_SLV_OE_E_DISD | 0x1   | Slave txd is disabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_SLV_OE
 * 
 * Slave txd is enabled
 */
#define ALT_SPIS_CTLR0_SLV_OE_E_END     0x0
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_SLV_OE
 * 
 * Slave txd is disabled
 */
#define ALT_SPIS_CTLR0_SLV_OE_E_DISD    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_CTLR0_SLV_OE register field. */
#define ALT_SPIS_CTLR0_SLV_OE_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_SPIS_CTLR0_SLV_OE register field. */
#define ALT_SPIS_CTLR0_SLV_OE_MSB        10
/* The width in bits of the ALT_SPIS_CTLR0_SLV_OE register field. */
#define ALT_SPIS_CTLR0_SLV_OE_WIDTH      1
/* The mask used to set the ALT_SPIS_CTLR0_SLV_OE register field value. */
#define ALT_SPIS_CTLR0_SLV_OE_SET_MSK    0x00000400
/* The mask used to clear the ALT_SPIS_CTLR0_SLV_OE register field value. */
#define ALT_SPIS_CTLR0_SLV_OE_CLR_MSK    0xfffffbff
/* The reset value of the ALT_SPIS_CTLR0_SLV_OE register field. */
#define ALT_SPIS_CTLR0_SLV_OE_RESET      0x0
/* Extracts the ALT_SPIS_CTLR0_SLV_OE field value from a register. */
#define ALT_SPIS_CTLR0_SLV_OE_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_SPIS_CTLR0_SLV_OE register field value suitable for setting the register. */
#define ALT_SPIS_CTLR0_SLV_OE_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Shift Register Loop - srl
 * 
 * Used for testing purposes only. When internally active, connects the transmit
 * shift register output to the receive shift register input.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description          
 * :-----------------------------|:------|:----------------------
 *  ALT_SPIS_CTLR0_SRL_E_NORMMOD | 0x0   | Normal Mode Operation
 *  ALT_SPIS_CTLR0_SRL_E_TESTMOD | 0x1   | Test Mode Operation  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_SRL
 * 
 * Normal Mode Operation
 */
#define ALT_SPIS_CTLR0_SRL_E_NORMMOD    0x0
/*
 * Enumerated value for register field ALT_SPIS_CTLR0_SRL
 * 
 * Test Mode Operation
 */
#define ALT_SPIS_CTLR0_SRL_E_TESTMOD    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_CTLR0_SRL register field. */
#define ALT_SPIS_CTLR0_SRL_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_SPIS_CTLR0_SRL register field. */
#define ALT_SPIS_CTLR0_SRL_MSB        11
/* The width in bits of the ALT_SPIS_CTLR0_SRL register field. */
#define ALT_SPIS_CTLR0_SRL_WIDTH      1
/* The mask used to set the ALT_SPIS_CTLR0_SRL register field value. */
#define ALT_SPIS_CTLR0_SRL_SET_MSK    0x00000800
/* The mask used to clear the ALT_SPIS_CTLR0_SRL register field value. */
#define ALT_SPIS_CTLR0_SRL_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_SPIS_CTLR0_SRL register field. */
#define ALT_SPIS_CTLR0_SRL_RESET      0x0
/* Extracts the ALT_SPIS_CTLR0_SRL field value from a register. */
#define ALT_SPIS_CTLR0_SRL_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_SPIS_CTLR0_SRL register field value suitable for setting the register. */
#define ALT_SPIS_CTLR0_SRL_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : Control Frame Size - cfs
 * 
 * Selects the length of the control word for the Microwire frame format. The
 * length (in bits) is the value of this field plus 1.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIS_CTLR0_CFS register field. */
#define ALT_SPIS_CTLR0_CFS_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_SPIS_CTLR0_CFS register field. */
#define ALT_SPIS_CTLR0_CFS_MSB        15
/* The width in bits of the ALT_SPIS_CTLR0_CFS register field. */
#define ALT_SPIS_CTLR0_CFS_WIDTH      4
/* The mask used to set the ALT_SPIS_CTLR0_CFS register field value. */
#define ALT_SPIS_CTLR0_CFS_SET_MSK    0x0000f000
/* The mask used to clear the ALT_SPIS_CTLR0_CFS register field value. */
#define ALT_SPIS_CTLR0_CFS_CLR_MSK    0xffff0fff
/* The reset value of the ALT_SPIS_CTLR0_CFS register field. */
#define ALT_SPIS_CTLR0_CFS_RESET      0x0
/* Extracts the ALT_SPIS_CTLR0_CFS field value from a register. */
#define ALT_SPIS_CTLR0_CFS_GET(value) (((value) & 0x0000f000) >> 12)
/* Produces a ALT_SPIS_CTLR0_CFS register field value suitable for setting the register. */
#define ALT_SPIS_CTLR0_CFS_SET(value) (((value) << 12) & 0x0000f000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_CTLR0.
 */
struct ALT_SPIS_CTLR0_s
{
    uint32_t  dfs    :  4;  /* Data Frame Size */
    uint32_t  frf    :  2;  /* Frame Format */
    uint32_t  scph   :  1;  /* Serial Clock Phase */
    uint32_t  scpol  :  1;  /* Serial Clock Polarity */
    uint32_t  tmod   :  2;  /* Transfer Mode */
    uint32_t  slv_oe :  1;  /* Slave Output Enable */
    uint32_t  srl    :  1;  /* Shift Register Loop */
    uint32_t  cfs    :  4;  /* Control Frame Size */
    uint32_t         : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_CTLR0. */
typedef volatile struct ALT_SPIS_CTLR0_s  ALT_SPIS_CTLR0_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_CTLR0 register from the beginning of the component. */
#define ALT_SPIS_CTLR0_OFST        0x0
/* The address of the ALT_SPIS_CTLR0 register. */
#define ALT_SPIS_CTLR0_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_CTLR0_OFST))

/*
 * Register : Enable Register - spienr
 * 
 * Enables and disables all SPI operations.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [0]    | RW     | 0x0   | Enable     
 *  [31:1] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Enable - spi_en
 * 
 * When disabled, all serial transfers are halted immediately. Transmit and receive
 * FIFO buffers are cleared when the device is disabled. It is impossible to
 * program some of the SPI Slave control registers when enabled.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                        
 * :------------------------------|:------|:------------------------------------
 *  ALT_SPIS_SPIENR_SPI_EN_E_DISD | 0x0   | Disables serial transfer operations
 *  ALT_SPIS_SPIENR_SPI_EN_E_END  | 0x1   | Enables serial transfer operations 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_SPIENR_SPI_EN
 * 
 * Disables serial transfer operations
 */
#define ALT_SPIS_SPIENR_SPI_EN_E_DISD   0x0
/*
 * Enumerated value for register field ALT_SPIS_SPIENR_SPI_EN
 * 
 * Enables serial transfer operations
 */
#define ALT_SPIS_SPIENR_SPI_EN_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_SPIENR_SPI_EN register field. */
#define ALT_SPIS_SPIENR_SPI_EN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_SPIENR_SPI_EN register field. */
#define ALT_SPIS_SPIENR_SPI_EN_MSB        0
/* The width in bits of the ALT_SPIS_SPIENR_SPI_EN register field. */
#define ALT_SPIS_SPIENR_SPI_EN_WIDTH      1
/* The mask used to set the ALT_SPIS_SPIENR_SPI_EN register field value. */
#define ALT_SPIS_SPIENR_SPI_EN_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIS_SPIENR_SPI_EN register field value. */
#define ALT_SPIS_SPIENR_SPI_EN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIS_SPIENR_SPI_EN register field. */
#define ALT_SPIS_SPIENR_SPI_EN_RESET      0x0
/* Extracts the ALT_SPIS_SPIENR_SPI_EN field value from a register. */
#define ALT_SPIS_SPIENR_SPI_EN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIS_SPIENR_SPI_EN register field value suitable for setting the register. */
#define ALT_SPIS_SPIENR_SPI_EN_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_SPIENR.
 */
struct ALT_SPIS_SPIENR_s
{
    uint32_t  spi_en :  1;  /* Enable */
    uint32_t         : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_SPIENR. */
typedef volatile struct ALT_SPIS_SPIENR_s  ALT_SPIS_SPIENR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_SPIENR register from the beginning of the component. */
#define ALT_SPIS_SPIENR_OFST        0x8
/* The address of the ALT_SPIS_SPIENR register. */
#define ALT_SPIS_SPIENR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_SPIENR_OFST))

/*
 * Register : Microwire Control Register - mwcr
 * 
 * This register controls the direction of the data word for the half-duplex
 * Microwire serial protocol. It is impossible to write to this register when the
 * SPI Slave is enabled. The SPI Slave is enabled and disabled by writing to the
 * SPIENR register.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description            
 * :-------|:-------|:------|:------------------------
 *  [0]    | RW     | 0x0   | Microwire Transfer Mode
 *  [1]    | RW     | 0x0   | Microwire Control      
 *  [31:2] | ???    | 0x0   | *UNDEFINED*            
 * 
 */
/*
 * Field : Microwire Transfer Mode - mwmod
 * 
 * Defines whether the Microwire transfer is sequential or non-sequential. When
 * sequential mode is used, only one control word is needed to transmit or receive
 * a block of data words. When non-sequential mode is used, there must be a control
 * word for each data word that is transmitted or received.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description            
 * :-----------------------------|:------|:------------------------
 *  ALT_SPIS_MWCR_MWMOD_E_NONSEQ | 0x0   | non-sequential transfer
 *  ALT_SPIS_MWCR_MWMOD_E_SEQ    | 0x1   | sequential transfer    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_MWCR_MWMOD
 * 
 * non-sequential transfer
 */
#define ALT_SPIS_MWCR_MWMOD_E_NONSEQ    0x0
/*
 * Enumerated value for register field ALT_SPIS_MWCR_MWMOD
 * 
 * sequential transfer
 */
#define ALT_SPIS_MWCR_MWMOD_E_SEQ       0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_MWCR_MWMOD register field. */
#define ALT_SPIS_MWCR_MWMOD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_MWCR_MWMOD register field. */
#define ALT_SPIS_MWCR_MWMOD_MSB        0
/* The width in bits of the ALT_SPIS_MWCR_MWMOD register field. */
#define ALT_SPIS_MWCR_MWMOD_WIDTH      1
/* The mask used to set the ALT_SPIS_MWCR_MWMOD register field value. */
#define ALT_SPIS_MWCR_MWMOD_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIS_MWCR_MWMOD register field value. */
#define ALT_SPIS_MWCR_MWMOD_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIS_MWCR_MWMOD register field. */
#define ALT_SPIS_MWCR_MWMOD_RESET      0x0
/* Extracts the ALT_SPIS_MWCR_MWMOD field value from a register. */
#define ALT_SPIS_MWCR_MWMOD_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIS_MWCR_MWMOD register field value suitable for setting the register. */
#define ALT_SPIS_MWCR_MWMOD_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Microwire Control - mdd
 * 
 * Defines the direction of the data word when the Microwire serial protocol is
 * used.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description             
 * :--------------------------|:------|:-------------------------
 *  ALT_SPIS_MWCR_MDD_E_RXMOD | 0x0   | SPI Slave receives data 
 *  ALT_SPIS_MWCR_MDD_E_TXMOD | 0x1   | SPI Slave transmits data
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_MWCR_MDD
 * 
 * SPI Slave receives data
 */
#define ALT_SPIS_MWCR_MDD_E_RXMOD   0x0
/*
 * Enumerated value for register field ALT_SPIS_MWCR_MDD
 * 
 * SPI Slave transmits data
 */
#define ALT_SPIS_MWCR_MDD_E_TXMOD   0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_MWCR_MDD register field. */
#define ALT_SPIS_MWCR_MDD_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SPIS_MWCR_MDD register field. */
#define ALT_SPIS_MWCR_MDD_MSB        1
/* The width in bits of the ALT_SPIS_MWCR_MDD register field. */
#define ALT_SPIS_MWCR_MDD_WIDTH      1
/* The mask used to set the ALT_SPIS_MWCR_MDD register field value. */
#define ALT_SPIS_MWCR_MDD_SET_MSK    0x00000002
/* The mask used to clear the ALT_SPIS_MWCR_MDD register field value. */
#define ALT_SPIS_MWCR_MDD_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SPIS_MWCR_MDD register field. */
#define ALT_SPIS_MWCR_MDD_RESET      0x0
/* Extracts the ALT_SPIS_MWCR_MDD field value from a register. */
#define ALT_SPIS_MWCR_MDD_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SPIS_MWCR_MDD register field value suitable for setting the register. */
#define ALT_SPIS_MWCR_MDD_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_MWCR.
 */
struct ALT_SPIS_MWCR_s
{
    uint32_t  mwmod :  1;  /* Microwire Transfer Mode */
    uint32_t  mdd   :  1;  /* Microwire Control */
    uint32_t        : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_MWCR. */
typedef volatile struct ALT_SPIS_MWCR_s  ALT_SPIS_MWCR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_MWCR register from the beginning of the component. */
#define ALT_SPIS_MWCR_OFST        0xc
/* The address of the ALT_SPIS_MWCR register. */
#define ALT_SPIS_MWCR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_MWCR_OFST))

/*
 * Register : Transmit FIFO Threshold Level Register - txftlr
 * 
 * This register controls the threshold value for the transmit FIFO memory. It is
 * impossible to write to this register when the SPI Slave is enabled. The SPI
 * Slave is enabled and disabled by writing to the SPIENR register.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description            
 * :-------|:-------|:------|:------------------------
 *  [7:0]  | RW     | 0x0   | Transmit FIFO Threshold
 *  [31:8] | ???    | 0x0   | *UNDEFINED*            
 * 
 */
/*
 * Field : Transmit FIFO Threshold - tft
 * 
 * Controls the level of entries (or below) at which the transmit FIFO controller
 * triggers an interrupt. When the number of transmit FIFO entries is less than or
 * equal to this value, the transmit FIFO empty interrupt is triggered.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIS_TXFTLR_TFT register field. */
#define ALT_SPIS_TXFTLR_TFT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_TXFTLR_TFT register field. */
#define ALT_SPIS_TXFTLR_TFT_MSB        7
/* The width in bits of the ALT_SPIS_TXFTLR_TFT register field. */
#define ALT_SPIS_TXFTLR_TFT_WIDTH      8
/* The mask used to set the ALT_SPIS_TXFTLR_TFT register field value. */
#define ALT_SPIS_TXFTLR_TFT_SET_MSK    0x000000ff
/* The mask used to clear the ALT_SPIS_TXFTLR_TFT register field value. */
#define ALT_SPIS_TXFTLR_TFT_CLR_MSK    0xffffff00
/* The reset value of the ALT_SPIS_TXFTLR_TFT register field. */
#define ALT_SPIS_TXFTLR_TFT_RESET      0x0
/* Extracts the ALT_SPIS_TXFTLR_TFT field value from a register. */
#define ALT_SPIS_TXFTLR_TFT_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_SPIS_TXFTLR_TFT register field value suitable for setting the register. */
#define ALT_SPIS_TXFTLR_TFT_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_TXFTLR.
 */
struct ALT_SPIS_TXFTLR_s
{
    uint32_t  tft :  8;  /* Transmit FIFO Threshold */
    uint32_t      : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_TXFTLR. */
typedef volatile struct ALT_SPIS_TXFTLR_s  ALT_SPIS_TXFTLR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_TXFTLR register from the beginning of the component. */
#define ALT_SPIS_TXFTLR_OFST        0x18
/* The address of the ALT_SPIS_TXFTLR register. */
#define ALT_SPIS_TXFTLR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_TXFTLR_OFST))

/*
 * Register : Receive FIFO Threshold Level Register - rxftlr
 * 
 * This register controls the threshold value for the receive FIFO memory. It is
 * impossible to write to this register when the SPI Slave is enabled. The SPI
 * Slave is enabled and disabled by writing to the SPIENR register.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description           
 * :-------|:-------|:------|:-----------------------
 *  [7:0]  | RW     | 0x0   | Receive FIFO Threshold
 *  [31:8] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : Receive FIFO Threshold - rft
 * 
 * Controls the level of entries (or above) at which the receive FIFO controller
 * triggers an interrupt. When the number of receive FIFO entries is greater than
 * or equal to this value + 1, the receive FIFO full interrupt is triggered.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIS_RXFTLR_RFT register field. */
#define ALT_SPIS_RXFTLR_RFT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_RXFTLR_RFT register field. */
#define ALT_SPIS_RXFTLR_RFT_MSB        7
/* The width in bits of the ALT_SPIS_RXFTLR_RFT register field. */
#define ALT_SPIS_RXFTLR_RFT_WIDTH      8
/* The mask used to set the ALT_SPIS_RXFTLR_RFT register field value. */
#define ALT_SPIS_RXFTLR_RFT_SET_MSK    0x000000ff
/* The mask used to clear the ALT_SPIS_RXFTLR_RFT register field value. */
#define ALT_SPIS_RXFTLR_RFT_CLR_MSK    0xffffff00
/* The reset value of the ALT_SPIS_RXFTLR_RFT register field. */
#define ALT_SPIS_RXFTLR_RFT_RESET      0x0
/* Extracts the ALT_SPIS_RXFTLR_RFT field value from a register. */
#define ALT_SPIS_RXFTLR_RFT_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_SPIS_RXFTLR_RFT register field value suitable for setting the register. */
#define ALT_SPIS_RXFTLR_RFT_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_RXFTLR.
 */
struct ALT_SPIS_RXFTLR_s
{
    uint32_t  rft :  8;  /* Receive FIFO Threshold */
    uint32_t      : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_RXFTLR. */
typedef volatile struct ALT_SPIS_RXFTLR_s  ALT_SPIS_RXFTLR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_RXFTLR register from the beginning of the component. */
#define ALT_SPIS_RXFTLR_OFST        0x1c
/* The address of the ALT_SPIS_RXFTLR register. */
#define ALT_SPIS_RXFTLR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_RXFTLR_OFST))

/*
 * Register : Transmit FIFO Level Register - txflr
 * 
 * This register contains the number of valid data entries in the transmit FIFO
 * memory. Ranges from 0 to 256.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description        
 * :-------|:-------|:------|:--------------------
 *  [8:0]  | R      | 0x0   | Transmit FIFO Level
 *  [31:9] | ???    | 0x0   | *UNDEFINED*        
 * 
 */
/*
 * Field : Transmit FIFO Level - txtfl
 * 
 * Contains the number of valid data entries in the transmit FIFO.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIS_TXFLR_TXTFL register field. */
#define ALT_SPIS_TXFLR_TXTFL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_TXFLR_TXTFL register field. */
#define ALT_SPIS_TXFLR_TXTFL_MSB        8
/* The width in bits of the ALT_SPIS_TXFLR_TXTFL register field. */
#define ALT_SPIS_TXFLR_TXTFL_WIDTH      9
/* The mask used to set the ALT_SPIS_TXFLR_TXTFL register field value. */
#define ALT_SPIS_TXFLR_TXTFL_SET_MSK    0x000001ff
/* The mask used to clear the ALT_SPIS_TXFLR_TXTFL register field value. */
#define ALT_SPIS_TXFLR_TXTFL_CLR_MSK    0xfffffe00
/* The reset value of the ALT_SPIS_TXFLR_TXTFL register field. */
#define ALT_SPIS_TXFLR_TXTFL_RESET      0x0
/* Extracts the ALT_SPIS_TXFLR_TXTFL field value from a register. */
#define ALT_SPIS_TXFLR_TXTFL_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_SPIS_TXFLR_TXTFL register field value suitable for setting the register. */
#define ALT_SPIS_TXFLR_TXTFL_SET(value) (((value) << 0) & 0x000001ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_TXFLR.
 */
struct ALT_SPIS_TXFLR_s
{
    const uint32_t  txtfl :  9;  /* Transmit FIFO Level */
    uint32_t              : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_TXFLR. */
typedef volatile struct ALT_SPIS_TXFLR_s  ALT_SPIS_TXFLR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_TXFLR register from the beginning of the component. */
#define ALT_SPIS_TXFLR_OFST        0x20
/* The address of the ALT_SPIS_TXFLR register. */
#define ALT_SPIS_TXFLR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_TXFLR_OFST))

/*
 * Register : Receive FIFO Level Register - rxflr
 * 
 * This register contains the number of valid data entriesin the receive FIFO
 * memory. This register can be read at any time. Ranges from 0 to 256.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description       
 * :-------|:-------|:------|:-------------------
 *  [8:0]  | R      | 0x0   | Receive FIFO Level
 *  [31:9] | ???    | 0x0   | *UNDEFINED*       
 * 
 */
/*
 * Field : Receive FIFO Level - rxtfl
 * 
 * Contains the number of valid data entries in the receive FIFO.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIS_RXFLR_RXTFL register field. */
#define ALT_SPIS_RXFLR_RXTFL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_RXFLR_RXTFL register field. */
#define ALT_SPIS_RXFLR_RXTFL_MSB        8
/* The width in bits of the ALT_SPIS_RXFLR_RXTFL register field. */
#define ALT_SPIS_RXFLR_RXTFL_WIDTH      9
/* The mask used to set the ALT_SPIS_RXFLR_RXTFL register field value. */
#define ALT_SPIS_RXFLR_RXTFL_SET_MSK    0x000001ff
/* The mask used to clear the ALT_SPIS_RXFLR_RXTFL register field value. */
#define ALT_SPIS_RXFLR_RXTFL_CLR_MSK    0xfffffe00
/* The reset value of the ALT_SPIS_RXFLR_RXTFL register field. */
#define ALT_SPIS_RXFLR_RXTFL_RESET      0x0
/* Extracts the ALT_SPIS_RXFLR_RXTFL field value from a register. */
#define ALT_SPIS_RXFLR_RXTFL_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_SPIS_RXFLR_RXTFL register field value suitable for setting the register. */
#define ALT_SPIS_RXFLR_RXTFL_SET(value) (((value) << 0) & 0x000001ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_RXFLR.
 */
struct ALT_SPIS_RXFLR_s
{
    const uint32_t  rxtfl :  9;  /* Receive FIFO Level */
    uint32_t              : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_RXFLR. */
typedef volatile struct ALT_SPIS_RXFLR_s  ALT_SPIS_RXFLR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_RXFLR register from the beginning of the component. */
#define ALT_SPIS_RXFLR_OFST        0x24
/* The address of the ALT_SPIS_RXFLR register. */
#define ALT_SPIS_RXFLR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_RXFLR_OFST))

/*
 * Register : Status Register - sr
 * 
 * Reports FIFO transfer status, and any transmission/reception errors that may
 * have occurred. The status register may be read at any time. None of the bits in
 * this register request an interrupt.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description           
 * :-------|:-------|:------|:-----------------------
 *  [0]    | R      | 0x0   | SPI Busy Flag         
 *  [1]    | R      | 0x1   | Transmit FIFO Not Full
 *  [2]    | R      | 0x1   | Transmit FIFO Empty   
 *  [3]    | R      | 0x0   | Receive FIFO Not Empty
 *  [4]    | R      | 0x0   | Receive FIFO Full     
 *  [5]    | R      | 0x0   | Transmission Error    
 *  [31:6] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : SPI Busy Flag - busy
 * 
 * Reports the status of a serial transfer
 * 
 * Field Enumeration Values:
 * 
 *  Enum                     | Value | Description                             
 * :-------------------------|:------|:-----------------------------------------
 *  ALT_SPIS_SR_BUSY_E_INACT | 0x0   | SPI Slave is inactive (idle or disabled)
 *  ALT_SPIS_SR_BUSY_E_ACT   | 0x1   | SPI Slave is actively transferring data 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_SR_BUSY
 * 
 * SPI Slave is inactive (idle or disabled)
 */
#define ALT_SPIS_SR_BUSY_E_INACT    0x0
/*
 * Enumerated value for register field ALT_SPIS_SR_BUSY
 * 
 * SPI Slave is actively transferring data
 */
#define ALT_SPIS_SR_BUSY_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_SR_BUSY register field. */
#define ALT_SPIS_SR_BUSY_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_SR_BUSY register field. */
#define ALT_SPIS_SR_BUSY_MSB        0
/* The width in bits of the ALT_SPIS_SR_BUSY register field. */
#define ALT_SPIS_SR_BUSY_WIDTH      1
/* The mask used to set the ALT_SPIS_SR_BUSY register field value. */
#define ALT_SPIS_SR_BUSY_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIS_SR_BUSY register field value. */
#define ALT_SPIS_SR_BUSY_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIS_SR_BUSY register field. */
#define ALT_SPIS_SR_BUSY_RESET      0x0
/* Extracts the ALT_SPIS_SR_BUSY field value from a register. */
#define ALT_SPIS_SR_BUSY_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIS_SR_BUSY register field value suitable for setting the register. */
#define ALT_SPIS_SR_BUSY_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Transmit FIFO Not Full - tfnf
 * 
 * Reports the status of the transmit FIFO.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description              
 * :---------------------------|:------|:--------------------------
 *  ALT_SPIS_SR_TFNF_E_FULL    | 0x0   | Transmit FIFO is full    
 *  ALT_SPIS_SR_TFNF_E_NOTFULL | 0x1   | Transmit FIFO is not full
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_SR_TFNF
 * 
 * Transmit FIFO is full
 */
#define ALT_SPIS_SR_TFNF_E_FULL     0x0
/*
 * Enumerated value for register field ALT_SPIS_SR_TFNF
 * 
 * Transmit FIFO is not full
 */
#define ALT_SPIS_SR_TFNF_E_NOTFULL  0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_SR_TFNF register field. */
#define ALT_SPIS_SR_TFNF_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SPIS_SR_TFNF register field. */
#define ALT_SPIS_SR_TFNF_MSB        1
/* The width in bits of the ALT_SPIS_SR_TFNF register field. */
#define ALT_SPIS_SR_TFNF_WIDTH      1
/* The mask used to set the ALT_SPIS_SR_TFNF register field value. */
#define ALT_SPIS_SR_TFNF_SET_MSK    0x00000002
/* The mask used to clear the ALT_SPIS_SR_TFNF register field value. */
#define ALT_SPIS_SR_TFNF_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SPIS_SR_TFNF register field. */
#define ALT_SPIS_SR_TFNF_RESET      0x1
/* Extracts the ALT_SPIS_SR_TFNF field value from a register. */
#define ALT_SPIS_SR_TFNF_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SPIS_SR_TFNF register field value suitable for setting the register. */
#define ALT_SPIS_SR_TFNF_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Transmit FIFO Empty - tfe
 * 
 * Reports the status of transmit FIFO empty. This bit field does not request an
 * interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description               
 * :---------------------------|:------|:---------------------------
 *  ALT_SPIS_SR_TFE_E_EMPTY    | 0x1   | Transmit FIFO is empty    
 *  ALT_SPIS_SR_TFE_E_NOTEMPTY | 0x0   | Transmit FIFO is not empty
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_SR_TFE
 * 
 * Transmit FIFO is empty
 */
#define ALT_SPIS_SR_TFE_E_EMPTY     0x1
/*
 * Enumerated value for register field ALT_SPIS_SR_TFE
 * 
 * Transmit FIFO is not empty
 */
#define ALT_SPIS_SR_TFE_E_NOTEMPTY  0x0

/* The Least Significant Bit (LSB) position of the ALT_SPIS_SR_TFE register field. */
#define ALT_SPIS_SR_TFE_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SPIS_SR_TFE register field. */
#define ALT_SPIS_SR_TFE_MSB        2
/* The width in bits of the ALT_SPIS_SR_TFE register field. */
#define ALT_SPIS_SR_TFE_WIDTH      1
/* The mask used to set the ALT_SPIS_SR_TFE register field value. */
#define ALT_SPIS_SR_TFE_SET_MSK    0x00000004
/* The mask used to clear the ALT_SPIS_SR_TFE register field value. */
#define ALT_SPIS_SR_TFE_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SPIS_SR_TFE register field. */
#define ALT_SPIS_SR_TFE_RESET      0x1
/* Extracts the ALT_SPIS_SR_TFE field value from a register. */
#define ALT_SPIS_SR_TFE_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SPIS_SR_TFE register field value suitable for setting the register. */
#define ALT_SPIS_SR_TFE_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Receive FIFO Not Empty - rfne
 * 
 * Reports the status of receive FIFO empty.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description              
 * :----------------------------|:------|:--------------------------
 *  ALT_SPIS_SR_RFNE_E_EMPTY    | 0x0   | Receive FIFO is empty    
 *  ALT_SPIS_SR_RFNE_E_NOTEMPTY | 0x1   | Receive FIFO is not empty
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_SR_RFNE
 * 
 * Receive FIFO is empty
 */
#define ALT_SPIS_SR_RFNE_E_EMPTY    0x0
/*
 * Enumerated value for register field ALT_SPIS_SR_RFNE
 * 
 * Receive FIFO is not empty
 */
#define ALT_SPIS_SR_RFNE_E_NOTEMPTY 0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_SR_RFNE register field. */
#define ALT_SPIS_SR_RFNE_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SPIS_SR_RFNE register field. */
#define ALT_SPIS_SR_RFNE_MSB        3
/* The width in bits of the ALT_SPIS_SR_RFNE register field. */
#define ALT_SPIS_SR_RFNE_WIDTH      1
/* The mask used to set the ALT_SPIS_SR_RFNE register field value. */
#define ALT_SPIS_SR_RFNE_SET_MSK    0x00000008
/* The mask used to clear the ALT_SPIS_SR_RFNE register field value. */
#define ALT_SPIS_SR_RFNE_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SPIS_SR_RFNE register field. */
#define ALT_SPIS_SR_RFNE_RESET      0x0
/* Extracts the ALT_SPIS_SR_RFNE field value from a register. */
#define ALT_SPIS_SR_RFNE_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SPIS_SR_RFNE register field value suitable for setting the register. */
#define ALT_SPIS_SR_RFNE_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Receive FIFO Full - rff
 * 
 * Reports the status of receive FIFO Full
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description             
 * :--------------------------|:------|:-------------------------
 *  ALT_SPIS_SR_RFF_E_NOTFULL | 0x0   | Receive FIFO is not full
 *  ALT_SPIS_SR_RFF_E_FULL    | 0x1   | Receive FIFO is full    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_SR_RFF
 * 
 * Receive FIFO is not full
 */
#define ALT_SPIS_SR_RFF_E_NOTFULL   0x0
/*
 * Enumerated value for register field ALT_SPIS_SR_RFF
 * 
 * Receive FIFO is full
 */
#define ALT_SPIS_SR_RFF_E_FULL      0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_SR_RFF register field. */
#define ALT_SPIS_SR_RFF_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SPIS_SR_RFF register field. */
#define ALT_SPIS_SR_RFF_MSB        4
/* The width in bits of the ALT_SPIS_SR_RFF register field. */
#define ALT_SPIS_SR_RFF_WIDTH      1
/* The mask used to set the ALT_SPIS_SR_RFF register field value. */
#define ALT_SPIS_SR_RFF_SET_MSK    0x00000010
/* The mask used to clear the ALT_SPIS_SR_RFF register field value. */
#define ALT_SPIS_SR_RFF_CLR_MSK    0xffffffef
/* The reset value of the ALT_SPIS_SR_RFF register field. */
#define ALT_SPIS_SR_RFF_RESET      0x0
/* Extracts the ALT_SPIS_SR_RFF field value from a register. */
#define ALT_SPIS_SR_RFF_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_SPIS_SR_RFF register field value suitable for setting the register. */
#define ALT_SPIS_SR_RFF_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Transmission Error - txe
 * 
 * Data from the previous transmission is resent on the txd line. This bit is
 * cleared when read.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description       
 * :--------------------------|:------|:-------------------
 *  ALT_SPIS_SR_TXE_E_NOERROR | 0x0   | No Error          
 *  ALT_SPIS_SR_TXE_E_ERROR   | 0x1   | Transmission Error
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_SR_TXE
 * 
 * No Error
 */
#define ALT_SPIS_SR_TXE_E_NOERROR   0x0
/*
 * Enumerated value for register field ALT_SPIS_SR_TXE
 * 
 * Transmission Error
 */
#define ALT_SPIS_SR_TXE_E_ERROR     0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_SR_TXE register field. */
#define ALT_SPIS_SR_TXE_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_SPIS_SR_TXE register field. */
#define ALT_SPIS_SR_TXE_MSB        5
/* The width in bits of the ALT_SPIS_SR_TXE register field. */
#define ALT_SPIS_SR_TXE_WIDTH      1
/* The mask used to set the ALT_SPIS_SR_TXE register field value. */
#define ALT_SPIS_SR_TXE_SET_MSK    0x00000020
/* The mask used to clear the ALT_SPIS_SR_TXE register field value. */
#define ALT_SPIS_SR_TXE_CLR_MSK    0xffffffdf
/* The reset value of the ALT_SPIS_SR_TXE register field. */
#define ALT_SPIS_SR_TXE_RESET      0x0
/* Extracts the ALT_SPIS_SR_TXE field value from a register. */
#define ALT_SPIS_SR_TXE_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_SPIS_SR_TXE register field value suitable for setting the register. */
#define ALT_SPIS_SR_TXE_SET(value) (((value) << 5) & 0x00000020)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_SR.
 */
struct ALT_SPIS_SR_s
{
    const uint32_t  busy :  1;  /* SPI Busy Flag */
    const uint32_t  tfnf :  1;  /* Transmit FIFO Not Full */
    const uint32_t  tfe  :  1;  /* Transmit FIFO Empty */
    const uint32_t  rfne :  1;  /* Receive FIFO Not Empty */
    const uint32_t  rff  :  1;  /* Receive FIFO Full */
    const uint32_t  txe  :  1;  /* Transmission Error */
    uint32_t             : 26;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_SR. */
typedef volatile struct ALT_SPIS_SR_s  ALT_SPIS_SR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_SR register from the beginning of the component. */
#define ALT_SPIS_SR_OFST        0x28
/* The address of the ALT_SPIS_SR register. */
#define ALT_SPIS_SR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_SR_OFST))

/*
 * Register : Interrupt Mask Register - imr
 * 
 * This register masks or enables all interrupts generated by the SPI Slave.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                          
 * :-------|:-------|:------|:--------------------------------------
 *  [0]    | RW     | 0x1   | Transmit FIFO Empty Interrupt Mask   
 *  [1]    | RW     | 0x1   | Transmit FIFO Overflow Interrupt Mask
 *  [2]    | RW     | 0x1   | Receive FIFO Underflow Interrupt Mask
 *  [3]    | RW     | 0x1   | Receive FIFO Overflow Interrupt Mask 
 *  [4]    | RW     | 0x1   | Receive FIFO Full Interrupt Mask     
 *  [31:5] | ???    | 0x0   | *UNDEFINED*                          
 * 
 */
/*
 * Field : Transmit FIFO Empty Interrupt Mask - txeim
 * 
 * Empty mask.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                
 * :---------------------------|:------|:--------------------------------------------
 *  ALT_SPIS_IMR_TXEIM_E_MSKED | 0x0   | spi_txe_intr interrupt is masked (disabled)
 *  ALT_SPIS_IMR_TXEIM_E_END   | 0x1   | spi_txe_intr interrupt is enabled          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_IMR_TXEIM
 * 
 * spi_txe_intr interrupt is masked (disabled)
 */
#define ALT_SPIS_IMR_TXEIM_E_MSKED  0x0
/*
 * Enumerated value for register field ALT_SPIS_IMR_TXEIM
 * 
 * spi_txe_intr interrupt is enabled
 */
#define ALT_SPIS_IMR_TXEIM_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_IMR_TXEIM register field. */
#define ALT_SPIS_IMR_TXEIM_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_IMR_TXEIM register field. */
#define ALT_SPIS_IMR_TXEIM_MSB        0
/* The width in bits of the ALT_SPIS_IMR_TXEIM register field. */
#define ALT_SPIS_IMR_TXEIM_WIDTH      1
/* The mask used to set the ALT_SPIS_IMR_TXEIM register field value. */
#define ALT_SPIS_IMR_TXEIM_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIS_IMR_TXEIM register field value. */
#define ALT_SPIS_IMR_TXEIM_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIS_IMR_TXEIM register field. */
#define ALT_SPIS_IMR_TXEIM_RESET      0x1
/* Extracts the ALT_SPIS_IMR_TXEIM field value from a register. */
#define ALT_SPIS_IMR_TXEIM_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIS_IMR_TXEIM register field value suitable for setting the register. */
#define ALT_SPIS_IMR_TXEIM_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Transmit FIFO Overflow Interrupt Mask - txoim
 * 
 * Overflow mask.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                
 * :---------------------------|:------|:--------------------------------------------
 *  ALT_SPIS_IMR_TXOIM_E_MSKED | 0x0   | spi_txo_intr interrupt is masked (disabled)
 *  ALT_SPIS_IMR_TXOIM_E_END   | 0x1   | spi_txo_intr interrupt is enabled          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_IMR_TXOIM
 * 
 * spi_txo_intr interrupt is masked (disabled)
 */
#define ALT_SPIS_IMR_TXOIM_E_MSKED  0x0
/*
 * Enumerated value for register field ALT_SPIS_IMR_TXOIM
 * 
 * spi_txo_intr interrupt is enabled
 */
#define ALT_SPIS_IMR_TXOIM_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_IMR_TXOIM register field. */
#define ALT_SPIS_IMR_TXOIM_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SPIS_IMR_TXOIM register field. */
#define ALT_SPIS_IMR_TXOIM_MSB        1
/* The width in bits of the ALT_SPIS_IMR_TXOIM register field. */
#define ALT_SPIS_IMR_TXOIM_WIDTH      1
/* The mask used to set the ALT_SPIS_IMR_TXOIM register field value. */
#define ALT_SPIS_IMR_TXOIM_SET_MSK    0x00000002
/* The mask used to clear the ALT_SPIS_IMR_TXOIM register field value. */
#define ALT_SPIS_IMR_TXOIM_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SPIS_IMR_TXOIM register field. */
#define ALT_SPIS_IMR_TXOIM_RESET      0x1
/* Extracts the ALT_SPIS_IMR_TXOIM field value from a register. */
#define ALT_SPIS_IMR_TXOIM_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SPIS_IMR_TXOIM register field value suitable for setting the register. */
#define ALT_SPIS_IMR_TXOIM_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Receive FIFO Underflow Interrupt Mask - rxuim
 * 
 * Underfow Mask
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                
 * :---------------------------|:------|:--------------------------------------------
 *  ALT_SPIS_IMR_RXUIM_E_MSKED | 0x0   | spi_rxu_intr interrupt is masked (disabled)
 *  ALT_SPIS_IMR_RXUIM_E_END   | 0x1   | spi_rxu_intr interrupt is enabled          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_IMR_RXUIM
 * 
 * spi_rxu_intr interrupt is masked (disabled)
 */
#define ALT_SPIS_IMR_RXUIM_E_MSKED  0x0
/*
 * Enumerated value for register field ALT_SPIS_IMR_RXUIM
 * 
 * spi_rxu_intr interrupt is enabled
 */
#define ALT_SPIS_IMR_RXUIM_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_IMR_RXUIM register field. */
#define ALT_SPIS_IMR_RXUIM_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SPIS_IMR_RXUIM register field. */
#define ALT_SPIS_IMR_RXUIM_MSB        2
/* The width in bits of the ALT_SPIS_IMR_RXUIM register field. */
#define ALT_SPIS_IMR_RXUIM_WIDTH      1
/* The mask used to set the ALT_SPIS_IMR_RXUIM register field value. */
#define ALT_SPIS_IMR_RXUIM_SET_MSK    0x00000004
/* The mask used to clear the ALT_SPIS_IMR_RXUIM register field value. */
#define ALT_SPIS_IMR_RXUIM_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SPIS_IMR_RXUIM register field. */
#define ALT_SPIS_IMR_RXUIM_RESET      0x1
/* Extracts the ALT_SPIS_IMR_RXUIM field value from a register. */
#define ALT_SPIS_IMR_RXUIM_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SPIS_IMR_RXUIM register field value suitable for setting the register. */
#define ALT_SPIS_IMR_RXUIM_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Receive FIFO Overflow Interrupt Mask - rxoim
 * 
 * Overflow Mask.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                
 * :---------------------------|:------|:--------------------------------------------
 *  ALT_SPIS_IMR_RXOIM_E_MSKED | 0x0   | spi_rxo_intr interrupt is masked (disabled)
 *  ALT_SPIS_IMR_RXOIM_E_END   | 0x1   | spi_rxo_intr interrupt is enabled          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_IMR_RXOIM
 * 
 * spi_rxo_intr interrupt is masked (disabled)
 */
#define ALT_SPIS_IMR_RXOIM_E_MSKED  0x0
/*
 * Enumerated value for register field ALT_SPIS_IMR_RXOIM
 * 
 * spi_rxo_intr interrupt is enabled
 */
#define ALT_SPIS_IMR_RXOIM_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_IMR_RXOIM register field. */
#define ALT_SPIS_IMR_RXOIM_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SPIS_IMR_RXOIM register field. */
#define ALT_SPIS_IMR_RXOIM_MSB        3
/* The width in bits of the ALT_SPIS_IMR_RXOIM register field. */
#define ALT_SPIS_IMR_RXOIM_WIDTH      1
/* The mask used to set the ALT_SPIS_IMR_RXOIM register field value. */
#define ALT_SPIS_IMR_RXOIM_SET_MSK    0x00000008
/* The mask used to clear the ALT_SPIS_IMR_RXOIM register field value. */
#define ALT_SPIS_IMR_RXOIM_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SPIS_IMR_RXOIM register field. */
#define ALT_SPIS_IMR_RXOIM_RESET      0x1
/* Extracts the ALT_SPIS_IMR_RXOIM field value from a register. */
#define ALT_SPIS_IMR_RXOIM_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SPIS_IMR_RXOIM register field value suitable for setting the register. */
#define ALT_SPIS_IMR_RXOIM_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Receive FIFO Full Interrupt Mask - rxfim
 * 
 * FIFO Full Mask.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                
 * :---------------------------|:------|:--------------------------------------------
 *  ALT_SPIS_IMR_RXFIM_E_MSKED | 0x0   | spi_rxf_intr interrupt is masked (disabled)
 *  ALT_SPIS_IMR_RXFIM_E_END   | 0x1   | spi_rxf_intr interrupt is enabled          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_IMR_RXFIM
 * 
 * spi_rxf_intr interrupt is masked (disabled)
 */
#define ALT_SPIS_IMR_RXFIM_E_MSKED  0x0
/*
 * Enumerated value for register field ALT_SPIS_IMR_RXFIM
 * 
 * spi_rxf_intr interrupt is enabled
 */
#define ALT_SPIS_IMR_RXFIM_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_IMR_RXFIM register field. */
#define ALT_SPIS_IMR_RXFIM_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SPIS_IMR_RXFIM register field. */
#define ALT_SPIS_IMR_RXFIM_MSB        4
/* The width in bits of the ALT_SPIS_IMR_RXFIM register field. */
#define ALT_SPIS_IMR_RXFIM_WIDTH      1
/* The mask used to set the ALT_SPIS_IMR_RXFIM register field value. */
#define ALT_SPIS_IMR_RXFIM_SET_MSK    0x00000010
/* The mask used to clear the ALT_SPIS_IMR_RXFIM register field value. */
#define ALT_SPIS_IMR_RXFIM_CLR_MSK    0xffffffef
/* The reset value of the ALT_SPIS_IMR_RXFIM register field. */
#define ALT_SPIS_IMR_RXFIM_RESET      0x1
/* Extracts the ALT_SPIS_IMR_RXFIM field value from a register. */
#define ALT_SPIS_IMR_RXFIM_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_SPIS_IMR_RXFIM register field value suitable for setting the register. */
#define ALT_SPIS_IMR_RXFIM_SET(value) (((value) << 4) & 0x00000010)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_IMR.
 */
struct ALT_SPIS_IMR_s
{
    uint32_t  txeim :  1;  /* Transmit FIFO Empty Interrupt Mask */
    uint32_t  txoim :  1;  /* Transmit FIFO Overflow Interrupt Mask */
    uint32_t  rxuim :  1;  /* Receive FIFO Underflow Interrupt Mask */
    uint32_t  rxoim :  1;  /* Receive FIFO Overflow Interrupt Mask */
    uint32_t  rxfim :  1;  /* Receive FIFO Full Interrupt Mask */
    uint32_t        : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_IMR. */
typedef volatile struct ALT_SPIS_IMR_s  ALT_SPIS_IMR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_IMR register from the beginning of the component. */
#define ALT_SPIS_IMR_OFST        0x2c
/* The address of the ALT_SPIS_IMR register. */
#define ALT_SPIS_IMR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_IMR_OFST))

/*
 * Register : Interrupt Status Register - isr
 * 
 * This register reports the status of the SPI Slave interrupts after they have
 * been masked.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                            
 * :-------|:-------|:------|:----------------------------------------
 *  [0]    | R      | 0x0   | Transmit FIFO Empty Interrupt Status   
 *  [1]    | R      | 0x0   | Transmit FIFO Overflow Interrupt Status
 *  [2]    | R      | 0x0   | Receive FIFO Underflow Interrupt Status
 *  [3]    | R      | 0x0   | Receive FIFO Overflow Interrupt Status 
 *  [4]    | R      | 0x0   | Receive FIFO Full Interrupt Status     
 *  [31:5] | ???    | 0x0   | *UNDEFINED*                            
 * 
 */
/*
 * Field : Transmit FIFO Empty Interrupt Status - txeis
 * 
 * Empty Status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                   
 * :---------------------------|:------|:-----------------------------------------------
 *  ALT_SPIS_ISR_TXEIS_E_INACT | 0x0   | spi_txe_intr interrupt is not active after    
 * :                           |       | masking                                       
 *  ALT_SPIS_ISR_TXEIS_E_ACT   | 0x1   | spi_txe_intr interrupt is active after masking
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_ISR_TXEIS
 * 
 * spi_txe_intr interrupt is not active after masking
 */
#define ALT_SPIS_ISR_TXEIS_E_INACT  0x0
/*
 * Enumerated value for register field ALT_SPIS_ISR_TXEIS
 * 
 * spi_txe_intr interrupt is active after masking
 */
#define ALT_SPIS_ISR_TXEIS_E_ACT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_ISR_TXEIS register field. */
#define ALT_SPIS_ISR_TXEIS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_ISR_TXEIS register field. */
#define ALT_SPIS_ISR_TXEIS_MSB        0
/* The width in bits of the ALT_SPIS_ISR_TXEIS register field. */
#define ALT_SPIS_ISR_TXEIS_WIDTH      1
/* The mask used to set the ALT_SPIS_ISR_TXEIS register field value. */
#define ALT_SPIS_ISR_TXEIS_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIS_ISR_TXEIS register field value. */
#define ALT_SPIS_ISR_TXEIS_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIS_ISR_TXEIS register field. */
#define ALT_SPIS_ISR_TXEIS_RESET      0x0
/* Extracts the ALT_SPIS_ISR_TXEIS field value from a register. */
#define ALT_SPIS_ISR_TXEIS_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIS_ISR_TXEIS register field value suitable for setting the register. */
#define ALT_SPIS_ISR_TXEIS_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Transmit FIFO Overflow Interrupt Status - txois
 * 
 * Overflow Status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                   
 * :---------------------------|:------|:-----------------------------------------------
 *  ALT_SPIS_ISR_TXOIS_E_INACT | 0x0   | spi_txo_intr interrupt is not active after    
 * :                           |       | masking                                       
 *  ALT_SPIS_ISR_TXOIS_E_ACT   | 0x1   | spi_txo_intr interrupt is active after masking
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_ISR_TXOIS
 * 
 * spi_txo_intr interrupt is not active after masking
 */
#define ALT_SPIS_ISR_TXOIS_E_INACT  0x0
/*
 * Enumerated value for register field ALT_SPIS_ISR_TXOIS
 * 
 * spi_txo_intr interrupt is active after masking
 */
#define ALT_SPIS_ISR_TXOIS_E_ACT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_ISR_TXOIS register field. */
#define ALT_SPIS_ISR_TXOIS_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SPIS_ISR_TXOIS register field. */
#define ALT_SPIS_ISR_TXOIS_MSB        1
/* The width in bits of the ALT_SPIS_ISR_TXOIS register field. */
#define ALT_SPIS_ISR_TXOIS_WIDTH      1
/* The mask used to set the ALT_SPIS_ISR_TXOIS register field value. */
#define ALT_SPIS_ISR_TXOIS_SET_MSK    0x00000002
/* The mask used to clear the ALT_SPIS_ISR_TXOIS register field value. */
#define ALT_SPIS_ISR_TXOIS_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SPIS_ISR_TXOIS register field. */
#define ALT_SPIS_ISR_TXOIS_RESET      0x0
/* Extracts the ALT_SPIS_ISR_TXOIS field value from a register. */
#define ALT_SPIS_ISR_TXOIS_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SPIS_ISR_TXOIS register field value suitable for setting the register. */
#define ALT_SPIS_ISR_TXOIS_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Receive FIFO Underflow Interrupt Status - rxuis
 * 
 * Underflow Status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                   
 * :---------------------------|:------|:-----------------------------------------------
 *  ALT_SPIS_ISR_RXUIS_E_INACT | 0x0   | spi_rxu_intr interrupt is not active after    
 * :                           |       | masking                                       
 *  ALT_SPIS_ISR_RXUIS_E_ACT   | 0x1   | spi_rxu_intr interrupt is active after masking
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_ISR_RXUIS
 * 
 * spi_rxu_intr interrupt is not active after masking
 */
#define ALT_SPIS_ISR_RXUIS_E_INACT  0x0
/*
 * Enumerated value for register field ALT_SPIS_ISR_RXUIS
 * 
 * spi_rxu_intr interrupt is active after masking
 */
#define ALT_SPIS_ISR_RXUIS_E_ACT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_ISR_RXUIS register field. */
#define ALT_SPIS_ISR_RXUIS_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SPIS_ISR_RXUIS register field. */
#define ALT_SPIS_ISR_RXUIS_MSB        2
/* The width in bits of the ALT_SPIS_ISR_RXUIS register field. */
#define ALT_SPIS_ISR_RXUIS_WIDTH      1
/* The mask used to set the ALT_SPIS_ISR_RXUIS register field value. */
#define ALT_SPIS_ISR_RXUIS_SET_MSK    0x00000004
/* The mask used to clear the ALT_SPIS_ISR_RXUIS register field value. */
#define ALT_SPIS_ISR_RXUIS_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SPIS_ISR_RXUIS register field. */
#define ALT_SPIS_ISR_RXUIS_RESET      0x0
/* Extracts the ALT_SPIS_ISR_RXUIS field value from a register. */
#define ALT_SPIS_ISR_RXUIS_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SPIS_ISR_RXUIS register field value suitable for setting the register. */
#define ALT_SPIS_ISR_RXUIS_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Receive FIFO Overflow Interrupt Status - rxois
 * 
 * Overflow Status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                   
 * :---------------------------|:------|:-----------------------------------------------
 *  ALT_SPIS_ISR_RXOIS_E_INACT | 0x0   | spi_rxo_intr interrupt is not active after    
 * :                           |       | masking                                       
 *  ALT_SPIS_ISR_RXOIS_E_ACT   | 0x1   | spi_rxo_intr interrupt is active after masking
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_ISR_RXOIS
 * 
 * spi_rxo_intr interrupt is not active after masking
 */
#define ALT_SPIS_ISR_RXOIS_E_INACT  0x0
/*
 * Enumerated value for register field ALT_SPIS_ISR_RXOIS
 * 
 * spi_rxo_intr interrupt is active after masking
 */
#define ALT_SPIS_ISR_RXOIS_E_ACT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_ISR_RXOIS register field. */
#define ALT_SPIS_ISR_RXOIS_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SPIS_ISR_RXOIS register field. */
#define ALT_SPIS_ISR_RXOIS_MSB        3
/* The width in bits of the ALT_SPIS_ISR_RXOIS register field. */
#define ALT_SPIS_ISR_RXOIS_WIDTH      1
/* The mask used to set the ALT_SPIS_ISR_RXOIS register field value. */
#define ALT_SPIS_ISR_RXOIS_SET_MSK    0x00000008
/* The mask used to clear the ALT_SPIS_ISR_RXOIS register field value. */
#define ALT_SPIS_ISR_RXOIS_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SPIS_ISR_RXOIS register field. */
#define ALT_SPIS_ISR_RXOIS_RESET      0x0
/* Extracts the ALT_SPIS_ISR_RXOIS field value from a register. */
#define ALT_SPIS_ISR_RXOIS_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SPIS_ISR_RXOIS register field value suitable for setting the register. */
#define ALT_SPIS_ISR_RXOIS_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Receive FIFO Full Interrupt Status - rxfis
 * 
 * Full Status
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                 
 * :---------------------------|:------|:---------------------------------------------
 *  ALT_SPIS_ISR_RXFIS_E_INACT | 0x0   | spi_rxf_intr interrupt is not active after  
 * :                           |       | masking                                     
 *  ALT_SPIS_ISR_RXFIS_E_ACT   | 0x1   | spi_rxf_intr interrupt is full after masking
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_ISR_RXFIS
 * 
 * spi_rxf_intr interrupt is not active after masking
 */
#define ALT_SPIS_ISR_RXFIS_E_INACT  0x0
/*
 * Enumerated value for register field ALT_SPIS_ISR_RXFIS
 * 
 * spi_rxf_intr interrupt is full after masking
 */
#define ALT_SPIS_ISR_RXFIS_E_ACT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_ISR_RXFIS register field. */
#define ALT_SPIS_ISR_RXFIS_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SPIS_ISR_RXFIS register field. */
#define ALT_SPIS_ISR_RXFIS_MSB        4
/* The width in bits of the ALT_SPIS_ISR_RXFIS register field. */
#define ALT_SPIS_ISR_RXFIS_WIDTH      1
/* The mask used to set the ALT_SPIS_ISR_RXFIS register field value. */
#define ALT_SPIS_ISR_RXFIS_SET_MSK    0x00000010
/* The mask used to clear the ALT_SPIS_ISR_RXFIS register field value. */
#define ALT_SPIS_ISR_RXFIS_CLR_MSK    0xffffffef
/* The reset value of the ALT_SPIS_ISR_RXFIS register field. */
#define ALT_SPIS_ISR_RXFIS_RESET      0x0
/* Extracts the ALT_SPIS_ISR_RXFIS field value from a register. */
#define ALT_SPIS_ISR_RXFIS_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_SPIS_ISR_RXFIS register field value suitable for setting the register. */
#define ALT_SPIS_ISR_RXFIS_SET(value) (((value) << 4) & 0x00000010)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_ISR.
 */
struct ALT_SPIS_ISR_s
{
    const uint32_t  txeis :  1;  /* Transmit FIFO Empty Interrupt Status */
    const uint32_t  txois :  1;  /* Transmit FIFO Overflow Interrupt Status */
    const uint32_t  rxuis :  1;  /* Receive FIFO Underflow Interrupt Status */
    const uint32_t  rxois :  1;  /* Receive FIFO Overflow Interrupt Status */
    const uint32_t  rxfis :  1;  /* Receive FIFO Full Interrupt Status */
    uint32_t              : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_ISR. */
typedef volatile struct ALT_SPIS_ISR_s  ALT_SPIS_ISR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_ISR register from the beginning of the component. */
#define ALT_SPIS_ISR_OFST        0x30
/* The address of the ALT_SPIS_ISR register. */
#define ALT_SPIS_ISR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_ISR_OFST))

/*
 * Register : Raw Interrupt Status Register - risr
 * 
 * This register reports the status of the SPI Slave interrupts prior to masking.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                                
 * :-------|:-------|:------|:--------------------------------------------
 *  [0]    | R      | 0x0   | Transmit FIFO Empty Raw Interrupt Status   
 *  [1]    | R      | 0x0   | Transmit FIFO Overflow Raw Interrupt Status
 *  [2]    | R      | 0x0   | Receive FIFO Underflow Raw Interrupt Status
 *  [3]    | R      | 0x0   | Receive FIFO Overflow Raw Interrupt Status 
 *  [4]    | R      | 0x0   | Receive FIFO Full Raw Interrupt Status     
 *  [31:5] | ???    | 0x0   | *UNDEFINED*                                
 * 
 */
/*
 * Field : Transmit FIFO Empty Raw Interrupt Status - txeir
 * 
 * The interrupt is active or inactive prior to masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                                   
 * :----------------------------|:------|:-----------------------------------------------
 *  ALT_SPIS_RISR_TXEIR_E_INACT | 0x0   | spi_txe_intr interrupt is not active prior to 
 * :                            |       | masking                                       
 *  ALT_SPIS_RISR_TXEIR_E_ACT   | 0x1   | spi_txe_intr interrupt is active prior masking
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_RISR_TXEIR
 * 
 * spi_txe_intr interrupt is not active prior to masking
 */
#define ALT_SPIS_RISR_TXEIR_E_INACT 0x0
/*
 * Enumerated value for register field ALT_SPIS_RISR_TXEIR
 * 
 * spi_txe_intr interrupt is active prior masking
 */
#define ALT_SPIS_RISR_TXEIR_E_ACT   0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_RISR_TXEIR register field. */
#define ALT_SPIS_RISR_TXEIR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_RISR_TXEIR register field. */
#define ALT_SPIS_RISR_TXEIR_MSB        0
/* The width in bits of the ALT_SPIS_RISR_TXEIR register field. */
#define ALT_SPIS_RISR_TXEIR_WIDTH      1
/* The mask used to set the ALT_SPIS_RISR_TXEIR register field value. */
#define ALT_SPIS_RISR_TXEIR_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIS_RISR_TXEIR register field value. */
#define ALT_SPIS_RISR_TXEIR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIS_RISR_TXEIR register field. */
#define ALT_SPIS_RISR_TXEIR_RESET      0x0
/* Extracts the ALT_SPIS_RISR_TXEIR field value from a register. */
#define ALT_SPIS_RISR_TXEIR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIS_RISR_TXEIR register field value suitable for setting the register. */
#define ALT_SPIS_RISR_TXEIR_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Transmit FIFO Overflow Raw Interrupt Status - txoir
 * 
 * The interrupt is active or inactive prior to masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                                   
 * :----------------------------|:------|:-----------------------------------------------
 *  ALT_SPIS_RISR_TXOIR_E_INACT | 0x0   | spi_txo_intr interrupt is not active prior to 
 * :                            |       | masking                                       
 *  ALT_SPIS_RISR_TXOIR_E_ACT   | 0x1   | spi_txo_intr interrupt is active prior masking
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_RISR_TXOIR
 * 
 * spi_txo_intr interrupt is not active prior to masking
 */
#define ALT_SPIS_RISR_TXOIR_E_INACT 0x0
/*
 * Enumerated value for register field ALT_SPIS_RISR_TXOIR
 * 
 * spi_txo_intr interrupt is active prior masking
 */
#define ALT_SPIS_RISR_TXOIR_E_ACT   0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_RISR_TXOIR register field. */
#define ALT_SPIS_RISR_TXOIR_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SPIS_RISR_TXOIR register field. */
#define ALT_SPIS_RISR_TXOIR_MSB        1
/* The width in bits of the ALT_SPIS_RISR_TXOIR register field. */
#define ALT_SPIS_RISR_TXOIR_WIDTH      1
/* The mask used to set the ALT_SPIS_RISR_TXOIR register field value. */
#define ALT_SPIS_RISR_TXOIR_SET_MSK    0x00000002
/* The mask used to clear the ALT_SPIS_RISR_TXOIR register field value. */
#define ALT_SPIS_RISR_TXOIR_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SPIS_RISR_TXOIR register field. */
#define ALT_SPIS_RISR_TXOIR_RESET      0x0
/* Extracts the ALT_SPIS_RISR_TXOIR field value from a register. */
#define ALT_SPIS_RISR_TXOIR_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SPIS_RISR_TXOIR register field value suitable for setting the register. */
#define ALT_SPIS_RISR_TXOIR_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Receive FIFO Underflow Raw Interrupt Status - rxuir
 * 
 * The interrupt is active or inactive prior to masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                                  
 * :----------------------------|:------|:----------------------------------------------
 *  ALT_SPIS_RISR_RXUIR_E_INACT | 0x0   | spi_rxu_intr interrupt is not active prior to
 * :                            |       | masking                                      
 *  ALT_SPIS_RISR_RXUIR_E_ACT   | 0x1   | spi_rxu_intr interrupt is active prior to    
 * :                            |       | masking                                      
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_RISR_RXUIR
 * 
 * spi_rxu_intr interrupt is not active prior to masking
 */
#define ALT_SPIS_RISR_RXUIR_E_INACT 0x0
/*
 * Enumerated value for register field ALT_SPIS_RISR_RXUIR
 * 
 * spi_rxu_intr interrupt is active prior to masking
 */
#define ALT_SPIS_RISR_RXUIR_E_ACT   0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_RISR_RXUIR register field. */
#define ALT_SPIS_RISR_RXUIR_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SPIS_RISR_RXUIR register field. */
#define ALT_SPIS_RISR_RXUIR_MSB        2
/* The width in bits of the ALT_SPIS_RISR_RXUIR register field. */
#define ALT_SPIS_RISR_RXUIR_WIDTH      1
/* The mask used to set the ALT_SPIS_RISR_RXUIR register field value. */
#define ALT_SPIS_RISR_RXUIR_SET_MSK    0x00000004
/* The mask used to clear the ALT_SPIS_RISR_RXUIR register field value. */
#define ALT_SPIS_RISR_RXUIR_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SPIS_RISR_RXUIR register field. */
#define ALT_SPIS_RISR_RXUIR_RESET      0x0
/* Extracts the ALT_SPIS_RISR_RXUIR field value from a register. */
#define ALT_SPIS_RISR_RXUIR_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SPIS_RISR_RXUIR register field value suitable for setting the register. */
#define ALT_SPIS_RISR_RXUIR_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Receive FIFO Overflow Raw Interrupt Status - rxoir
 * 
 * The interrupt is active or inactive prior to masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                                   
 * :----------------------------|:------|:-----------------------------------------------
 *  ALT_SPIS_RISR_RXOIR_E_INACT | 0x0   | spi_rxo_intr interrupt is not active prior to 
 * :                            |       | masking                                       
 *  ALT_SPIS_RISR_RXOIR_E_ACT   | 0x1   | spi_rxo_intr interrupt is active prior masking
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_RISR_RXOIR
 * 
 * spi_rxo_intr interrupt is not active prior to masking
 */
#define ALT_SPIS_RISR_RXOIR_E_INACT 0x0
/*
 * Enumerated value for register field ALT_SPIS_RISR_RXOIR
 * 
 * spi_rxo_intr interrupt is active prior masking
 */
#define ALT_SPIS_RISR_RXOIR_E_ACT   0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_RISR_RXOIR register field. */
#define ALT_SPIS_RISR_RXOIR_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SPIS_RISR_RXOIR register field. */
#define ALT_SPIS_RISR_RXOIR_MSB        3
/* The width in bits of the ALT_SPIS_RISR_RXOIR register field. */
#define ALT_SPIS_RISR_RXOIR_WIDTH      1
/* The mask used to set the ALT_SPIS_RISR_RXOIR register field value. */
#define ALT_SPIS_RISR_RXOIR_SET_MSK    0x00000008
/* The mask used to clear the ALT_SPIS_RISR_RXOIR register field value. */
#define ALT_SPIS_RISR_RXOIR_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SPIS_RISR_RXOIR register field. */
#define ALT_SPIS_RISR_RXOIR_RESET      0x0
/* Extracts the ALT_SPIS_RISR_RXOIR field value from a register. */
#define ALT_SPIS_RISR_RXOIR_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SPIS_RISR_RXOIR register field value suitable for setting the register. */
#define ALT_SPIS_RISR_RXOIR_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Receive FIFO Full Raw Interrupt Status - rxfir
 * 
 * The interrupt is active or inactive prior to masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                                  
 * :----------------------------|:------|:----------------------------------------------
 *  ALT_SPIS_RISR_RXFIR_E_INACT | 0x0   | spi_rxf_intr interrupt is not active prior to
 * :                            |       | masking                                      
 *  ALT_SPIS_RISR_RXFIR_E_ACT   | 0x1   | spi_rxf_intr interrupt is active prior to    
 * :                            |       | masking                                      
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_RISR_RXFIR
 * 
 * spi_rxf_intr interrupt is not active prior to masking
 */
#define ALT_SPIS_RISR_RXFIR_E_INACT 0x0
/*
 * Enumerated value for register field ALT_SPIS_RISR_RXFIR
 * 
 * spi_rxf_intr interrupt is active prior to masking
 */
#define ALT_SPIS_RISR_RXFIR_E_ACT   0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_RISR_RXFIR register field. */
#define ALT_SPIS_RISR_RXFIR_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SPIS_RISR_RXFIR register field. */
#define ALT_SPIS_RISR_RXFIR_MSB        4
/* The width in bits of the ALT_SPIS_RISR_RXFIR register field. */
#define ALT_SPIS_RISR_RXFIR_WIDTH      1
/* The mask used to set the ALT_SPIS_RISR_RXFIR register field value. */
#define ALT_SPIS_RISR_RXFIR_SET_MSK    0x00000010
/* The mask used to clear the ALT_SPIS_RISR_RXFIR register field value. */
#define ALT_SPIS_RISR_RXFIR_CLR_MSK    0xffffffef
/* The reset value of the ALT_SPIS_RISR_RXFIR register field. */
#define ALT_SPIS_RISR_RXFIR_RESET      0x0
/* Extracts the ALT_SPIS_RISR_RXFIR field value from a register. */
#define ALT_SPIS_RISR_RXFIR_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_SPIS_RISR_RXFIR register field value suitable for setting the register. */
#define ALT_SPIS_RISR_RXFIR_SET(value) (((value) << 4) & 0x00000010)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_RISR.
 */
struct ALT_SPIS_RISR_s
{
    const uint32_t  txeir :  1;  /* Transmit FIFO Empty Raw Interrupt Status */
    const uint32_t  txoir :  1;  /* Transmit FIFO Overflow Raw Interrupt Status */
    const uint32_t  rxuir :  1;  /* Receive FIFO Underflow Raw Interrupt Status */
    const uint32_t  rxoir :  1;  /* Receive FIFO Overflow Raw Interrupt Status */
    const uint32_t  rxfir :  1;  /* Receive FIFO Full Raw Interrupt Status */
    uint32_t              : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_RISR. */
typedef volatile struct ALT_SPIS_RISR_s  ALT_SPIS_RISR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_RISR register from the beginning of the component. */
#define ALT_SPIS_RISR_OFST        0x34
/* The address of the ALT_SPIS_RISR register. */
#define ALT_SPIS_RISR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_RISR_OFST))

/*
 * Register : Transmit FIFO Overflow Interrupt Clear Register - txoicr
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                           
 * :-------|:-------|:------|:---------------------------------------
 *  [0]    | R      | 0x0   | Clear Transmit FIFO Overflow Interrupt
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                           
 * 
 */
/*
 * Field : Clear Transmit FIFO Overflow Interrupt - txoicr
 * 
 * This register reflects the status of the interrupt. A read from this register
 * clears the ssi_txo_intr interrupt; writing has no effect.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIS_TXOICR_TXOICR register field. */
#define ALT_SPIS_TXOICR_TXOICR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_TXOICR_TXOICR register field. */
#define ALT_SPIS_TXOICR_TXOICR_MSB        0
/* The width in bits of the ALT_SPIS_TXOICR_TXOICR register field. */
#define ALT_SPIS_TXOICR_TXOICR_WIDTH      1
/* The mask used to set the ALT_SPIS_TXOICR_TXOICR register field value. */
#define ALT_SPIS_TXOICR_TXOICR_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIS_TXOICR_TXOICR register field value. */
#define ALT_SPIS_TXOICR_TXOICR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIS_TXOICR_TXOICR register field. */
#define ALT_SPIS_TXOICR_TXOICR_RESET      0x0
/* Extracts the ALT_SPIS_TXOICR_TXOICR field value from a register. */
#define ALT_SPIS_TXOICR_TXOICR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIS_TXOICR_TXOICR register field value suitable for setting the register. */
#define ALT_SPIS_TXOICR_TXOICR_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_TXOICR.
 */
struct ALT_SPIS_TXOICR_s
{
    const uint32_t  txoicr :  1;  /* Clear Transmit FIFO Overflow Interrupt */
    uint32_t               : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_TXOICR. */
typedef volatile struct ALT_SPIS_TXOICR_s  ALT_SPIS_TXOICR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_TXOICR register from the beginning of the component. */
#define ALT_SPIS_TXOICR_OFST        0x38
/* The address of the ALT_SPIS_TXOICR register. */
#define ALT_SPIS_TXOICR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_TXOICR_OFST))

/*
 * Register : Receive FIFO Overflow Interrupt Clear Register - rxoicr
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                          
 * :-------|:-------|:------|:--------------------------------------
 *  [0]    | R      | 0x0   | Clear Receive FIFO Overflow Interrupt
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                          
 * 
 */
/*
 * Field : Clear Receive FIFO Overflow Interrupt - rxoicr
 * 
 * This register reflects the status of the interrupt. A read from this register
 * clears the ssi_rxo_intr interrupt; writing has no effect.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIS_RXOICR_RXOICR register field. */
#define ALT_SPIS_RXOICR_RXOICR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_RXOICR_RXOICR register field. */
#define ALT_SPIS_RXOICR_RXOICR_MSB        0
/* The width in bits of the ALT_SPIS_RXOICR_RXOICR register field. */
#define ALT_SPIS_RXOICR_RXOICR_WIDTH      1
/* The mask used to set the ALT_SPIS_RXOICR_RXOICR register field value. */
#define ALT_SPIS_RXOICR_RXOICR_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIS_RXOICR_RXOICR register field value. */
#define ALT_SPIS_RXOICR_RXOICR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIS_RXOICR_RXOICR register field. */
#define ALT_SPIS_RXOICR_RXOICR_RESET      0x0
/* Extracts the ALT_SPIS_RXOICR_RXOICR field value from a register. */
#define ALT_SPIS_RXOICR_RXOICR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIS_RXOICR_RXOICR register field value suitable for setting the register. */
#define ALT_SPIS_RXOICR_RXOICR_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_RXOICR.
 */
struct ALT_SPIS_RXOICR_s
{
    const uint32_t  rxoicr :  1;  /* Clear Receive FIFO Overflow Interrupt */
    uint32_t               : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_RXOICR. */
typedef volatile struct ALT_SPIS_RXOICR_s  ALT_SPIS_RXOICR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_RXOICR register from the beginning of the component. */
#define ALT_SPIS_RXOICR_OFST        0x3c
/* The address of the ALT_SPIS_RXOICR register. */
#define ALT_SPIS_RXOICR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_RXOICR_OFST))

/*
 * Register : Receive FIFO Underflow Interrupt Clear Register - rxuicr
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                           
 * :-------|:-------|:------|:---------------------------------------
 *  [0]    | R      | 0x0   | Clear Receive FIFO Underflow Interrupt
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                           
 * 
 */
/*
 * Field : Clear Receive FIFO Underflow Interrupt - rxuicr
 * 
 * This register reflects the status of the interrupt. A read from this register
 * clears the ssi_rxu_intr interrupt; writing has no effect.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIS_RXUICR_RXUICR register field. */
#define ALT_SPIS_RXUICR_RXUICR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_RXUICR_RXUICR register field. */
#define ALT_SPIS_RXUICR_RXUICR_MSB        0
/* The width in bits of the ALT_SPIS_RXUICR_RXUICR register field. */
#define ALT_SPIS_RXUICR_RXUICR_WIDTH      1
/* The mask used to set the ALT_SPIS_RXUICR_RXUICR register field value. */
#define ALT_SPIS_RXUICR_RXUICR_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIS_RXUICR_RXUICR register field value. */
#define ALT_SPIS_RXUICR_RXUICR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIS_RXUICR_RXUICR register field. */
#define ALT_SPIS_RXUICR_RXUICR_RESET      0x0
/* Extracts the ALT_SPIS_RXUICR_RXUICR field value from a register. */
#define ALT_SPIS_RXUICR_RXUICR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIS_RXUICR_RXUICR register field value suitable for setting the register. */
#define ALT_SPIS_RXUICR_RXUICR_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_RXUICR.
 */
struct ALT_SPIS_RXUICR_s
{
    const uint32_t  rxuicr :  1;  /* Clear Receive FIFO Underflow Interrupt */
    uint32_t               : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_RXUICR. */
typedef volatile struct ALT_SPIS_RXUICR_s  ALT_SPIS_RXUICR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_RXUICR register from the beginning of the component. */
#define ALT_SPIS_RXUICR_OFST        0x40
/* The address of the ALT_SPIS_RXUICR register. */
#define ALT_SPIS_RXUICR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_RXUICR_OFST))

/*
 * Register : Interrupt Clear Register - icr
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description     
 * :-------|:-------|:------|:-----------------
 *  [0]    | R      | 0x0   | Clear Interrupts
 *  [31:1] | ???    | 0x0   | *UNDEFINED*     
 * 
 */
/*
 * Field : Clear Interrupts - icr
 * 
 * This register is set if any of the interrupts below are active. A read clears
 * the ssi_txo_intr, ssi_rxu_intr, ssi_rxo_intr, and the ssi_mst_intr interrupts.
 * Writing to this register has no effect.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIS_ICR_ICR register field. */
#define ALT_SPIS_ICR_ICR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_ICR_ICR register field. */
#define ALT_SPIS_ICR_ICR_MSB        0
/* The width in bits of the ALT_SPIS_ICR_ICR register field. */
#define ALT_SPIS_ICR_ICR_WIDTH      1
/* The mask used to set the ALT_SPIS_ICR_ICR register field value. */
#define ALT_SPIS_ICR_ICR_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIS_ICR_ICR register field value. */
#define ALT_SPIS_ICR_ICR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIS_ICR_ICR register field. */
#define ALT_SPIS_ICR_ICR_RESET      0x0
/* Extracts the ALT_SPIS_ICR_ICR field value from a register. */
#define ALT_SPIS_ICR_ICR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIS_ICR_ICR register field value suitable for setting the register. */
#define ALT_SPIS_ICR_ICR_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_ICR.
 */
struct ALT_SPIS_ICR_s
{
    const uint32_t  icr :  1;  /* Clear Interrupts */
    uint32_t            : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_ICR. */
typedef volatile struct ALT_SPIS_ICR_s  ALT_SPIS_ICR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_ICR register from the beginning of the component. */
#define ALT_SPIS_ICR_OFST        0x48
/* The address of the ALT_SPIS_ICR register. */
#define ALT_SPIS_ICR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_ICR_OFST))

/*
 * Register : DMA Control Register - dmacr
 * 
 * The register is used to enable the DMA Controller interface operation.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description        
 * :-------|:-------|:------|:--------------------
 *  [0]    | RW     | 0x0   | Receive DMA Enable 
 *  [1]    | RW     | 0x0   | Transmit DMA Enable
 *  [31:2] | ???    | 0x0   | *UNDEFINED*        
 * 
 */
/*
 * Field : Receive DMA Enable - rdmae
 * 
 * This bit enables/disables the receive FIFO DMA channel
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description         
 * :----------------------------|:------|:---------------------
 *  ALT_SPIS_DMACR_RDMAE_E_DISD | 0x0   | Receive DMA disabled
 *  ALT_SPIS_DMACR_RDMAE_E_END  | 0x1   | Receive DMA enabled 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_DMACR_RDMAE
 * 
 * Receive DMA disabled
 */
#define ALT_SPIS_DMACR_RDMAE_E_DISD 0x0
/*
 * Enumerated value for register field ALT_SPIS_DMACR_RDMAE
 * 
 * Receive DMA enabled
 */
#define ALT_SPIS_DMACR_RDMAE_E_END  0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_DMACR_RDMAE register field. */
#define ALT_SPIS_DMACR_RDMAE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_DMACR_RDMAE register field. */
#define ALT_SPIS_DMACR_RDMAE_MSB        0
/* The width in bits of the ALT_SPIS_DMACR_RDMAE register field. */
#define ALT_SPIS_DMACR_RDMAE_WIDTH      1
/* The mask used to set the ALT_SPIS_DMACR_RDMAE register field value. */
#define ALT_SPIS_DMACR_RDMAE_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIS_DMACR_RDMAE register field value. */
#define ALT_SPIS_DMACR_RDMAE_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIS_DMACR_RDMAE register field. */
#define ALT_SPIS_DMACR_RDMAE_RESET      0x0
/* Extracts the ALT_SPIS_DMACR_RDMAE field value from a register. */
#define ALT_SPIS_DMACR_RDMAE_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIS_DMACR_RDMAE register field value suitable for setting the register. */
#define ALT_SPIS_DMACR_RDMAE_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Transmit DMA Enable - tdmae
 * 
 * This bit enables/disables the transmit FIFO DMA channel.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description          
 * :----------------------------|:------|:----------------------
 *  ALT_SPIS_DMACR_TDMAE_E_DISD | 0x0   | Transmit DMA disabled
 *  ALT_SPIS_DMACR_TDMAE_E_END  | 0x1   | Transmit DMA enabled 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIS_DMACR_TDMAE
 * 
 * Transmit DMA disabled
 */
#define ALT_SPIS_DMACR_TDMAE_E_DISD 0x0
/*
 * Enumerated value for register field ALT_SPIS_DMACR_TDMAE
 * 
 * Transmit DMA enabled
 */
#define ALT_SPIS_DMACR_TDMAE_E_END  0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIS_DMACR_TDMAE register field. */
#define ALT_SPIS_DMACR_TDMAE_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SPIS_DMACR_TDMAE register field. */
#define ALT_SPIS_DMACR_TDMAE_MSB        1
/* The width in bits of the ALT_SPIS_DMACR_TDMAE register field. */
#define ALT_SPIS_DMACR_TDMAE_WIDTH      1
/* The mask used to set the ALT_SPIS_DMACR_TDMAE register field value. */
#define ALT_SPIS_DMACR_TDMAE_SET_MSK    0x00000002
/* The mask used to clear the ALT_SPIS_DMACR_TDMAE register field value. */
#define ALT_SPIS_DMACR_TDMAE_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SPIS_DMACR_TDMAE register field. */
#define ALT_SPIS_DMACR_TDMAE_RESET      0x0
/* Extracts the ALT_SPIS_DMACR_TDMAE field value from a register. */
#define ALT_SPIS_DMACR_TDMAE_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SPIS_DMACR_TDMAE register field value suitable for setting the register. */
#define ALT_SPIS_DMACR_TDMAE_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_DMACR.
 */
struct ALT_SPIS_DMACR_s
{
    uint32_t  rdmae :  1;  /* Receive DMA Enable */
    uint32_t  tdmae :  1;  /* Transmit DMA Enable */
    uint32_t        : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_DMACR. */
typedef volatile struct ALT_SPIS_DMACR_s  ALT_SPIS_DMACR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_DMACR register from the beginning of the component. */
#define ALT_SPIS_DMACR_OFST        0x4c
/* The address of the ALT_SPIS_DMACR register. */
#define ALT_SPIS_DMACR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_DMACR_OFST))

/*
 * Register : DMA Transmit Data Level Regoster - dmatdlr
 * 
 * Controls DMA Transmit FIFO Threshold
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description        
 * :-------|:-------|:------|:--------------------
 *  [7:0]  | RW     | 0x0   | Transmit Data Level
 *  [31:8] | ???    | 0x0   | *UNDEFINED*        
 * 
 */
/*
 * Field : Transmit Data Level - dmatdl
 * 
 * This bit field controls the level at which a DMA request is made by the transmit
 * logic. It is equal to the watermark level; that is, the dma_tx_req signal is
 * generated when the number of valid data entries in the transmit FIFO is equal to
 * or below this field value, and TDMAE = 1.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIS_DMATDLR_DMATDL register field. */
#define ALT_SPIS_DMATDLR_DMATDL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_DMATDLR_DMATDL register field. */
#define ALT_SPIS_DMATDLR_DMATDL_MSB        7
/* The width in bits of the ALT_SPIS_DMATDLR_DMATDL register field. */
#define ALT_SPIS_DMATDLR_DMATDL_WIDTH      8
/* The mask used to set the ALT_SPIS_DMATDLR_DMATDL register field value. */
#define ALT_SPIS_DMATDLR_DMATDL_SET_MSK    0x000000ff
/* The mask used to clear the ALT_SPIS_DMATDLR_DMATDL register field value. */
#define ALT_SPIS_DMATDLR_DMATDL_CLR_MSK    0xffffff00
/* The reset value of the ALT_SPIS_DMATDLR_DMATDL register field. */
#define ALT_SPIS_DMATDLR_DMATDL_RESET      0x0
/* Extracts the ALT_SPIS_DMATDLR_DMATDL field value from a register. */
#define ALT_SPIS_DMATDLR_DMATDL_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_SPIS_DMATDLR_DMATDL register field value suitable for setting the register. */
#define ALT_SPIS_DMATDLR_DMATDL_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_DMATDLR.
 */
struct ALT_SPIS_DMATDLR_s
{
    uint32_t  dmatdl :  8;  /* Transmit Data Level */
    uint32_t         : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_DMATDLR. */
typedef volatile struct ALT_SPIS_DMATDLR_s  ALT_SPIS_DMATDLR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_DMATDLR register from the beginning of the component. */
#define ALT_SPIS_DMATDLR_OFST        0x50
/* The address of the ALT_SPIS_DMATDLR register. */
#define ALT_SPIS_DMATDLR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_DMATDLR_OFST))

/*
 * Register : DMA Receive Data Level Register - dmardlr
 * 
 * Controls DMA Receive FIFO Threshold
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description       
 * :-------|:-------|:------|:-------------------
 *  [7:0]  | RW     | 0x0   | Receive Data Level
 *  [31:8] | ???    | 0x0   | *UNDEFINED*       
 * 
 */
/*
 * Field : Receive Data Level - dmardl
 * 
 * This bit field controls the level at which a DMA request is made by the receive
 * logic. The watermark level = DMARDL+1; that is, dma_rx_req is generated when the
 * number of valid data entries in the receive FIFO is equal to or above this field
 * value + 1, and RDMAE=1.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIS_DMARDLR_DMARDL register field. */
#define ALT_SPIS_DMARDLR_DMARDL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_DMARDLR_DMARDL register field. */
#define ALT_SPIS_DMARDLR_DMARDL_MSB        7
/* The width in bits of the ALT_SPIS_DMARDLR_DMARDL register field. */
#define ALT_SPIS_DMARDLR_DMARDL_WIDTH      8
/* The mask used to set the ALT_SPIS_DMARDLR_DMARDL register field value. */
#define ALT_SPIS_DMARDLR_DMARDL_SET_MSK    0x000000ff
/* The mask used to clear the ALT_SPIS_DMARDLR_DMARDL register field value. */
#define ALT_SPIS_DMARDLR_DMARDL_CLR_MSK    0xffffff00
/* The reset value of the ALT_SPIS_DMARDLR_DMARDL register field. */
#define ALT_SPIS_DMARDLR_DMARDL_RESET      0x0
/* Extracts the ALT_SPIS_DMARDLR_DMARDL field value from a register. */
#define ALT_SPIS_DMARDLR_DMARDL_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_SPIS_DMARDLR_DMARDL register field value suitable for setting the register. */
#define ALT_SPIS_DMARDLR_DMARDL_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_DMARDLR.
 */
struct ALT_SPIS_DMARDLR_s
{
    uint32_t  dmardl :  8;  /* Receive Data Level */
    uint32_t         : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_DMARDLR. */
typedef volatile struct ALT_SPIS_DMARDLR_s  ALT_SPIS_DMARDLR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_DMARDLR register from the beginning of the component. */
#define ALT_SPIS_DMARDLR_OFST        0x54
/* The address of the ALT_SPIS_DMARDLR register. */
#define ALT_SPIS_DMARDLR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_DMARDLR_OFST))

/*
 * Register : Identification Register - idr
 * 
 * This register stores a peripheral identification code
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset     | Description        
 * :-------|:-------|:----------|:--------------------
 *  [31:0] | R      | 0x5510005 | Identification Code
 * 
 */
/*
 * Field : Identification Code - idr
 * 
 * This filed contains the peripherals identification code, 0x05510005.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIS_IDR_IDR register field. */
#define ALT_SPIS_IDR_IDR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_IDR_IDR register field. */
#define ALT_SPIS_IDR_IDR_MSB        31
/* The width in bits of the ALT_SPIS_IDR_IDR register field. */
#define ALT_SPIS_IDR_IDR_WIDTH      32
/* The mask used to set the ALT_SPIS_IDR_IDR register field value. */
#define ALT_SPIS_IDR_IDR_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SPIS_IDR_IDR register field value. */
#define ALT_SPIS_IDR_IDR_CLR_MSK    0x00000000
/* The reset value of the ALT_SPIS_IDR_IDR register field. */
#define ALT_SPIS_IDR_IDR_RESET      0x5510005
/* Extracts the ALT_SPIS_IDR_IDR field value from a register. */
#define ALT_SPIS_IDR_IDR_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SPIS_IDR_IDR register field value suitable for setting the register. */
#define ALT_SPIS_IDR_IDR_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_IDR.
 */
struct ALT_SPIS_IDR_s
{
    const uint32_t  idr : 32;  /* Identification Code */
};

/* The typedef declaration for register ALT_SPIS_IDR. */
typedef volatile struct ALT_SPIS_IDR_s  ALT_SPIS_IDR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_IDR register from the beginning of the component. */
#define ALT_SPIS_IDR_OFST        0x58
/* The address of the ALT_SPIS_IDR register. */
#define ALT_SPIS_IDR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_IDR_OFST))

/*
 * Register : Component Version Register - spi_version_id
 * 
 * This read-only register stores the specific SPI Slave component version.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset      | Description      
 * :-------|:-------|:-----------|:------------------
 *  [31:0] | RW     | 0x3332302a | Component Version
 * 
 */
/*
 * Field : Component Version - spi_version_id
 * 
 * Contains the hex representation of the Synopsys component version. Consists of
 * ASCII value for each number in the version.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIS_SPI_VER_ID_SPI_VER_ID register field. */
#define ALT_SPIS_SPI_VER_ID_SPI_VER_ID_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_SPI_VER_ID_SPI_VER_ID register field. */
#define ALT_SPIS_SPI_VER_ID_SPI_VER_ID_MSB        31
/* The width in bits of the ALT_SPIS_SPI_VER_ID_SPI_VER_ID register field. */
#define ALT_SPIS_SPI_VER_ID_SPI_VER_ID_WIDTH      32
/* The mask used to set the ALT_SPIS_SPI_VER_ID_SPI_VER_ID register field value. */
#define ALT_SPIS_SPI_VER_ID_SPI_VER_ID_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SPIS_SPI_VER_ID_SPI_VER_ID register field value. */
#define ALT_SPIS_SPI_VER_ID_SPI_VER_ID_CLR_MSK    0x00000000
/* The reset value of the ALT_SPIS_SPI_VER_ID_SPI_VER_ID register field. */
#define ALT_SPIS_SPI_VER_ID_SPI_VER_ID_RESET      0x3332302a
/* Extracts the ALT_SPIS_SPI_VER_ID_SPI_VER_ID field value from a register. */
#define ALT_SPIS_SPI_VER_ID_SPI_VER_ID_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SPIS_SPI_VER_ID_SPI_VER_ID register field value suitable for setting the register. */
#define ALT_SPIS_SPI_VER_ID_SPI_VER_ID_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_SPI_VER_ID.
 */
struct ALT_SPIS_SPI_VER_ID_s
{
    uint32_t  spi_version_id : 32;  /* Component Version */
};

/* The typedef declaration for register ALT_SPIS_SPI_VER_ID. */
typedef volatile struct ALT_SPIS_SPI_VER_ID_s  ALT_SPIS_SPI_VER_ID_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_SPI_VER_ID register from the beginning of the component. */
#define ALT_SPIS_SPI_VER_ID_OFST        0x5c
/* The address of the ALT_SPIS_SPI_VER_ID register. */
#define ALT_SPIS_SPI_VER_ID_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_SPI_VER_ID_OFST))

/*
 * Register : Data Register - dr
 * 
 * The data register is a 16-bit read/write buffer for the transmit/receive FIFOs.
 * When the register is read, data in the receive FIFO buffer is accessed. When it
 * is written to, data are moved into the transmit FIFO buffer; a write can occur
 * only when SPI_EN = 1. FIFOs are reset when SPI_EN = 0.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description
 * :--------|:-------|:------|:------------
 *  [15:0]  | RW     | 0x0   | Data       
 *  [31:16] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Data - dr
 * 
 * When writing to this register, you must right-justify the data. Read data are
 * automatically right-justified.
 * 
 * Read = Receive FIFO buffer
 * 
 * Write = Transmit FIFO buffer
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIS_DR_DR register field. */
#define ALT_SPIS_DR_DR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIS_DR_DR register field. */
#define ALT_SPIS_DR_DR_MSB        15
/* The width in bits of the ALT_SPIS_DR_DR register field. */
#define ALT_SPIS_DR_DR_WIDTH      16
/* The mask used to set the ALT_SPIS_DR_DR register field value. */
#define ALT_SPIS_DR_DR_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_SPIS_DR_DR register field value. */
#define ALT_SPIS_DR_DR_CLR_MSK    0xffff0000
/* The reset value of the ALT_SPIS_DR_DR register field. */
#define ALT_SPIS_DR_DR_RESET      0x0
/* Extracts the ALT_SPIS_DR_DR field value from a register. */
#define ALT_SPIS_DR_DR_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_SPIS_DR_DR register field value suitable for setting the register. */
#define ALT_SPIS_DR_DR_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIS_DR.
 */
struct ALT_SPIS_DR_s
{
    uint32_t  dr : 16;  /* Data */
    uint32_t     : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIS_DR. */
typedef volatile struct ALT_SPIS_DR_s  ALT_SPIS_DR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIS_DR register from the beginning of the component. */
#define ALT_SPIS_DR_OFST        0x60
/* The address of the ALT_SPIS_DR register. */
#define ALT_SPIS_DR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIS_DR_OFST))

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_SPIS.
 */
struct ALT_SPIS_s
{
    volatile ALT_SPIS_CTLR0_t       ctrlr0;             /* ALT_SPIS_CTLR0 */
    volatile uint32_t               _pad_0x4_0x7;       /* *UNDEFINED* */
    volatile ALT_SPIS_SPIENR_t      spienr;             /* ALT_SPIS_SPIENR */
    volatile ALT_SPIS_MWCR_t        mwcr;               /* ALT_SPIS_MWCR */
    volatile uint32_t               _pad_0x10_0x17[2];  /* *UNDEFINED* */
    volatile ALT_SPIS_TXFTLR_t      txftlr;             /* ALT_SPIS_TXFTLR */
    volatile ALT_SPIS_RXFTLR_t      rxftlr;             /* ALT_SPIS_RXFTLR */
    volatile ALT_SPIS_TXFLR_t       txflr;              /* ALT_SPIS_TXFLR */
    volatile ALT_SPIS_RXFLR_t       rxflr;              /* ALT_SPIS_RXFLR */
    volatile ALT_SPIS_SR_t          sr;                 /* ALT_SPIS_SR */
    volatile ALT_SPIS_IMR_t         imr;                /* ALT_SPIS_IMR */
    volatile ALT_SPIS_ISR_t         isr;                /* ALT_SPIS_ISR */
    volatile ALT_SPIS_RISR_t        risr;               /* ALT_SPIS_RISR */
    volatile ALT_SPIS_TXOICR_t      txoicr;             /* ALT_SPIS_TXOICR */
    volatile ALT_SPIS_RXOICR_t      rxoicr;             /* ALT_SPIS_RXOICR */
    volatile ALT_SPIS_RXUICR_t      rxuicr;             /* ALT_SPIS_RXUICR */
    volatile uint32_t               _pad_0x44_0x47;     /* *UNDEFINED* */
    volatile ALT_SPIS_ICR_t         icr;                /* ALT_SPIS_ICR */
    volatile ALT_SPIS_DMACR_t       dmacr;              /* ALT_SPIS_DMACR */
    volatile ALT_SPIS_DMATDLR_t     dmatdlr;            /* ALT_SPIS_DMATDLR */
    volatile ALT_SPIS_DMARDLR_t     dmardlr;            /* ALT_SPIS_DMARDLR */
    volatile ALT_SPIS_IDR_t         idr;                /* ALT_SPIS_IDR */
    volatile ALT_SPIS_SPI_VER_ID_t  spi_version_id;     /* ALT_SPIS_SPI_VER_ID */
    volatile ALT_SPIS_DR_t          dr;                 /* ALT_SPIS_DR */
    volatile uint32_t               _pad_0x64_0x80[7];  /* *UNDEFINED* */
};

/* The typedef declaration for register group ALT_SPIS. */
typedef volatile struct ALT_SPIS_s  ALT_SPIS_t;
/* The struct declaration for the raw register contents of register group ALT_SPIS. */
struct ALT_SPIS_raw_s
{
    volatile uint32_t  ctrlr0;             /* ALT_SPIS_CTLR0 */
    volatile uint32_t  _pad_0x4_0x7;       /* *UNDEFINED* */
    volatile uint32_t  spienr;             /* ALT_SPIS_SPIENR */
    volatile uint32_t  mwcr;               /* ALT_SPIS_MWCR */
    volatile uint32_t  _pad_0x10_0x17[2];  /* *UNDEFINED* */
    volatile uint32_t  txftlr;             /* ALT_SPIS_TXFTLR */
    volatile uint32_t  rxftlr;             /* ALT_SPIS_RXFTLR */
    volatile uint32_t  txflr;              /* ALT_SPIS_TXFLR */
    volatile uint32_t  rxflr;              /* ALT_SPIS_RXFLR */
    volatile uint32_t  sr;                 /* ALT_SPIS_SR */
    volatile uint32_t  imr;                /* ALT_SPIS_IMR */
    volatile uint32_t  isr;                /* ALT_SPIS_ISR */
    volatile uint32_t  risr;               /* ALT_SPIS_RISR */
    volatile uint32_t  txoicr;             /* ALT_SPIS_TXOICR */
    volatile uint32_t  rxoicr;             /* ALT_SPIS_RXOICR */
    volatile uint32_t  rxuicr;             /* ALT_SPIS_RXUICR */
    volatile uint32_t  _pad_0x44_0x47;     /* *UNDEFINED* */
    volatile uint32_t  icr;                /* ALT_SPIS_ICR */
    volatile uint32_t  dmacr;              /* ALT_SPIS_DMACR */
    volatile uint32_t  dmatdlr;            /* ALT_SPIS_DMATDLR */
    volatile uint32_t  dmardlr;            /* ALT_SPIS_DMARDLR */
    volatile uint32_t  idr;                /* ALT_SPIS_IDR */
    volatile uint32_t  spi_version_id;     /* ALT_SPIS_SPI_VER_ID */
    volatile uint32_t  dr;                 /* ALT_SPIS_DR */
    volatile uint32_t  _pad_0x64_0x80[7];  /* *UNDEFINED* */
};

/* The typedef declaration for the raw register contents of register group ALT_SPIS. */
typedef volatile struct ALT_SPIS_raw_s  ALT_SPIS_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_SPIS_H__ */

